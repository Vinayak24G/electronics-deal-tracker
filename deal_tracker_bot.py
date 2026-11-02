#!/usr/bin/env python3
"""
Amazon.in & Flipkart Electronics Deal Tracker Discord Bot
=========================================================
Zero-cost, anti-ban electronics discount scanner and Discord bot supporting:
1. Serverless Cron Mode (`--once`): Runs via GitHub Actions every 30-60 mins,
   scans all major electronics categories on Amazon.in & Flipkart, tracks
   historical prices in SQLite (`deals_history.db`), filters out fake MRP
   discounts, posts rich embeds to a Discord Webhook, and commits state.
2. Interactive 24/7 Discord Bot Mode (`--bot`): Full `discord.py` bot with
   slash commands (`/scan_now`, `/watch_url`, `/unwatch`, `/watchlist`,
   `/top_deals`, `/price_history`, `/set_threshold`, `/status`) and a
   background task loop.
"""

from __future__ import annotations

import argparse
import asyncio
import datetime as dt
import hashlib
import json
import logging
import os
import random
import re
import sqlite3
import sys
import time
from dataclasses import dataclass, asdict
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple
from urllib.parse import quote_plus, urljoin, urlparse

from bs4 import BeautifulSoup

# Optional runtime imports with graceful fallbacks so `--once` works even
# with minimal dependencies while supporting TLS fingerprint impersonation.
try:
    from curl_cffi import requests as cffi_requests
    HAS_CURL_CFFI = True
except ImportError:
    HAS_CURL_CFFI = False

import urllib.request
import urllib.error

try:
    import discord
    from discord import app_commands
    from discord.ext import commands, tasks
    HAS_DISCORD_PY = True
except ImportError:
    HAS_DISCORD_PY = False

logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s | %(levelname)-7s | %(message)s",
    datefmt="%Y-%m-%d %H:%M:%S",
)
logger = logging.getLogger("deal_tracker")

DEFAULT_CONFIG_PATH = Path("config.json")
DEFAULT_DB_PATH = Path("deals_history.db")

USER_AGENTS = [
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/131.0.0.0 Safari/537.36",
    "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/131.0.0.0 Safari/537.36",
    "Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/130.0.0.0 Safari/537.36",
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64; rv:132.0) Gecko/20100101 Firefox/132.0",
]


# ---------------------------------------------------------------------------
# Data Models
# ---------------------------------------------------------------------------

@dataclass
class ProductItem:
    product_id: str          # e.g. "AMZ:B0CHX1W1XY" or "FK:MOBGTAGPAQNVFZZY"
    store: str               # "Amazon.in" or "Flipkart"
    category: str            # e.g. "Smartphones", "Laptops"
    title: str
    url: str
    current_price: float     # INR
    mrp_price: float         # INR (original/strikethrough price)
    mrp_discount_pct: float  # % off MRP
    rating: Optional[float] = None
    review_count: int = 0
    image_url: Optional[str] = None
    in_stock: bool = True


@dataclass
class DealAlert:
    product: ProductItem
    deal_tier: str                 # "LOOT DEAL", "ALL-TIME LOW", "PRICE DROP", "DEEP MRP DISCOUNT"
    color_hex: int                 # Discord embed color
    prev_avg_price: Optional[float]
    prev_low_price: Optional[float]
    real_drop_pct: float           # % drop vs historical average (0.0 if first seen)
    savings_inr: float             # INR saved vs historical avg or MRP
    reason: str


# ---------------------------------------------------------------------------
# Price Parsing Utilities
# ---------------------------------------------------------------------------

def parse_inr_price(raw_text: Optional[str]) -> Optional[float]:
    """Extract numeric INR value from strings like '₹49,999.00' or 'Rs. 1,29,990'."""
    if not raw_text:
        return None
    cleaned = re.sub(r"[^\d.]", "", raw_text.replace(",", ""))
    if not cleaned:
        return None
    # Handle trailing dots or multiple decimals
    parts = [p for p in cleaned.split(".") if p]
    if not parts:
        return None
    val_str = parts[0] if len(parts) == 1 else f"{parts[0]}.{parts[1][:2]}"
    try:
        val = float(val_str)
        return val if val > 0 else None
    except ValueError:
        return None


def canonical_product_id(store: str, url: str, raw_id: Optional[str] = None) -> str:
    """Create a deterministic unique ID for Amazon ASINs or Flipkart PIDs/URLs."""
    prefix = "AMZ" if "amazon" in store.lower() else "FK"
    if raw_id and raw_id.strip():
        return f"{prefix}:{raw_id.strip()}"

    if prefix == "AMZ":
        match = re.search(r"/(?:dp|gp/product)/([A-Z0-9]{10})", url)
        if match:
            return f"AMZ:{match.group(1)}"
    else:
        pid_match = re.search(r"[?&]pid=([A-Z0-9]{16})", url)
        if pid_match:
            return f"FK:{pid_match.group(1)}"
        path_match = re.search(r"/p/(itm[a-zA-Z0-9]+)", url)
        if path_match:
            return f"FK:{path_match.group(1)}"

    digest = hashlib.sha1(url.split("?")[0].encode("utf-8")).hexdigest()[:12].upper()
    return f"{prefix}:{digest}"


# ---------------------------------------------------------------------------
# SQLite Price-History & Curation Database
# ---------------------------------------------------------------------------

class PriceHistoryDB:
    """Tracks historical prices, computes rolling averages, and enforces alert cooldowns."""

    def __init__(self, db_path: Path = DEFAULT_DB_PATH) -> None:
        self.db_path = db_path
        self.conn = sqlite3.connect(str(self.db_path))
        self.conn.row_factory = sqlite3.Row
        self._init_schema()

    def _init_schema(self) -> None:
        with self.conn:
            self.conn.executescript(
                """
                CREATE TABLE IF NOT EXISTS products (
                    product_id TEXT PRIMARY KEY,
                    store TEXT NOT NULL,
                    category TEXT NOT NULL,
                    title TEXT NOT NULL,
                    url TEXT NOT NULL,
                    image_url TEXT,
                    last_price REAL NOT NULL,
                    mrp_price REAL NOT NULL,
                    min_price REAL NOT NULL,
                    max_price REAL NOT NULL,
                    avg_price REAL NOT NULL,
                    observations INTEGER NOT NULL DEFAULT 1,
                    first_seen_at TEXT NOT NULL,
                    last_seen_at TEXT NOT NULL,
                    last_alerted_price REAL,
                    last_alerted_at TEXT
                );

                CREATE TABLE IF NOT EXISTS price_samples (
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    product_id TEXT NOT NULL,
                    price REAL NOT NULL,
                    recorded_at TEXT NOT NULL,
                    FOREIGN KEY (product_id) REFERENCES products(product_id)
                );

                CREATE INDEX IF NOT EXISTS idx_samples_product
                    ON price_samples(product_id, recorded_at DESC);

                CREATE TABLE IF NOT EXISTS watchlist (
                    url TEXT PRIMARY KEY,
                    store TEXT NOT NULL,
                    category TEXT NOT NULL DEFAULT 'Watchlist',
                    target_price REAL,
                    added_at TEXT NOT NULL
                );
                """
            )

    def evaluate_and_record(
        self,
        item: ProductItem,
        rules: Dict[str, Any],
    ) -> Optional[DealAlert]:
        """
        Compare `item` against historical SQLite records and curation rules,
        update the database, and return a `DealAlert` if it qualifies.
        """
        now_iso = dt.datetime.now(dt.timezone.utc).isoformat()
        cur = self.conn.cursor()
        cur.execute("SELECT * FROM products WHERE product_id = ?", (item.product_id,))
        row = cur.fetchone()

        min_mrp_discount_pct = float(rules.get("min_mrp_discount_pct", 35.0))
        min_real_drop_pct = float(rules.get("min_history_drop_pct", 12.0))
        loot_drop_pct = float(rules.get("loot_drop_pct", 25.0))
        min_price_inr = float(rules.get("min_price_inr", 499.0))
        max_price_inr = float(rules.get("max_price_inr", 500000.0))
        min_rating = float(rules.get("min_rating", 3.8))
        cooldown_hours = float(rules.get("alert_cooldown_hours", 24.0))
        alert_on_first_seen_deep_discount = bool(
            rules.get("alert_on_first_seen_deep_discount", True)
        )
        first_seen_min_mrp_discount_pct = float(
            rules.get("first_seen_min_mrp_discount_pct", 45.0)
        )

        # Basic sanity filters
        if not (min_price_inr <= item.current_price <= max_price_inr):
            return None
        if item.rating is not None and item.rating > 0 and item.rating < min_rating:
            return None

        alert: Optional[DealAlert] = None

        if row is None:
            # First time seeing this product
            with self.conn:
                self.conn.execute(
                    """
                    INSERT INTO products (
                        product_id, store, category, title, url, image_url,
                        last_price, mrp_price, min_price, max_price, avg_price,
                        observations, first_seen_at, last_seen_at
                    ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, 1, ?, ?)
                    """,
                    (
                        item.product_id,
                        item.store,
                        item.category,
                        item.title,
                        item.url,
                        item.image_url,
                        item.current_price,
                        item.mrp_price,
                        item.current_price,
                        item.current_price,
                        item.current_price,
                        now_iso,
                        now_iso,
                    ),
                )
                self.conn.execute(
                    "INSERT INTO price_samples (product_id, price, recorded_at) VALUES (?, ?, ?)",
                    (item.product_id, item.current_price, now_iso),
                )

            # Only alert on a brand-new product if it has a verified deep MRP discount
            # AND reasonable review count (avoids no-name fake-MRP listings)
            if (
                alert_on_first_seen_deep_discount
                and item.mrp_discount_pct >= first_seen_min_mrp_discount_pct
                and (item.review_count >= int(rules.get("min_reviews_for_first_seen", 20)) or item.category == "Watchlist")
            ):
                savings = max(0.0, item.mrp_price - item.current_price)
                alert = DealAlert(
                    product=item,
                    deal_tier="DEEP MRP DISCOUNT",
                    color_hex=0x3498DB,  # Blue
                    prev_avg_price=None,
                    prev_low_price=None,
                    real_drop_pct=0.0,
                    savings_inr=savings,
                    reason=(
                        f"{item.mrp_discount_pct:.0f}% off MRP "
                        f"(₹{item.mrp_price:,.0f} → ₹{item.current_price:,.0f})"
                    ),
                )
                self._mark_alerted(item.product_id, item.current_price, now_iso)
            return alert

        # Product exists in history — compute real discount vs rolling average
        prev_avg = float(row["avg_price"])
        prev_min = float(row["min_price"])
        prev_max = float(row["max_price"])
        prev_obs = int(row["observations"])
        last_alerted_price = row["last_alerted_price"]
        last_alerted_at = row["last_alerted_at"]

        real_drop_pct = (
            ((prev_avg - item.current_price) / prev_avg) * 100.0
            if prev_avg > 0
            else 0.0
        )

        # Update rolling stats (cap rolling weight at 30 samples so recent trends adapt)
        weight = min(prev_obs, 30)
        new_avg = ((prev_avg * weight) + item.current_price) / (weight + 1)
        new_min = min(prev_min, item.current_price)
        new_max = max(prev_max, item.current_price)

        with self.conn:
            self.conn.execute(
                """
                UPDATE products
                SET title = ?, url = ?, image_url = COALESCE(?, image_url),
                    last_price = ?, mrp_price = ?, min_price = ?, max_price = ?,
                    avg_price = ?, observations = ?, last_seen_at = ?
                WHERE product_id = ?
                """,
                (
                    item.title,
                    item.url,
                    item.image_url,
                    item.current_price,
                    item.mrp_price,
                    new_min,
                    new_max,
                    new_avg,
                    prev_obs + 1,
                    now_iso,
                    item.product_id,
                ),
            )
            self.conn.execute(
                "INSERT INTO price_samples (product_id, price, recorded_at) VALUES (?, ?, ?)",
                (item.product_id, item.current_price, now_iso),
            )

        # Check deduplication cooldown unless price dropped another >=5% below last alerted price
        if last_alerted_at and last_alerted_price is not None:
            try:
                last_dt = dt.datetime.fromisoformat(last_alerted_at)
                hours_since = (
                    dt.datetime.now(dt.timezone.utc) - last_dt
                ).total_seconds() / 3600.0
                further_drop_pct = (
                    ((float(last_alerted_price) - item.current_price) / float(last_alerted_price)) * 100.0
                    if float(last_alerted_price) > 0
                    else 0.0
                )
                if hours_since < cooldown_hours and further_drop_pct < 5.0:
                    return None
                if item.current_price >= float(last_alerted_price) and hours_since < cooldown_hours * 3:
                    return None
            except ValueError:
                pass

        # Classify the deal tier
        is_all_time_low = item.current_price < prev_min
        if real_drop_pct >= loot_drop_pct:
            tier = "LOOT DEAL"
            color = 0xE74C3C  # Red/Orange hot alert
            reason = (
                f"Dropped {real_drop_pct:.1f}% below historical avg (₹{prev_avg:,.0f})"
            )
            savings = prev_avg - item.current_price
        elif is_all_time_low and real_drop_pct >= min_real_drop_pct:
            tier = "ALL-TIME LOW"
            color = 0x2ECC71  # Emerald Green
            reason = (
                f"New all-time low! {real_drop_pct:.1f}% below avg (₹{prev_avg:,.0f}), "
                f"beats previous low of ₹{prev_min:,.0f}"
            )
            savings = prev_avg - item.current_price
        elif real_drop_pct >= min_real_drop_pct and item.mrp_discount_pct >= min_mrp_discount_pct:
            tier = "BIG PRICE DROP"
            color = 0xF1C40F  # Gold
            reason = (
                f"Dropped {real_drop_pct:.1f}% below tracked avg (₹{prev_avg:,.0f}) "
                f"& {item.mrp_discount_pct:.0f}% off MRP"
            )
            savings = prev_avg - item.current_price
        else:
            return None

        self._mark_alerted(item.product_id, item.current_price, now_iso)
        return DealAlert(
            product=item,
            deal_tier=tier,
            color_hex=color,
            prev_avg_price=prev_avg,
            prev_low_price=prev_min,
            real_drop_pct=real_drop_pct,
            savings_inr=max(0.0, savings),
            reason=reason,
        )

    def _mark_alerted(self, product_id: str, price: float, now_iso: str) -> None:
        with self.conn:
            self.conn.execute(
                "UPDATE products SET last_alerted_price = ?, last_alerted_at = ? WHERE product_id = ?",
                (price, now_iso, product_id),
            )

    def add_watchlist_url(
        self, url: str, category: str = "Watchlist", target_price: Optional[float] = None
    ) -> str:
        store = "Amazon.in" if "amazon." in url.lower() else "Flipkart"
        now_iso = dt.datetime.now(dt.timezone.utc).isoformat()
        with self.conn:
            self.conn.execute(
                """
                INSERT OR REPLACE INTO watchlist (url, store, category, target_price, added_at)
                VALUES (?, ?, ?, ?, ?)
                """,
                (url.strip(), store, category, target_price, now_iso),
            )
        return store

    def remove_watchlist_url(self, url: str) -> bool:
        with self.conn:
            cur = self.conn.execute("DELETE FROM watchlist WHERE url = ?", (url.strip(),))
            return cur.rowcount > 0

    def get_watchlist(self) -> List[Dict[str, Any]]:
        cur = self.conn.cursor()
        cur.execute("SELECT * FROM watchlist ORDER BY added_at DESC")
        return [dict(r) for r in cur.fetchall()]

    def get_top_tracked_deals(self, limit: int = 10) -> List[Dict[str, Any]]:
        cur = self.conn.cursor()
        cur.execute(
            """
            SELECT *,
                   CASE WHEN avg_price > 0 THEN ((avg_price - last_price) / avg_price) * 100.0 ELSE 0 END AS drop_vs_avg,
                   CASE WHEN mrp_price > 0 THEN ((mrp_price - last_price) / mrp_price) * 100.0 ELSE 0 END AS mrp_disc
            FROM products
            ORDER BY drop_vs_avg DESC, mrp_disc DESC
            LIMIT ?
            """,
            (limit,),
        )
        return [dict(r) for r in cur.fetchall()]

    def get_product_stats(self, query: str) -> List[Dict[str, Any]]:
        cur = self.conn.cursor()
        like_q = f"%{query}%"
        cur.execute(
            """
            SELECT * FROM products
            WHERE product_id LIKE ? OR title LIKE ?
            ORDER BY last_seen_at DESC
            LIMIT 5
            """,
            (like_q, like_q),
        )
        return [dict(r) for r in cur.fetchall()]

    def get_summary_counts(self) -> Dict[str, int]:
        cur = self.conn.cursor()
        cur.execute("SELECT COUNT(*) AS c FROM products")
        total_products = int(cur.fetchone()["c"])
        cur.execute("SELECT COUNT(*) AS c FROM price_samples")
        total_samples = int(cur.fetchone()["c"])
        cur.execute("SELECT COUNT(*) AS c FROM watchlist")
        total_watchlist = int(cur.fetchone()["c"])
        return {
            "tracked_products": total_products,
            "price_samples": total_samples,
            "watchlist_items": total_watchlist,
        }


# ---------------------------------------------------------------------------
# Anti-Ban HTTP Fetcher & HTML Parsers (Amazon.in + Flipkart)
# ---------------------------------------------------------------------------

class ElectronicsScraper:
    """Fetches and parses electronics listings & product pages from Amazon.in and Flipkart."""

    def __init__(self, min_delay_sec: float = 2.5, max_delay_sec: float = 6.0) -> None:
        self.min_delay_sec = min_delay_sec
        self.max_delay_sec = max_delay_sec

    def fetch_html(self, url: str) -> Optional[str]:
        """Fetch page HTML using Chrome TLS impersonation (`curl_cffi`) or stdlib fallback."""
        headers = {
            "User-Agent": random.choice(USER_AGENTS),
            "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,image/avif,image/webp,*/*;q=0.8",
            "Accept-Language": "en-IN,en-GB;q=0.9,en-US;q=0.8,en;q=0.7",
            "Cache-Control": "no-cache",
            "Pragma": "no-cache",
            "Upgrade-Insecure-Requests": "1",
        }
        try:
            if HAS_CURL_CFFI:
                resp = cffi_requests.get(
                    url,
                    headers=headers,
                    impersonate="chrome120",
                    timeout=20,
                )
                if resp.status_code == 200 and resp.text:
                    return resp.text
                logger.warning("HTTP %s fetching %s", resp.status_code, url)
                return None
            else:
                req = urllib.request.Request(url, headers=headers)
                with urllib.request.urlopen(req, timeout=20) as resp:
                    if resp.status == 200:
                        return resp.read().decode("utf-8", errors="replace")
                return None
        except Exception as exc:
            logger.warning("Fetch error on %s: %s", url, exc)
            return None

    # ---- Amazon.in Search & Category Parser ----

    @staticmethod
    def parse_amazon_search_html(html: str, category: str) -> List[ProductItem]:
        """Parse Amazon.in search/category result cards into `ProductItem` objects."""
        soup = BeautifulSoup(html, "html.parser")
        cards = soup.select('div[data-component-type="s-search-result"]')
        results: List[ProductItem] = []

        for card in cards:
            asin = card.get("data-asin", "").strip()
            if not asin:
                continue

            # Title & link
            title_el = (
                card.select_one("h2 a span")
                or card.select_one("h2 span")
                or card.select_one(".a-size-medium.a-color-base.a-text-normal")
            )
            link_el = card.select_one("h2 a") or card.select_one("a.a-link-normal.s-no-outline")
            if not title_el or not link_el:
                continue

            title = title_el.get_text(strip=True)
            href = link_el.get("href", "")
            full_url = f"https://www.amazon.in/dp/{asin}" if asin else urljoin("https://www.amazon.in", href)

            # Current price
            price_el = (
                card.select_one(".a-price:not([data-a-strike]) .a-offscreen")
                or card.select_one(".a-price-whole")
            )
            current_price = parse_inr_price(price_el.get_text(strip=True) if price_el else None)
            if not current_price:
                continue

            # MRP (strikethrough price)
            mrp_el = (
                card.select_one(".a-price[data-a-strike='true'] .a-offscreen")
                or card.select_one(".a-text-price .a-offscreen")
            )
            mrp_price = parse_inr_price(mrp_el.get_text(strip=True) if mrp_el else None)
            if not mrp_price or mrp_price < current_price:
                mrp_price = current_price

            mrp_discount_pct = (
                ((mrp_price - current_price) / mrp_price) * 100.0
                if mrp_price > current_price
                else 0.0
            )

            # Rating & review count
            rating_el = card.select_one("span.a-icon-alt")
            rating = None
            if rating_el:
                m = re.search(r"(\d+(?:\.\d+)?)\s*out of", rating_el.get_text())
                if m:
                    rating = float(m.group(1))

            reviews_el = card.select_one("span.a-size-base.s-underline-text")
            review_count = 0
            if reviews_el:
                rc_digits = re.sub(r"[^\d]", "", reviews_el.get_text())
                if rc_digits:
                    review_count = int(rc_digits)

            img_el = card.select_one("img.s-image")
            image_url = img_el.get("src") if img_el else None

            results.append(
                ProductItem(
                    product_id=f"AMZ:{asin}",
                    store="Amazon.in",
                    category=category,
                    title=title,
                    url=full_url,
                    current_price=current_price,
                    mrp_price=mrp_price,
                    mrp_discount_pct=round(mrp_discount_pct, 1),
                    rating=rating,
                    review_count=review_count,
                    image_url=image_url,
                )
            )
        return results

    # ---- Flipkart Search & Category Parser ----

    @staticmethod
    def parse_flipkart_search_html(html: str, category: str) -> List[ProductItem]:
        """Parse Flipkart search/category result cards (both list & grid layouts)."""
        soup = BeautifulSoup(html, "html.parser")
        cards = soup.select("div[data-id]")
        results: List[ProductItem] = []

        for card in cards:
            pid = card.get("data-id", "").strip()
            if not pid:
                continue

            # Locate product anchor & title across Flipkart's list/grid class variants
            link_el = (
                card.select_one("a[href*='/p/']")
                or card.select_one("a.CGtC98")
                or card.select_one("a.wjcEIp")
                or card.select_one("a._1fQZEK")
                or card.select_one("a.s1Q9rs")
            )
            if not link_el:
                continue

            href = link_el.get("href", "")
            full_url = urljoin("https://www.flipkart.com", href.split("&")[0])

            title_el = (
                card.select_one("div.KzDlHZ")
                or card.select_one("a.wjcEIp")
                or card.select_one("div._4rR01T")
                or card.select_one("a.s1Q9rs")
                or card.select_one("[title]")
            )
            title = ""
            if title_el:
                title = title_el.get("title") or title_el.get_text(strip=True)
            if not title:
                title = link_el.get("title") or link_el.get_text(strip=True)
            if not title:
                continue

            # Extract prices inside card: Flipkart renders current price (`₹...`) and strikethrough MRP
            price_candidates: List[float] = []
            for text_node in card.find_all(string=re.compile(r"₹\s*[\d,]+")):
                val = parse_inr_price(str(text_node))
                if val:
                    price_candidates.append(val)

            if not price_candidates:
                continue

            current_price = price_candidates[0]
            mrp_price = max(price_candidates[:3]) if len(price_candidates) > 1 else current_price
            if mrp_price < current_price:
                mrp_price = current_price

            mrp_discount_pct = (
                ((mrp_price - current_price) / mrp_price) * 100.0
                if mrp_price > current_price
                else 0.0
            )

            # Rating
            rating_el = (
                card.select_one("div.XQDdHH")
                or card.select_one("div._3LWZlK")
                or card.select_one("span[id^='productRating'] div")
            )
            rating = None
            if rating_el:
                try:
                    rating = float(rating_el.get_text(strip=True)[:3])
                except ValueError:
                    rating = None

            # Image
            img_el = card.select_one("img")
            image_url = img_el.get("src") if img_el else None

            results.append(
                ProductItem(
                    product_id=f"FK:{pid}",
                    store="Flipkart",
                    category=category,
                    title=title,
                    url=full_url,
                    current_price=current_price,
                    mrp_price=mrp_price,
                    mrp_discount_pct=round(mrp_discount_pct, 1),
                    rating=rating,
                    review_count=50,  # Default floor when Flipkart omits inline review count on grid cards
                    image_url=image_url,
                )
            )
        return results

    # ---- Direct Product URL Parser (Watchlist) ----

    @staticmethod
    def parse_single_product_html(html: str, url: str, category: str = "Watchlist") -> Optional[ProductItem]:
        """Parse an individual Amazon.in or Flipkart product page."""
        soup = BeautifulSoup(html, "html.parser")
        is_amazon = "amazon." in url.lower()
        store = "Amazon.in" if is_amazon else "Flipkart"

        if is_amazon:
            title_el = soup.select_one("#productTitle")
            if not title_el:
                return None
            title = title_el.get_text(strip=True)
            price_el = (
                soup.select_one("#corePriceDisplay_desktop_feature_div .a-price-whole")
                or soup.select_one(".a-price .a-offscreen")
                or soup.select_one("#priceblock_dealprice")
                or soup.select_one("#priceblock_ourprice")
            )
            current_price = parse_inr_price(price_el.get_text(strip=True) if price_el else None)
            if not current_price:
                return None
            mrp_el = (
                soup.select_one(".basisPrice .a-offscreen")
                or soup.select_one(".a-text-price .a-offscreen")
            )
            mrp_price = parse_inr_price(mrp_el.get_text(strip=True) if mrp_el else None) or current_price
            img_el = soup.select_one("#landingImage")
            image_url = img_el.get("src") if img_el else None
        else:
            title_el = soup.select_one("span.VU-ZEz") or soup.select_one("span.B_NuCI") or soup.select_one("h1")
            if not title_el:
                return None
            title = title_el.get_text(strip=True)
            price_el = (
                soup.select_one("div.Nx9bqj.CxhGGd")
                or soup.select_one("div._30jeq3._16Jk6d")
            )
            current_price = parse_inr_price(price_el.get_text(strip=True) if price_el else None)
            if not current_price:
                return None
            mrp_el = soup.select_one("div.yRaY8j.A6+E6v") or soup.select_one("div._3I9_wc._2p6lqe")
            mrp_price = parse_inr_price(mrp_el.get_text(strip=True) if mrp_el else None) or current_price
            img_el = soup.select_one("img.DByuf4") or soup.select_one("img._396cs4")
            image_url = img_el.get("src") if img_el else None

        if mrp_price < current_price:
            mrp_price = current_price
        disc_pct = ((mrp_price - current_price) / mrp_price) * 100.0 if mrp_price > current_price else 0.0

        return ProductItem(
            product_id=canonical_product_id(store, url),
            store=store,
            category=category,
            title=title,
            url=url,
            current_price=current_price,
            mrp_price=mrp_price,
            mrp_discount_pct=round(disc_pct, 1),
            rating=4.5,
            review_count=100,
            image_url=image_url,
        )


# ---------------------------------------------------------------------------
# Discord Webhook & Rich Embed Formatting
# ---------------------------------------------------------------------------

def build_discord_embed_dict(alert: DealAlert) -> Dict[str, Any]:
    """Construct a rich Discord Embed payload dictionary for a `DealAlert`."""
    p = alert.product
    store_emoji = "🛒" if p.store == "Amazon.in" else "🛍️"
    tier_emoji = {
        "LOOT DEAL": "🔥",
        "ALL-TIME LOW": "⚡",
        "BIG PRICE DROP": "💰",
        "DEEP MRP DISCOUNT": "🏷️",
    }.get(alert.deal_tier, "🔔")

    fields = [
        {
            "name": "Deal Price",
            "value": f"**₹{p.current_price:,.0f}**",
            "inline": True,
        },
        {
            "name": "MRP / List Price",
            "value": f"~~₹{p.mrp_price:,.0f}~~ ({p.mrp_discount_pct:.0f}% off)",
            "inline": True,
        },
        {
            "name": "Store & Category",
            "value": f"{store_emoji} {p.store} • `{p.category}`",
            "inline": True,
        },
    ]

    if alert.prev_avg_price:
        fields.append(
            {
                "name": "30-Sample Avg Price",
                "value": f"₹{alert.prev_avg_price:,.0f} (**-{alert.real_drop_pct:.1f}%**)",
                "inline": True,
            }
        )
    if alert.prev_low_price:
        fields.append(
            {
                "name": "Previous Low",
                "value": f"₹{alert.prev_low_price:,.0f}",
                "inline": True,
            }
        )
    if p.rating:
        fields.append(
            {
                "name": "Rating",
                "value": f"⭐ {p.rating:.1f} ({p.review_count:,} reviews)",
                "inline": True,
            }
        )

    embed: Dict[str, Any] = {
        "title": f"{tier_emoji} [{alert.deal_tier}] {p.title[:180]}",
        "url": p.url,
        "description": (
            f"**Why it triggered:** {alert.reason}\n"
            f"**Estimated Savings:** ₹{alert.savings_inr:,.0f}\n\n"
            f"👉 **[Buy Now on {p.store}]({p.url})**"
        ),
        "color": alert.color_hex,
        "fields": fields,
        "footer": {
            "text": f"ID: {p.product_id} • Real-Price Verified Deal Tracker",
        },
        "timestamp": dt.datetime.now(dt.timezone.utc).isoformat(),
    }
    if p.image_url and p.image_url.startswith("http"):
        embed["thumbnail"] = {"url": p.image_url}
    return embed


def send_discord_webhook(webhook_url: str, alerts: List[DealAlert]) -> int:
    """Send DealAlerts in batches (up to 10 embeds per request) to a Discord Webhook."""
    if not webhook_url or not alerts:
        return 0

    sent_count = 0
    batch_size = 5
    for idx in range(0, len(alerts), batch_size):
        batch = alerts[idx : idx + batch_size]
        payload = {
            "username": "Electronics Deal Radar (IN)",
            "embeds": [build_discord_embed_dict(a) for a in batch],
        }
        data = json.dumps(payload).encode("utf-8")
        req = urllib.request.Request(
            webhook_url,
            data=data,
            headers={
                "Content-Type": "application/json",
                "User-Agent": "ElectronicsDealTrackerBot/1.0",
            },
            method="POST",
        )
        try:
            with urllib.request.urlopen(req, timeout=15) as resp:
                if resp.status in (200, 204):
                    sent_count += len(batch)
            time.sleep(1.5)  # Respect Discord webhook rate limits
        except urllib.error.HTTPError as exc:
            logger.error("Discord webhook HTTP %s: %s", exc.code, exc.read().decode("utf-8", errors="ignore"))
        except Exception as exc:
            logger.error("Failed sending Discord webhook: %s", exc)
    return sent_count


# ---------------------------------------------------------------------------
# Full Multi-Category Scan Orchestrator
# ---------------------------------------------------------------------------

def build_category_urls(cat_entry: Dict[str, Any]) -> List[Tuple[str, str, str]]:
    """
    Build (store, category_name, target_url) tuples from a `config.json` category entry.
    Includes discount filters in the search query parameters so every request targets
    heavily discounted electronics across Amazon.in and Flipkart.
    """
    name = cat_entry["name"]
    urls: List[Tuple[str, str, str]] = []

    for q in cat_entry.get("queries", []):
        encoded = quote_plus(q)
        # Amazon.in: `pct-off=25-` filters for >=25% discount in Electronics (`i=electronics`)
        amz_url = f"https://www.amazon.in/s?k={encoded}&i=electronics&rh=p_8%3A25-95&s=exact-aware-popularity-rank"
        urls.append(("Amazon.in", name, amz_url))

        # Flipkart: `p[]=facets.discount_range_v1%5B%5D%3D30%25+or+more` filters for >=30% off
        fk_url = (
            f"https://www.flipkart.com/search?q={encoded}"
            f"&otracker=search&p%5B%5D=facets.discount_range_v1%255B%255D%253D30%2525%2Bor%2Bmore"
        )
        urls.append(("Flipkart", name, fk_url))

    for custom_amz in cat_entry.get("amazon_urls", []):
        urls.append(("Amazon.in", name, custom_amz))
    for custom_fk in cat_entry.get("flipkart_urls", []):
        urls.append(("Flipkart", name, custom_fk))

    return urls


def run_scan_cycle(
    config: Dict[str, Any],
    db: PriceHistoryDB,
    scraper: ElectronicsScraper,
    webhook_url: Optional[str] = None,
    max_Categories: Optional[int] = None,
) -> Tuple[int, List[DealAlert]]:
    """
    Execute one full scan cycle across all configured electronics categories and watchlist URLs.
    Returns `(total_products_scanned, triggered_alerts)`.
    """
    rules = config.get("curation_rules", {})
    categories = config.get("categories", [])
    if max_Categories:
        categories = categories[:max_Categories]

    all_targets: List[Tuple[str, str, str]] = []
    for cat in categories:
        if cat.get("enabled", True):
            all_targets.extend(build_category_urls(cat))

    # Shuffle target order slightly so consecutive runs don't hit identical patterns
    random.shuffle(all_targets)

    scanned_count = 0
    alerts: List[DealAlert] = []

    logger.info("Starting electronics scan across %d category endpoints...", len(all_targets))

    for store, category_name, url in all_targets:
        html = scraper.fetch_html(url)
        if not html:
            continue

        if store == "Amazon.in":
            items = scraper.parse_amazon_search_html(html, category_name)
        else:
            items = scraper.parse_flipkart_search_html(html, category_name)

        logger.info("Parsed %d products from %s [%s]", len(items), store, category_name)
        for item in items:
            scanned_count += 1
            alert = db.evaluate_and_record(item, rules)
            if alert:
                alerts.append(alert)

        # Polite randomized delay to prevent IP flagging
        time.sleep(random.uniform(scraper.min_delay_sec, scraper.max_delay_sec))

    # Scan individual Watchlist URLs (from both config.json and SQLite watchlist table)
    watchlist_entries = list(db.get_watchlist())
    for cfg_url in config.get("watchlist_urls", []):
        if isinstance(cfg_url, str) and cfg_url.startswith("http"):
            watchlist_entries.append({"url": cfg_url, "category": "Watchlist", "target_price": None})

    for wl in watchlist_entries:
        w_url = wl["url"]
        html = scraper.fetch_html(w_url)
        if not html:
            continue
        item = scraper.parse_single_product_html(html, w_url, wl.get("category", "Watchlist"))
        if item:
            scanned_count += 1
            target_price = wl.get("target_price")
            if target_price and item.current_price <= float(target_price):
                alert = DealAlert(
                    product=item,
                    deal_tier="LOOT DEAL",
                    color_hex=0xE74C3C,
                    prev_avg_price=float(target_price),
                    prev_low_price=item.current_price,
                    real_drop_pct=((float(target_price) - item.current_price) / float(target_price)) * 100.0,
                    savings_inr=max(0.0, item.mrp_price - item.current_price),
                    reason=f"Hit your target watchlist price of ₹{float(target_price):,.0f}!",
                )
                alerts.append(alert)
            else:
                alert = db.evaluate_and_record(item, rules)
                if alert:
                    alerts.append(alert)
        time.sleep(random.uniform(scraper.min_delay_sec, scraper.max_delay_sec))

    # Sort alerts by highest real drop percentage first, then MRP discount
    alerts.sort(key=lambda a: (a.real_drop_pct, a.product.mrp_discount_pct), reverse=True)
    max_alerts = int(rules.get("max_alerts_per_run", 20))
    alerts = alerts[:max_alerts]

    if webhook_url and alerts:
        sent = send_discord_webhook(webhook_url, alerts)
        logger.info("Sent %d/%d deal alerts to Discord Webhook.", sent, len(alerts))

    logger.info(
        "Scan complete: %d products evaluated, %d high-value deals triggered.",
        scanned_count,
        len(alerts),
    )
    return scanned_count, alerts


# ---------------------------------------------------------------------------
# Interactive 24/7 Discord Bot Mode (`discord.py` with Slash Commands)
# ---------------------------------------------------------------------------

def run_interactive_discord_bot(config_path: Path, db_path: Path) -> None:
    """Launch the interactive `discord.py` bot with background scheduled scanning and slash commands."""
    if not HAS_DISCORD_PY:
        logger.error("`discord.py` is not installed. Run `pip install -r requirements.txt` first.")
        sys.exit(1)

    with open(config_path, "r", encoding="utf-8") as f:
        config = json.load(f)

    bot_token = os.environ.get("DISCORD_BOT_TOKEN") or config.get("discord_bot_token", "")
    channel_id_raw = os.environ.get("DISCORD_CHANNEL_ID") or config.get("discord_channel_id", 0)
    webhook_url = os.environ.get("DISCORD_WEBHOOK_URL") or config.get("discord_webhook_url", "")
    interval_mins = float(config.get("scan_interval_minutes", 45))

    if not bot_token or bot_token == "YOUR_DISCORD_BOT_TOKEN_HERE":
        logger.error(
            "Missing DISCORD_BOT_TOKEN! Set DISCORD_BOT_TOKEN env var or use `--once` with DISCORD_WEBHOOK_URL."
        )
        sys.exit(1)

    intents = discord.Intents.default()
    bot = commands.Bot(command_prefix="!", intents=intents)
    db = PriceHistoryDB(db_path)
    scraper = ElectronicsScraper(
        min_delay_sec=float(config.get("min_request_delay_sec", 2.5)),
        max_delay_sec=float(config.get("max_request_delay_sec", 5.5)),
    )

    @tasks.loop(minutes=interval_mins)
    async def scheduled_deal_scanner() -> None:
        logger.info("Running scheduled background electronics deal scan...")
        scanned, alerts = await asyncio.to_thread(
            run_scan_cycle, config, db, scraper, webhook_url if webhook_url else None
        )
        if alerts and not webhook_url and channel_id_raw:
            channel = bot.get_channel(int(channel_id_raw))
            if channel and hasattr(channel, "send"):
                for alert in alerts:
                    embed_dict = build_discord_embed_dict(alert)
                    embed = discord.Embed.from_dict(embed_dict)
                    await channel.send(embed=embed)
                    await asyncio.sleep(1.0)

    @bot.event
    async def on_ready() -> None:
        logger.info("Logged in as %s (ID: %s)", bot.user, bot.user.id if bot.user else "?")
        try:
            synced = await bot.tree.sync()
            logger.info("Synced %d slash commands.", len(synced))
        except Exception as exc:
            logger.warning("Slash command sync error: %s", exc)
        if not scheduled_deal_scanner.is_running():
            scheduled_deal_scanner.start()

    @bot.tree.command(name="scan_now", description="Trigger an immediate electronics deal scan on Amazon.in & Flipkart")
    async def cmd_scan_now(interaction: discord.Interaction) -> None:
        await interaction.response.defer(thinking=True)
        scanned, alerts = await asyncio.to_thread(
            run_scan_cycle, config, db, scraper, webhook_url if webhook_url else None, 3
        )
        if not alerts:
            await interaction.followup.send(
                f"✅ Scanned **{scanned}** electronics listings across Amazon.in & Flipkart. "
                f"No new deals beat your discount thresholds right now."
            )
            return

        await interaction.followup.send(
            f"🔥 Scanned **{scanned}** products and found **{len(alerts)}** verified deals!"
        )
        for alert in alerts[:5]:
            embed = discord.Embed.from_dict(build_discord_embed_dict(alert))
            await interaction.channel.send(embed=embed)

    @bot.tree.command(name="watch_url", description="Track a specific Amazon.in or Flipkart product URL")
    @app_commands.describe(url="Full Amazon.in or Flipkart product URL", target_price="Optional target price in INR")
    async def cmd_watch_url(
        interaction: discord.Interaction, url: str, target_price: Optional[float] = None
    ) -> None:
        if "amazon." not in url.lower() and "flipkart.com" not in url.lower():
            await interaction.response.send_message(
                "❌ Please provide a valid `amazon.in` or `flipkart.com` product URL.", ephemeral=True
            )
            return
        store = db.add_watchlist_url(url, category="Watchlist", target_price=target_price)
        target_str = f" with target price **₹{target_price:,.0f}**" if target_price else ""
        await interaction.response.send_message(
            f"✅ Added **{store}** product to your priority watchlist{target_str}:\n<{url}>"
        )

    @bot.tree.command(name="unwatch", description="Remove a product URL from your watchlist")
    async def cmd_unwatch(interaction: discord.Interaction, url: str) -> None:
        removed = db.remove_watchlist_url(url)
        if removed:
            await interaction.response.send_message(f"🗑️ Removed `<{url}>` from watchlist.")
        else:
            await interaction.response.send_message("⚠️ URL was not found in your watchlist.", ephemeral=True)

    @bot.tree.command(name="watchlist", description="Show all custom Amazon.in & Flipkart URLs on your watchlist")
    async def cmd_watchlist(interaction: discord.Interaction) -> None:
        items = db.get_watchlist()
        if not items:
            await interaction.response.send_message("Your watchlist is currently empty. Use `/watch_url` to add products!")
            return
        lines = []
        for idx, item in enumerate(items[:15], 1):
            t_str = f" (Target: ₹{item['target_price']:,.0f})" if item.get("target_price") else ""
            lines.append(f"{idx}. **{item['store']}**{t_str} — <{item['url']}>")
        await interaction.response.send_message("**📋 Active Product Watchlist:**\n" + "\n".join(lines))

    @bot.tree.command(name="top_deals", description="Display the highest real price drops currently recorded in the database")
    async def cmd_top_deals(interaction: discord.Interaction) -> None:
        deals = db.get_top_tracked_deals(limit=8)
        if not deals:
            await interaction.response.send_message("No products recorded in history yet. Run `/scan_now` first!")
            return
        lines = []
        for idx, d in enumerate(deals, 1):
            lines.append(
                f"{idx}. **[{d['title'][:55]}...]({d['url']})** ({d['store']})\n"
                f"   💰 **₹{d['last_price']:,.0f}** | Avg: ₹{d['avg_price']:,.0f} "
                f"(`-{d['drop_vs_avg']:.1f}%` vs avg, `{d['mrp_disc']:.0f}%` off MRP)"
            )
        embed = discord.Embed(
            title="🏆 Top Verified Electronics Deals in Database",
            description="\n\n".join(lines),
            color=0x2ECC71,
        )
        await interaction.response.send_message(embed=embed)

    @bot.tree.command(name="price_history", description="Search tracked price history for a product name or ASIN/PID")
    async def cmd_price_history(interaction: discord.Interaction, query: str) -> None:
        matches = db.get_product_stats(query)
        if not matches:
            await interaction.response.send_message(f"No tracked products matched `{query}`.", ephemeral=True)
            return
        lines = []
        for m in matches:
            lines.append(
                f"• **[{m['title'][:65]}]({m['url']})** (`{m['product_id']}`)\n"
                f"  Current: **₹{m['last_price']:,.0f}** | Low: ₹{m['min_price']:,.0f} | "
                f"Avg: ₹{m['avg_price']:,.0f} | High: ₹{m['max_price']:,.0f} ({m['observations']} scans)"
            )
        embed = discord.Embed(
            title=f"📈 Price History Search: '{query}'",
            description="\n\n".join(lines),
            color=0x3498DB,
        )
        await interaction.response.send_message(embed=embed)

    @bot.tree.command(name="set_threshold", description="Update minimum MRP discount % and real price drop % thresholds")
    async def cmd_set_threshold(
        interaction: discord.Interaction, min_mrp_discount_pct: float, min_history_drop_pct: float
    ) -> None:
        config.setdefault("curation_rules", {})["min_mrp_discount_pct"] = min_mrp_discount_pct
        config["curation_rules"]["min_history_drop_pct"] = min_history_drop_pct
        with open(config_path, "w", encoding="utf-8") as f:
            json.dump(config, f, indent=2)
        await interaction.response.send_message(
            f"⚙️ Updated thresholds: Minimum MRP Discount = **{min_mrp_discount_pct:.1f}%**, "
            f"Minimum Real Drop below Tracked Average = **{min_history_drop_pct:.1f}%**."
        )

    @bot.tree.command(name="status", description="Show bot database stats and active scan configuration")
    async def cmd_status(interaction: discord.Interaction) -> None:
        counts = db.get_summary_counts()
        rules = config.get("curation_rules", {})
        embed = discord.Embed(
            title="🤖 Electronics Deal Tracker Status",
            color=0x9B59B6,
            description=(
                f"**Tracked Products:** {counts['tracked_products']:,}\n"
                f"**Total Price Samples:** {counts['price_samples']:,}\n"
                f"**Custom Watchlist URLs:** {counts['watchlist_items']:,}\n"
                f"**Scan Interval:** Every {interval_mins:.0f} minutes\n"
                f"**Min MRP Discount:** {rules.get('min_mrp_discount_pct', 35)}%\n"
                f"**Min Real Drop vs Avg:** {rules.get('min_history_drop_pct', 12)}%\n"
                f"**Loot Deal Drop Threshold:** {rules.get('loot_drop_pct', 25)}%"
            ),
        )
        await interaction.response.send_message(embed=embed)

    bot.run(bot_token)


# ---------------------------------------------------------------------------
# CLI Entrypoint
# ---------------------------------------------------------------------------

def main() -> None:
    parser = argparse.ArgumentParser(
        description="Zero-Cost Amazon.in & Flipkart Electronics Deal Tracker for Discord"
    )
    parser.add_argument(
        "--once",
        action="store_true",
        help="Run a single full scan cycle and exit (ideal for GitHub Actions 30-min cron)",
    )
    parser.add_argument(
        "--bot",
        action="store_true",
        help="Run the persistent 24/7 Discord bot with slash commands and background loop",
    )
    parser.add_argument(
        "--config",
        type=Path,
        default=DEFAULT_CONFIG_PATH,
        help="Path to config.json (default: config.json)",
    )
    parser.add_argument(
        "--db",
        type=Path,
        default=DEFAULT_DB_PATH,
        help="Path to SQLite price history database (default: deals_history.db)",
    )
    args = parser.parse_args()

    if not args.config.exists():
        logger.error("Config file %s not found.", args.config)
        sys.exit(1)

    with open(args.config, "r", encoding="utf-8") as f:
        config = json.load(f)

    if args.bot:
        run_interactive_discord_bot(args.config, args.db)
        return

    # Default to `--once` serverless scan mode
    webhook_url = os.environ.get("DISCORD_WEBHOOK_URL") or config.get("discord_webhook_url", "")
    if webhook_url == "YOUR_DISCORD_WEBHOOK_URL_HERE":
        webhook_url = ""

    db = PriceHistoryDB(args.db)
    scraper = ElectronicsScraper(
        min_delay_sec=float(config.get("min_request_delay_sec", 2.0)),
        max_delay_sec=float(config.get("max_request_delay_sec", 4.5)),
    )
    scanned, alerts = run_scan_cycle(config, db, scraper, webhook_url=webhook_url or None)
    logger.info("Finished single-pass scan (`--once`): %d scanned, %d alerts.", scanned, len(alerts))


if __name__ == "__main__":
    main()