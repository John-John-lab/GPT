"""
Database Management Module for Bybit Signal App

This module handles all database-related functionality including:
- Parquet file management and monitoring
- Database verification and integrity checks
- Data analysis UI and callbacks
- Database maintenance operations

This module is intentionally isolated from:
- Bybit API download logic
- Strategy detection
- Impulse trading logic
- Event analysis
"""

import os
import json
import time
import threading
import queue
import hashlib
import shutil
import uuid
from datetime import datetime, timezone
import pandas as pd
import numpy as np
import pyarrow.parquet as pq

# Dash imports
from dash import dcc, html, Input, Output, State, MATCH, ALL, no_update, ctx
import plotly.express as px
import plotly.graph_objects as go
from plotly.subplots import make_subplots

# Optional DuckDB support
try:
    import duckdb
    DUCKDB_AVAILABLE = True
except ImportError:
    DUCKDB_AVAILABLE = False
    print("DuckDB not installed. The DuckDB query button will not work. Install with: pip install duckdb")

# =============================================================================
# CONSTANTS (must match main app)
# =============================================================================
MARKET_DATA_DIR = "./market_data"
os.makedirs(MARKET_DATA_DIR, exist_ok=True)

INTERVAL_MS = {
    "1": 60000, "3": 180000, "5": 300000, "10": 600000, "15": 900000,
    "30": 1800000, "60": 3600000, "120": 7200000, "240": 14400000,
    "D": 86400000, "W": 604800000
}

DATABASE_INFO_CACHE_SECONDS = 2.0
_DATABASE_INFO_CACHE = {"signature": None, "created": 0.0, "info": None}

# =============================================================================
# DATABASE HELPER FUNCTIONS
# =============================================================================

def symbol_timeframe_path(symbol, timeframe):
    """Return the folder path for a given symbol and timeframe."""
    return os.path.join(MARKET_DATA_DIR, symbol.replace("/", "_"), timeframe)


def _database_file_signature():
    """Fast change detector for market-data metadata caching."""
    signature = []
    for root, _, files in os.walk(MARKET_DATA_DIR):
        for f in files:
            if f == "data.parquet":
                fp = os.path.join(root, f)
                try:
                    stat = os.stat(fp)
                    signature.append((fp, stat.st_size, stat.st_mtime_ns))
                except OSError:
                    continue
    return tuple(sorted(signature))


def _split_contiguous_periods(timestamps, interval_ms):
    """Return inclusive contiguous timestamp segments for one timeframe."""
    numeric = pd.to_numeric(timestamps, errors="coerce")
    if numeric.isna().any():
        raise ValueError("timestamp column contains null or non-numeric values")
    ordered = np.sort(numeric.astype("int64").unique())
    if not len(ordered):
        return []
    break_positions = np.flatnonzero(np.diff(ordered) != int(interval_ms)) + 1
    groups = np.split(ordered, break_positions)
    return [
        {"start_ms": int(group[0]), "end_ms": int(group[-1]), "candles": int(len(group))}
        for group in groups if len(group)
    ]


def _read_parquet_summary(fp, timeframe):
    """Read timestamps only and report every gap-separated candle period."""
    interval_ms = INTERVAL_MS.get(str(timeframe))
    if interval_ms is None:
        raise ValueError(f"unsupported timeframe folder: {timeframe}")
    ts = pd.read_parquet(fp, columns=["timestamp"])["timestamp"]
    periods = _split_contiguous_periods(ts, interval_ms)
    numeric_ts = pd.to_numeric(ts, errors="coerce")
    duplicate_timestamps = int(numeric_ts.duplicated().sum())
    unaligned_timestamps = int((numeric_ts % interval_ms != 0).sum())
    file_size = os.path.getsize(fp)
    period_count = len(periods)
    summaries = []
    for index, period in enumerate(periods, 1):
        summaries.append({
            "start": pd.to_datetime(period["start_ms"], unit="ms"),
            "end": pd.to_datetime(period["end_ms"], unit="ms"),
            "start_ms": period["start_ms"],
            "end_ms": period["end_ms"],
            "candles": period["candles"],
            "period_index": index,
            "period_count": period_count,
            "file_size": file_size,
            "duplicate_timestamps": duplicate_timestamps,
            "unaligned_timestamps": unaligned_timestamps,
            # Count each physical file once in table totals/display.
            "size": file_size if index == 1 else 0,
        })
    return summaries


def get_database_info(force_refresh=False):
    """
    Walk the market_data folder and collect metadata about each Parquet file.
    Safely skips unreadable files without deleting or modifying them.
    """
    signature = _database_file_signature()
    now = time.time()
    cached = _DATABASE_INFO_CACHE
    if (
        not force_refresh and
        cached["info"] is not None and
        cached["signature"] == signature and
        now - cached["created"] < DATABASE_INFO_CACHE_SECONDS
    ):
        return cached["info"]

    details, total_size, symbols = [], 0, set()
    unreadable_files = []
    for fp, file_size, _ in signature:
        rel = os.path.relpath(os.path.dirname(fp), MARKET_DATA_DIR).split(os.sep)
        if len(rel) != 2:
            continue
        sym, tf = rel
        symbols.add(sym)
        total_size += file_size
        try:
            summaries = _read_parquet_summary(fp, tf)
            for summary in summaries:
                details.append({
                    "symbol": sym,
                    "timeframe": tf,
                    **summary,
                })
        except Exception as e:
            unreadable_files.append((fp, str(e)))
            print(f"⚠️ Preserving but skipping unreadable market-data file: {fp} ({e})")
                    
    if unreadable_files:
        print("\n" + "="*60)
        print("⚠️ UNREADABLE MARKET-DATA FILES DETECTED ⚠️")
        print("No file was changed or deleted. Keep the original and its backups;")
        print("inspect/restore it manually before considering a fresh download:")
        for file_path, error in unreadable_files:
            print(f"  • {file_path}: {error}")
        print("="*60 + "\n")
        
    details.sort(key=lambda item: (item["symbol"], item["timeframe"], item["start_ms"]))
    info = {
        "size": total_size,
        "symbols": len(symbols),
        "details": details,
        "unreadable_files": unreadable_files,
    }
    _DATABASE_INFO_CACHE.update({"signature": signature, "created": now, "info": info})
    return info


# =============================================================================
# VERIFICATION MANAGER
# =============================================================================

class VerificationManager:
    """
    Runs background threads to scan all Parquet files and report issues.
    Two modes: basic (gaps, duplicates) and deep (adds alignment, OHLCV, data types, statistical outliers).
    Also can generate a Merkle‑style integrity report.
    """
    def __init__(self):
        self.thread = None
        self.stop_event = threading.Event()
        self.log_queue = queue.Queue()
        self.running = False
        self.all_logs = []
        self.log_lock = threading.Lock()

    def add_log(self, message):
        with self.log_lock:
            self.all_logs.append(message)
            self.log_queue.put(message + "\n")

    def start_verification(self, deep=False):
        if self.running:
            self.add_log("Verification already running.")
            return
        self.stop_event.clear()
        self.running = True
        with self.log_lock:
            self.all_logs = []
        if deep:
            self.thread = threading.Thread(target=self._run_deep_verification, daemon=True)
            self.add_log("▶️ Deep verification started – checking all files with advanced statistics.")
        else:
            self.thread = threading.Thread(target=self._run_verification, daemon=True)
            self.add_log("▶️ Basic verification started.")
        self.thread.start()
        print("Verification thread started.")

    def stop_verification(self):
        self.stop_event.set()
        self.add_log("⏹️ Stop signal sent. Waiting for thread to finish...")

    def generate_integrity_report(self):
        report = {}
        all_hashes = []
        for root, dirs, files in os.walk(MARKET_DATA_DIR):
            for file in files:
                if file == "data.parquet":
                    full_path = os.path.join(root, file)
                    rel_path = os.path.relpath(full_path, MARKET_DATA_DIR)
                    sha = hashlib.sha256()
                    with open(full_path, "rb") as f:
                        for chunk in iter(lambda: f.read(65536), b""):
                            sha.update(chunk)
                    file_hash = sha.hexdigest()
                    report[rel_path] = file_hash
                    all_hashes.append(file_hash)
        all_hashes.sort()
        combined = "".join(all_hashes).encode()
        root_hash = hashlib.sha256(combined).hexdigest()
        report["_root"] = root_hash
        return report

    def _run_verification(self):
        try:
            self.add_log("Verification started.")
            total_files = 0
            for root, dirs, files in os.walk(MARKET_DATA_DIR):
                for file in files:
                    if file == "data.parquet":
                        total_files += 1
            self.add_log(f"Found {total_files} Parquet files to check.\n")
            processed = 0
            for root, dirs, files in os.walk(MARKET_DATA_DIR):
                if self.stop_event.is_set():
                    self.add_log("Verification stopped by user.")
                    return
                for file in files:
                    if file == "data.parquet":
                        processed += 1
                        full_path = os.path.join(root, file)
                        rel_path = os.path.relpath(full_path, MARKET_DATA_DIR)
                        parts = rel_path.split(os.sep)
                        if len(parts) != 3:
                            self.add_log(f"  Skipping unexpected path: {rel_path}")
                            continue
                        symbol, timeframe, _ = parts
                        self.add_log(f"\n[{processed}/{total_files}] Checking {symbol} ({timeframe})...")
                        try:
                            df = pd.read_parquet(full_path)
                            count = len(df)
                            if count == 0:
                                self.add_log("  File empty.")
                                continue
                            min_ts = df["timestamp"].min()
                            max_ts = df["timestamp"].max()
                            self.add_log(f"  Candles: {count}")
                            self.add_log(f"  Range: {pd.to_datetime(min_ts, unit='ms')} to {pd.to_datetime(max_ts, unit='ms')}")
                            dups = df["timestamp"].duplicated().sum()
                            if dups:
                                self.add_log(f"  ⚠ Duplicates: {dups}")
                            else:
                                self.add_log(f"  ✓ No duplicates")
                            interval_ms = INTERVAL_MS.get(timeframe)
                            if interval_ms is None:
                                self.add_log(f"  ✗ Unsupported timeframe folder: {timeframe}")
                                continue
                            if len(df) > 1:
                                ordered_ts = pd.to_numeric(df["timestamp"], errors="coerce").sort_values()
                                diffs = ordered_ts.diff().iloc[1:]
                                gaps = diffs[diffs > interval_ms]
                                if not gaps.empty:
                                    self.add_log(f"  ⚠ Gaps: {len(gaps)} detected")
                                    for i, gap in enumerate(gaps.head(5)):
                                        missing = max(0, int(gap // interval_ms) - 1)
                                        self.add_log(f"    Gap {i+1}: {gap:.0f} ms ({missing} missing timeframe candles)")
                                    if len(gaps) > 5:
                                        self.add_log(f"    ... and {len(gaps)-5} more")
                                else:
                                    self.add_log(f"  ✓ No significant gaps")
                            if not df["timestamp"].is_monotonic_increasing:
                                self.add_log(f"  ⚠ Timestamps not sorted!")
                            self.add_log(f"  ✓ OK")
                        except Exception as e:
                            self.add_log(f"  ✗ ERROR: {str(e)}")
            self.add_log("\nVerification completed.")
        except Exception as e:
            self.add_log(f"Verification thread error: {str(e)}")
        finally:
            self.running = False
            print("Verification thread finished.")

    def _run_deep_verification(self):
        try:
            self.add_log("Deep verification started.")
            total_files = 0
            for root, dirs, files in os.walk(MARKET_DATA_DIR):
                for file in files:
                    if file == "data.parquet":
                        total_files += 1
            self.add_log(f"Found {total_files} Parquet files to check.\n")
            processed = 0
            for root, dirs, files in os.walk(MARKET_DATA_DIR):
                if self.stop_event.is_set():
                    self.add_log("Deep verification stopped by user.")
                    return
                for file in files:
                    if file == "data.parquet":
                        processed += 1
                        full_path = os.path.join(root, file)
                        rel_path = os.path.relpath(full_path, MARKET_DATA_DIR)
                        parts = rel_path.split(os.sep)
                        if len(parts) != 3:
                            self.add_log(f"  Skipping unexpected path: {rel_path}")
                            continue
                        symbol, timeframe, _ = parts
                        self.add_log(f"\n[{processed}/{total_files}] DEEP CHECK: {symbol} ({timeframe})...")
                        try:
                            try:
                                meta = pq.read_metadata(full_path)
                                self.add_log(f"  Parquet: {meta.num_rows} rows, {meta.num_columns} cols")
                            except Exception as e:
                                self.add_log(f"  ✗ Parquet metadata error: {e}")
                            df = pd.read_parquet(full_path)
                            count = len(df)
                            if count == 0:
                                self.add_log("  File empty.")
                                continue
                            min_ts = df["timestamp"].min()
                            max_ts = df["timestamp"].max()
                            self.add_log(f"  Candles: {count}")
                            self.add_log(f"  Range: {pd.to_datetime(min_ts, unit='ms')} to {pd.to_datetime(max_ts, unit='ms')}")
                            dups = df["timestamp"].duplicated().sum()
                            if dups:
                                self.add_log(f"  ⚠ Duplicates: {dups}")
                            else:
                                self.add_log(f"  ✓ No duplicates")
                            interval_ms = INTERVAL_MS.get(timeframe)
                            if interval_ms is None:
                                self.add_log(f"  ✗ Unsupported timeframe folder: {timeframe}")
                                continue
                            if len(df) > 1:
                                ordered_ts = pd.to_numeric(df["timestamp"], errors="coerce").sort_values()
                                diffs = ordered_ts.diff().iloc[1:]
                                gaps = diffs[diffs > interval_ms]
                                if not gaps.empty:
                                    self.add_log(f"  ⚠ Gaps: {len(gaps)} detected")
                                    for i, gap in enumerate(gaps.head(5)):
                                        missing = max(0, int(gap // interval_ms) - 1)
                                        self.add_log(f"    Gap {i+1}: {gap:.0f} ms ({missing} missing timeframe candles)")
                                    if len(gaps) > 5:
                                        self.add_log(f"    ... and {len(gaps)-5} more")
                                else:
                                    self.add_log(f"  ✓ No significant gaps")
                            aligned = df["timestamp"] % interval_ms == 0
                            if not aligned.all():
                                bad_count = (~aligned).sum()
                                self.add_log(f"  ⚠ {bad_count} timestamps not aligned to {interval_ms}ms interval!")
                            else:
                                self.add_log(f"  ✓ All timestamps aligned")
                            invalid = df[
                                (df['high'] < df['low']) |
                                (df['high'] < df['open']) |
                                (df['high'] < df['close']) |
                                (df['low'] > df['open']) |
                                (df['low'] > df['close']) |
                                (df['volume'] < 0)
                            ]
                            if not invalid.empty:
                                self.add_log(f"  ⚠ {len(invalid)} candles with OHLCV inconsistency!")
                                for idx, row in invalid.head(3).iterrows():
                                    self.add_log(f"    {row['timestamp']}: H={row['high']:.2f}, L={row['low']:.2f}, O={row['open']:.2f}, C={row['close']:.2f}")
                            else:
                                self.add_log(f"  ✓ OHLCV consistent")
                            expected_types = {'float64', 'int64'}
                            type_issues = False
                            for col in ['open', 'high', 'low', 'close', 'volume']:
                                if col in df.columns and df[col].dtype not in expected_types:
                                    self.add_log(f"  ⚠ Column '{col}' has unexpected type {df[col].dtype}")
                                    type_issues = True
                            if not type_issues:
                                self.add_log(f"  ✓ Data types OK")
                            nan_cols = df.columns[df.isna().any()].tolist()
                            if nan_cols:
                                self.add_log(f"  ⚠ NaN values found in columns: {nan_cols}")
                            else:
                                self.add_log(f"  ✓ No NaN values")
                            zero_vol = (df['volume'] == 0).sum()
                            if zero_vol > 0:
                                self.add_log(f"  ℹ {zero_vol} candles have zero volume")
                            returns = df['close'].pct_change().fillna(0)
                            mean_ret = returns.mean()
                            std_ret = returns.std()
                            outliers = returns[abs(returns - mean_ret) > 5 * std_ret]
                            if len(outliers) > 0:
                                self.add_log(f"  ⚠ {len(outliers)} candles with extreme price movements (potential errors)")
                            if len(df) > 20:
                                vol_mean = df['volume'].rolling(20).mean()
                                vol_std = df['volume'].rolling(20).std()
                                volume_spikes = df[(df['volume'] > vol_mean + 3 * vol_std) & (vol_std > 0)]
                                if len(volume_spikes) > 0:
                                    self.add_log(f"  ℹ {len(volume_spikes)} volume spikes detected")
                                zero_streaks = (df['volume'] == 0).astype(int).groupby(df['volume'].ne(0).cumsum()).sum()
                                long_streaks = zero_streaks[zero_streaks > 10]
                                if not long_streaks.empty:
                                    self.add_log(f"  ⚠ {len(long_streaks)} periods of extended zero volume (>10 candles)")
                            self.add_log(f"  ✓ Deep check passed")
                        except Exception as e:
                            self.add_log(f"  ✗ ERROR: {str(e)}")
            self.add_log("\nDeep verification completed.")
        except Exception as e:
            self.add_log(f"Deep verification thread error: {str(e)}")
        finally:
            self.running = False
            print("Deep verification thread finished.")

    def get_logs(self):
        with self.log_lock:
            return "\n".join(self.all_logs)


# Global instance
vm = VerificationManager()

# =============================================================================
# SAFE LEFT-SIDE PERIOD EXTENSION
# =============================================================================
# Kept in database.py by request. This section is intentionally isolated from
# layout builders and verification code so it can be moved later if desired.

BYBIT_BASE_URL = "https://api.bybit.com"
RATE_LIMIT_SECONDS = 0.05


def _symbol_timeframe_path(market_data_dir, symbol, timeframe):
    return os.path.join(market_data_dir, symbol.replace("/", "_"), str(timeframe))


def _safe_int_timestamp(value):
    """Convert stored timestamp values to integer milliseconds without changing source data."""
    return int(pd.to_numeric(value))


def _validate_ohlcv_frame(df):
    """Return a list of data-quality issues for a candle DataFrame."""
    issues = []
    required = {"timestamp", "open", "high", "low", "close", "volume"}
    missing = required - set(df.columns)
    if missing:
        issues.append(f"missing columns: {', '.join(sorted(missing))}")
        return issues
    if df.empty:
        issues.append("empty frame")
        return issues
    if df["timestamp"].isna().any():
        issues.append("null timestamps")
    if df["timestamp"].duplicated().any():
        issues.append("duplicate timestamps")
    numeric_columns = ["timestamp", "open", "high", "low", "close", "volume"]
    numeric = df[numeric_columns].apply(pd.to_numeric, errors="coerce")
    if numeric.isna().any().any() or not np.isfinite(numeric.to_numpy(dtype=float)).all():
        issues.append("null, non-numeric, or non-finite OHLCV values")
        return issues
    invalid = df[
        (df["high"] < df["low"]) |
        (df["high"] < df["open"]) |
        (df["high"] < df["close"]) |
        (df["low"] > df["open"]) |
        (df["low"] > df["close"]) |
        (df["volume"] < 0)
    ]
    if not invalid.empty:
        issues.append(f"{len(invalid)} OHLCV inconsistencies")
    return issues


def fetch_klines_for_extension(symbol, interval, start, end, limit=200, max_retries=3):
    """Fetch Bybit candles for safe database extension (newest first, matching Bybit v5)."""
    import requests

    url = f"{BYBIT_BASE_URL}/v5/market/kline"
    params = {
        "category": "linear",
        "symbol": symbol,
        "interval": interval,
        "start": int(start),
        "end": int(end),
        "limit": limit,
    }
    for attempt in range(max_retries):
        try:
            resp = requests.get(url, params=params, timeout=10)
            resp.raise_for_status()
            data = resp.json()
            if data.get("retCode") != 0:
                if attempt < max_retries - 1:
                    time.sleep(2 ** attempt)
                    continue
                raise RuntimeError(f"Bybit API error: {data}")
            rows = []
            for k in data.get("result", {}).get("list", []):
                rows.append([int(k[0]), float(k[1]), float(k[2]), float(k[3]), float(k[4]), float(k[5])])
            return pd.DataFrame(rows, columns=["timestamp", "open", "high", "low", "close", "volume"])
        except Exception:
            if attempt < max_retries - 1:
                time.sleep(2 ** attempt)
                continue
            raise
    return pd.DataFrame(columns=["timestamp", "open", "high", "low", "close", "volume"])


def _contiguous_period_bounds(existing, interval_ms, anchor_start=None):
    """Locate a stored period and its neighboring stored timestamps."""
    periods = _split_contiguous_periods(existing["timestamp"], interval_ms)
    if not periods:
        raise RuntimeError("existing file contains no candle periods")
    if anchor_start is None:
        selected_index = 0
    else:
        anchor_start = int(anchor_start)
        selected_index = next(
            (index for index, period in enumerate(periods) if period["start_ms"] == anchor_start),
            None,
        )
        if selected_index is None:
            # A prior batch item may have just connected this period to its
            # predecessor. Locate the now-merged segment containing the anchor.
            selected_index = next(
                (index for index, period in enumerate(periods)
                 if period["start_ms"] <= anchor_start <= period["end_ms"]),
                None,
            )
        if selected_index is None:
            raise RuntimeError(f"stored period starting at {anchor_start} was not found")
    selected = periods[selected_index]
    previous_end = periods[selected_index - 1]["end_ms"] if selected_index > 0 else None
    next_start = periods[selected_index + 1]["start_ms"] if selected_index + 1 < len(periods) else None
    return selected, previous_end, next_start


def validate_stored_candle_range(symbol, timeframe, start_ms, end_ms):
    """Deeply validate one inclusive stored range without modifying the file."""
    try:
        interval_ms = INTERVAL_MS.get(str(timeframe))
        if interval_ms is None:
            return False, f"unsupported timeframe {timeframe}"
        file_path = os.path.join(
            _symbol_timeframe_path(MARKET_DATA_DIR, symbol, timeframe), "data.parquet"
        )
        if not os.path.exists(file_path):
            return False, f"data.parquet not found for {symbol} {timeframe}"
        first_candle = ((int(start_ms) + interval_ms - 1) // interval_ms) * interval_ms
        last_candle = (int(end_ms) // interval_ms) * interval_ms
        frame = pd.read_parquet(
            file_path,
            filters=[("timestamp", ">=", first_candle), ("timestamp", "<=", last_candle)],
        ).sort_values("timestamp").reset_index(drop=True)
        issues = _validate_ohlcv_frame(frame)
        if issues:
            return False, "; ".join(issues)
        numeric_ts = pd.to_numeric(frame["timestamp"], errors="coerce").astype("int64")
        expected = max(0, ((last_candle - first_candle) // interval_ms) + 1)
        if len(numeric_ts) != expected:
            return False, f"needs {expected} candles but found {len(numeric_ts)}"
        if expected and (
            int(numeric_ts.iloc[0]) != first_candle or
            int(numeric_ts.iloc[-1]) != last_candle or
            (len(numeric_ts) > 1 and not (numeric_ts.diff().iloc[1:] == interval_ms).all())
        ):
            return False, "timestamps are not a complete aligned sequence"
        return True, f"validated {len(frame)} candles"
    except Exception as exc:
        return False, f"range validation failed: {exc}"


class ExtensionManager:
    """Safely extends existing Parquet periods to the left without replacing old candles."""

    def __init__(self, market_data_dir, interval_ms):
        self.market_data_dir = market_data_dir
        self.interval_ms = interval_ms
        self.thread = None
        self.running = False
        self.progress = 0.0
        self.status = "Idle."
        self.log = []
        self.lock = threading.Lock()

    def _set_state(self, status=None, progress=None):
        with self.lock:
            if status is not None:
                self.status = status
                self.log.append(f"[{datetime.now().strftime('%H:%M:%S')}] {status}")
                # Long 1-minute history jobs can contain thousands of API
                # batches. Keep monitoring useful without unbounded RAM use.
                if len(self.log) > 1000:
                    self.log = self.log[-1000:]
            if progress is not None:
                self.progress = float(progress)

    def get_state(self):
        with self.lock:
            return self.running, self.progress, self.status, "\n".join(self.log[-200:])

    def extend_left_safely(self, symbol, timeframe, minutes, period_start=None,
                           progress_base=0, progress_span=100):
        """Use the canonical validated/backup/atomic left-extension pipeline."""
        return self._extend_left(
            symbol, timeframe, minutes, progress_base, progress_span, period_start
        )

    def start(self, symbol, timeframe, minutes, period_start=None):
        if self.running:
            return False, "⚠️ Another extension is already running. Please wait."
        try:
            minutes = int(minutes)
        except Exception:
            return False, "❌ Enter a whole number of minutes."
        if minutes <= 0:
            return False, "❌ Minutes must be greater than zero."
        self.running = True
        with self.lock:
            self.progress = 0.0
            self.status = "Starting safe extension..."
            self.log = []
        self.thread = threading.Thread(
            target=self._run, args=(symbol, timeframe, minutes, period_start), daemon=True
        )
        self.thread.start()
        return True, (
            f"▶️ Started safe extension for {symbol} {timeframe} period "
            f"{period_start} by {minutes} minutes."
        )

    def start_all(self, periods, minutes=None, through_now=False):
        """Start one serial job for every discovered period.

        Serial processing deliberately limits API pressure, memory use and disk
        writes.  ``minutes=None`` means continue left until Bybit has no older
        candles; ``through_now`` additionally fills the right side to the time
        at which the button was pressed.
        """
        if self.running:
            return False, "⚠️ Another extension is already running. Please wait."
        unique_periods = sorted({
            (str(symbol), str(timeframe), int(period_start))
            for symbol, timeframe, period_start in periods
        })
        if not unique_periods:
            return False, "⚠️ No downloaded periods were found. Existing data was not changed."
        if minutes is not None:
            try:
                minutes = int(minutes)
            except Exception:
                return False, "❌ Enter a whole number of minutes for all periods."
            if minutes <= 0:
                return False, "❌ Minutes must be greater than zero."
        self.running = True
        with self.lock:
            self.progress = 0.0
            self.status = "Starting safe batch operation..."
            self.log = []
        pressed_at_ms = int(time.time() * 1000)
        self.thread = threading.Thread(
            target=self._run_all,
            args=(unique_periods, minutes, through_now, pressed_at_ms),
            daemon=True,
        )
        self.thread.start()
        action = "complete history" if through_now else ("earliest available candle" if minutes is None else f"{minutes} minutes left")
        return True, f"▶️ Started {action} for {len(unique_periods)} downloaded periods."

    def _run_all(self, periods, minutes, through_now, pressed_at_ms):
        failures = []
        try:
            total = len(periods)
            for index, (symbol, timeframe, period_start) in enumerate(periods, 1):
                base = (index - 1) / total * 100
                span = 100 / total
                self._set_state(
                    f"[{index}/{total}] Processing {symbol} {timeframe} period {period_start}...",
                    base,
                )
                try:
                    self._extend_left(
                        symbol, timeframe, minutes, base,
                        span * (0.5 if through_now else 1.0), period_start,
                    )
                    if through_now:
                        self._extend_right(
                            symbol, timeframe, pressed_at_ms,
                            base + span * 0.5, span * 0.5, period_start,
                        )
                except Exception as exc:
                    failures.append(f"{symbol} {timeframe}: {exc}")
                    self._set_state(
                        f"⚠️ [{index}/{total}] {symbol} {timeframe} stopped: {exc}. "
                        "No unvalidated write was installed; any earlier completed atomic step and its backup remain.",
                        base + span,
                    )
            if failures:
                self._set_state(
                    f"⚠️ Batch finished: {total - len(failures)}/{total} periods completed; "
                    f"{len(failures)} unavailable or failed. Existing files were kept.",
                    100,
                )
            else:
                self._set_state(f"✅ Batch completed safely for all {total} periods.", 100)
        except Exception as exc:
            self._set_state(f"❌ Batch stopped: {exc}", self.progress)
        finally:
            self.running = False

    def _run(self, symbol, timeframe, minutes, period_start):
        try:
            self._extend_left(symbol, timeframe, minutes, period_start=period_start)
            self._set_state("✅ Extension completed safely.", 100)
        except Exception as e:
            self._set_state(f"❌ Extension stopped: {e}", self.progress)
        finally:
            self.running = False

    def _extend_left(self, symbol, timeframe, minutes, progress_base=0,
                     progress_span=100, period_start=None):
        interval_ms = self.interval_ms.get(str(timeframe))
        if interval_ms is None:
            raise RuntimeError(f"unsupported timeframe {timeframe}")
        path = _symbol_timeframe_path(self.market_data_dir, symbol, timeframe)
        file_path = os.path.join(path, "data.parquet")
        if not os.path.exists(file_path):
            raise RuntimeError(f"data.parquet not found for {symbol} {timeframe}")

        self._set_state(
            "Reading existing file and validating current data...",
            progress_base + progress_span * 0.02,
        )
        existing = pd.read_parquet(file_path)
        issues = _validate_ohlcv_frame(existing)
        if issues:
            raise RuntimeError("existing file failed safety validation: " + "; ".join(issues))
        if not (pd.to_numeric(existing["timestamp"]) % interval_ms == 0).all():
            raise RuntimeError("existing file contains timestamps not aligned to its timeframe")
        existing = existing.sort_values("timestamp").reset_index(drop=True)
        selected, previous_end, _next_start = _contiguous_period_bounds(
            existing, interval_ms, period_start
        )
        existing_start = selected["start_ms"]
        requested_start = 0 if minutes is None else max(
            0, existing_start - int(minutes) * 60_000
        )
        # Never request candles already stored in an earlier period. If there
        # is a prior segment, this operation safely fills only the gap between
        # that segment and the selected one.
        target_start = max(
            requested_start,
            previous_end + interval_ms if previous_end is not None else 0,
        )
        target_end = existing_start - interval_ms
        if target_start > target_end:
            self._set_state(
                "Requested extension is shorter than one candle; nothing to download.",
                progress_base + progress_span,
            )
            return

        expected = max(1, ((target_end - target_start) // interval_ms) + 1)
        self._set_state(
            f"Downloading only missing left-side candles: {pd.to_datetime(target_start, unit='ms')} to {pd.to_datetime(target_end, unit='ms')} (~{expected}).",
            progress_base + progress_span * 0.05,
        )
        batches, cur_end, downloaded = [], target_end, 0
        while cur_end >= target_start:
            time.sleep(RATE_LIMIT_SECONDS)
            df = fetch_klines_for_extension(symbol, timeframe, target_start, cur_end, limit=200)
            if df.empty:
                break
            if not (df["timestamp"] % interval_ms == 0).all():
                raise RuntimeError("downloaded batch contains timestamps not aligned to timeframe")
            if df["timestamp"].max() >= existing_start:
                df = df[df["timestamp"] < existing_start]
            df = df[(df["timestamp"] >= target_start) & (df["timestamp"] <= target_end)]
            if df.empty:
                break
            issues = _validate_ohlcv_frame(df)
            if issues:
                raise RuntimeError("downloaded batch failed safety validation: " + "; ".join(issues))
            batches.append(df)
            downloaded += len(df)
            oldest = int(df["timestamp"].min())
            if oldest > cur_end:
                raise RuntimeError("Bybit response did not move toward older candles")
            cur_end = oldest - interval_ms
            self._set_state(
                f"Downloaded {downloaded} raw candles; checking for overlaps and gaps...",
                progress_base + min(progress_span * 0.9, downloaded / expected * progress_span * 0.8),
            )

        if not batches:
            self._set_state(
                "No earlier candles returned by Bybit; existing file was not changed.",
                progress_base + progress_span,
            )
            return

        new_data = pd.concat(batches, ignore_index=True).sort_values("timestamp").drop_duplicates("timestamp", keep="last")
        new_data = new_data[new_data["timestamp"] < existing_start]
        if new_data.empty:
            self._set_state(
                "Downloaded data overlapped existing period only; existing file was not changed.",
                progress_base + progress_span,
            )
            return

        overlap = set(new_data["timestamp"].astype(int)).intersection(set(existing["timestamp"].astype(int)))
        if overlap:
            raise RuntimeError(f"overlap safety check failed for {len(overlap)} timestamps")

        self._set_state(
            "Merging with existing data using existing rows as immutable source of truth...",
            progress_base + progress_span * 0.92,
        )
        self._set_state(
            "Writing atomically with backup; original file remains until final replace...",
            progress_base + progress_span * 0.96,
        )
        backup_path = self._write_preserving_existing(
            file_path, existing, new_data, symbol, timeframe
        )
        self._set_state(
            f"Saved {len(new_data)} new candles. Backup kept at {backup_path}.",
            progress_base + progress_span,
        )

    def _extend_right(self, symbol, timeframe, pressed_at_ms, progress_base=0,
                      progress_span=100, period_start=None):
        """Extend one period right without crossing a following stored period."""
        interval_ms = self.interval_ms.get(str(timeframe))
        if interval_ms is None:
            raise RuntimeError(f"unsupported timeframe {timeframe}")
        file_path = os.path.join(
            _symbol_timeframe_path(self.market_data_dir, symbol, timeframe), "data.parquet"
        )
        existing = pd.read_parquet(file_path).sort_values("timestamp").reset_index(drop=True)
        issues = _validate_ohlcv_frame(existing)
        if issues:
            raise RuntimeError("existing file failed safety validation: " + "; ".join(issues))
        if not (pd.to_numeric(existing["timestamp"]) % interval_ms == 0).all():
            raise RuntimeError("existing file contains timestamps not aligned to its timeframe")
        selected, _previous_end, next_start = _contiguous_period_bounds(
            existing, interval_ms, period_start
        )
        existing_end = selected["end_ms"]
        # Never persist an in-progress candle.
        last_closed = (int(pressed_at_ms) // interval_ms) * interval_ms - interval_ms
        target_end = min(
            last_closed,
            next_start - interval_ms if next_start is not None else last_closed,
        )
        cursor = existing_end + interval_ms
        if cursor > target_end:
            self._set_state(f"{symbol} {timeframe} is already current through the last closed candle.", progress_base + progress_span)
            return

        expected = max(1, ((target_end - cursor) // interval_ms) + 1)
        batches, downloaded = [], 0
        while cursor <= target_end:
            batch_end = min(target_end, cursor + (200 - 1) * interval_ms)
            time.sleep(RATE_LIMIT_SECONDS)
            frame = fetch_klines_for_extension(symbol, timeframe, cursor, batch_end, limit=200)
            if frame.empty:
                break
            frame = frame[(frame["timestamp"] >= cursor) & (frame["timestamp"] <= target_end)]
            if frame.empty:
                break
            if not (frame["timestamp"] % interval_ms == 0).all():
                raise RuntimeError("downloaded batch contains timestamps not aligned to timeframe")
            batch_issues = _validate_ohlcv_frame(frame)
            if batch_issues:
                raise RuntimeError("downloaded batch failed safety validation: " + "; ".join(batch_issues))
            batches.append(frame)
            downloaded += len(frame)
            newest = int(frame["timestamp"].max())
            if newest < cursor:
                raise RuntimeError("Bybit response did not advance the download cursor")
            cursor = newest + interval_ms
            self._set_state(
                f"{symbol} {timeframe}: downloaded {downloaded}/{expected} newer candles...",
                progress_base + min(progress_span * 0.9, downloaded / expected * progress_span * 0.9),
            )

        if not batches:
            self._set_state(f"No newer candles are available for {symbol} {timeframe}; existing file was kept.", progress_base + progress_span)
            return
        new_data = pd.concat(batches, ignore_index=True).sort_values("timestamp").drop_duplicates("timestamp", keep="last")
        new_data = new_data[new_data["timestamp"] > existing_end]
        self._write_preserving_existing(file_path, existing, new_data, symbol, timeframe)
        self._set_state(f"Saved {len(new_data)} newer candles for {symbol} {timeframe}.", progress_base + progress_span)

    def _write_preserving_existing(self, file_path, existing, new_data, symbol, timeframe):
        """Validate, reread and atomically replace while proving old rows survived."""
        if new_data.empty:
            return
        if set(new_data["timestamp"].astype(int)).intersection(set(existing["timestamp"].astype(int))):
            raise RuntimeError("overlap safety check failed")
        combined = pd.concat([existing, new_data], ignore_index=True).sort_values("timestamp").reset_index(drop=True)
        issues = _validate_ohlcv_frame(combined)
        if issues:
            raise RuntimeError("combined file failed safety validation: " + "; ".join(issues))
        existing_sorted = existing.sort_values("timestamp").reset_index(drop=True)
        old_rows = combined[combined["timestamp"].isin(existing["timestamp"])].reset_index(drop=True)
        try:
            pd.testing.assert_frame_equal(old_rows[existing_sorted.columns], existing_sorted)
        except AssertionError as exc:
            raise RuntimeError("preservation check failed: existing candle values changed") from exc
        backup_path = f"{file_path}.bak_{datetime.now().strftime('%Y%m%d_%H%M%S')}_{uuid.uuid4().hex[:8]}"
        temp_path = f"{file_path}.tmp_{uuid.uuid4().hex}"
        shutil.copy2(file_path, backup_path)
        try:
            combined.to_parquet(temp_path, compression="zstd")
            reread = pd.read_parquet(temp_path)
            if len(reread) != len(combined) or _validate_ohlcv_frame(reread):
                raise RuntimeError("new parquet failed reread validation")
            reread_old = reread[reread["timestamp"].isin(existing_sorted["timestamp"])].reset_index(drop=True)
            try:
                pd.testing.assert_frame_equal(reread_old[existing_sorted.columns], existing_sorted)
            except AssertionError as exc:
                raise RuntimeError("parquet reread preservation check failed") from exc
            os.replace(temp_path, file_path)
            return backup_path
        finally:
            if os.path.exists(temp_path):
                os.remove(temp_path)


em = ExtensionManager(MARKET_DATA_DIR, INTERVAL_MS)


# =============================================================================
# DATA ANALYSIS TAB UI
# =============================================================================

def _build_extend_cell(detail):
    """Build the compact left-side extension controls for one data period."""
    identity = {
        "symbol": detail["symbol"],
        "timeframe": detail["timeframe"],
        "period_start": int(detail["start_ms"]),
    }
    return html.Td(html.Div([
        dcc.Input(
            id={"type": "extend-minutes-input", **identity},
            type="number",
            min=1,
            step=1,
            placeholder="extra min",
            style={"width": "95px", "marginRight": "4px"},
        ),
        html.Button(
            "⬅️ Extend",
            id={"type": "extend-left-btn", **identity},
            n_clicks=0,
            title="Safely download this many extra minutes before the current start time.",
        ),
    ]))


def _build_details_table(details):
    """Build the database-period table without embedding download logic."""
    rows = []
    for d in details:
        warnings = []
        if d.get("duplicate_timestamps"):
            warnings.append(f"{d['duplicate_timestamps']} duplicate timestamps")
        if d.get("unaligned_timestamps"):
            warnings.append(f"{d['unaligned_timestamps']} unaligned timestamps")
        rows.append(html.Tr([
            _build_extend_cell(d),
            html.Td(d["symbol"]),
            html.Td(d["timeframe"]),
            html.Td(f"{d['period_index']}/{d['period_count']}"),
            html.Td(d["start"].strftime("%Y-%m-%d %H:%M")),
            html.Td(d["end"].strftime("%Y-%m-%d %H:%M")),
            html.Td(f"{d['candles']:,}"),
            html.Td(f"{d['file_size']/1e6:.2f} MB" if d["period_index"] == 1 else "↑ same file"),
            html.Td("; ".join(warnings) if d["period_index"] == 1 and warnings else "—"),
        ]))
    return html.Table([
        html.Thead(html.Tr([
            html.Th("Extend left"),
            html.Th("Symbol"),
            html.Th("TF"),
            html.Th("Period"),
            html.Th("Start"),
            html.Th("End"),
            html.Th("Candles"),
            html.Th("File size"),
            html.Th("File warnings"),
        ])),
        html.Tbody(rows)
    ], style={"width": "100%", "border": "1px solid black", "borderCollapse": "collapse"})


def _build_extension_status_panel():
    """Build progress/status/log widgets for safe period extension."""
    return html.Div([
        html.H4("Safe contiguous-period extension"),
        html.P("Each row is one uninterrupted candle segment. Enter extra minutes beside a segment to fill candles immediately before that segment; the operation stops at an earlier stored segment, rejects overlaps, validates OHLCV data, writes through a temporary file, and keeps a timestamped backup."),
        html.Progress(id="extend-progress", value="0", max="100", style={"width": "100%", "height": "18px"}),
        html.Div(id="extend-status", style={"marginTop": "8px", "fontWeight": "bold", "color": "#0b63b6"}),
        html.Pre(id="extend-log", style={"height": "140px", "overflowY": "scroll", "border": "1px solid #ccc", "padding": "5px", "marginTop": "8px"}),
    ], style={"border": "1px solid #d9e8ff", "backgroundColor": "#f7fbff", "padding": "10px", "margin": "10px 0"})


def _build_period_extension_box(details):
    """Build collapsible batch controls followed by the per-period table."""
    period_count = len(details)
    return html.Details([
        html.Summary(
            f"⬅️ Safe candle history tools and downloaded periods ({period_count})",
            style={"fontWeight": "bold", "fontSize": "17px", "cursor": "pointer", "padding": "8px"},
        ),
        html.Div([
            html.H4("All downloaded periods", style={"marginBottom": "5px"}),
            html.P(
                "Periods are detected wherever adjacent timestamps differ by more than one timeframe candle. "
                "Jobs run one detected period at a time. Existing candles are validated and preserved; "
                "new files are reread before an atomic replacement and a backup is retained. "
                "Unavailable or delisted pairs are logged and skipped without deleting their data.",
                style={"marginTop": "0"},
            ),
            html.P(
                "A gap is treated as a period boundary, not automatically as corruption. An unreadable Parquet/schema/timestamp file is preserved and excluded. Readable files with duplicate or unaligned timestamps are shown with warnings and extension is refused until they are reviewed; full OHLCV checks run before every extension.",
                style={"fontSize": "12px", "color": "#555"},
            ),
            html.Div([
                dcc.Input(
                    id="extend-all-minutes",
                    type="number",
                    min=1,
                    step=1,
                    placeholder="extra minutes",
                    style={"width": "145px", "marginRight": "6px"},
                ),
                html.Button("⬅️ Extend all by minutes", id="extend-all-minutes-btn", n_clicks=0),
            ], style={"margin": "7px 0"}),
            html.Div([
                html.Button(
                    "⏮️ Extend all to earliest available Bybit candle",
                    id="extend-all-earliest-btn",
                    n_clicks=0,
                    title="Continues backwards until Bybit returns no older candles.",
                ),
                html.Button(
                    "📅 Complete all histories through now",
                    id="complete-all-history-btn",
                    n_clicks=0,
                    style={"marginLeft": "7px"},
                    title="For every downloaded period, fetches earliest available history and then all closed candles through the time pressed.",
                ),
            ], style={"margin": "7px 0"}),
            dcc.Checklist(
                id="confirm-long-history-download",
                options=[{
                    "label": "I understand earliest/full-history jobs can take a long time and use substantial disk space",
                    "value": "confirm",
                }],
                value=[],
                style={"margin": "8px 0", "color": "#7a4b00"},
            ),
            _build_extension_status_panel(),
            html.H4("Downloaded periods", style={"marginBottom": "6px"}),
            _build_details_table(details),
        ], style={"padding": "0 10px 10px"}),
    ], open=False, style={"border": "1px solid #b9cbe3", "borderRadius": "5px", "margin": "10px 0"})


def _build_candles_per_symbol_figure(details):
    """Build a lightweight summary figure from already collected metadata."""
    if details:
        df = pd.DataFrame(details)
        df_grouped = df.groupby("symbol")["candles"].sum().reset_index()
        return px.bar(df_grouped, x="symbol", y="candles", title="Total Candles per Symbol")
    return px.bar(title="No data downloaded yet")


def create_data_analysis_tab():
    """Create the Data Analysis tab UI layout."""
    info = get_database_info()
    total_candles = sum(d["candles"] for d in info["details"])
    total_size_mb = info["size"] / 1e6
    total_symbols = info["symbols"]
    total_files = len({(d["symbol"], d["timeframe"]) for d in info["details"]})
    total_periods = len(info["details"])
    fig = _build_candles_per_symbol_figure(info["details"])
    
    # Build symbol/timeframe dropdown options
    symbol_options = [{"label": s, "value": s} for s in sorted(set(d["symbol"] for d in info["details"]))] if info["details"] else []
    unreadable_warning = None
    if info.get("unreadable_files"):
        unreadable_warning = html.Div([
            html.Strong("⚠️ Unreadable market-data files were preserved and excluded:"),
            html.Ul([
                html.Li(f"{path}: {error}")
                for path, error in info["unreadable_files"]
            ]),
            html.P("The app does not delete these files. Inspect a backup or run verification before any manual replacement."),
        ], style={"border": "1px solid #d98c00", "backgroundColor": "#fff8e1", "padding": "10px"})
    
    return html.Div([
        html.H3("Data Statistics"),
        # Keep task-tab callback outputs addressable while this dynamic tab is
        # mounted. Dash requires callback Output components to exist in the
        # current layout even if the task-only status is visually hidden here.
        html.Div(id="bulk-rerun-status", style={"display": "none"}),
        html.P(f"Total symbols: {total_symbols}"),
        html.P(f"Readable symbol/timeframe files: {total_files}"),
        html.P(f"Detected continuous candle periods: {total_periods}"),
        html.P(f"Total candles: {total_candles:,}"),
        html.P(f"Total database size: {total_size_mb:.2f} MB"),
        unreadable_warning,
        html.Button("Download Backup", id="download-db-btn"),
        dcc.Download(id="download-db"),
        _build_period_extension_box(info["details"]),
        html.H4("Candles per Symbol"),
        dcc.Graph(figure=fig),
        html.Hr(),
        html.H4("Database Structure"),
        dcc.Markdown("""
- **Root folder**: `market_data/`
- **Symbol folders**: e.g., `BTCUSDT/`, `ETHUSDT/` (slashes in symbol names replaced with `_`)
- **Timeframe subfolders**: e.g., `1/`, `5/`, `60/`, `D/`, `W/` (matching Bybit interval codes)
- **Data files**: each timeframe folder contains a single `data.parquet` file
- **Schema**:
  - `timestamp` (int64): Unix timestamp in milliseconds (UTC)
  - `open`, `high`, `low`, `close` (float64): OHLC prices
  - `volume` (float64): trading volume
- **Compression**: ZSTD (via PyArrow)
"""),
        html.Hr(),
        html.H4("Database Verification"),
        html.Div([
            html.Button("Start Basic Verification", id="start-verify-btn", n_clicks=0),
            html.Button("Start Deep Verification", id="start-deep-verify-btn", n_clicks=0),
            html.Button("Stop Verification", id="stop-verify-btn", n_clicks=0),
            html.Br(),
            html.Button("Generate Integrity Report", id="generate-report-btn", n_clicks=0),
            dcc.Download(id="download-report"),
            html.Pre(id="verify-log", style={"height": "300px", "overflow-y": "scroll", "border": "1px solid #ccc", "padding": "5px", "marginTop": "10px"}),
            html.Br(),
            html.Button("Run DuckDB Query (Unified View)", id="run-duckdb-btn", n_clicks=0),
            html.Pre(id="duckdb-result", style={"height": "200px", "overflow-y": "scroll", "border": "1px solid #ccc", "padding": "5px", "marginTop": "10px"}),
            html.Br(),
            html.H4("TradingView‑Style Chart"),
            html.Div([
                dcc.Dropdown(
                    id="chart-symbol-dropdown",
                    placeholder="Select Symbol",
                    options=symbol_options,
                    value=None
                ),
                dcc.Dropdown(
                    id="chart-timeframe-dropdown",
                    placeholder="Select Timeframe",
                    options=[],
                    value=None
                ),
                dcc.Graph(id="candlestick-chart", style={"height": "600px"}),
                html.Hr(),
                html.H4("Database Maintenance", style={"marginTop": "20px"}),
                html.Div([
                    html.Label("Symbol:"),
                    dcc.Dropdown(id="clean-symbol", placeholder="Select symbol", style={"width": "200px", "display": "inline-block", "marginRight": "10px"}),
                    html.Label("Timeframe:", style={"marginLeft": "10px"}),
                    dcc.Dropdown(id="clean-timeframe", placeholder="Select timeframe", style={"width": "150px", "display": "inline-block", "marginRight": "10px"}),
                    html.Button("🗑️ Delete selected data", id="delete-selected-btn", style={"margin": "5px", "backgroundColor": "#ffcccc"}),
                    html.Button("🔄 Re-download full history", id="redownload-full-btn", style={"margin": "5px", "backgroundColor": "#ccffcc"}),
                    html.Br(),
                    dcc.Checklist(id="confirm-delete-all", options=[{"label": "I understand, delete ALL market data (cannot undo)", "value": "confirm"}], value=[]),
                    html.Button("⚠️ Delete ALL market data", id="delete-all-btn", style={"margin": "5px", "backgroundColor": "#ff9999"}, disabled=True),
                    html.Div(id="delete-status", style={"marginTop": "10px", "color": "red", "fontWeight": "bold"}),
                    html.Button("🔄 Re-download ALL Existing Data", id="redownload-all-btn", style={"margin": "5px", "backgroundColor": "#ccffcc"}),
                    html.Div(id="redownload-all-status", style={"marginTop": "10px", "color": "blue", "fontSize": "13px"}),
                ]),
            ])
        ])
    ])


# =============================================================================
# CALLBACKS FOR DATA ANALYSIS TAB
# =============================================================================

def register_database_callbacks(app):
    """Register all database-related callbacks with the Dash app."""

    @app.callback(
        Output("extend-status", "children"),
        Input({"type": "extend-left-btn", "symbol": ALL, "timeframe": ALL, "period_start": ALL}, "n_clicks"),
        State({"type": "extend-minutes-input", "symbol": ALL, "timeframe": ALL, "period_start": ALL}, "value"),
        State({"type": "extend-minutes-input", "symbol": ALL, "timeframe": ALL, "period_start": ALL}, "id"),
        prevent_initial_call=True
    )
    def start_left_extension(_clicks, minute_values, input_ids):
        triggered = ctx.triggered_id
        if not isinstance(triggered, dict):
            return no_update
        symbol = triggered.get("symbol")
        timeframe = triggered.get("timeframe")
        period_start = triggered.get("period_start")
        minutes = None
        for value, input_id in zip(minute_values or [], input_ids or []):
            if (
                input_id.get("symbol") == symbol and
                input_id.get("timeframe") == timeframe and
                input_id.get("period_start") == period_start
            ):
                minutes = value
                break
        _, message = em.start(symbol, timeframe, minutes, period_start)
        return message

    @app.callback(
        Output("extend-status", "children", allow_duplicate=True),
        Input("extend-all-minutes-btn", "n_clicks"),
        Input("extend-all-earliest-btn", "n_clicks"),
        Input("complete-all-history-btn", "n_clicks"),
        State("extend-all-minutes", "value"),
        State("confirm-long-history-download", "value"),
        prevent_initial_call=True,
    )
    def start_all_period_extension(_minutes_clicks, _earliest_clicks, _complete_clicks,
                                   minutes, confirmations):
        """Dispatch batch jobs using a fresh inventory of existing periods."""
        trigger = ctx.triggered_id
        info = get_database_info(force_refresh=True)
        periods = [
            (detail["symbol"], detail["timeframe"], detail["start_ms"])
            for detail in info["details"]
        ]
        if trigger == "extend-all-minutes-btn":
            _, message = em.start_all(periods, minutes=minutes, through_now=False)
            return message
        if trigger in {"extend-all-earliest-btn", "complete-all-history-btn"}:
            if "confirm" not in (confirmations or []):
                return "⚠️ Confirm the long download and disk-space warning before starting. Nothing was changed."
            _, message = em.start_all(
                periods,
                minutes=None,
                through_now=(trigger == "complete-all-history-btn"),
            )
            return message
        return no_update

    @app.callback(
        Output("extend-progress", "value"),
        Output("extend-status", "children", allow_duplicate=True),
        Output("extend-log", "children"),
        Input("verify-interval", "n_intervals"),
        prevent_initial_call=True
    )
    def update_left_extension_status(_):
        _running, progress, status, log = em.get_state()
        return str(progress), status, log
    
    # Verification control callback
    @app.callback(
        Output("start-verify-btn", "disabled"),
        Output("start-deep-verify-btn", "disabled"),
        Output("stop-verify-btn", "disabled"),
        Input("start-verify-btn", "n_clicks"),
        Input("start-deep-verify-btn", "n_clicks"),
        Input("stop-verify-btn", "n_clicks"),
        prevent_initial_call=True
    )
    def control_verification(start_clicks, deep_clicks, stop_clicks):
        triggered = ctx.triggered_id
        if triggered == "start-verify-btn" and not vm.running:
            vm.start_verification(deep=False)
            return True, True, False
        elif triggered == "start-deep-verify-btn" and not vm.running:
            vm.start_verification(deep=True)
            return True, True, False
        elif triggered == "stop-verify-btn" and vm.running:
            vm.stop_verification()
            return no_update, no_update, no_update
        return no_update, no_update, no_update

    # Update button states based on verification status
    @app.callback(
        Output("start-verify-btn", "disabled", allow_duplicate=True),
        Output("start-deep-verify-btn", "disabled", allow_duplicate=True),
        Output("stop-verify-btn", "disabled", allow_duplicate=True),
        Input("verify-interval", "n_intervals"),
        prevent_initial_call=True
    )
    def update_button_states(_):
        if not vm.running:
            return False, False, True
        return True, True, False

    # Update verification log
    @app.callback(
        Output("verify-log", "children"),
        Input("verify-interval", "n_intervals")
    )
    def update_verify_log(_):
        return vm.get_logs()

    # Generate integrity report
    @app.callback(
        Output("download-report", "data"),
        Input("generate-report-btn", "n_clicks"),
        prevent_initial_call=True
    )
    def generate_report(_):
        report = vm.generate_integrity_report()
        report_str = json.dumps(report, indent=2)
        return dcc.send_string(report_str, f"integrity_report_{datetime.now().strftime('%Y%m%d_%H%M%S')}.json")

    # Run DuckDB query
    @app.callback(
        Output("duckdb-result", "children"),
        Input("run-duckdb-btn", "n_clicks"),
        prevent_initial_call=True
    )
    def run_duckdb_query(_):
        if not DUCKDB_AVAILABLE:
            return "DuckDB not installed. Please run: pip install duckdb"
        try:
            conn = duckdb.connect()
            query = """
            SELECT
            regexp_extract(filename, 'market_data/([^/]+)/', 1) as symbol,
            COUNT(*) as candle_count,
            MIN(timestamp) as earliest,
            MAX(timestamp) as latest,
            AVG(close) as avg_close,
            STDDEV(close) as volatility,
            SUM(volume) as total_volume
            FROM read_parquet('market_data/*/60/data.parquet', filename=true)
            GROUP BY symbol
            ORDER BY symbol
            """
            df = conn.execute(query).df()
            return df.to_string()
        except Exception as e:
            return f"Error: {e}"

    # Update timeframe dropdown based on symbol selection
    @app.callback(
        Output("chart-timeframe-dropdown", "options"),
        Input("chart-symbol-dropdown", "value")
    )
    def update_timeframe_options(selected_symbol):
        if not selected_symbol:
            return []
        info = get_database_info()
        timeframes = sorted(set(
            d["timeframe"] for d in info["details"] if d["symbol"] == selected_symbol
        ))
        return [{"label": tf, "value": tf} for tf in timeframes]

    # Update candlestick chart
    @app.callback(
        Output("candlestick-chart", "figure"),
        Input("chart-symbol-dropdown", "value"),
        Input("chart-timeframe-dropdown", "value")
    )
    def update_chart(symbol, timeframe):
        if not symbol or not timeframe:
            fig = make_subplots(rows=2, cols=1, shared_xaxes=True,
                                vertical_spacing=0.05, row_heights=[0.7, 0.3])
            fig.update_layout(title="Select a symbol and timeframe to view chart")
            return fig
        
        path = symbol_timeframe_path(symbol, timeframe)
        file_path = os.path.join(path, "data.parquet")
        
        if not os.path.exists(file_path):
            fig = make_subplots(rows=2, cols=1, shared_xaxes=True,
                                vertical_spacing=0.05, row_heights=[0.7, 0.3])
            fig.update_layout(title=f"No data for {symbol} {timeframe}")
            return fig
        
        df = pd.read_parquet(file_path)
        if df.empty:
            fig = make_subplots(rows=2, cols=1, shared_xaxes=True,
                                vertical_spacing=0.05, row_heights=[0.7, 0.3])
            fig.update_layout(title=f"Empty data for {symbol} {timeframe}")
            return fig
        
        df['date'] = pd.to_datetime(df['timestamp'], unit='ms')
        
        fig = make_subplots(rows=2, cols=1, shared_xaxes=True,
                            vertical_spacing=0.05, row_heights=[0.7, 0.3])
        
        fig.add_trace(go.Candlestick(
            x=df['date'],
            open=df['open'],
            high=df['high'],
            low=df['low'],
            close=df['close'],
            name="OHLC",
            increasing_line_color='#26a69a',
            decreasing_line_color='#ef5350'
        ), row=1, col=1)
        
        colors = ['#26a69a' if row['close'] >= row['open'] else '#ef5350' for _, row in df.iterrows()]
        fig.add_trace(go.Bar(
            x=df['date'],
            y=df['volume'],
            name="Volume",
            marker_color=colors,
            showlegend=False
        ), row=2, col=1)
        
        fig.update_layout(
            title=f"{symbol} – {timeframe}",
            xaxis_rangeslider_visible=False,
            template="plotly_white",
            hovermode="x unified",
            height=600,
            margin=dict(l=50, r=50, t=50, b=50)
        )
        fig.update_xaxes(title_text="Date", row=2, col=1)
        fig.update_yaxes(title_text="Price", row=1, col=1)
        fig.update_yaxes(title_text="Volume", row=2, col=1)
        
        return fig

    # Download database backup
    @app.callback(
        Output("download-db", "data"),
        Input("download-db-btn", "n_clicks"),
        prevent_initial_call=True
    )
    def backup(_):
        zip_name = f"market_data_backup_{datetime.now().strftime('%Y%m%d_%H%M%S')}.zip"
        shutil.make_archive(zip_name.replace('.zip', ''), 'zip', MARKET_DATA_DIR)
        return dcc.send_file(zip_name)

    # Update clean symbol dropdown
    @app.callback(
        Output("clean-symbol", "options"),
        Input("main-tabs", "value")
    )
    def update_clean_symbols(tab):
        if tab != "tab-analysis":
            return []
        info = get_database_info()
        symbols = sorted(set(d["symbol"] for d in info["details"]))
        return [{"label": s, "value": s} for s in symbols]

    # Update clean timeframe dropdown
    @app.callback(
        Output("clean-timeframe", "options"),
        Input("clean-symbol", "value")
    )
    def update_clean_timeframes(symbol):
        if not symbol:
            return []
        info = get_database_info()
        timeframes = sorted(set(d["timeframe"] for d in info["details"] if d["symbol"] == symbol))
        return [{"label": tf, "value": tf} for tf in timeframes]

    # Delete selected data
    @app.callback(
        Output("delete-status", "children"),
        Input("delete-selected-btn", "n_clicks"),
        State("clean-symbol", "value"),
        State("clean-timeframe", "value"),
        prevent_initial_call=True
    )
    def delete_selected_data(n_clicks, symbol, timeframe):
        if not symbol or not timeframe:
            return "❌ Please select both symbol and timeframe."
        path = symbol_timeframe_path(symbol, timeframe)
        fp = os.path.join(path, "data.parquet")
        if not os.path.exists(fp):
            return f"⚠️ Data file not found for {symbol} {timeframe}."
        try:
            os.remove(fp)
            if os.path.exists(path) and not os.listdir(path):
                os.rmdir(path)
            return f"✅ Deleted {symbol} {timeframe} data. You can now re‑run tasks with 'Overwrite' checked."
        except Exception as e:
            return f"❌ Error deleting: {str(e)}"

    # Enable delete all button
    @app.callback(
        Output("delete-all-btn", "disabled"),
        Input("confirm-delete-all", "value")
    )
    def enable_delete_all(confirm):
        return "confirm" not in confirm

    # Delete all data
    @app.callback(
        Output("delete-status", "children", allow_duplicate=True),
        Input("delete-all-btn", "n_clicks"),
        prevent_initial_call=True
    )
    def delete_all_data(n_clicks):
        if n_clicks is None:
            return ""
        try:
            shutil.rmtree(MARKET_DATA_DIR)
            os.makedirs(MARKET_DATA_DIR, exist_ok=True)
            return "✅ All market data deleted. You can now re‑run tasks to download fresh data."
        except Exception as e:
            return f"❌ Error deleting all data: {str(e)}"

    # Redownload full history
    @app.callback(
        Output("delete-status", "children", allow_duplicate=True),
        Input("redownload-full-btn", "n_clicks"),
        State("clean-symbol", "value"),
        State("clean-timeframe", "value"),
        prevent_initial_call=True
    )
    def redownload_full_history(n_clicks, symbol, timeframe):
        # This callback needs access to DownloadTask and tm from main app
        # It will be handled by a wrapper in the main app
        return "⚠️ This function requires task manager access. Please use the Tasks tab."

    # Redownload all existing data - REMOVED: This callback requires DownloadTask and tm
    # from the main app, so it has been kept in qw_signal_2-7-5-json5-3-table.py
    # The database.py version was just a placeholder.
