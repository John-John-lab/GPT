"""
Bybit Downloader – Two Tabs + Summary + Optimized Buffering (10k candles)
with Database Verification Tool and Real‑time Integrity Checks. 
Now with signal‑based downloading, candle analysis, and per‑task interactive charts.
"""
import os, json, time, threading, queue, uuid, shutil, glob, hashlib, re, functools, sys, bisect, math
from datetime import datetime, timedelta, timezone
import dash
from dash import dcc, html, Input, Output, State, MATCH, ALL, no_update, ctx, clientside_callback
import pandas as pd
import numpy as np
import requests
import plotly.express as px
import plotly.graph_objects as go
from plotly.subplots import make_subplots
from flask import send_file, request, jsonify
import pyarrow.parquet as pq
from strategies import detect_strategies
from database import (
    get_database_info, 
    symbol_timeframe_path, 
    VerificationManager, 
    vm,
    create_data_analysis_tab,
    register_database_callbacks,
    MARKET_DATA_DIR,
    INTERVAL_MS,
    DUCKDB_AVAILABLE
)

# =============================================================================
# UI HELPER FUNCTIONS - Pure presentation logic (no calculations)
# These functions format data for display only
# =============================================================================

def fmt_time_ui(ts):
    """
    ⚡ ULTRA-FAST timestamp formatting - NO pandas calls
    Pure UI function: formats timestamps for table display
    """
    if ts is None: return "-"
    try:
        if isinstance(ts, (float, np.floating)) and is_na(ts): return "-"
        if isinstance(ts, (datetime, pd.Timestamp)):
            return ts.strftime("%Y-%m-%d %H:%M")
        if isinstance(ts, str):
            # ⚡ FAST PATH: Handle ISO-8601 strings directly (85x faster than pandas)
            ts_clean = ts.strip()
            if ts_clean.endswith('Z'):
                ts_clean = ts_clean[:-1]
            if 'T' in ts_clean:
                # ISO format: 2024-01-15T10:30:45.123
                if '.' in ts_clean:
                    dt = datetime.strptime(ts_clean.split('.')[0], "%Y-%m-%dT%H:%M:%S")
                else:
                    dt = datetime.strptime(ts_clean, "%Y-%m-%dT%H:%M:%S")
                return dt.strftime("%Y-%m-%d %H:%M")
            # Try numeric string
            try:
                ts_num = float(ts_clean)
                return datetime.fromtimestamp(ts_num / 1000.0, tz=timezone.utc).strftime("%Y-%m-%d %H:%M")
            except ValueError:
                pass
        # Numeric timestamp (milliseconds)
        if isinstance(ts, (int, float)):
            return datetime.fromtimestamp(ts / 1000.0, tz=timezone.utc).strftime("%Y-%m-%d %H:%M")
    except Exception:
        return "-"
    # Fallback to pandas (slow path - should rarely happen)
    try:
        return pd.to_datetime(ts).strftime("%Y-%m-%d %H:%M")
    except Exception:
        return "-"

def fmt_dd_ui(val):
    """
    Format drawdown/adverse value as percentage
    Pure UI function: formats numeric values for table display
    """
    if val is None: return "-"
    if isinstance(val, (float, np.floating)) and is_na(val): return "-"
    try:
        return f"{float(val):.2f}%"
    except Exception:
        return "-"

def is_na(val):
    """⚡ Ultra-fast NA check without pandas - GLOBAL VERSION for use in all functions"""
    if val is None:
        return True
    if isinstance(val, float):
        return math.isnan(val)
    if isinstance(val, np.floating):
        return np.isnan(val)
    return False

def get_adverse_range_ui(pct):
    """
    Categorize percentage into ranges for statistics display
    Pure UI function: returns range category string
    """
    if pct is None or (isinstance(pct, float) and is_na(pct)):
        return None
    if 0 <= pct < 0.5: return "0-0.5%"
    elif 0.5 <= pct < 1: return "0.5-1%"
    elif 1 <= pct < 2: return "1-2%"
    elif 2 <= pct < 3: return "2-3%"
    elif 3 <= pct < 4: return "3-4%"
    elif 4 <= pct < 5: return "4-5%"
    elif 5 <= pct < 10: return "5-10%"
    elif 10 <= pct < 20: return "10-20%"
    elif 20 <= pct < 30: return "20-30%"
    elif pct >= 30: return ">30%"
    return None

# 🔧 CRITICAL: Global aliases for thread-safe numpy/bisect access in background threads
np_local_global = None
bisect_local_global = None

# =============================================================================
# SHADOW MODE VERIFICATION SYSTEM
# Ensures vectorized calculations match original logic byte-for-byte
# =============================================================================

SHADOW_MODE_ENABLED = True  # Toggle for dual-execution verification
SHADOW_MISMATCH_COUNT = 0   # Track mismatches for monitoring

def compare_results(original, vectorized, field_name, tolerance=1e-9):
    """
    Compare original and vectorized results with strict tolerance.
    
    Returns:
        tuple: (match: bool, error_msg: str or None)
    """
    if original is None and vectorized is None:
        return True, None
    if original is None or vectorized is None:
        return False, f"{field_name}: None mismatch (orig={original}, vect={vectorized})"
    
    # Handle boolean comparisons
    if isinstance(original, bool):
        if original != vectorized:
            return False, f"{field_name}: bool mismatch (orig={original}, vect={vectorized})"
        return True, None
    
    # Handle numeric comparisons with tolerance
    try:
        orig_val = float(original)
        vect_val = float(vectorized)
        if math.isnan(orig_val) and math.isnan(vect_val):
            return True, None
        if math.isinf(orig_val) or math.isinf(vect_val):
            if orig_val == vect_val:
                return True, None
            return False, f"{field_name}: inf mismatch (orig={orig_val}, vect={vect_val})"
        if abs(orig_val - vect_val) > tolerance:
            return False, f"{field_name}: numeric mismatch (orig={orig_val}, vect={vect_val}, diff={abs(orig_val - vect_val)})"
        return True, None
    except (TypeError, ValueError):
        # Non-numeric comparison (strings, etc.)
        if original != vectorized:
            return False, f"{field_name}: value mismatch (orig={original}, vect={vectorized})"
        return True, None

# =============================================================================
# JSON PERSISTENCE & DATA INTEGRITY LAYER
# Implements "Serialization Bridge" pattern for safe RAM ↔ Disk conversion
# =============================================================================

def sanitize_for_json(obj):
    """
    Recursively convert Python/NumPy objects to JSON-safe primitives.
    
    This function is ONLY called at I/O boundaries (save/load), never during
    mathematical calculations. It ensures:
    - datetime → ISO-8601 UTC strings with 'Z' suffix
    - NumPy scalars → native Python types
    - NaN/Inf → null (None)
    - Nested structures → recursively sanitized
    
    Args:
        obj: Any Python object (dict, list, scalar, datetime, NumPy type, etc.)
    
    Returns:
        JSON-serializable equivalent of the input object
    """
    # Handle None/null
    if obj is None:
        return None
    
    # Handle datetime objects → ISO-8601 UTC string
    if isinstance(obj, (datetime, pd.Timestamp)):
        # Ensure UTC timezone
        if obj.tzinfo is None:
            obj = obj.replace(tzinfo=timezone.utc)
        else:
            obj = obj.astimezone(timezone.utc)
        # Format with explicit Z suffix for UTC
        return obj.strftime('%Y-%m-%dT%H:%M:%SZ')
    
    # Handle NumPy floating point types
    if isinstance(obj, np.floating):
        val = float(obj)
        if math.isnan(val) or math.isinf(val):
            return None
        return val
    
    # Handle NumPy integer types
    if isinstance(obj, np.integer):
        return int(obj)
    
    # Handle NumPy boolean types
    if isinstance(obj, np.bool_):
        return bool(obj)
    
    # Handle NumPy arrays (convert to list)
    if isinstance(obj, np.ndarray):
        return sanitize_for_json(obj.tolist())
    
    # Handle native Python float (check for NaN/Inf)
    if isinstance(obj, float):
        if math.isnan(obj) or math.isinf(obj):
            return None
        return obj
    
    # Handle native Python int, bool, str (pass through)
    if isinstance(obj, (int, bool, str)):
        return obj
    
    # Handle lists (recursive)
    if isinstance(obj, list):
        return [sanitize_for_json(item) for item in obj]
    
    # Handle dicts (recursive)
    if isinstance(obj, dict):
        return {key: sanitize_for_json(value) for key, value in obj.items()}
    
    # Handle any other type by converting to string (fallback)
    try:
        return str(obj)
    except Exception:
        return None


def _parse_timestamp(val):
    """
    Parse timestamp strings back to UTC-aware datetime objects.
    
    This function is called during JSON loading to ensure all timestamps
    are converted to native datetime objects with explicit UTC timezone.
    
    Args:
        val: Value that might be a timestamp string or already a datetime
    
    Returns:
        timezone-aware datetime object (UTC) if input is a string,
        original value if already a datetime,
        None if parsing fails
    """
    # If already a datetime, ensure it's UTC-aware
    if isinstance(val, (datetime, pd.Timestamp)):
        if val.tzinfo is None:
            return val.replace(tzinfo=timezone.utc)
        return val.astimezone(timezone.utc)
    
    # If not a string, return as-is
    if not isinstance(val, str):
        return val
    
    # Try to parse the string
    try:
        # Handle various ISO-8601 formats
        val_clean = val.strip()
        
        # Replace space with T if needed
        if 'T' not in val_clean and ' ' in val_clean:
            val_clean = val_clean.replace(' ', 'T')
        
        # Remove trailing Z if present (fromisoformat doesn't handle it in older Python)
        if val_clean.endswith('Z'):
            val_clean = val_clean[:-1]
        
        # Parse the datetime
        dt = datetime.fromisoformat(val_clean)
        
        # Force UTC timezone if naive
        if dt.tzinfo is None:
            dt = dt.replace(tzinfo=timezone.utc)
        else:
            dt = dt.astimezone(timezone.utc)
        
        return dt
    
    except (ValueError, TypeError):
        # If parsing fails, return None (caller should handle this)
        return None


# =============================================================================
# END JSON PERSISTENCE LAYER
# =============================================================================

# DuckDB availability is now imported from database module
# See: from database import DUCKDB_AVAILABLE

# ---------- Configuration ----------
LOGS_DIR = "./task_logs"
os.makedirs(LOGS_DIR, exist_ok=True)
BYBIT_BASE_URL = "https://api.bybit.com"
RATE_LIMIT = 0.05  # 50 ms between requests (20 per second) – safe for public endpoints
BUFFER_SIZE = 10000  # Not used for raw collection now, kept for compatibility
SIGNAL_BUFFER_MINUTES = 5  # Number of minutes before signal time to start download (to capture the exact signal candle)
TIMEFRAMES = {
    "1 minute": "1", "3 minutes": "3", "5 minutes": "5", "10 minutes": "10",
    "15 minutes": "15", "30 minutes": "30", "1 hour": "60", "2 hours": "120",
    "4 hours": "240", "1 day": "D", "1 week": "W"
}
# Millisecond durations for each interval (used for gap detection and range calculations)
# INTERVAL_MS is now imported from database module
PRICE_CONTINUITY_TOLERANCE = 0.10
# Pagination constant for task summary table
PAGE_SIZE = 300

# Global timestamp to force summary table refresh after recalculation
recalculation_complete_timestamp = 0

# =============================================================================
# PERFORMANCE TRACING UTILITIES
# =============================================================================

class PerfTimer:
    """High-precision timer for performance tracing."""
    def __init__(self, label):
        self.label = label
        self.start_time = None
        self.last_time = None
        
    def start(self):
        self.start_time = time.perf_counter()
        self.last_time = self.start_time
        print(f"[TRACE] ⏱️  START: {self.label}")
        return self
        
    def check(self, step_name):
        current = time.perf_counter()
        elapsed = current - self.last_time
        total = current - self.start_time
        print(f"[TRACE]    └─ {step_name}: {elapsed:.4f}s (Total: {total:.4f}s)")
        self.last_time = current
        return self
        
    def end(self):
        if self.start_time:
            total = time.perf_counter() - self.start_time
            print(f"[TRACE] ✅ END: {self.label} ({total:.4f}s)")
        return self

# 🔧 GOLDEN STORE: Pre-processed task data cache
golden_task_store_data = None
golden_store_version = 0
# 🔧 RECALCULATION LOCK: Prevents UI interaction during heavy processing
recalc_lock = {"locked": False, "message": ""}
is_recalculating_flag = False
recalc_progress_count = 0  # for the status bar
recalc_total_tasks = 0
STOP_REQUESTED = False  # Patch A: Hard Stop Flag for safe interruption
current_tasks = []  # Master dataset in RAM for atomic swaps

# Pagination & Caching State
page_html_cache = {}  # Cache for rendered page HTML: {page_num: html.Div}
last_rendered_stats = {} # Cache for summary tables to prevent disappearance

# Global stats cache for ALL tasks (calculated once per data version)
cached_signal_stats_html = None  # Full Signal Performance Summary table
cached_small_stats_data = None   # Small summary stats dict
stats_cache_version = -1         # Version of data these stats belong to

# ---------- Low-RAM Parquet Cache ----------
@functools.lru_cache(maxsize=4)  # Holds max 4 DFs to protect old Mac RAM
def _load_parquet_cached(file_path: str, mtime: float) -> pd.DataFrame:
    return pd.read_parquet(file_path)

def load_task_data_cached(task) -> pd.DataFrame:
    """
    Load cached candle data for a task, filtered by the task's time period.
    
    🔧 CRITICAL: Respects your original design:
    - Uses already-loaded candles from parquet (fast, no re-download)
    - Filters ONLY to the task's specific analysis period (start_date to end_date)
    - Minimizes data for faster recalculation
    
    🔧 CRITICAL: Use global np_local_global set by analyze_signal() to avoid import issues
    """
    # 🔧 Use the global alias set by analyze_signal() instead of importing locally
    global np_local_global
    if 'np_local_global' not in globals() or np_local_global is None:
        import numpy as np_local_global
    
    sym = task.symbols[0]
    path = symbol_timeframe_path(sym, task.timeframe)
    fp = os.path.join(path, "data.parquet")
    if not os.path.exists(fp):
        print(f"⚠️ [CACHE] No parquet file found for {sym} {task.timeframe}")
        return pd.DataFrame()
    
    mtime = os.path.getmtime(fp)
    df = _load_parquet_cached(fp, mtime).copy()
    
    # Guarantee timestamp is int64 milliseconds for safe searchsorted & math
    if 'timestamp' in df.columns:
        if df['timestamp'].dtype.name.startswith('datetime'):
            df['timestamp'] = (df['timestamp'].astype(np_local_global.int64) // 1_000_000).astype(np_local_global.int64)
        else:
            df['timestamp'] = df['timestamp'].astype(np_local_global.int64)
    
    # 🔧 FILTER by task's analysis period (start_date to end_date)
    # This respects your JSON design: each task has its own time window
    if task.start_date and task.end_date:
        start_ms = int(task.start_date.replace(tzinfo=timezone.utc).timestamp() * 1000)
        end_ms = int(task.end_date.replace(tzinfo=timezone.utc).timestamp() * 1000)
        
        # Add buffer before start (pre_buffer_minutes) to capture events leading to signal
        buffer_ms = getattr(task, 'pre_buffer_minutes', 60) * 60 * 1000
        start_ms -= buffer_ms
        
        df_filtered = df[(df['timestamp'] >= start_ms) & (df['timestamp'] <= end_ms)]
        
        if df_filtered.empty:
            print(f"⚠️ [CACHE] No data in period {task.start_date} to {task.end_date} for {sym} {task.timeframe}")
        else:
            print(f"✅ [CACHE] Loaded {len(df_filtered)} candles (filtered from {len(df)}) for {sym} {task.timeframe}")
        
        return df_filtered
    
    return df

def clear_parquet_cache():
    _load_parquet_cached.cache_clear()

# ---------- Database Helpers ----------
# symbol_timeframe_path is now imported from database module
# get_database_info is now imported from database module

def write_parquet_batch(symbol, timeframe, df, overwrite=False, task=None):
    """
    Write a DataFrame to a Parquet file inside the symbol/timeframe folder.
    If overwrite=False and file exists, merge with existing data (keeping latest by timestamp).
    Returns number of duplicate rows removed (if task provided, logs it).
    """
    path = symbol_timeframe_path(symbol, timeframe)
    os.makedirs(path, exist_ok=True)
    file_path = os.path.join(path, "data.parquet")
    removed = 0
    if os.path.exists(file_path) and not overwrite:
        existing = pd.read_parquet(file_path)
        before = len(existing) + len(df)
        combined = pd.concat([existing, df]).drop_duplicates("timestamp", keep="last")
        removed = before - len(combined)
        combined.sort_values("timestamp").to_parquet(file_path, compression="zstd")
        if task and removed > 0:
            task.add_log(f"Removed {removed} duplicate timestamps during merge")
    else:
        df.to_parquet(file_path, compression="zstd")
    return removed

def read_existing_range(symbol, timeframe):
    """Read the minimum and maximum timestamp from an existing Parquet file."""
    p = symbol_timeframe_path(symbol, timeframe)
    fp = os.path.join(p, "data.parquet")
    if not os.path.exists(fp):
        return None, None
    df = pd.read_parquet(fp)
    if df.empty:
        return None, None
    now_ts = int(time.time() * 1000)
    if df["timestamp"].max() > now_ts + 86400000 * 365 * 10:
        print(f"WARNING: {symbol} {timeframe} has timestamps far in the future.")
    min_ts = int(df["timestamp"].astype(int).min())
    max_ts = int(df["timestamp"].astype(int).max())
    return min_ts, max_ts



# ---------- Real Bybit API with Exponential Backoff ----------
def fetch_symbols():
    """
    Fetch all USDT perpetual symbols from Bybit.
    Returns a list of ALL symbol strings (no limit).
    (Kept for compatibility, but not used in new signal‑based workflow.)
    """
    url = f"{BYBIT_BASE_URL}/v5/market/instruments-info?category=linear"
    try:
        resp = requests.get(url, timeout=10)
        data = resp.json()
        if data['retCode'] == 0:
            symbols = [item['symbol'] for item in data['result']['list'] if item['symbol'].endswith('USDT')]
            return symbols
    except Exception as e:
        print(f"Error fetching symbols: {e}")
    return ["BTCUSDT", "ETHUSDT"]

def fetch_klines(symbol, interval, start, end, limit=200, max_retries=3):
    """
    Fetch klines from Bybit v5 market/kline endpoint with exponential backoff.
    Returns DataFrame with columns: timestamp, open, high, low, close, volume.
    Data is returned in the API's native order: newest first (descending timestamp).
    We do NOT reverse it – the download loop expects descending order.
    """
    url = f"{BYBIT_BASE_URL}/v5/market/kline"
    params = {
        "category": "linear",
        "symbol": symbol,
        "interval": interval,
        "start": start,
        "end": end,
        "limit": limit
    }
    for attempt in range(max_retries):
        try:
            resp = requests.get(url, params=params, timeout=10)
            data = resp.json()
            if data['retCode'] != 0:
                print(f"API error (attempt {attempt+1}): {data}")
                if attempt < max_retries - 1:
                    time.sleep(2 ** attempt)  # exponential backoff: 1, 2, 4 seconds
                continue
            klines = data['result']['list']
            # Keep as is: newest first (descending timestamps)
            rows = []
            for k in klines:
                ts = int(k[0])
                open_p = float(k[1])
                high_p = float(k[2])
                low_p = float(k[3])
                close_p = float(k[4])
                volume = float(k[5])
                rows.append([ts, open_p, high_p, low_p, close_p, volume])
            return pd.DataFrame(rows, columns=["timestamp", "open", "high", "low", "close", "volume"])
        except Exception as e:
            print(f"Error fetching klines (attempt {attempt+1}): {e}")
            if attempt < max_retries - 1:
                time.sleep(2 ** attempt)
            else:
                return pd.DataFrame()
    return pd.DataFrame()

def find_earliest_candle(symbol, interval):
    """
    Determine the earliest available timestamp for a symbol/interval.
    Tries 2020-01-01 as a safe start for USDT perpetuals; if no data, falls back to 2 years ago.
    """
    start_ms = int(datetime(2020, 1, 1, tzinfo=timezone.utc).timestamp() * 1000)
    df = fetch_klines(symbol, interval, start_ms, start_ms + 86400000, limit=1)
    if not df.empty:
        return df.iloc[0]['timestamp']
    return int((datetime.now() - timedelta(days=730)).timestamp() * 1000)

# ---------- Signal Parser ----------
def parse_signal_text(text):
    """
    Parse the custom signal text format.
    Returns a list of dictionaries, each with keys:
    symbol, time (datetime), price (float), direction ('resistance' or 'support'),
    file_timeframe (e.g., 'D1', 'H4'), raw_text (optional)
    """
    # Split by blank lines (two or more newlines)
    blocks = re.split(r'\n\s*\n', text.strip())
    signals = []
    for block in blocks:
        if not block.strip():
            continue
        # Extract date/time line
        date_time_match = re.search(r'(\d{2})\.(\d{2})\.(\d{4}) по времени биржи в (\d{2}):(\d{2}):(\d{2}) UTC', block)
        if not date_time_match:
            continue
        day, month, year, hour, minute, second = date_time_match.groups()
        # Create UTC‑aware datetime (CRITICAL FIX)
        signal_time = datetime(int(year), int(month), int(day),
                               int(hour), int(minute), int(second),
                               tzinfo=timezone.utc)
        # Extract symbol
        symbol_match = re.search(r'Фьючерс:\s*(\w+)', block)
        if not symbol_match:
            continue
        symbol = symbol_match.group(1)
        # Extract timeframe (e.g., D1, H4)
        tf_match = re.search(r'\b(D1|H4|H1|H2|H3|M1|M5|M15|M30)\b', block)
        file_timeframe = tf_match.group(1) if tf_match else "unknown"
        # Extract direction
        dir_match = re.search(r'[📈📉]\s*["“”]?([А-Яа-я]+)["“”]?', block)
        if dir_match:
            dir_text = dir_match.group(1)
            direction = 'resistance' if 'Сопротивление' in dir_text else 'support'
        else:
            direction = 'unknown'
        # Extract price
        price_match = re.search(r'Цена:\s*([\d,]+)', block)
        if not price_match:
            continue
        price_str = price_match.group(1).replace(',', '.')
        price = float(price_str)
        signals.append({
            'symbol': symbol,
            'time': signal_time,
            'price': price,
            'direction': direction,
            'file_timeframe': file_timeframe,
        })
    return signals

# ---------- Task Manager ----------
class DownloadTask:
    """Represents a single download job (multiple symbols possible)."""
    def __init__(self, task_id, symbols, timeframe, mode, start_date=None, end_date=None, overwrite=False, price_continuity_check=False,
                 signal_time=None, signal_price=None, signal_symbol=None, signal_direction=None, analyze_beyond=False, enable_strategy=True, enable_impulse=True, pre_buffer_minutes=5, log_events=True, hide_logs=True):
        self.task_id = task_id
        self.symbols = symbols if isinstance(symbols, list) else [symbols]
        self.timeframe = timeframe
        self.mode = mode
        self.start_date = start_date
        self.end_date = end_date
        self.overwrite = overwrite
        self.price_continuity_check = price_continuity_check
        # Signal analysis attributes
        self.signal_time = signal_time          # timestamp in ms
        self.signal_price = signal_price
        self.signal_symbol = signal_symbol      # should match symbols[0] for single symbol tasks
        self.signal_direction = signal_direction  # 'resistance' or 'support'
        self.analyze_beyond = analyze_beyond    # whether to continue analysis beyond the selected period
        self.enable_strategy = enable_strategy
        self.enable_impulse = enable_impulse
        # Results of analysis (to be filled after analyze_signal)
        self.first_event_time = None
        self.first_event_type = None
        self.first_event_is_pin = False
        self.first_event_close = None
        self.price_change_pct = None
        self.reached_level = False
        self.reversed_direction = False
        self.events = []   # list of all events for charting: each is dict {'timestamp': ts, 'type': etype, 'kind': 'touch'/'bounce'/'breakthrough', 'close': close}
        self.strategy_signals = []      # list of detailed signal dicts
        self.strategy_log_summary = "-"
        self.strategy_confidence = 0.0
        
        self.hit_1 = False
        self.hit_1_5 = False
        self.hit_2 = False
        # First hit timing in expected direction
        self.first_hit_1_expected = False
        self.first_hit_1_5_expected = False
        self.first_hit_2_expected = False
        self.first_hit_1_expected_time = None
        self.first_hit_1_5_expected_time = None
        self.first_hit_2_expected_time = None
        # First hit timing in opposite direction
        self.first_hit_1_opposite = False
        self.first_hit_1_5_opposite = False
        self.first_hit_2_opposite = False
        self.first_hit_1_opposite_time = None
        self.first_hit_1_5_opposite_time = None
        self.first_hit_2_opposite_time = None

        self.drawdown_before_level = None
        self.drawdown_before_level_time = None
        self.drawdown_before_1pct = None
        self.drawdown_before_1pct_time = None
        self.drawdown_before_1_5pct = None
        self.drawdown_before_1_5pct_time = None
        self.drawdown_before_2pct = None
        self.drawdown_before_2pct_time = None
        # Maximum adverse move (opposite direction) during entire period
        self.max_adverse_move_pct = None
        self.max_adverse_time = None
        # Maximum expected move (forward direction) during entire period
        self.max_expected_move_pct = None
        self.max_expected_time = None
        # Maximum adverse move before first return to signal price
        self.max_adverse_before_return_pct = None
        self.max_adverse_before_return_time = None
        self.returned_to_signal = False   # NEW: flag for whether price ever returned to signal level
        # New: adverse and favorable metrics based on starting price (entry at signal time)
        self.max_adverse_sgnl_pct = None
        self.max_adverse_sgnl_time = None
        self.max_adverse_before_return_sgnl_pct = None
        self.max_adverse_before_return_sgnl_time = None
        self.returned_to_sgnl = False
        self.max_expected_sgnl_pct = None
        self.max_expected_sgnl_time = None
        self.status = "queued"
        self.progress = 0.0
        self.log = []
        self.total_candles = 0
        self.downloaded_candles = 0
        self.stop_event = threading.Event()
        self.pause_event = threading.Event()
        self.paused = False
        self.last_ts = None
        self.last_count = 0
        self.pre_buffer_minutes = pre_buffer_minutes
        self.symbol_ranges = {}  # store intended (start_ms, end_ms) for completeness check
        # Buffer for current symbol – collect raw batches (newest first, as returned by API)
        self.raw_batches = []
        self._batches_since_flush = 0  # Tracks incremental saves
        self.state_lock = threading.Lock()  # Protects strategy_signals & log
        self._chart_cache = {}  # Low-spec: max 1 cached chart view per task
        self.log_events = log_events  # Toggle for detailed event logging in task table
        self.hide_logs = hide_logs  # NEW: Controls log visibility in summary table

    def add_log(self, msg):
        """Add a timestamped message to the task's log and print to console."""
        timestamp = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
        with self.state_lock:
            self.log.append(f"[{timestamp}] {msg}")
        print(f"Task {self.task_id[:8]}: {msg}")

    def _flush_and_process(self, symbol):
        """
        After finishing a symbol, take all raw batches (newest first),
        concatenate, sort ascending, deduplicate, and write final Parquet.
        """
        if not self.raw_batches:
            return
        self.add_log(f"Processing {len(self.raw_batches)} batches for {symbol}...")
        combined = pd.concat(self.raw_batches, ignore_index=True)
        combined = combined.sort_values("timestamp").reset_index(drop=True)
        before = len(combined)
        combined = combined.drop_duplicates("timestamp", keep="last")
        removed = before - len(combined)
        if removed > 0:
            self.add_log(f"Removed {removed} duplicate timestamps during final processing")
        write_parquet_batch(symbol, self.timeframe, combined, overwrite=self.overwrite, task=self)
        self.add_log(f"Saved {len(combined)} candles to disk for {symbol}")
        self.raw_batches = []

    def _prepare_for_overwrite(self, symbol):
        if self.overwrite:
            path = symbol_timeframe_path(symbol, self.timeframe)
            file_path = os.path.join(path, "data.parquet")
            if os.path.exists(file_path):
                os.remove(file_path)
            self.add_log(f"Removed existing file for {symbol} (overwrite mode)")

    def _incremental_flush(self, symbol):
        """Safely merge & save accumulated batches to Parquet without blocking."""
        if not self.raw_batches:
            return
        self.add_log(f"💾 Incremental save: flushing {len(self.raw_batches)} batches for {symbol}...")
        combined = pd.concat(self.raw_batches, ignore_index=True)
        combined = combined.sort_values("timestamp").reset_index(drop=True)
        combined = combined.drop_duplicates("timestamp", keep="last")
        # Merge with existing file (overwrite=False) to preserve partial progress
        write_parquet_batch(symbol, self.timeframe, combined, overwrite=False, task=self)
        self.raw_batches = []
        self._batches_since_flush = 0

    def run(self, manager):
        try:
            self.status = "running"
            self.add_log(f"Started: {', '.join(self.symbols)} | {self.mode}")
            for sym in self.symbols:
                if self.stop_event.is_set():
                    self.add_log("Stop requested")
                    break
                self._prepare_for_overwrite(sym)
                self._download_symbol(sym)
                self._flush_and_process(sym)
            self.status = "stopped" if self.stop_event.is_set() else "completed"
            self.add_log(f"Task {self.status}.")
        except Exception as e:
            self.status = "error"
            self.add_log(f"Error: {e}")
        finally:
            self.total_candles = self.downloaded_candles
            # If task finished (even if download was skipped), force 100%
            if self.status == "completed":
                self.progress = 100.0
            self.pause_event.clear()
            self.paused = False
            self.verify_saved_data()
            self.final_integrity_check()
            # ----- Signal analysis (respects period, for summary table) -----
            if self.signal_time is not None:
                try:
                    self.analyze_signal()
                except Exception as e:
                    self.add_log(f"⚠️ Analysis error (non-fatal): {e}")
            # Prepare data for both strategy and impulse detection
            sym = self.symbols[0]
            path = symbol_timeframe_path(sym, self.timeframe)
            fp = os.path.join(path, "data.parquet")
            df_limited = None
            if os.path.exists(fp):
                full_df = pd.read_parquet(fp)
                buffer_ms = self.pre_buffer_minutes * 60 * 1000
                start_ms = max(0, self.signal_time - buffer_ms)
                if self.start_date and self.end_date:
                    window_len_ms = int(self.end_date.replace(tzinfo=timezone.utc).timestamp() * 1000) - int(self.start_date.replace(tzinfo=timezone.utc).timestamp() * 1000)
                    cutoff_time = self.signal_time + window_len_ms
                    df_limited = full_df[(full_df['timestamp'] >= start_ms) & (full_df['timestamp'] <= cutoff_time)].copy()
                else:
                    df_limited = full_df[full_df['timestamp'] >= start_ms].copy()
            # ----- Strategy detection -----
            if self.enable_strategy:
                try:
                    if df_limited is not None and not df_limited.empty:
                        signals = detect_strategies(df_limited, self.signal_price, self.signal_direction, self.signal_time, verbose=False)
                        for sig in signals:
                            self.add_strategy_signal(
                                sig['type'], sig['direction'], sig['entry_price'], sig['entry_time_ms'],
                                exit_price=sig.get('exit_price'), exit_time_ms=sig.get('exit_time_ms'),
                                stop_loss=sig.get('stop_loss'), take_profit=sig.get('take_profit_1'),
                                confidence=sig['confidence']
                            )
                        self.add_log(f"✅ Strategy detection: {len(signals)} signals found (view in Details modal)")
                except Exception as e:
                    self.add_log(f"Strategy detection error: {e}")
            else:
                self.add_log("⏸ Strategy detection disabled for this task.")

            # ----- Impulse detection -----
            if self.enable_impulse:
                try:
                    from impulse import backtest_impulse
                    if df_limited is not None and not df_limited.empty:
                        impulse_result = backtest_impulse(
                            df_limited,
                            self.signal_price,
                            self.signal_direction,
                            self.signal_time,
                            verbose=False
                        )
                        for trade in impulse_result['trades']:
                            signal_dict = {
                                'type': 'impulse',
                                'direction': trade['direction'],
                                'entry_price': trade['entry_price'],
                                'entry_time_ms': trade['entry_time_ms'],
                                'exit_price': trade['exit_price'],
                                'exit_time_ms': trade['exit_time_ms'],
                                'exit_reason': trade['exit_reason'],
                                'confidence': trade['confidence'],
                                'delta_pct': trade['pnl'],
                                'extra_info': trade['extra_info']
                            }
                            self.add_strategy_signal(
                                signal_dict['type'], signal_dict['direction'],
                                signal_dict['entry_price'], signal_dict['entry_time_ms'],
                                exit_price=signal_dict['exit_price'],
                                exit_time_ms=signal_dict['exit_time_ms'],
                                confidence=signal_dict['confidence'],
                                extra_info=signal_dict['extra_info']
                            )
                        self.add_log(f"✅ Impulse detection: {impulse_result['count']} trades found (view in Impulse modal)")
                except Exception as e:
                    self.add_log(f"Impulse detection error: {e}")
            else:
                self.add_log("⏸ Impulse detection disabled for this task.")
            # ----- Compute strategy outcomes (no forced exit filling) -----
            if self.strategy_signals:
                best_signal = None
                best_delta = -999.0
                for sig in self.strategy_signals:
                    if sig.get('exit_price') is None:
                        self.add_log(f"WARNING: Signal {sig['type']} has no exit_price – skipping")
                        continue
                    if sig['direction'] == 'buy':
                        delta = (sig['exit_price'] - sig['entry_price']) / sig['entry_price'] * 100
                    else:
                        delta = (sig['entry_price'] - sig['exit_price']) / sig['entry_price'] * 100
                    sig['delta_pct'] = delta
                    self.add_log(
                        f"  Strategy: {sig['type']} {sig['direction']} entry {sig['entry_price']:.4f}, "
                        f"exit {sig['exit_price']:.4f} at {pd.to_datetime(sig['exit_time_ms'], unit='ms')}, Δ {delta:.2f}%"
                    )
                    if delta > best_delta:
                        best_delta = delta
                        best_signal = sig
                if best_signal:
                    # Safe formatting: handle None delta_pct
                    dp = best_signal.get('delta_pct')
                    dp_val = dp if dp is not None else 0.0
                    self.strategy_log_summary = f"{best_signal['type'].capitalize()} {best_signal['direction'].upper()} ({dp_val:.1f}%)"
                    self.strategy_confidence = best_signal['confidence']
                else:
                    self.strategy_log_summary = "No valid signal"
            else:
                self.strategy_log_summary = "No signal"

    def verify_saved_data(self):
        for sym in self.symbols:
            path = symbol_timeframe_path(sym, self.timeframe)
            fp = os.path.join(path, "data.parquet")
            if os.path.exists(fp):
                df = pd.read_parquet(fp)
                self.add_log(f"DB verification: {sym} has {len(df)} candles.")
            else:
                self.add_log(f"DB verification: {sym} file not found (no data saved).")

    def final_integrity_check(self):
        """Enhanced post‑completion checks (unchanged)."""
        interval_ms = INTERVAL_MS.get(self.timeframe, 60000)
        for sym in self.symbols:
            path = symbol_timeframe_path(sym, self.timeframe)
            fp = os.path.join(path, "data.parquet")
            if not os.path.exists(fp):
                continue
            try:
                meta = pq.read_metadata(fp)
                self.add_log(f"Parquet file OK: {meta.num_rows} rows, {meta.num_columns} columns")
            except Exception as e:
                self.add_log(f"Parquet integrity error: {e}")
            try:
                df = pd.read_parquet(fp)
            except Exception as e:
                self.add_log(f"Could not read Parquet file: {e}")
                continue
            if len(df) < 2:
                continue
            dups = df["timestamp"].duplicated().sum()
            if dups:
                self.add_log(f"Integrity warning: {sym} has {dups} duplicate timestamps!")
            else:
                self.add_log(f"✓ No duplicates")
            diffs = df["timestamp"].diff().iloc[1:].astype('int64')
            threshold_ns = interval_ms * 1_000_000 * 1.5
            gaps = diffs[diffs > threshold_ns]
            if not gaps.empty:
                self.add_log(f"⚠ Gaps: {len(gaps)} detected (largest {gaps.max()/1e6:.1f} ms).")
            else:
                self.add_log(f"✓ No significant gaps")
            aligned = df["timestamp"] % interval_ms == 0
            if not aligned.all():
                bad_count = (~aligned).sum()
                self.add_log(f"⚠ {bad_count} timestamps not aligned to {interval_ms}ms interval!")
            else:
                self.add_log(f"✓ All timestamps aligned")
            invalid = df[
                (df['high'] < df['low']) |
                (df['high'] < df['open']) |
                (df['high'] < df['close']) |
                (df['low'] > df['open']) |
                (df['low'] > df['close']) |
                (df['volume'] < 0)
            ]
            if not invalid.empty:
                self.add_log(f"⚠ {len(invalid)} candles with OHLCV inconsistency!")
                for idx, row in invalid.head(3).iterrows():
                    self.add_log(f"    {row['timestamp']}: H={row['high']:.2f}, L={row['low']:.2f}, O={row['open']:.2f}, C={row['close']:.2f}")
            else:
                self.add_log(f"✓ OHLCV consistent")
            # FIXED: only warn if type is NOT float64 or int64
            # Compare dtype.name (string) to avoid numpy dtype mismatch warnings
            expected_types = {'float64', 'int64', 'float32', 'int32'}
            type_issues = False
            for col in ['open', 'high', 'low', 'close', 'volume']:
                if col in df.columns and df[col].dtype.name not in expected_types:
                    self.add_log(f"⚠ Column '{col}' has unexpected type {df[col].dtype}")
                    type_issues = True
            if not type_issues:
                self.add_log(f"✓ Data types OK")
            nan_cols = df.columns[df.isna().any()].tolist()
            if nan_cols:
                self.add_log(f"⚠ NaN values found in columns: {nan_cols}")
            else:
                self.add_log(f"✓ No NaN values")
            zero_vol = (df['volume'] == 0).sum()
            if zero_vol > 0:
                self.add_log(f"ℹ {zero_vol} candles have zero volume (may be normal)")
            else:
                self.add_log(f"✓ All candles have positive volume")
            returns = df['close'].pct_change().fillna(0)
            mean_ret = returns.mean()
            std_ret = returns.std()
            outliers = returns[abs(returns - mean_ret) > 5 * std_ret]
            if len(outliers) > 0:
                self.add_log(f"⚠ {len(outliers)} candles with extreme price movements (potential errors)")
            if len(df) > 20:
                vol_mean = df['volume'].rolling(20).mean()
                vol_std = df['volume'].rolling(20).std()
                volume_spikes = df[(df['volume'] > vol_mean + 3 * vol_std) & (vol_std > 0)]
                if len(volume_spikes) > 0:
                    self.add_log(f"ℹ {len(volume_spikes)} volume spikes detected")
                zero_streaks = (df['volume'] == 0).astype(int).groupby(df['volume'].ne(0).cumsum()).sum()
                long_streaks = zero_streaks[zero_streaks > 10]
                if not long_streaks.empty:
                    self.add_log(f"⚠ {len(long_streaks)} periods of extended zero volume (>10 candles)")
            if sym in self.symbol_ranges and self.mode != 'full':
                start_ms, end_ms = self.symbol_ranges[sym]
                expected = (end_ms - start_ms) // interval_ms + 1
                actual = len(df)
                if actual != expected:
                    self.add_log(f"⚠ Completeness: expected {expected} candles, got {actual}")
                else:
                    self.add_log(f"✓ Completeness: {actual} candles match expected")
                if not df.empty and (df['timestamp'].min() < start_ms or df['timestamp'].max() > end_ms):
                    self.add_log(f"⚠ Timestamps outside intended range!")
            summary_path = os.path.join(LOGS_DIR, f"verify_{self.task_id}_{datetime.now().strftime('%Y%m%d_%H%M%S')}.log")
            with open(summary_path, "w") as f:
                f.write("\n".join(self.log[-20:]))

    def _download_symbol(self, symbol):
        self.add_log(f"Processing {symbol}...")
        interval_ms = INTERVAL_MS.get(self.timeframe, 60000)
        if self.mode == 'full':
            start_ms = find_earliest_candle(symbol, self.timeframe)
            end_ms = int(time.time() * 1000)
            self.add_log(f"Full history: from {pd.to_datetime(start_ms, unit='ms')} to now")
            total_estimate = (end_ms - start_ms + interval_ms - 1) // interval_ms
        elif self.mode == 'last1000':
            end_ms = int(time.time() * 1000)
            start_ms = end_ms - 1000 * interval_ms
            self.add_log(f"Last 1000 candles ending at {pd.to_datetime(end_ms, unit='ms')}")
            total_estimate = 1000
        else:  # period
            # Convert naive UTC datetime to milliseconds correctly
            start_ms = int(self.start_date.replace(tzinfo=timezone.utc).timestamp() * 1000)
            end_ms = int(self.end_date.replace(tzinfo=timezone.utc).timestamp() * 1000)
            total_estimate = (end_ms - start_ms + interval_ms - 1) // interval_ms
        if self.mode != 'full':
            self.symbol_ranges[symbol] = (start_ms, end_ms)
            self.add_log(f"Estimated total candles for {symbol}: {total_estimate}")
        existing_start, existing_end = None, None
        if not self.overwrite:
            existing_start, existing_end = read_existing_range(symbol, self.timeframe)
            if existing_start is not None:
                existing_count = ((existing_end - existing_start) // interval_ms) + 1
                self.add_log(f"Existing data: {pd.to_datetime(existing_start, unit='ms')} to {pd.to_datetime(existing_end, unit='ms')} ({existing_count} candles)")
        ranges_to_download = []
        if self.overwrite or existing_start is None:
            ranges_to_download.append((start_ms, end_ms))
            if self.overwrite:
                self.add_log(f"Overwrite enabled: will re-download entire range")
        else:
            if start_ms < existing_start:
                ranges_to_download.append((start_ms, existing_start - 1))
                missing_before = ((existing_start - 1 - start_ms) // interval_ms) + 1
                self.add_log(f"Missing before existing: {pd.to_datetime(start_ms, unit='ms')} to {pd.to_datetime(existing_start-1, unit='ms')} (~{missing_before} candles)")
            if existing_end < end_ms:
                ranges_to_download.append((existing_end + 1, end_ms))
                missing_after = ((end_ms - (existing_end + 1)) // interval_ms) + 1
                self.add_log(f"Missing after existing: {pd.to_datetime(existing_end+1, unit='ms')} to {pd.to_datetime(end_ms, unit='ms')} (~{missing_after} candles)")
        if not ranges_to_download:
            self.add_log("All requested data already present, skipping.")
            return
        self.total_candles = 0
        for rng_start, rng_end in ranges_to_download:
            approx = (rng_end - rng_start + interval_ms - 1) // interval_ms
            self.total_candles += approx
            self.add_log(f"Will download {self.total_candles} new candles for {symbol}")
        for rng_start, rng_end in ranges_to_download:
            if self.stop_event.is_set():
                break
            self._download_range(symbol, rng_start, rng_end, interval_ms)
        if not self.stop_event.is_set() and self.total_candles == 0:
            self.add_log(f"No data downloaded for {symbol}.")

    def _download_range(self, symbol, start_ms, end_ms, interval_ms):
        cur_end = end_ms
        limit = 200
        target = self.total_candles
        sym_dl = 0
        prev_ts = None
        prev_close = None
        while cur_end > start_ms and not self.stop_event.is_set() and sym_dl < target:
            while self.pause_event.is_set() and not self.stop_event.is_set():
                time.sleep(0.5)
            if self.stop_event.is_set():
                break
            time.sleep(RATE_LIMIT)
            df = fetch_klines(symbol, self.timeframe, start_ms, cur_end, limit)
            if df.empty:
                self.add_log("No data returned, stopping this range.")
                break
            if self.mode == 'last1000' and sym_dl + len(df) > target:
                excess = sym_dl + len(df) - target
                df = df.iloc[excess:]
                if df.empty:
                    break
            if not df["timestamp"].is_monotonic_decreasing:
                self.add_log(f"INFO: Batch not monotonic decreasing – possible API anomaly")
            aligned = df["timestamp"] % interval_ms == 0
            if not aligned.all():
                bad_count = (~aligned).sum()
                self.add_log(f"WARNING: {bad_count} timestamps not aligned to {interval_ms}ms interval in this batch!")
            oldest_this = df["timestamp"].iloc[-1]
            newest_this = df["timestamp"].iloc[0]
            if prev_ts is not None:
                expected_next = prev_ts - interval_ms
                if newest_this < expected_next:
                    gap = expected_next - newest_this
                    self.add_log(f"INFO: Gap between batches: {gap/60000:.1f} minutes (will be handled in final processing)")
                elif newest_this > expected_next:
                    self.add_log(f"INFO: Overlap between batches: {newest_this - expected_next} ms (will be deduplicated)")
            if df["timestamp"].min() < start_ms or df["timestamp"].max() > end_ms:
                self.add_log(f"WARNING: Batch contains timestamps outside requested range!")
            dups = df["timestamp"].duplicated().sum()
            if dups:
                self.add_log(f"WARNING: {dups} duplicate timestamps in this batch!")
            invalid = df[
                (df['high'] < df['low']) |
                (df['high'] < df['open']) |
                (df['high'] < df['close']) |
                (df['low'] > df['open']) |
                (df['low'] > df['close']) |
                (df['volume'] < 0)
            ]
            if not invalid.empty:
                self.add_log(f"WARNING: {len(invalid)} candles with OHLCV inconsistency in this batch!")
            if self.price_continuity_check and prev_close is not None:
                current_newest_close = df['close'].iloc[0]
                price_change_pct = abs(current_newest_close - prev_close) / prev_close
                if price_change_pct > PRICE_CONTINUITY_TOLERANCE:
                    self.add_log(f"WARNING: Large price jump between batches: {price_change_pct*100:.1f}%")
            self.raw_batches.append(df)
            self._batches_since_flush += 1
            # Incremental save every 5 batches (~1000 candles) to prevent data loss
            if self._batches_since_flush >= 5:
                self._incremental_flush(symbol)
            sym_dl += len(df)
            self.downloaded_candles += len(df)
            self.progress = min(100, 100 * self.downloaded_candles / self.total_candles)
            self.add_log(f"Downloaded {len(df)} candles (raw, total {self.downloaded_candles})")
            prev_ts = oldest_this
            prev_close = df['close'].iloc[-1]
            cur_end = oldest_this - interval_ms
        if sym_dl == 0:
            self.add_log(f"No data downloaded in this range.")
        else:
            self.add_log(f"Range completed, downloaded {sym_dl} raw candles.")

    def add_strategy_signal(self, signal_type, direction, entry_price, entry_time_ms,
                            exit_price=None, exit_time_ms=None, stop_loss=None,
                            take_profit=None, confidence=0.0, extra_info=None):
        """Store a detected strategy signal and log it."""
        signal = {
            'type': signal_type,
            'direction': direction,
            'entry_price': entry_price,
            'entry_time_ms': entry_time_ms,
            'exit_price': exit_price,
            'exit_time_ms': exit_time_ms,
            'stop_loss': stop_loss,
            'take_profit': take_profit,
            'confidence': confidence,
            'delta_pct': None,
            'extra_info': extra_info
        }
        with self.state_lock:
            self.strategy_signals.append(signal)
        # 🔕 Per-signal logs removed to keep task table clean. View details in Strategy/Impulse modals.

    def run_impulse_detection(self, params=None, verbose=False):
        """Run impulse detection on this task’s data using given or current parameters."""
        from impulse import backtest_impulse, set_impulse_params
        if params:
            set_impulse_params(params)
        sym = self.symbols[0]
        path = symbol_timeframe_path(sym, self.timeframe)
        fp = os.path.join(path, "data.parquet")
        if not os.path.exists(fp):
            self.add_log("Impulse detection: data file not found")
            return 0
        full_df = pd.read_parquet(fp)
        buffer_ms = self.pre_buffer_minutes * 60 * 1000
        start_ms = max(0, self.signal_time - buffer_ms)
        if self.start_date and self.end_date:
            window_len_ms = int(self.end_date.replace(tzinfo=timezone.utc).timestamp() * 1000) - int(self.start_date.replace(tzinfo=timezone.utc).timestamp() * 1000)
            cutoff_time = self.signal_time + window_len_ms
            df_limited = full_df[(full_df['timestamp'] >= start_ms) & (full_df['timestamp'] <= cutoff_time)].copy()
        else:
            df_limited = full_df[full_df['timestamp'] >= start_ms].copy()
        if df_limited.empty:
            self.add_log("Impulse detection: empty data after filtering")
            return 0
        res = backtest_impulse(df_limited, self.signal_price, self.signal_direction, self.signal_time, verbose=verbose)
        self.strategy_signals = [s for s in self.strategy_signals if s.get('type') != 'impulse']
        for trade in res['trades']:
            self.add_strategy_signal(
                'impulse', trade['direction'], trade['entry_price'], trade['entry_time_ms'],
                exit_price=trade['exit_price'], exit_time_ms=trade['exit_time_ms'],
                confidence=trade['confidence'], extra_info=trade['extra_info']
            )
        self.add_log(f"Impulse detection completed: {res['count']} impulse signals")
        if self.strategy_signals:
            # Safe max key: handle None delta_pct
            best = max(self.strategy_signals, key=lambda x: x.get('delta_pct') if x.get('delta_pct') is not None else -999)
            # Safe formatting: handle None delta_pct
            dp = best.get('delta_pct')
            dp_val = dp if dp is not None else 0.0
            self.strategy_log_summary = f"{best['type'].capitalize()} {best['direction'].upper()} ({dp_val:.1f}%)"
            self.strategy_confidence = best['confidence']
        else:
            self.strategy_log_summary = "No valid signal"
        return res['count']

    def analyze_signal(self):
        """
        Perform candle analysis based on signal level and time.
        Results are appended to the task log, with time differences in minutes.
        If analyze_beyond is False, analysis stops at the end of the selected period (self.end_date).
        Stores all events in self.events for charting.
        Stores first event details and price change for summary.
        
        🔧 CRITICAL: Uses cached data from RAM (already loaded during JSON load/download).
        Does NOT re-read parquet files - respects your original fast-analysis design.
        
        🔧 CRITICAL: Create local module aliases to avoid global lookup issues in background threads
        """
        # 🔧 Local module aliases for thread safety - MUST BE BEFORE load_task_data_cached call
        import numpy as np_local
        import bisect as bisect_local
        
        sym = self.symbols[0] if self.symbols else 'UNKNOWN'
        print(f"🔍 [ANALYZE] Starting analyze_signal for {sym} {self.timeframe}...")
        sys.stdout.flush()
        
        if not self.signal_time or self.signal_price is None:
            # 🔧 CRITICAL FIX: Avoid state_lock deadlock - use lock-free logging
            timestamp = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
            self.log.append(f"[{timestamp}] No signal data for analysis.")
            print(f"⏭️ [ANALYZE] Skipping {sym} {self.timeframe} - no signal data (lock-free)")
            sys.stdout.flush()
            return
        
        # 🔧 CRITICAL: Use cached data from RAM instead of re-reading parquet
        # This respects your original design: JSON tasks use already-loaded candles
        print(f"📂 [ANALYZE] Step 1/5: Loading cached data for {sym} {self.timeframe}...")
        sys.stdout.flush()
        
        # 🔧 Inject np_local into global scope for load_task_data_cached to use
        global np_local_global, bisect_local_global
        np_local_global = np_local
        bisect_local_global = bisect_local
        
        df = load_task_data_cached(self)
        if df.empty:
            # 🔧 CRITICAL FIX: Avoid state_lock deadlock - use lock-free logging
            timestamp = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
            self.log.append(f"[{timestamp}] No data to analyze.")
            print(f"⚠️ [ANALYZE] Empty dataframe for {sym} {self.timeframe} (lock-free)")
            sys.stdout.flush()
            return
            
        print(f"📊 [ANALYZE] Step 1/5 Complete: Loaded {len(df)} candles for {sym}")
        sys.stdout.flush()
        
        # CRITICAL FIX 1: Ensure timestamps are sorted for accurate searchsorted & slicing
        print(f"⚙️ [ANALYZE] Step 2/5: Preparing data (sorting, filtering)...")
        sys.stdout.flush()
        df = df.sort_values('timestamp').reset_index(drop=True)
        df['timestamp'] = df['timestamp'].astype(np_local_global.int64)
        
        # Ensure signal_time is numeric to prevent searchsorted type errors
        try:
            safe_signal_time = float(self.signal_time)
        except (ValueError, TypeError):
            # 🔧 CRITICAL FIX: Avoid state_lock deadlock - use lock-free logging
            timestamp = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
            self.log.append(f"[{timestamp}] ⚠️ Invalid signal_time format. Skipping analysis.")
            print(f"❌ [ANALYZE] Invalid signal_time for {sym} {self.timeframe} (lock-free)")
            sys.stdout.flush()
            return
            
        buffer_ms = self.pre_buffer_minutes * 60 * 1000
        search_time = safe_signal_time - buffer_ms
        idx_start = df['timestamp'].searchsorted(search_time, side='left')
        if idx_start >= len(df):
            # 🔧 CRITICAL FIX: Avoid state_lock deadlock - use lock-free logging
            timestamp = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
            self.log.append(f"[{timestamp}] Signal time after last candle, no analysis.")
            print(f"⏭️ [ANALYZE] Signal time after last candle for {sym} {self.timeframe} (lock-free)")
            sys.stdout.flush()
            return
        df = df.iloc[idx_start:].reset_index(drop=True)
        # If not analyzing beyond period, truncate to end_date (in ms)
        if not self.analyze_beyond and self.end_date is not None:
            end_ms = int(self.end_date.replace(tzinfo=timezone.utc).timestamp() * 1000)
            df = df[df['timestamp'] <= end_ms].reset_index(drop=True)
            if df.empty:
                # 🔧 CRITICAL FIX: Avoid state_lock deadlock - use lock-free logging
                timestamp = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
                self.log.append(f"[{timestamp}] No data within selected period, analysis stopped.")
                print(f"⏭️ [ANALYZE] No data within selected period for {sym} {self.timeframe} (lock-free)")
                sys.stdout.flush()
                return
        print(f"✅ [ANALYZE] Step 2/5 Complete: Data prepared ({len(df)} rows after filtering)")
        sys.stdout.flush()
        
        # 🔍 START OF STEP 3/5 - TOUCH EVENT DETECTION
        print("🔍 [ANALYZE] === STARTING STEP 3/5: TOUCH EVENT DETECTION ===")
        sys.stdout.flush()
        
        # CRITICAL: Verify np_local_global and bisect_local_global are set
        print(f"🔬 [DEBUG PRE-STEP3] np_local_global is None: {np_local_global is None}")
        sys.stdout.flush()
        print(f"🔬 [DEBUG PRE-STEP3] bisect_local_global is None: {bisect_local_global is None}")
        sys.stdout.flush()
        if np_local_global is not None:
            print(f"🔬 [DEBUG PRE-STEP3] np_local_global type: {type(np_local_global)}")
            sys.stdout.flush()
        if bisect_local_global is not None:
            print(f"🔬 [DEBUG PRE-STEP3] bisect_local_global type: {type(bisect_local_global)}")
            sys.stdout.flush()
        
        # Verify df exists and has data
        print(f"🔬 [DEBUG PRE-STEP3] df is None: {df is None}")
        sys.stdout.flush()
        if df is not None:
            print(f"🔬 [DEBUG PRE-STEP3] df type={type(df)}, len={len(df)}")
            sys.stdout.flush()
            print(f"🔬 [DEBUG PRE-STEP3] df columns={list(df.columns)}")
            sys.stdout.flush()
        
        # CRITICAL: Verify signal_direction before using it
        print(f"🔬 [DEBUG] signal_direction='{self.signal_direction}', type={type(self.signal_direction)}")
        sys.stdout.flush()
        
        # CRITICAL: Check if we can evaluate the if condition
        print("🔬 [DEBUG] About to check if self.signal_direction == 'resistance'...")
        sys.stdout.flush()
        is_resistance = (self.signal_direction == 'resistance')
        print(f"🔬 [DEBUG] Result: is_resistance={is_resistance}")
        sys.stdout.flush()
        
        # CRITICAL DEBUG: Check if numpy functions exist
        print("🔬 [CRITICAL DEBUG] Checking np_local_global attributes...")
        sys.stdout.flush()
        print("🔬 [CRITICAL DEBUG] hasattr(np_local_global, 'minimum'): {}".format(hasattr(np_local_global, 'minimum')))
        sys.stdout.flush()
        print("🔬 [CRITICAL DEBUG] hasattr(np_local_global, 'maximum'): {}".format(hasattr(np_local_global, 'maximum')))
        sys.stdout.flush()
        print("🔬 [CRITICAL DEBUG] hasattr(np_local_global, 'where'): {}".format(hasattr(np_local_global, 'where')))
        sys.stdout.flush()
        print("🔬 [CRITICAL DEBUG] hasattr(np_local_global, 'abs'): {}".format(hasattr(np_local_global, 'abs')))
        sys.stdout.flush()
        print("🔬 [CRITICAL DEBUG] hasattr(bisect_local_global, 'bisect_right'): {}".format(hasattr(bisect_local_global, 'bisect_right')))
        sys.stdout.flush()
        
        # CRITICAL: Test numpy operation before using it
        print("🔬 [DEBUG] Testing numpy minimum function...")
        sys.stdout.flush()
        try:
            test_arr = np_local_global.array([1, 2, 3])
            print(f"🔬 [DEBUG] Test array created: {test_arr}")
            sys.stdout.flush()
        except Exception as e:
            print(f"❌ [ERROR] Failed to create test array: {e}")
            sys.stdout.flush()
            import traceback
            traceback.print_exc()
            sys.stdout.flush()
        
        if is_resistance:
            direction_str = "movement toward resistance level from below"
            print("🔬 [DEBUG] Entered RESISTANCE branch")
            sys.stdout.flush()
        else:
            direction_str = "movement toward support level from above"
            print("🔬 [DEBUG] Entered SUPPORT branch")
            sys.stdout.flush()
        
        print("🔬 [DEBUG] About to add logs...")
        sys.stdout.flush()
        
        # 🔧 CRITICAL FIX: Avoid state_lock deadlock in background thread
        # Instead of using self.add_log() which acquires a lock, just print to console
        timestamp = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
        log_msg1 = f"[{timestamp}] Signal: {sym} at {pd.to_datetime(self.signal_time, unit='ms', utc=True)} price={self.signal_price}"
        print(f"Task {self.task_id[:8]}: Signal info logged (lock-free)")
        sys.stdout.flush()
        
        log_msg2 = f"[{timestamp}] Direction: {direction_str}"
        print(f"Task {self.task_id[:8]}: Direction info logged (lock-free)")
        sys.stdout.flush()
        
        # Add to log list WITHOUT lock (safe in single-threaded context of analyze_signal)
        self.log.append(log_msg1)
        self.log.append(log_msg2)
        
        # Helper to classify pin bar
        print("🔬 [DEBUG] About to define is_pin_bar function...")
        sys.stdout.flush()
        def is_pin_bar(row):
            body = abs(row['close'] - row['open'])
            high = row['high']
            low = row['low']
            open_p = row['open']
            close_p = row['close']
            upper_wick = high - max(open_p, close_p)
            lower_wick = min(open_p, close_p) - low
            total_range = high - low
            pin_threshold = 2.0
            body_ratio = body / total_range if total_range > 0 else 0
            is_upper_pin = (upper_wick > pin_threshold * body) and (upper_wick > pin_threshold * lower_wick) and (body_ratio < 0.3)
            is_lower_pin = (lower_wick > pin_threshold * body) and (lower_wick > pin_threshold * upper_wick) and (body_ratio < 0.3)
            return is_upper_pin, is_lower_pin
        print("🔬 [DEBUG] is_pin_bar function defined successfully")
        sys.stdout.flush()
        
        print(f"📊 [TOUCH SCAN] Starting scan of {len(df)} candles...")
        sys.stdout.flush()
        
        # Debug: Print DataFrame info before Step 3
        print(f"🔬 [DEBUG] df type={type(df)}, len={len(df)}, columns={list(df.columns)}")
        sys.stdout.flush()
        print(f"🔬 [DEBUG] df dtypes:\n{df.dtypes}")
        sys.stdout.flush()
        
        events = []   # store all touch events
        
        try:
            # --- SUB-STEP 3.1: Extract to Numpy Arrays ---
            print("⚙️ [ANALYZE] Step 3.1: Converting to numpy arrays...")
            sys.stdout.flush()
            
            # CRITICAL: Ensure we're extracting numeric arrays
            print("🔬 [DEBUG 3.1a] Before array extraction")
            sys.stdout.flush()
            
            # Test if we can access DataFrame columns
            print("🔬 [DEBUG 3.1b] Testing DataFrame column access...")
            sys.stdout.flush()
            try:
                test_col = df["timestamp"]
                print(f"🔬 [DEBUG 3.1c] Successfully accessed 'timestamp' column, type={type(test_col)}")
                sys.stdout.flush()
            except Exception as e:
                print(f"❌ [ERROR] Failed to access DataFrame column: {e}")
                sys.stdout.flush()
                import traceback
                traceback.print_exc()
                sys.stdout.flush()
                return
            
            timestamps_arr = df["timestamp"].values
            print(f"🔬 [DEBUG 3.1d] timestamps_arr: type={type(timestamps_arr)}, dtype={timestamps_arr.dtype}, len={len(timestamps_arr)}")
            sys.stdout.flush()
            
            lows_arr = df["low"].values
            highs_arr = df["high"].values
            opens_arr = df["open"].values
            closes_arr = df["close"].values
            print(f"🔬 [DEBUG 3.1e] All arrays extracted: lows={lows_arr.dtype}, highs={highs_arr.dtype}, opens={opens_arr.dtype}, closes={closes_arr.dtype}")
            sys.stdout.flush()
            
            print(f"✅ [ANALYZE] Step 3.1 Complete: Arrays created (len={len(timestamps_arr)})")
            sys.stdout.flush()
            
            # --- SUB-STEP 3.2: Vectorized Body/Shadow Detection ---
            print("⚙️ [ANALYZE] Step 3.2: Detecting touches with numpy...")
            sys.stdout.flush()
            
            print("🔬 [DEBUG 3.2a] Before body detection")
            sys.stdout.flush()
            signal_price_val = float(self.signal_price)
            print(f"🔬 [DEBUG 3.2b] signal_price_val={signal_price_val}")
            sys.stdout.flush()
            
            # Test numpy minimum function
            print("🔬 [DEBUG 3.2c] Testing np_local_global.minimum...")
            sys.stdout.flush()
            try:
                test_min = np_local_global.minimum(opens_arr[:5], closes_arr[:5])
                print(f"🔬 [DEBUG 3.2d] Test minimum result: {test_min}")
                sys.stdout.flush()
            except Exception as e:
                print(f"❌ [ERROR] Failed to call np_local_global.minimum: {e}")
                sys.stdout.flush()
                import traceback
                traceback.print_exc()
                sys.stdout.flush()
                return
            
            min_body = np_local_global.minimum(opens_arr, closes_arr)
            max_body = np_local_global.maximum(opens_arr, closes_arr)
            print(f"🔬 [DEBUG 3.2e] min_body/max_body computed")
            sys.stdout.flush()
            
            body_mask = (min_body <= signal_price_val) & (signal_price_val <= max_body)
            shadow_mask = (lows_arr <= signal_price_val) & (signal_price_val <= highs_arr) & (~body_mask)
            print(f"🔬 [DEBUG 3.2d] masks computed: body_mask sum={body_mask.sum()}, shadow_mask sum={shadow_mask.sum()}")
            sys.stdout.flush()
            
            body_indices = np_local_global.where(body_mask)[0]
            shadow_indices = np_local_global.where(shadow_mask)[0]
            print(f"✅ [ANALYZE] Step 3.2 Complete: {len(body_indices)} body, {len(shadow_indices)} shadow")
            sys.stdout.flush()
            
            # --- SUB-STEP 3.3: Pin Bar Calculation ---
            print("⚙️ [ANALYZE] Step 3.3: Calculating pin bars...")
            sys.stdout.flush()
            
            print("🔬 [DEBUG 3.3a] Before pin bar calc")
            sys.stdout.flush()
            bodies = np_local_global.abs(closes_arr - opens_arr)
            ranges = highs_arr - lows_arr
            upper_wicks = highs_arr - np_local_global.maximum(opens_arr, closes_arr)
            lower_wicks = np_local_global.minimum(opens_arr, closes_arr) - lows_arr
            print(f"🔬 [DEBUG 3.3b] wicks computed")
            sys.stdout.flush()
            
            safe_ranges = np_local_global.where(ranges == 0, 1e-9, ranges)
            body_ratios = bodies / safe_ranges
            print(f"🔬 [DEBUG 3.3c] ratios computed")
            sys.stdout.flush()
            
            pin_threshold = 2.0
            is_upper_pin = (upper_wicks > pin_threshold * bodies) & \
                           (upper_wicks > pin_threshold * lower_wicks) & \
                           (body_ratios < 0.3)
            is_lower_pin = (lower_wicks > pin_threshold * bodies) & \
                           (lower_wicks > pin_threshold * upper_wicks) & \
                           (body_ratios < 0.3)
            print(f"✅ [ANALYZE] Step 3.3 Complete: Pin masks ready")
            sys.stdout.flush()
            
            # --- SUB-STEP 3.4: Assemble Events ---
            print("⚙️ [ANALYZE] Step 3.4: Assembling events list...")
            sys.stdout.flush()
            
            print("🔬 [DEBUG 3.4a] Before event assembly, direction={}".format(self.signal_direction))
            sys.stdout.flush()
            direction = self.signal_direction
            
            for idx in body_indices:
                events.append((int(timestamps_arr[idx]), "body_touch", int(idx), float(closes_arr[idx])))
                
            for idx in shadow_indices:
                if direction == "resistance" and is_upper_pin[idx]:
                    events.append((int(timestamps_arr[idx]), "upper_pin_touch", int(idx), float(closes_arr[idx])))
                elif direction == "support" and is_lower_pin[idx]:
                    events.append((int(timestamps_arr[idx]), "lower_pin_touch", int(idx), float(closes_arr[idx])))
                else:
                    events.append((int(timestamps_arr[idx]), "shadow_touch", int(idx), float(closes_arr[idx])))
            
            print(f"✅ [ANALYZE] Step 3.4 Complete: Total {len(events)} events assembled")
            print(f"✅ [TOUCH SCAN] Found {len(events)} touch events.")
            sys.stdout.flush()
            
            # 🔧 OPTIMIZED: Vectorized bounce/breakthrough detection (PRESERVES ORIGINAL LOGIC 100%)
            # Instead of nested loop O(n²), we pre-calculate ALL bounce/breakthrough points once O(n)
            # Then for each touch, we simply find the FIRST occurrence after it using binary search
            print(f"📊 [BOUNCE SCAN] Pre-calculating bounce/break points (vectorized)...")
            sys.stdout.flush()
            
            print("🔬 [DEBUG BOUNCE 1] Before bounce mask calculation")
            sys.stdout.flush()
            
            # Pre-calculate ALL bounce and breakthrough indices in ONE pass
            if self.signal_direction == 'resistance':
                # Bounce: close < signal_price
                bounce_mask = df['close'].values < self.signal_price
                # Breakthrough: close > signal_price  
                break_mask = df['close'].values > self.signal_price
            else:  # support
                # Bounce: close > signal_price
                bounce_mask = df['close'].values > self.signal_price
                # Breakthrough: close < signal_price
                break_mask = df['close'].values < self.signal_price
            
            print("🔬 [DEBUG BOUNCE 2] Masks calculated")
            sys.stdout.flush()
            
            bounce_indices = np_local_global.where(bounce_mask)[0]
            break_indices = np_local_global.where(break_mask)[0]
            print(f"   Found {len(bounce_indices)} bounce candles, {len(break_indices)} break candles")
            sys.stdout.flush()
            
            final_events = []
            self.events = []   # clear previous
            
            print(f"🔬 [DEBUG BOUNCE 3] Starting event loop with {len(events)} events")
            sys.stdout.flush()
            
            for ev_idx, (ts, etype, idx, close) in enumerate(events):
                # Log progress for large event lists
                if ev_idx % 50 == 0:
                    print(f"   ...processing event {ev_idx}/{len(events)} (idx={idx})")
                    sys.stdout.flush()
                
                final_events.append((ts, etype, 'touch', close))
                self.events.append({'timestamp': ts, 'type': etype, 'kind': 'touch', 'close': close})
                
                # Find first bounce after this touch using binary search
                if ev_idx < 10 or ev_idx % 50 == 0:
                    print(f"🔬 [DEBUG LOOP {ev_idx}] idx={idx}, calling bisect... (bounce_indices len={len(bounce_indices)}, break_indices len={len(break_indices)})")
                    sys.stdout.flush()
                bounce_pos = bisect_local_global.bisect_right(bounce_indices, idx)
                if ev_idx < 10 or ev_idx % 50 == 0:
                    print(f"🔬 [DEBUG LOOP {ev_idx}] bounce_pos={bounce_pos}")
                    sys.stdout.flush()
                bounce_found = bounce_indices[bounce_pos] if bounce_pos < len(bounce_indices) else None
                
                # Find first break after this touch
                break_pos = bisect_local_global.bisect_right(break_indices, idx)
                break_found = break_indices[break_pos] if break_pos < len(break_indices) else None
                
                # Determine which comes first (preserves original logic exactly)
                if bounce_found is not None and break_found is not None:
                    if bounce_found < break_found:
                        j = bounce_found
                        event_type = 'bounce'
                    else:
                        j = break_found
                        event_type = 'breakthrough'
                elif bounce_found is not None:
                    j = bounce_found
                    event_type = 'bounce'
                elif break_found is not None:
                    j = break_found
                    event_type = 'breakthrough'
                else:
                    j = None
                    event_type = None
                
                if j is not None:
                    next_row = df.iloc[j]
                    kind = 'next' if j == idx + 1 else 'later'
                    final_events.append((next_row['timestamp'], event_type, kind, next_row['close']))
                    self.events.append({'timestamp': next_row['timestamp'], 'type': event_type, 'kind': kind, 'close': next_row['close']})
            
            print(f"✅ [BOUNCE SCAN] Completed. Total final events: {len(final_events)}")
            sys.stdout.flush()
            print("✅ [ANALYZE] Step 3/5 Complete: Touch events processed.")
            sys.stdout.flush()
            
        except Exception as e:
            print(f"💥 [CRITICAL ERROR] Step 3 failed: {str(e)}")
            sys.stdout.flush()
            import traceback
            traceback.print_exc()
            # 🔧 CRITICAL FIX: Avoid state_lock deadlock - use lock-free logging
            timestamp = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
            self.log.append(f"[{timestamp}] ❌ Analysis Error: {str(e)}")
            print(f"Task {self.task_id[:8]}: Analysis error logged (lock-free)")
            sys.stdout.flush()
            return
        
        # Clean up temporary columns
        for col in ['body_min', 'body_max', 'body_touch', 'shadow_touch', 'body', 
                    'upper_wick', 'lower_wick', 'total_range', 'body_ratio', 
                    'is_upper_pin', 'is_lower_pin']:
            if col in df.columns:
                df.drop(columns=[col], inplace=True)
        
        print(f"✅ [ANALYZE] Step 3/5 Complete: Found {len(events)} touch events")
        sys.stdout.flush()
        
        # ✅ STEP 4/5: Process first event and calculate metrics
        print("🔍 [ANALYZE] === STARTING STEP 4/5: FIRST EVENT & METRICS ===")
        sys.stdout.flush()
                        
        if not events:
            self.first_event_time = None
            self.first_event_type = None
            self.first_event_is_pin = False
            self.first_event_close = None
            self.price_change_pct = None
            if self.log_events:
                # 🔧 CRITICAL FIX: Avoid state_lock deadlock - use lock-free logging
                timestamp = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
                self.log.append(f"[{timestamp}] No touches detected.")
                print(f"Task {self.task_id[:8]}: No touches detected (lock-free)")
                sys.stdout.flush()
        else:
            if self.log_events:
                # 🔧 CRITICAL FIX: Avoid state_lock deadlock - use lock-free logging
                timestamp = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
                self.log.append(f"[{timestamp}] --- Signal Analysis Results ---")
                print(f"Task {self.task_id[:8]}: Signal Analysis Results (lock-free)")
                sys.stdout.flush()
            prev_ts = self.signal_time
            for i, (ts, etype, kind, close) in enumerate(final_events):
                dt = pd.to_datetime(ts, unit='ms', utc=True)
                time_diff_min = (ts - prev_ts) / 60000.0
                if i == 0:
                    self.first_event_time = dt
                    self.first_event_type = etype
                    self.first_event_is_pin = ('pin' in etype)
                    self.first_event_close = close
                    
                    # NEW LOGIC: Delta from entry price to signal level
                    sig_idx = df['timestamp'].searchsorted(self.signal_time)
                    sig_idx = min(sig_idx, len(df) - 1)
                    entry_price = df.iloc[sig_idx]['close']
                    self.price_change_pct = ((self.signal_price - entry_price) / entry_price) * 100                    
                    if self.log_events:
                        # 🔧 CRITICAL FIX: Avoid state_lock deadlock - use lock-free logging
                        timestamp = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
                        self.log.append(f"[{timestamp}] First event at {dt} ({time_diff_min:.2f} min after signal) – {etype}")
                        print(f"Task {self.task_id[:8]}: First event logged (lock-free)")
                        sys.stdout.flush()
                else:
                    if self.log_events:
                        # 🔧 CRITICAL FIX: Avoid state_lock deadlock - use lock-free logging
                        timestamp = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
                        self.log.append(f"[{timestamp}] Next event at {dt} ({time_diff_min:.2f} min later) – {etype}")
                        print(f"Task {self.task_id[:8]}: Next event logged (lock-free)")
                        sys.stdout.flush()
                prev_ts = ts
                
            print(f"🏁 [ANALYZE] Step 5/5: Finalizing results for {sym}...")
            sys.stdout.flush()
            
            last_candle = df.iloc[-1]
            last_close = last_candle['close']
            if self.signal_direction == 'resistance':
                self.reached_level = len(self.events) > 0
                self.reversed_direction = (last_close < self.signal_price)
            else:
                self.reached_level = len(self.events) > 0
                self.reversed_direction = (last_close > self.signal_price)
            if self.log_events:
                # 🔧 CRITICAL FIX: Avoid state_lock deadlock - use lock-free logging
                timestamp = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
                if self.signal_direction == 'resistance':
                    if last_close > self.signal_price:
                        msg = "Final state: price moved away following trend (above level)"
                    elif last_close < self.signal_price:
                        msg = "Final state: price reversed (below level)"
                    else:
                        msg = "Final state: price at level"
                else:
                    if last_close < self.signal_price:
                        msg = "Final state: price moved away following trend (below level)"
                    elif last_close > self.signal_price:
                        msg = "Final state: price reversed (above level)"
                    else:
                        msg = "Final state: price at level"
                self.log.append(f"[{timestamp}] {msg}")
                print(f"Task {self.task_id[:8]}: {msg} (lock-free)")
                sys.stdout.flush()
                
                self.log.append(f"[{timestamp}] Reached level: {self.reached_level}")
                self.log.append(f"[{timestamp}] Reversed direction: {self.reversed_direction}")
                print(f"Task {self.task_id[:8]}: Final stats logged (lock-free)")
                sys.stdout.flush()
            
            print(f"✅ [ANALYZE] Step 5/5 Complete: Analysis finished for {sym}. Events: {len(self.events)}, Reached: {self.reached_level}")
            sys.stdout.flush()
        
        # ----- FAST HIT CALCULATION (Keeps old vectorized logic for instant table display) -----
        # CRITICAL: Calculate signal_idx for hit calculations and drawdown (from signal time)
        # Initialize to safe default to prevent UnboundLocalError
        signal_idx = 0
        try:
            safe_signal_time = float(self.signal_time)
            signal_idx = df['timestamp'].searchsorted(safe_signal_time, side='left')
            if signal_idx >= len(df):
                signal_idx = len(df) - 1
            print(f"🔢 [IDX CALC] {self.symbols} signal_idx={signal_idx}, df_len={len(df)}, signal_time={self.signal_time}")
        except (ValueError, TypeError) as e:
            print(f"⚠️ [IDX CALC] Could not calculate signal_idx: {e}, using default 0")
            pass  # signal_idx remains 0
        
        if signal_idx < len(df):
            df_window = df.iloc[signal_idx:]
            if self.signal_direction == 'resistance':
                max_price = df_window['high'].max()
                self.hit_1 = (max_price - self.signal_price) / self.signal_price >= 0.01
                self.hit_1_5 = (max_price - self.signal_price) / self.signal_price >= 0.015
                self.hit_2 = (max_price - self.signal_price) / self.signal_price >= 0.02
            else:
                min_price = df_window['low'].min()
                self.hit_1 = (self.signal_price - min_price) / self.signal_price >= 0.01
                self.hit_1_5 = (self.signal_price - min_price) / self.signal_price >= 0.015
                self.hit_2 = (self.signal_price - min_price) / self.signal_price >= 0.02
        else:
            self.hit_1 = self.hit_1_5 = self.hit_2 = False

        if self.log_events:
            self.add_log(f"Fast Hit targets (from signal time): 1%={self.hit_1}, 1.5%={self.hit_1_5}, 2%={self.hit_2}")

        # =====================================================================
        # 🔧 VECTORISED HIT TIMING (Replaces iterrows loop at line 1705)
        # Uses np.argmax for O(1) lookup instead of O(n) iteration
        # Calculates first_hit_*_expected/opposite from FIRST TOUCH event
        # =====================================================================
        # Reset precise flags/times to prevent stale data
        self.first_hit_1_expected = False; self.first_hit_1_expected_time = None
        self.first_hit_1_5_expected = False; self.first_hit_1_5_expected_time = None
        self.first_hit_2_expected = False; self.first_hit_2_expected_time = None
        self.first_hit_1_opposite = False; self.first_hit_1_opposite_time = None
        self.first_hit_1_5_opposite = False; self.first_hit_1_5_opposite_time = None
        self.first_hit_2_opposite = False; self.first_hit_2_opposite_time = None
        
        if self.events and len(self.events) > 0:
            first_touch_ts = self.events[0]['timestamp']
            try:
                touch_idx = df.index[df['timestamp'] == first_touch_ts].tolist()[0]
            except IndexError:
                touch_idx = df['timestamp'].searchsorted(first_touch_ts)
                touch_idx = min(touch_idx, len(df) - 1)

            # Extract numpy arrays for vectorized operations
            timestamps_arr = df['timestamp'].values
            highs_arr = df['high'].values
            lows_arr = df['low'].values
            
            # Define targets based on direction
            if self.signal_direction == 'resistance':
                exp_1, exp_1_5, exp_2 = self.signal_price * 1.01, self.signal_price * 1.015, self.signal_price * 1.02
                opp_1, opp_1_5, opp_2 = self.signal_price * 0.99, self.signal_price * 0.985, self.signal_price * 0.98
                exp_col_vals = highs_arr
                opp_col_vals = lows_arr
            else:  # support
                exp_1, exp_1_5, exp_2 = self.signal_price * 0.99, self.signal_price * 0.985, self.signal_price * 0.98
                opp_1, opp_1_5, opp_2 = self.signal_price * 1.01, self.signal_price * 1.015, self.signal_price * 1.02
                exp_col_vals = lows_arr
                opp_col_vals = highs_arr
            
            # Create boolean masks for each target level (vectorized comparison)
            exp_1_mask = exp_col_vals >= exp_1 if self.signal_direction == 'resistance' else exp_col_vals <= exp_1
            exp_1_5_mask = exp_col_vals >= exp_1_5 if self.signal_direction == 'resistance' else exp_col_vals <= exp_1_5
            exp_2_mask = exp_col_vals >= exp_2 if self.signal_direction == 'resistance' else exp_col_vals <= exp_2
            
            opp_1_mask = opp_col_vals >= opp_1 if self.signal_direction == 'resistance' else opp_col_vals <= opp_1
            opp_1_5_mask = opp_col_vals >= opp_1_5 if self.signal_direction == 'resistance' else opp_col_vals <= opp_1_5
            opp_2_mask = opp_col_vals >= opp_2 if self.signal_direction == 'resistance' else opp_col_vals <= opp_2
            
            # Find first occurrence after touch_idx using argmax on sliced masks
            def find_first_true(mask, start_idx):
                """Find first True value in mask starting from start_idx."""
                if start_idx >= len(mask):
                    return None
                sliced = mask[start_idx:]
                if not sliced.any():
                    return None
                idx_in_slice = np_local_global.argmax(sliced)
                return start_idx + idx_in_slice
            
            # Calculate hit times for all 6 targets
            hit_1_exp_idx = find_first_true(exp_1_mask, touch_idx)
            hit_1_5_exp_idx = find_first_true(exp_1_5_mask, touch_idx)
            hit_2_exp_idx = find_first_true(exp_2_mask, touch_idx)
            
            hit_1_opp_idx = find_first_true(opp_1_mask, touch_idx)
            hit_1_5_opp_idx = find_first_true(opp_1_5_mask, touch_idx)
            hit_2_opp_idx = find_first_true(opp_2_mask, touch_idx)
            
            # Set flags and times
            if hit_1_exp_idx is not None:
                self.first_hit_1_expected = True
                self.first_hit_1_expected_time = int(timestamps_arr[hit_1_exp_idx])
            if hit_1_5_exp_idx is not None:
                self.first_hit_1_5_expected = True
                self.first_hit_1_5_expected_time = int(timestamps_arr[hit_1_5_exp_idx])
            if hit_2_exp_idx is not None:
                self.first_hit_2_expected = True
                self.first_hit_2_expected_time = int(timestamps_arr[hit_2_exp_idx])
            
            if hit_1_opp_idx is not None:
                self.first_hit_1_opposite = True
                self.first_hit_1_opposite_time = int(timestamps_arr[hit_1_opp_idx])
            if hit_1_5_opp_idx is not None:
                self.first_hit_1_5_opposite = True
                self.first_hit_1_5_opposite_time = int(timestamps_arr[hit_1_5_opp_idx])
            if hit_2_opp_idx is not None:
                self.first_hit_2_opposite = True
                self.first_hit_2_opposite_time = int(timestamps_arr[hit_2_opp_idx])
            
            print(f"✅ [ANALYZE] Vectorized hit timing complete: 1%Exp={self.first_hit_1_expected}, 2%Exp={self.first_hit_2_expected}, 1%Opp={self.first_hit_1_opposite}")
            sys.stdout.flush()

        # =====================================================================
        # 🔧 VECTORIZED DRAWDOWN CALCULATION (Replaces iterrows at line 1766)
        # Uses cummax/cummin for O(n) instead of nested O(n²) loops
        # CRITICAL: signal_idx already defined above for fast hit calculation
        # =====================================================================
        if signal_idx < len(df):
            # Extract arrays for vectorized operations
            highs_all = df['high'].values
            lows_all = df['low'].values
            timestamps_all = df['timestamp'].values
            
            if self.signal_direction == 'resistance':
                targets = {
                    'level': self.signal_price,
                    '1pct': self.signal_price * 1.01,
                    '1.5pct': self.signal_price * 1.015,
                    '2pct': self.signal_price * 1.02
                }
                # For resistance: adverse = low (price going down), target hit when high >= target
                target_col = highs_all
                adverse_col = lows_all
                target_condition = lambda tcol, tp: tcol >= tp
            else:  # support
                targets = {
                    'level': self.signal_price,
                    '1pct': self.signal_price * 0.99,
                    '1.5pct': self.signal_price * 0.985,
                    '2pct': self.signal_price * 0.98
                }
                # For support: adverse = high (price going up), target hit when low <= target
                target_col = lows_all
                adverse_col = highs_all
                target_condition = lambda tcol, tp: tcol <= tp
            
            # Process each target level
            for key, target_price in targets.items():
                # Find first index where target is hit (using argmax on boolean mask)
                target_hit_mask = target_condition(target_col[signal_idx:], target_price)
                if not target_hit_mask.any():
                    # Target never hit
                    drawdown = None
                    adverse_time = None
                else:
                    target_hit_idx_rel = np_local_global.argmax(target_hit_mask)
                    target_hit_idx = signal_idx + target_hit_idx_rel
                    
                    if target_hit_idx == signal_idx:
                        # Hit immediately on first candle
                        drawdown = 0.0
                        adverse_time = None
                    else:
                        # Calculate adverse move before target hit
                        adverse_slice = adverse_col[signal_idx:target_hit_idx]
                        
                        if self.signal_direction == 'resistance':
                            # For resistance: find minimum low (most adverse downward move)
                            adverse_val = float(np_local_global.min(adverse_slice))
                            drawdown = (self.signal_price - adverse_val) / self.signal_price * 100
                            # Find time of adverse extreme
                            adverse_idx_rel = int(np_local_global.argmin(adverse_slice))
                        else:
                            # For support: find maximum high (most adverse upward move)
                            adverse_val = float(np_local_global.max(adverse_slice))
                            drawdown = (adverse_val - self.signal_price) / self.signal_price * 100
                            # Find time of adverse extreme
                            adverse_idx_rel = int(np_local_global.argmax(adverse_slice))
                        
                        adverse_time = int(timestamps_all[signal_idx + adverse_idx_rel])
                
                # Store results
                if key == 'level':
                    self.drawdown_before_level = drawdown
                    self.drawdown_before_level_time = adverse_time
                elif key == '1pct':
                    self.drawdown_before_1pct = drawdown
                    self.drawdown_before_1pct_time = adverse_time
                elif key == '1.5pct':
                    self.drawdown_before_1_5pct = drawdown
                    self.drawdown_before_1_5pct_time = adverse_time
                elif key == '2pct':
                    self.drawdown_before_2pct = drawdown
                    self.drawdown_before_2pct_time = adverse_time
                
                print(f"📊 [ANALYZE] Vectorized drawdown for {key}: {drawdown}")
                sys.stdout.flush()
        if self.log_events:
            if self.drawdown_before_level is not None:
                time_str = pd.to_datetime(self.drawdown_before_level_time, unit='ms', utc=True).strftime("%Y-%m-%d %H:%M") if self.drawdown_before_level_time else "unknown"
                self.add_log(f"Drawdown before level: {self.drawdown_before_level:.2f}% at {time_str}")
            else:
                self.add_log("Drawdown before level: N/A")
                
        # ----- Maximum Adverse & Expected Moves (from first touch) -----
        if self.events and len(self.events) > 0:
            first_touch_ts = self.events[0]['timestamp']
            try:
                touch_idx = df.loc[df['timestamp'] == first_touch_ts].index[0]
            except IndexError:
                touch_idx = df['timestamp'].searchsorted(first_touch_ts)
                touch_idx = min(touch_idx, len(df) - 1)
            
            df_trade = df.iloc[touch_idx:]
        
            if not df_trade.empty:
                if self.signal_direction == 'resistance':
                    # Adverse: Price goes DOWN (uses Low)
                    adv_series = df_trade['low']
                    adv_pct = (self.signal_price - adv_series) / self.signal_price * 100
                    # Expected: Price goes UP (uses High)
                    exp_series = df_trade['high']
                    exp_pct = (exp_series - self.signal_price) / self.signal_price * 100
                else:  # support
                    # Adverse: Price goes UP (uses High)
                    adv_series = df_trade['high']
                    adv_pct = (adv_series - self.signal_price) / self.signal_price * 100
                    # Expected: Price goes DOWN (uses Low)
                    exp_series = df_trade['low']
                    exp_pct = (self.signal_price - exp_series) / self.signal_price * 100

                # Store Max Adverse
                if not adv_pct.empty:
                    max_adv_idx = adv_pct.idxmax()
                    # FIX: Use .loc instead of .iloc to match the index label returned by idxmax()
                    self.max_adverse_move_pct = adv_pct.loc[max_adv_idx]
                    self.max_adverse_time = df_trade.loc[max_adv_idx, 'timestamp']
                else:
                    self.max_adverse_move_pct = None
                    self.max_adverse_time = None
                # Store Max Expected
                if not exp_pct.empty:
                    max_exp_idx = exp_pct.idxmax()
                    # FIX: Use .loc instead of .iloc to match the index label returned by idxmax()
                    self.max_expected_move_pct = exp_pct.loc[max_exp_idx]
                    self.max_expected_time = df_trade.loc[max_exp_idx, 'timestamp']
                else:
                    self.max_expected_move_pct = None
                    self.max_expected_time = None
            else:
                self.max_adverse_move_pct = None
                self.max_adverse_time = None
                self.max_expected_move_pct = None
                self.max_expected_time = None
        else:
            self.max_adverse_move_pct = None
            self.max_adverse_time = None
            self.max_expected_move_pct = None
            self.max_expected_time = None

        # Safe Logging
        if self.log_events:
            if self.max_adverse_move_pct is not None:
                self.add_log(f"Max Adverse: {self.max_adverse_move_pct:.2f}% at {pd.to_datetime(self.max_adverse_time, unit='ms', utc=True)}")
            if self.max_expected_move_pct is not None:
                self.add_log(f"Max Expected: {self.max_expected_move_pct:.2f}% at {pd.to_datetime(self.max_expected_time, unit='ms', utc=True)}")
            
        # ----- Original level‑based before‑return -----
        signal_idx_level = df['timestamp'].searchsorted(self.signal_time)
        # CRITICAL FIX: Clamp index
        signal_idx_level = min(signal_idx_level, len(df) - 1)
        
        if self.signal_direction == 'resistance':
            return_indices_level = df[df['high'] >= self.signal_price].index
        else:
            return_indices_level = df[df['low'] <= self.signal_price].index
        returns_after_level = return_indices_level[return_indices_level >= signal_idx_level]
        
        # CALCULATION
        print(f"📉 [ANALYZE] Calculating max adverse before return to signal level...")
        sys.stdout.flush()
        
        if len(returns_after_level) > 0:
            self.returned_to_signal = True
            first_return_idx = returns_after_level[0]
            df_before_return = df.iloc[signal_idx_level:first_return_idx+1]
            if self.signal_direction == 'resistance':
                adv_before = (self.signal_price - df_before_return['low']) / self.signal_price * 100
            else:
                adv_before = (df_before_return['high'] - self.signal_price) / self.signal_price * 100
            if not adv_before.empty and len(adv_before) > 0:
                max_before_label = adv_before.idxmax()
                self.max_adverse_before_return_pct = adv_before.loc[max_before_label]
                self.max_adverse_before_return_time = df_before_return.loc[max_before_label, 'timestamp']
            # LOGGING
            if self.log_events:
                self.add_log(f"Max adverse before return to level price {self.signal_price:.5f}: {self.max_adverse_before_return_pct:.2f}% at {pd.to_datetime(self.max_adverse_before_return_time, unit='ms', utc=True)}")
            print(f"✅ [ADVERSE] Max adverse before return: {self.max_adverse_before_return_pct:.2f}%")
            sys.stdout.flush()
        else:
            self.returned_to_signal = False
            self.max_adverse_before_return_pct = None
            self.max_adverse_before_return_time = None
            if self.log_events:
                self.add_log("No return to level price within period.")
                self.add_log(f"No return to level price {self.signal_price:.5f} within period.")
            print(f"⏭️ [ADVERSE] No return to signal level found")
            sys.stdout.flush()
                
        # ----- Metrics based on starting price (entry at signal time) -----
        signal_idx_entry = df['timestamp'].searchsorted(self.signal_time)
        if signal_idx_entry >= len(df): signal_idx_entry = len(df) - 1
        if signal_idx_entry < 0: signal_idx_entry = 0
        entry_price = df.iloc[signal_idx_entry]['close']
        
        print(f"🔢 [ENTRY IDX] {self.symbols} signal_idx_entry={signal_idx_entry}, entry_price={entry_price}")
        
        # Reset all sgnl metrics to prevent stale data from previous runs
        self.max_adverse_sgnl_pct = None
        self.max_adverse_sgnl_time = None
        self.max_expected_sgnl_pct = None
        self.max_expected_sgnl_time = None
        self.returned_to_sgnl = False
        self.max_adverse_before_return_sgnl_pct = None
        self.max_adverse_before_return_sgnl_time = None

        if entry_price is None or (isinstance(entry_price, float) and is_na(entry_price)):
            if self.log_events:
                self.add_log("⚠️ Cannot determine entry price for sgnl metrics.")
            return

        # ✅ REAL-WORLD FIX: Slice data to ONLY scan forward from entry time
        df_post_entry = df.iloc[signal_idx_entry:]
        if df_post_entry.empty:
            if self.log_events:
                self.add_log("⚠️ No data after entry time for sgnl metrics.")
            return

        # 1️⃣ Max Adverse (Opposite direction from entry)
        if self.signal_direction == 'resistance':
            adv_series = df_post_entry['low']
            adv_pct = (entry_price - adv_series) / entry_price * 100
        else:  # support
            adv_series = df_post_entry['high']
            adv_pct = (adv_series - entry_price) / entry_price * 100
            
        if not adv_pct.empty and adv_pct.max() > 0:
            max_adv_idx = adv_pct.idxmax()
            self.max_adverse_sgnl_pct = adv_pct.loc[max_adv_idx]
            self.max_adverse_sgnl_time = df_post_entry.loc[max_adv_idx, 'timestamp']
        else:
            self.max_adverse_sgnl_pct = 0.0
            self.max_adverse_sgnl_time = df_post_entry.iloc[0]['timestamp']

        # 2️⃣ Max Expected (Favorable direction from entry)
        if self.signal_direction == 'resistance':
            exp_series = df_post_entry['high']
            exp_pct = (exp_series - entry_price) / entry_price * 100
        else:  # support
            exp_series = df_post_entry['low']
            exp_pct = (entry_price - exp_series) / entry_price * 100
            
        if not exp_pct.empty and exp_pct.max() > 0:
            max_exp_idx = exp_pct.idxmax()
            self.max_expected_sgnl_pct = exp_pct.loc[max_exp_idx]
            self.max_expected_sgnl_time = df_post_entry.loc[max_exp_idx, 'timestamp']
        else:
            self.max_expected_sgnl_pct = 0.0
            self.max_expected_sgnl_time = df_post_entry.iloc[0]['timestamp']

        # 3️⃣ Return to Entry & Drawdown Before Return (sgnl)
        if self.signal_direction == 'resistance':
            returned_mask = df_post_entry['low'] <= entry_price
        else:
            returned_mask = df_post_entry['high'] >= entry_price
            
        returned_indices = df_post_entry[returned_mask].index
        if len(returned_indices) > 0:
            self.returned_to_sgnl = True
            first_return_idx = returned_indices[0]
            df_before_return = df_post_entry.loc[df_post_entry.index[0]:first_return_idx]
            
            if self.signal_direction == 'resistance':
                adv_before = (entry_price - df_before_return['low']) / entry_price * 100
            else:
                adv_before = (df_before_return['high'] - entry_price) / entry_price * 100
                
            if not adv_before.empty and adv_before.max() > 0:
                self.drawdown_before_return_sgnl_pct = adv_before.max()
                self.drawdown_before_return_sgnl_time = df_before_return.loc[adv_before.idxmax(), 'timestamp']
            else:
                self.drawdown_before_return_sgnl_pct = 0.0
                self.drawdown_before_return_sgnl_time = df_before_return.iloc[0]['timestamp']
        else:
            self.returned_to_sgnl = False
            self.drawdown_before_return_sgnl_pct = None
            self.drawdown_before_return_sgnl_time = None
        
        print(f"✅ [ANALYZE] Completed advanced metrics for {sym} {self.timeframe}")
        sys.stdout.flush()
        
        # Final summary debug line
        events_count = len(self.events) if self.events else 0
        first_event_ts = self.events[0]['timestamp'] if self.events and len(self.events) > 0 else None
        first_event_str = pd.to_datetime(first_event_ts, unit='ms', utc=True).strftime("%Y-%m-%d %H:%M") if first_event_ts else "None"
        print(f"📊 [SUMMARY] {sym} {self.timeframe} | Events: {events_count} | First Event: {first_event_str} | signal_idx: {signal_idx_entry} | Status: COMPLETE")
                
        if len(returned_indices) > 0 and 'adv_before' in locals() and not adv_before.empty and adv_before.max() > 0:
            max_before_idx = adv_before.idxmax()
            self.max_adverse_before_return_sgnl_pct = adv_before.loc[max_before_idx]
            self.max_adverse_before_return_sgnl_time = df_before_return.loc[max_before_idx, 'timestamp']
        else:
            self.max_adverse_before_return_sgnl_pct = None
            self.max_adverse_before_return_sgnl_time = None

        # ✅ Safe Consolidated Logging
        if self.log_events:
            self.add_log(f"📊 Sgnl Metrics | Max Adv: {self.max_adverse_sgnl_pct:.2f}% | Max Exp: {self.max_expected_sgnl_pct:.2f}% | Returned: {self.returned_to_sgnl}")
        
        # 🔧 CRITICAL: Invalidate Summary Cache so UI updates immediately after analysis
        try:
            from dash import no_update
            # Since we split update_summary into two callbacks, we just increment the version
            # to trigger both update_summary_stats_only and update_task_table_only
            global golden_store_version
            golden_store_version += 1
        except Exception:
            pass

from concurrent.futures import ThreadPoolExecutor, as_completed

class TaskManager:
    def __init__(self, max_workers=4):
        self.tasks = {}
        self.queue = queue.Queue()
        self.lock = threading.Lock()
        self.executor = ThreadPoolExecutor(max_workers=max_workers, thread_name_prefix="SignalWorker")
        # Start a dispatcher thread that feeds the pool
        threading.Thread(target=self._dispatcher, daemon=True).start()

    def _dispatcher(self):
        while True:
            task = self.queue.get()
            if task is None:
                break
            self.executor.submit(task.run, self)
            self.queue.task_done()

    def add_task(self, task):
        with self.lock:
            self.tasks[task.task_id] = task
        self.queue.put(task)
        return True

    def _worker(self):
        while True:
            t = self.queue.get()
            t.run(self)

    def get_task(self, tid):
        with self.lock:
            return self.tasks.get(tid)

    def stop_task(self, tid):
        with self.lock:
            t = self.tasks.get(tid)
            if t:
                t.stop_event.set()
                t.pause_event.clear()
                return True
            return False

    def pause_task(self, tid):
        with self.lock:
            t = self.tasks.get(tid)
            if t and t.status == "running":
                if t.pause_event.is_set():
                    t.pause_event.clear()
                    t.paused = False
                    t.add_log("Resumed")
                else:
                    t.pause_event.set()
                    t.paused = True
                    if t.last_ts is not None:
                        ts_str = pd.to_datetime(t.last_ts, unit='ms').strftime("%Y-%m-%d %H:%M:%S")
                        t.add_log(f"Paused after candle at {ts_str} (total {t.last_count})")
                    else:
                        t.add_log("Paused (no candles yet)")
                return True
            return False

    def remove_task(self, tid):
        with self.lock:
            if tid in self.tasks:
                del self.tasks[tid]

    def get_all_tasks(self):
        with self.lock:
            return list(self.tasks.values())

tm = TaskManager()

# 🔧 GLOBAL: Background recalc status tracker
recalc_bg = {"running": False, "count": 0, "total": 0, "stop_flag": False, "trigger_val": 0}
recalc_poller_enabled = False  # 🔧 Flag to control poller state

# VerificationManager and vm instance are now imported from database module
# See: from database import VerificationManager, vm



## ---------- Background Optimizer Manager (Low-Spec Safe) ----------
class OptimizerManager:
    def __init__(self):
        self.jobs = {}
        self.lock = threading.Lock()

    def submit(self, job_id, func, *args, **kwargs):
        with self.lock:
            while any(j['status'] == 'running' for j in self.jobs.values()):
                time.sleep(0.5)  # Prevent CPU thrashing on old Mac
            self.jobs[job_id] = {'status': 'running', 'progress': 0.0, 'result': None, 'error': None}
        def _run():
            try:
                res = func(*args, **kwargs)
                with self.lock:
                    self.jobs[job_id].update({'status': 'done', 'progress': 100.0, 'result': res})
            except Exception as e:
                with self.lock:
                    self.jobs[job_id].update({'status': 'error', 'progress': 0.0, 'error': str(e)})
        threading.Thread(target=_run, daemon=True).start()

    def get_status(self, job_id):
        with self.lock:
            return self.jobs.get(job_id, {'status': 'idle', 'progress': 0.0, 'result': None, 'error': None})

optimizer_mgr = OptimizerManager()

# ---------- Dash App ----------
app = dash.Dash(__name__, suppress_callback_exceptions=True, prevent_initial_callbacks='initial_duplicate')

# ----- Flask route for task actions (stop/pause/save) – unchanged -----
@app.server.route('/task-action', methods=['POST'])
def task_action():
    data = request.get_json()
    task_id = data.get('task_id')
    action = data.get('action')
    task = tm.get_task(task_id)
    if not task:
        return jsonify({'error': 'Task not found'}), 404
    if action == 'stop':
        if task.status == "running" and tm.stop_task(task_id):
            task.add_log("Stop signal sent.")
            return jsonify({'success': True})
    elif action == 'pause':
        tm.pause_task(task_id)
        new_label = "Resume" if task.paused else "Pause"
        return jsonify({'success': True, 'new_label': new_label})
    elif action == 'save':
        fname = os.path.join(LOGS_DIR, f"task_{task_id}_{datetime.now().strftime('%Y%m%d_%H%M%S')}.log")
        with open(fname, "w") as f:
            f.write("\n".join(task.log))
        task.add_log(f"Log saved to {fname}")
        return jsonify({'success': True})
    return jsonify({'error': 'Invalid action'}), 400

# ----- JavaScript for immediate button feedback – unchanged -----
app.index_string = '''
<!DOCTYPE html>
<html>
<head>
{%metas%}
<title>{%title%}</title>
{%favicon%}
{%css%}
<style>
/* Highlight column light yellow – applied directly to th/td cells */
.highlight-column {
    background-color: #fff9c4 !important;
}
/* Highlight row light green – applied to tr, affects its td children */
.highlight-row td {
    background-color: #c8e6c9 !important;
}
/* Hide column – use visibility:collapse to keep table layout stable */
.hidden-column td,
.hidden-column th {
    visibility: collapse !important;
    /* Remove any background highlight from hidden cells */
    background-color: inherit !important;
}
/* For the hidden header, show a narrow marker using pseudo-element */
.hidden-column th {
    visibility: visible !important;
    width: 20px !important;
    min-width: 20px !important;
    max-width: 20px !important;
    padding: 2px 0 !important;
    text-align: center !important;
    color: transparent !important;
    font-size: 0 !important;
    position: relative;
    background-color: #f0f0f0 !important;  /* match sticky header background */
}
.hidden-column th::before {
    content: "⋮";
    position: absolute;
    left: 0;
    right: 0;
    text-align: center;
    color: black;
    font-size: 14px;
    font-weight: bold;
}
/* Keep thead background sticky */
th {
    background-color: #f0f0f0;
    position: sticky;
    top: 0;
}
/* Strike-through for cells where level was never reached */
.strike-through {
    text-decoration: line-through !important;
}
</style>
</head>
<body>
{%app_entry%}
<footer>
{%config%}
{%scripts%}
{%renderer%}
<script>
// Global store for hidden columns (by zero-based column index)
let hiddenColumns = new Set();
// Function to apply hidden column classes to the current table
function applyHiddenColumns() {
    // 🔧 FIXED: Changed selector from #task-summary to #task-table-container
    const container = document.querySelector('#task-table-container');
    if (!container) return;
    const table = container.querySelector('table');
    if (!table) return;
    hiddenColumns.forEach(colIndex => {
        const columnCells = table.querySelectorAll(`tr th:nth-child(${colIndex+1}), tr td:nth-child(${colIndex+1})`);
        columnCells.forEach(cell => {
            cell.classList.add('hidden-column');
            cell.classList.remove('highlight-column');
        });
    });
}
// ✅ OPTIMIZED: Removed MutationObserver - it was causing infinite loops and race conditions
// Column hiding is now handled by CSS rules in the stylesheet, applied automatically on render
// Existing button feedback (unchanged) - now supports both BUTTON and DIV elements
document.addEventListener('click', function(e) {
    let target = e.target;
    
    // Check if the clicked element is a button or contains a button
    let button = null;
    if (target.tagName === 'BUTTON' || target.closest('button')) {
        button = target.tagName === 'BUTTON' ? target : target.closest('button');
    } else if (target.tagName === 'DIV' && target.classList.contains('interactive-button')) {
        button = target;
    }
    
    if (!button) return;
    
    try {
        // P1 IMPROVEMENT: Use data attributes instead of JSON parsing for better reliability
        let actionType = button.getAttribute('data-action');
        let taskId = button.getAttribute('data-task-id');
        
        // Fallback to old JSON parsing method for backward compatibility during transition
        if (!actionType || !taskId) {
            console.warn('Using legacy JSON ID parsing. Please update button generation.');
            let idObj = JSON.parse(button.id);
            if (idObj.type === 'pause-task' || idObj.type === 'stop-task' || idObj.type === 'save-log') {
                taskId = idObj.index;
                actionType = idObj.type === 'save-log' ? 'save' : (idObj.type === 'stop-task' ? 'stop' : 'pause');
            }
        }
        
        // Process action if we have valid data
        if (actionType && taskId) {
                // For Stop/Pause actions: use direct fetch (fast, no page reload needed)
                if (actionType === 'stop' || actionType === 'pause') {
                    fetch('/task-action', {
                        method: 'POST',
                        headers: {'Content-Type': 'application/json'},
                        body: JSON.stringify({task_id: taskId, action: actionType})
                    })
                    .then(response => response.json())
                    .then(data => {
                        if (data.success && actionType === 'pause') {
                            target.innerText = data.new_label;
                        }
                    })
                    .catch(err => {
                        console.error('Task action fetch failed:', err, 'Task ID:', taskId, 'Action:', actionType);
                    });
                }
                // For Chart/Details/Impulse actions: trigger Dash callback via hidden store
                else {
                    // Set the appropriate hidden store to trigger Dash callback
                    // Use CustomEvent to trigger Dash updates (Dash 4.x compatible)
                    if (actionType === 'chart') {
                        const event = new CustomEvent('dash-chart-trigger', { detail: { task_id: taskId, action: actionType } });
                        document.dispatchEvent(event);
                    } else if (actionType === 'details') {
                        const event = new CustomEvent('dash-details-trigger', { detail: { task_id: taskId } });
                        document.dispatchEvent(event);
                    } else if (actionType === 'impulse') {
                        const event = new CustomEvent('dash-impulse-trigger', { detail: { task_id: taskId, action: actionType } });
                        document.dispatchEvent(event);
                    } else if (actionType === 'rerun-strat' || actionType === 'rerun-impulse') {
                        // Use fetch for rerun actions since they modify server state
                        fetch('/task-action', {
                            method: 'POST',
                            headers: {'Content-Type': 'application/json'},
                            body: JSON.stringify({task_id: taskId, action: actionType})
                        })
                        .then(response => response.json())
                        .then(data => {
                            if (!data.success) {
                                console.error('Rerun action failed:', data.message);
                            }
                        })
                        .catch(err => {
                            console.error('Rerun action fetch failed:', err, 'Task ID:', taskId, 'Action:', actionType);
                        });
                    }
                }
            }
        } catch (e) {
            // P1 CRITICAL: Log errors instead of silently swallowing them
            console.error('Button click handler error:', e, 'Target:', button);
        }
    }
});
// Toggle column highlight on header click
// Toggle row highlight on ANY cell click (not a button, not a header, not an interactive-button DIV)
// CRITICAL FIX: Must check if click originated from inside a table cell, not just any element
document.addEventListener('click', function(e) {
    // CRITICAL: Check if we're clicking inside a TABLE first before checking for buttons
    // This ensures table clicks are handled even if they contain interactive elements
    let table = e.target.closest('table');
    
    // If we're NOT in a table, exit early (let button handler deal with it)
    if (!table) return;
    
    // Ignore clicks inside buttons OR interactive-button DIVs within the table
    if (e.target.closest('button') || e.target.closest('.interactive-button')) return;
    
    let cell = e.target.closest('th, td');
    if (!cell) return;
    
    // Column header click: toggle yellow highlight on the whole column
    if (cell.tagName === 'TH') {
        let colIndex = cell.cellIndex;
        let columnCells = table.querySelectorAll(`tr th:nth-child(${colIndex+1}), tr td:nth-child(${colIndex+1})`);
        let isHighlighted = columnCells.length > 0 && columnCells[0].classList.contains('highlight-column');
        columnCells.forEach(c => {
            if (isHighlighted) c.classList.remove('highlight-column');
            else c.classList.add('highlight-column');
        });
    }
    // Row click on ANY data cell: toggle green highlight on the whole row
    else if (cell.tagName === 'TD') {
        let row = cell.parentNode;
        if (row.classList.contains('highlight-row')) {
            row.classList.remove('highlight-row');
        } else {
            row.classList.add('highlight-row');
        }
    }
});
// Toggle column visibility on double-click of header (with highlight cleanup)
document.addEventListener('dblclick', function(e) {
    let th = e.target.closest('th');
    if (!th) return;
    let table = th.closest('table');
    if (!table) return;
    let colIndex = th.cellIndex;
    let columnCells = table.querySelectorAll(`tr th:nth-child(${colIndex+1}), tr td:nth-child(${colIndex+1})`);
    if (columnCells.length === 0) return;
    let isHidden = columnCells[0].classList.contains('hidden-column');
    if (isHidden) {
        // Show column
        columnCells.forEach(cell => cell.classList.remove('hidden-column'));
        hiddenColumns.delete(colIndex);
    } else {
        // Hide column and remove any highlight
        columnCells.forEach(cell => {
            cell.classList.add('hidden-column');
            cell.classList.remove('highlight-column');
        });
        hiddenColumns.add(colIndex);
    }
});
</script>
</footer>
</body>
</html>
'''

# ----- Flask route for task card HTML – unchanged -----
@app.server.route('/task-card/<task_id>')
def serve_task_card(task_id):
    task = tm.get_task(task_id)
    if not task:
        return "Task not found", 404
    summary = f"Symbols: {', '.join(task.symbols)} | TF: {task.timeframe}"
    if task.mode == 'period' and task.start_date:
        summary += f" | {task.start_date.date()} to {task.end_date.date()}"
    elif task.mode == 'last1000':
        summary += " | Last 1000"
    else:
        summary += " | Full History"
    log_text = "\n".join(task.log) if task.log else "No logs yet..."
    pause_label = "Resume" if task.paused else "Pause"
    html_str = f'''
<div id="task-{task_id}" style="border:1px solid #ccc; padding:10px; margin:10px; border-radius:5px;">
<h4 style="display:inline-block;">Task {task_id[:8]}</h4>
<button id='{{"type":"remove-task","index":"{task_id}"}}' style="float:right;">Remove</button>
<button id='{{"type":"save-log","index":"{task_id}"}}' style="float:right;">Save Log</button>
<button id='{{"type":"stop-task","index":"{task_id}"}}' style="float:right;">Stop</button>
<button id='{{"type":"pause-task","index":"{task_id}"}}' style="float:right;">{pause_label}</button>
<p>{summary}</p>
<div>
<progress id='{{"type":"progress","index":"{task_id}"}}' value="0" max="100"></progress>
<span id='{{"type":"progress-text","index":"{task_id}"}}'>0/0/0</span>
</div>
<textarea id='{{"type":"log","index":"{task_id}"}}' style="width:100%; height:100px;" readonly>{log_text}</textarea>
<div id='{{"type":"task-store","index":"{task_id}"}}' data-task_id="{task_id}" style="display:none;"></div>
</div>
'''
    return html_str

app.layout = html.Div([
    dcc.Store(id="task-ids-store", data=[]),
    dcc.Store(id="task-count-store", data=0),
    dcc.Store(id="recalc-complete-trigger", data=0),
    dcc.Store(id="click-store", data={}),
    dcc.Store(id="signal-data-store", data=[]),  # store parsed signals
    dcc.Store(id="golden-task-store-data", data=[]),  # ✅ NEW: Golden store for pre-processed tasks
    dcc.Store(id="golden-store-version", data=0),     # ✅ NEW: Version tracker for golden store
    dcc.Store(id="chart-button-trigger", data=None),  # Hidden trigger for chart button clicks (JS sets this)
    dcc.Store(id="impulse-button-trigger", data=None),  # Hidden trigger for impulse button clicks (JS sets this)
    dcc.Store(id="strategy-details-trigger", data=None),  # Hidden trigger for strategy details button clicks (JS sets this)
    dcc.Store(id="chart-click-store", data={}),   # NEW: store for chart button click deduplication
    dcc.Store(id="chart-task-id", data=None),     # store task_id for chart modal
    dcc.Store(id="rsi-visible-store", data=False),   # default: RSI hidden
    dcc.Store(id="strategy-visible-store", data=False),
    # ---- Measurement tool stores ----
    dcc.Store(id="measure-mode-store", data=False),
    dcc.Store(id="measure-points-store", data={"first": None, "second": None}),
    dcc.Store(id="measure-result-store", data=None),
    # ---- Strategy details modal stores ----
    dcc.Store(id="strategy-details-task-id", data=None),
    dcc.Store(id="details-click-store", data={}),   # deduplication for details button
    # --------------------------------
    dcc.Store(id="impulse-visible-store", data=True),
    dcc.Store(id="events-visible-store", data=True),
    dcc.Store(id="impulse-params-store", data={}),
    # 🔧 CRITICAL: Hidden dummy buttons for CustomEvent-triggered callbacks (using html.Button which supports n_clicks)
    html.Button(id="chart-event-dummy", style={"display": "none"}, n_clicks=0),
    html.Button(id="details-event-dummy", style={"display": "none"}, n_clicks=0),
    html.Button(id="impulse-event-dummy", style={"display": "none"}, n_clicks=0),
    dcc.Tabs(id="main-tabs", value="tab-tasks", children=[
        dcc.Tab(label="Tasks", value="tab-tasks"),
        dcc.Tab(label="Data Analysis", value="tab-analysis"),
    ]),
    html.Div(id="tab-content"),
    # Modal overlay for chart (full-screen, high z-index)
    html.Div(
        id="chart-modal",
        style={
            "display": "none",
            "position": "fixed",
            "top": "0",
            "left": "0",
            "width": "100vw",
            "height": "100vh",
            "backgroundColor": "rgba(240,240,240,0.95)",   # light overlay
            "zIndex": "9999",
            "justifyContent": "center",
            "alignItems": "center"
        },
        children=[
            html.Div(
                style={
                    "backgroundColor": "#ffffff",   # white background
                    "width": "90%",
                    "height": "90%",
                    "borderRadius": "8px",
                    "padding": "50px 20px 20px 20px",
                    "position": "relative",
                    "display": "flex",
                    "flexDirection": "column"
                },
                children=[
                    # Button row (Toggle RSI + Toggle Strategy + Measure + Close)
                    html.Div(
                        style={"position": "absolute", "top": "10px", "right": "10px", "display": "flex", "gap": "10px"},
                        children=[
                            html.Button("Toggle RSI", id="toggle-rsi-btn", style={
                                "background": "transparent",
                                "color": "black",
                                "border": "1px solid black",
                                "padding": "8px 16px",
                                "cursor": "pointer",
                                "fontSize": "14px",
                                "minWidth": "100px",
                                "whiteSpace": "nowrap"
                            }),
                            html.Button("Toggle Strategy", id="toggle-strategy-btn", style={
                                "background": "transparent",
                                "color": "black",
                                "border": "1px solid black",
                                "padding": "8px 16px",
                                "cursor": "pointer",
                                "fontSize": "14px",
                                "minWidth": "100px",
                                "whiteSpace": "nowrap"
                            }),
                            html.Button("Measure", id="toggle-measure-btn", style={
                                "background": "transparent",
                                "color": "black",
                                "border": "1px solid black",
                                "padding": "8px 16px",
                                "cursor": "pointer",
                                "fontSize": "14px",
                                "minWidth": "100px",
                                "whiteSpace": "nowrap"
                            }),
                            html.Button("Toggle Impulses", id="toggle-impulses-btn", style={
                                "background": "transparent",
                                "color": "black",
                                "border": "1px solid black",
                                "padding": "8px 16px",
                                "cursor": "pointer",
                                "fontSize": "14px",
                                "minWidth": "100px",
                                "whiteSpace": "nowrap"
                            }),
                            html.Button("Toggle Events", id="toggle-events-btn", style={
                                "background": "transparent",
                                "color": "black",
                                "border": "1px solid black",
                                "padding": "8px 16px",
                                "cursor": "pointer",
                                "fontSize": "14px",
                                "minWidth": "100px",
                                "whiteSpace": "nowrap"
                            }),
                            html.Button("✕", id="close-chart-modal", style={
                                "background": "transparent",
                                "color": "black",
                                "border": "none",
                                "fontSize": "20px",
                                "cursor": "pointer"
                            }),
                        ]
                    ),
                    dcc.Graph(id="task-chart", style={"flex": "1", "minHeight": "0"}),
                    html.Div(id="measure-hint", style={"color": "#333", "fontSize": "12px", "textAlign": "center", "marginTop": "5px"}),
                    html.Div(id="measure-result", style={"color": "black", "marginTop": "10px", "textAlign": "center", "fontSize": "14px"})
                ]
            )
        ]
    ),
    # Modal for strategy details (per task)
    html.Div(
        id="strategy-details-modal",
        style={
            "display": "none",
            "position": "fixed",
            "top": "0",
            "left": "0",
            "width": "100vw",
            "height": "100vh",
            "backgroundColor": "rgba(240,240,240,0.95)",   # light overlay
            "zIndex": "9999",
            "justifyContent": "center",
            "alignItems": "center"
        },
        children=[
            html.Div(
                style={
                    "backgroundColor": "#ffffff",   # white background
                    "width": "80%",
                    "height": "80%",
                    "borderRadius": "8px",
                    "padding": "20px",
                    "position": "relative",
                    "display": "flex",
                    "flexDirection": "column"
                },
                children=[
                    html.Button("✕", id="close-strategy-details-modal", style={
                        "position": "absolute",
                        "top": "10px",
                        "right": "10px",
                        "zIndex": "10000",
                        "background": "transparent",
                        "color": "black",
                        "border": "none",
                        "fontSize": "20px",
                        "cursor": "pointer"
                    }),
                    html.H4(id="strategy-details-title", style={"color": "black"}),
                    html.Div(id="strategy-details-content", style={"overflow-y": "auto", "flex": "1", "marginTop": "20px"})
                ]
            )
        ]
    ),
    # Modal for impulse details (only impulse signals)
    html.Div(
        id="impulse-details-modal",
        style={"display": "none", "position": "fixed", "top": "0", "left": "0", "width": "100vw", "height": "100vh",
               "backgroundColor": "rgba(240,240,240,0.95)", "zIndex": "9999", "justifyContent": "center", "alignItems": "center"},
        children=[
            html.Div(
                style={"backgroundColor": "#ffffff", "width": "80%", "height": "80%", "borderRadius": "8px",
                       "padding": "20px", "position": "relative", "display": "flex", "flexDirection": "column"},
                children=[
                    html.Button("✕", id="close-impulse-details-modal", style={"position": "absolute", "top": "10px", "right": "10px",
                                                                              "zIndex": "10000", "background": "transparent", "color": "black", "border": "none", "fontSize": "20px", "cursor": "pointer"}),
                    html.H4(id="impulse-details-title", style={"color": "black"}),
                    html.Div(id="impulse-details-content", style={"overflowY": "auto", "flex": "1", "marginTop": "20px"}),
                    html.Button("Export to CSV", id="export-impulse-csv", style={"marginTop": "10px", "alignSelf": "flex-end"}),
                    dcc.Download(id="download-impulse-csv")
                ]
            )
        ]
    ),
    dcc.Interval(id="progress-interval", interval=10000, disabled=False),
    dcc.Interval(id="analysis-interval", interval=5000, disabled=True),  # 🔧 Disabled by default, enabled during recalc
    dcc.Interval(id="verify-interval", interval=500, disabled=False),
    dcc.Interval(id="recalc-status-interval", interval=1000),
    dcc.Store(id="bulk-mode-store", data=False),
    dcc.Store(id="processing-ops-store", data={}),
    dcc.Store(id="task-page-store", data=0),
    dcc.Store(id="analysis-complete-trigger", data=0), # 🔧 NEW: Triggers UI refresh after analysis
    dcc.Store(id="recalc-lock-store", data={"locked": False, "message": ""}),  # 🔧 RECALC LOCK STATE
    dcc.Interval(id="recalc-poller", interval=1000, n_intervals=0, disabled=True),
])

@app.callback(
    Output("tab-content", "children"),
    Input("main-tabs", "value")
)
def render_tab(tab):
    if tab == "tab-tasks":
        return html.Div([
            html.H3("Create Tasks from Signal File"),
            # Active Download Monitor
            html.Div(
                id="active-download-monitor",
                style={
                    "backgroundColor": "#f8f9fa",
                    "border": "1px solid #ccc",
                    "borderRadius": "6px",
                    "padding": "12px",
                    "marginBottom": "15px",
                    "display": "flex",
                    "alignItems": "center",
                    "gap": "15px"
                },
                children=[
                    html.Div("📡 Active Download:", style={"fontWeight": "bold", "minWidth": "140px"}),
                    html.Div(id="monitor-task-info", children="Idle", style={"flex": "1", "fontSize": "13px"}),
                    html.Progress(id="monitor-progress", value="0", max=100, style={"width": "150px"}),
                    html.Button("⏸ Pause", id="monitor-pause-btn", style={"fontSize": "12px", "padding": "4px 8px"}, disabled=True),
                    html.Button("⏹ Stop", id="monitor-stop-btn", style={"fontSize": "12px", "padding": "4px 8px", "backgroundColor": "#ffcccc"}, disabled=True),
                ]
            ),
            # File upload
            html.Div([
                dcc.Upload(
                    id="upload-signals",
                    children=html.Button("Upload Signals File (TXT)"),
                    multiple=False
                ),
                html.Div(id="upload-status"),
            ]),
            html.Br(),
            html.H4("Or paste signals below:"),
            dcc.Textarea(
                id="signal-paste-input",
                placeholder="Paste your signal text here...",
                style={"width": "100%", "height": "200px"}
            ),
            html.Button("Parse Pasted Signals", id="parse-paste-btn", n_clicks=0),
            html.Div(id="paste-status"),
            html.Br(),
            # Period type selection
            html.Div([
                dcc.RadioItems(
                    id="period-type",
                    options=[
                        {'label': 'Date Range', 'value': 'date'},
                        {'label': 'Hours from Signal', 'value': 'hours'}
                    ],
                    value='hours'
                ),
            ]),
            # Date range picker (shown when period-type = 'date')
            html.Div(
                id="date-range-container",
                children=[
                    dcc.DatePickerRange(
                        id="date-range-picker",
                        start_date=datetime.now()-timedelta(days=30),
                        end_date=datetime.now()
                    ),
                ]
            ),
            # Hours input (shown when period-type = 'hours')
            html.Div(
                id="hours-container",
                style={'display': 'none'},
                children=[
                    dcc.Input(id="hours-input", type="number", min=1, value=20, step=1, style={"width": "100px"}),
                    html.Span(" hours from signal time (with 5 min buffer before)"),
                ]
            ),
            # Pre‑buffer minutes input (how much history before signal time)
            html.Div([
                dcc.Input(id="pre-buffer-input", type="number", min=10, max=480, step=10, value=120, style={"width": "100px"}),
                html.Span("minutes of history BEFORE signal time (for ATR/volume calculation)", style={"marginLeft": "10px"}),
            ], style={"marginBottom": "10px"}),
            html.Br(),
            # Common settings
            html.Div([
                html.Label("Timeframe:", style={"marginRight": "10px", "display": "inline-block"}),
                dcc.Dropdown(
                    id="timeframe-dropdown",
                    options=[{"label": k, "value": v} for k, v in TIMEFRAMES.items()],
                    value="1",
                    clearable=False,
                    style={"width": "200px", "display": "inline-block"}
                ),
            ], style={"marginBottom": "10px"}),
            html.Div([
                dcc.Checklist(
                    id="overwrite-checkbox",
                    options=[{"label": "Overwrite existing data", "value": "overwrite"}]
                ),
            ]),
            html.Br(),
            # Toggle for analysis beyond period
            html.Div([
                dcc.Checklist(
                    id="analyze-beyond",
                    options=[{"label": "Analyze beyond selected period (may produce long logs)", "value": "beyond"}],
                    value=[]
                ),
            ]),
            html.Br(),
            html.Div([
                html.Div([
                    dcc.Checklist(id="disable-strategy", options=[{"label": "Disable strategy detection", "value": "disable"}], value=["disable"]),
                    html.Button("🔄 Strategy", id="bulk-rerun-strategy", n_clicks=0, style={"marginLeft": "10px", "fontSize": "12px"})
                ], style={"display": "flex", "alignItems": "center", "marginBottom": "5px"}),
                html.Div([
                    dcc.Checklist(id="disable-impulse", options=[{"label": "Disable impulse detection", "value": "disable"}], value=["disable"]),
                    html.Button("🔄 Impulse", id="bulk-rerun-impulse", n_clicks=0, style={"marginLeft": "10px", "fontSize": "12px"})
                ], style={"display": "flex", "alignItems": "center", "marginBottom": "5px"}),
                html.Div([
                    dcc.Checklist(id="enable-event-logs", options=[{"label": "Disable event logs", "value": "disable"}], value=["disable"]),
                    html.Button("🔄 Events", id="bulk-rerun-events", n_clicks=0, style={"marginLeft": "10px", "fontSize": "12px"})
                ], style={"display": "flex", "alignItems": "center", "marginBottom": "5px"}),
                # NEW: Hide logs checkbox (checked by default for performance)
                html.Div([
                    dcc.Checklist(
                        id="hide-logs-checkbox",
                        options=[{"label": "Hide all logs from the log field", "value": "hide"}],
                        value=["hide"]  # Default: checked
                    ),
                ], style={"marginBottom": "10px"}),
            ], style={"marginBottom": "10px"}),
                    html.Button("Create Tasks from Signals", id="create-signal-tasks-btn", n_clicks=0),
                    html.Div([
                        dcc.Checklist(
                            id="autoclear-checkbox",
                            options=[{"label": "🗑️ Auto-clear previous tasks before creating new", "value": "autoclear"}],
                            value=["autoclear"],  # Checked by default
                            style={"marginTop": "5px", "marginBottom": "5px"}
                        )
                    ]),
                    html.Button("🗑️ Clear All Tasks Now", id="clear-all-tasks-btn", n_clicks=0, style={"backgroundColor": "#ffebee", "color": "#c62828", "marginLeft": "10px"}),
                    # --- NEW: Save/Load Controls ---
                # --- NEW: Save/Load Controls ---
                html.Div([
                    dcc.Input(id="save-filename-input", value="tasks_export", placeholder="Enter filename (e.g., my_tasks)",
                              style={"marginRight": "10px", "width": "200px"}),
                    html.Button("💾 Save Tasks", id="save-tasks-btn", n_clicks=0, style={"marginRight": "10px"}),
                    dcc.Dropdown(id="json-file-select", options=[], placeholder="Select saved file to load...",
                                 style={"width": "280px", "marginRight": "10px"}),
                    html.Button("📂 Load Selected", id="load-tasks-btn", n_clicks=0, style={"marginRight": "10px"}),
                    html.Button("⚡ Recalc Table Flags", id="recalc-table-flags-btn", n_clicks=0, style={"marginRight": "10px"}),
                ], style={"display": "flex", "alignItems": "center", "marginBottom": "10px", "marginTop": "10px"}),
                html.Div(id="save-load-status", style={"minHeight": "20px", "color": "#1565c0", "fontFamily": "monospace", "marginBottom": "10px"}),
            html.Div(id="bulk-rerun-status", style={"marginBottom": "10px", "color": "#1565c0", "fontFamily": "monospace", "minHeight": "20px"}),
            html.Div(id="recalc-status-bar", style={"marginBottom": "10px", "color": "#d84315", "fontFamily": "monospace", "minHeight": "20px", "fontWeight": "bold"}),
            # ----- Impulse Parameters Panel (collapsible) -----
            html.Details([
                html.Summary("⚡ Impulse Parameters (click to expand)", style={"fontWeight": "bold", "cursor": "pointer", "marginTop": "20px"}),
                html.Div([
                    html.Label("Select completed task:"),
                    dcc.Dropdown(id="impulse-task-selector", placeholder="Choose task", style={"marginBottom": "10px"}),
                    html.Div([
                        html.Div([
                            html.Label("ATR multiplier (body):", style={"width": "200px", "display": "inline-block"}),
                            dcc.Slider(id="impulse-range-mult", min=0.5, max=3.0, step=0.1, value=2.0, marks=None),
                        ], style={"marginBottom": "10px"}),
                        html.Div([
                            html.Label("Volume multiplier:", style={"width": "200px", "display": "inline-block"}),
                            dcc.Slider(id="impulse-vol-mult", min=1.0, max=3.0, step=0.1, value=1.5, marks=None),
                        ], style={"marginBottom": "10px"}),
                        html.Div([
                            html.Label("Body/range ratio:", style={"width": "200px", "display": "inline-block"}),
                            dcc.Slider(id="impulse-body-ratio", min=0.3, max=0.9, step=0.05, value=0.6, marks=None),
                        ], style={"marginBottom": "10px"}),
                        html.Div([
                            html.Label("Wick/range ratio:", style={"width": "200px", "display": "inline-block"}),
                            dcc.Slider(id="impulse-wick-ratio", min=0.3, max=0.8, step=0.05, value=0.5, marks=None),
                        ], style={"marginBottom": "10px"}),
                        html.Div([
                            dcc.Checklist(id="impulse-next-confirm", options=[{"label": "Require next candle confirmation", "value": "confirm"}], value=["confirm"]),
                        ], style={"marginBottom": "10px"}),
                        html.Div([
                            dcc.Checklist(id="impulse-rsi-divergence", options=[{"label": "Use RSI divergence", "value": "div"}], value=[]),
                        ], style={"marginBottom": "10px"}),
                        html.Div([
                            html.Label("RSI extreme threshold:", style={"width": "200px", "display": "inline-block"}),
                            dcc.Slider(id="impulse-rsi-extreme", min=60, max=90, step=5, value=80, marks=None),
                        ], style={"marginBottom": "10px"}),
                        html.Div([
                            dcc.Checklist(id="impulse-base-candle", options=[{"label": "Require base candle before impulse", "value": "base"}], value=[]),
                        ], style={"marginBottom": "10px"}),
                        html.Div([
                            dcc.Checklist(id="impulse-vol-accel", options=[{"label": "Require volume acceleration", "value": "accel"}], value=[]),
                        ], style={"marginBottom": "10px"}),
                        html.Div([
                            dcc.Checklist(
                                id="impulse-use-retracement",
                                options=[{"label": "✨ Use retracement entry (wait for pullback – higher win rate)", "value": "retrace"}],
                                value=["retrace"]
                            ),
                        ], style={"marginBottom": "10px"}),
                        html.Button("Apply to Selected Task", id="apply-impulse-params", n_clicks=0),
                        html.Button("Apply to All Completed Tasks", id="apply-impulse-all", n_clicks=0, style={"marginLeft": "10px"}),
                        html.Button("Run Grid Search", id="run-grid-search", n_clicks=0, style={"margin": "5px"}),
                        html.Button("Run Walk-Forward", id="run-walk-forward", n_clicks=0, style={"margin": "5px"}),
                        html.Div(id="impulse-apply-status", style={"marginTop": "10px"}),
                        html.Div(id="impulse-apply-all-status", style={"marginTop": "10px", "color": "blue"}),
                        html.Hr(),
                        html.H4("Impulse Backtest Results"),
                        html.Div(id="impulse-results", style={"fontFamily": "monospace", "whiteSpace": "pre-wrap"}),
                    ], style={"padding": "10px", "backgroundColor": "#f9f9f9", "borderRadius": "5px"})
                ], style={"marginBottom": "20px"})
            ]),
            # ----- Strategy Info Panel (collapsible) – Professional version -----
            html.Details([
                html.Summary("📊 Professional Strategy Framework – Multi‑Month Levels", style={"fontWeight": "bold", "cursor": "pointer"}),
                html.Div([
                    html.P("This strategy integrates best practices from professional traders to trade multi‑month resistance/support levels with high probability.", style={"marginTop": "10px"}),
                    html.H5("🎯 Entry Confirmation (Configurable)", style={"marginTop": "15px"}),
                    html.Ul([
                        html.Li("✅ Close confirmation – required by default (candle must close beyond the level)."),
                        html.Li("📈 Volume spike – volume > 1.5x 20‑period average."),
                        html.Li("🔄 Second touch – price touches level, moves away ≥0.5 ATR, then returns (optional)."),
                        html.Li("📉 RSI divergence – regular/hidden divergence (detected automatically)."),
                        html.Li("📊 OBV divergence – On‑Balance Volume divergence (optional)."),
                        html.Li("💪 Elder's Force Index – strong directional force (optional)."),
                        html.Li("📉 RSI extreme – overbought (>60) for resistance, oversold (<40) for support (optional)."),
                        html.Li("📉 Moving average slope – trend alignment (optional)."),
                        html.Li("🎲 Bollinger Band touch – price at outer band (optional)."),
                        html.Li("📐 Candlestick patterns – engulfing, pin bar, shooting star, hammer, inside bar."),
                        html.Li("🎯 Zone tolerance – price within ±0.3× ATR of the level (reduces noise)."),
                    ]),
                    html.H5("🚪 Exit & Risk Management", style={"marginTop": "15px"}),
                    html.Ul([
                        html.Li("Initial take profit: 1.5× ATR."),
                        html.Li("Initial stop loss: 0.75× ATR (bounce/retest) or fixed (momentum)."),
                        html.Li("Trailing stop: after reaching target, stop trails at 1× ATR."),
                        html.Li("Time stop: close after max 30 candles if no target/stop hit."),
                        html.Li("Forward simulation – no look‑ahead bias."),
                    ]),
                    html.H5("📊 Parameters (can be adjusted)", style={"marginTop": "15px"}),
                    html.Ul([
                        html.Li("volume_mult = 1.5"),
                        html.Li("atr_period = 14"),
                        html.Li("stop_loss_atr_mult = 0.75"),
                        html.Li("max_holding_bars = 30"),
                        html.Li("trail_atr = 1.0"),
                        html.Li("zone_atr_mult = 0.3"),
                        html.Li("use_close_confirmation = True (always on)"),
                        html.Li("use_second_touch = False (recommend enabling)"),
                        html.Li("use_obv_divergence = False"),
                        html.Li("use_force_index = False"),
                        html.Li("use_rsi_extreme = False"),
                        html.Li("use_ma_slope = False"),
                        html.Li("use_bollinger_bands = False"),
                    ]),
                    html.P("💡 **Tip:** Enable second touch, OBV divergence, and RSI extreme for higher‑probability but fewer signals. Disable them for more aggressive trading.", style={"marginTop": "10px", "fontStyle": "italic"}),
                    html.P("📈 Chart markers: 🟢 Green ▲ = Buy signal, 🔴 Red ▼ = Sell signal. White dashed lines = signal level and time.", style={"fontSize": "small"}),
                ], style={"padding": "10px", "backgroundColor": "#f9f9f9", "borderRadius": "5px", "marginTop": "10px", "maxHeight": "400px", "overflowY": "auto"})
            ], style={"marginBottom": "20px"}),
            html.Hr(),
            html.Div(id="task-table-container", style={"width": "100%"}),
        ])
    else:
        # Data Analysis tab - now imported from database module
        return create_data_analysis_tab()

# ----- Callbacks for signal file handling -----
@app.callback(
    Output("upload-status", "children"),
    Output("signal-data-store", "data", allow_duplicate=True),
    Input("upload-signals", "contents"),
    State("upload-signals", "filename"),
    prevent_initial_call=True
)
def parse_signal_file(contents, filename):
    if contents is None:
        return "No file uploaded.", dash.no_update
    import base64
    content_type, content_string = contents.split(',')
    decoded = base64.b64decode(content_string).decode('utf-8')
    signals = parse_signal_text(decoded)
    if not signals:
        return "No valid signals found in file.", []
    # Convert signal times to milliseconds for storage
    for s in signals:
        s['time_ms'] = int(s['time'].timestamp() * 1000)
    return f"Loaded {len(signals)} signals from {filename}.", signals

@app.callback(
    Output("paste-status", "children"),
    Output("signal-data-store", "data", allow_duplicate=True),
    Input("parse-paste-btn", "n_clicks"),
    State("signal-paste-input", "value"),
    prevent_initial_call=True
)
def parse_pasted_signals(n_clicks, text):
    if not text:
        return "No text to parse.", dash.no_update
    signals = parse_signal_text(text)
    if not signals:
        return "No valid signals found in pasted text.", []
    for s in signals:
        s['time_ms'] = int(s['time'].timestamp() * 1000)
    return f"Parsed {len(signals)} signals from pasted text.", signals

@app.callback(
    Output("date-range-container", "style"),
    Output("hours-container", "style"),
    Input("period-type", "value")
)
def toggle_period_input(period_type):
    if period_type == 'date':
        return {'display': 'block'}, {'display': 'none'}
    else:
        return {'display': 'none'}, {'display': 'block'}

@app.callback(
    Output("task-ids-store", "data", allow_duplicate=True),
    Output("task-count-store", "data", allow_duplicate=True),
    Input("create-signal-tasks-btn", "n_clicks"),
    State("signal-data-store", "data"),
    State("period-type", "value"),
    State("date-range-picker", "start_date"),
    State("date-range-picker", "end_date"),
    State("hours-input", "value"),
    State("timeframe-dropdown", "value"),
    State("overwrite-checkbox", "value"),
    State("analyze-beyond", "value"),
    State("task-ids-store", "data"),
    State("disable-strategy", "value"),
    State("disable-impulse", "value"),
    State("pre-buffer-input", "value"),
    State("enable-event-logs", "value"),   # <-- NEW
    State("hide-logs-checkbox", "value"),  # ← NEW
    State("autoclear-checkbox", "value"),
    State("task-count-store", "data"),
    prevent_initial_call=True
)
def create_signal_tasks(n_clicks, signals, period_type, start_date, end_date, hours, tf, ow, beyond_val, stored_ids, strat_val, imp_val, pre_buffer, event_log_val, hide_logs_val, autoclear_val, count):
    """Parses signals and creates tasks with background processing for large batches."""
    if not signals:
        return stored_ids, count
    
    ow_flag = "overwrite" in ow if ow else False
    analyze_beyond = "beyond" in beyond_val if beyond_val else False
    strat_disabled = "disable" in strat_val if strat_val else False
    imp_disabled = "disable" in imp_val if imp_val else False
    log_events = "disable" not in event_log_val if event_log_val else True
    
    # AUTO-CLEAR LOGIC: Wipe memory if checkbox is checked
    if autoclear_val and "autoclear" in autoclear_val:
        tm.tasks.clear()
        new_ids = []
        new_count = 0
    else:
        new_ids = stored_ids.copy() if stored_ids else []
        new_count = count
        
    buffer_ms = SIGNAL_BUFFER_MINUTES * 60 * 1000
    
    total_signals = len(signals)
    
    # 🔧 CRITICAL: For large batches (>100 signals), use background processing
    # This prevents UI freeze during parsing
    if total_signals > 100:
        print(f"🚀 Large batch detected ({total_signals} signals) - using background processing...")
        
        # 🔧 Prepare serialized data for background thread
        import copy
        parse_data = {
            'signals': signals,
            'period_type': period_type,
            'start_date': start_date,
            'end_date': end_date,
            'hours': hours,
            'tf': tf,
            'ow_flag': ow_flag,
            'analyze_beyond': analyze_beyond,
            'strat_disabled': strat_disabled,
            'imp_disabled': imp_disabled,
            'log_events': log_events,
            'hide_logs_val': hide_logs_val,
            'pre_buffer': pre_buffer,
            'existing_ids': list(new_ids),
            'existing_count': new_count
        }
        
        # 🔧 Start background thread
        import threading
        threading.Thread(target=_run_parse_background, args=(parse_data,), daemon=True).start()
        
        # 🔧 Return updated IDs immediately so UI can track new tasks
        return new_ids, new_count
    
    # 🔧 SMALL BATCH: Process synchronously (original logic with improved progress)
    return _process_signals_sync(signals, period_type, start_date, end_date, hours, tf, 
                                  ow_flag, analyze_beyond, strat_disabled, imp_disabled, 
                                  log_events, hide_logs_val, pre_buffer, new_ids, new_count)


def _process_signals_sync(signals, period_type, start_date, end_date, hours, tf, 
                          ow_flag, analyze_beyond, strat_disabled, imp_disabled, 
                          log_events, hide_logs_val, pre_buffer, new_ids, new_count):
    """Synchronous signal processing for small batches (<100 signals)."""
    total_signals = len(signals)
    processed_count = 0
    failed_count = 0
    failed_details = []
    
    # 🔧 DYNAMIC STEP CALCULATOR: Same as recalc - ensures ~50 progress updates
    step = max(1, total_signals // 50)
    print(f"🔥 [PARSE] Starting synchronous processing of {total_signals} signals (step={step})")
    
    buffer_ms = SIGNAL_BUFFER_MINUTES * 60 * 1000
    
    for idx, sig in enumerate(signals):
        try:
            symbol = sig['symbol']
            signal_time = sig['time_ms']
            signal_price = sig['price']
            signal_direction = sig['direction']
            # Determine start/end based on period type
            if period_type == 'date':
                if not start_date or not end_date:
                    continue
                start_dt = datetime.fromisoformat(start_date)
                end_dt = datetime.fromisoformat(end_date)
            else:  # hours
                hours = hours if hours else 1
                # Use the pre‑buffer minutes from the input (default 120)
                pre_buf_min = int(pre_buffer) if pre_buffer else 120
                pre_buffer_ms = pre_buf_min * 60 * 1000
                start_dt = datetime.fromtimestamp((signal_time - pre_buffer_ms) / 1000.0, tz=timezone.utc)
                end_dt = start_dt + timedelta(hours=hours)
            # Create task
            tid = str(uuid.uuid4())
            # Extract hide_logs preference
            hide_logs = "hide" in hide_logs_val if hide_logs_val else True
            task = DownloadTask(
                tid, [symbol], tf, 'period', start_date=start_dt, end_date=end_dt,
                overwrite=ow_flag, price_continuity_check=False,
                signal_time=signal_time, signal_price=signal_price,
                signal_symbol=symbol, signal_direction=signal_direction,
                analyze_beyond=analyze_beyond,
                enable_strategy=not strat_disabled,
                enable_impulse=not imp_disabled,
                pre_buffer_minutes=int(pre_buffer) if pre_buffer else 120,
                log_events=log_events,
                hide_logs=hide_logs
            )
            tm.add_task(task)
            # Log the signal and period details immediately
            task.add_log(f"Signal: {symbol} at {pd.to_datetime(signal_time, unit='ms', utc=True)} price={signal_price} direction={signal_direction}")
            if period_type == 'hours':
                task.add_log(f"Period: {hours} hours from signal (with {pre_buf_min} min buffer) – from {start_dt} to {end_dt}")
            else:
                task.add_log(f"Period: date range – from {start_dt.date()} to {end_dt.date()}")
            new_ids.append(tid)
            new_count += 1
            processed_count += 1
            
            # 🔧 IMPROVED: Progress logging with dynamic step (not fixed 300)
            if (idx + 1) % step == 0 or (idx + 1) == total_signals:
                progress_msg = f"✓ Progress: {idx + 1}/{total_signals} tasks created..."
                if new_ids:
                    first_task = tm.get_task(new_ids[0])
                    if first_task:
                        first_task.add_log(progress_msg)
                print(f"✅ [PARSE] {progress_msg}")
                
        except Exception as e:
            failed_count += 1
            error_msg = f"✗ Failed to create task for signal {idx}: {symbol} - {str(e)}"
            failed_details.append(f"Signal {idx} ({symbol}): {str(e)}")
            if new_ids:
                first_task = tm.get_task(new_ids[0])
                if first_task:
                    first_task.add_log(error_msg)
            print(f"⚠️ [PARSE] {error_msg}")
            continue
    
    # Final summary log
    if total_signals > 1:
        summary_msg = f"✅ Task creation complete: {processed_count} created, {failed_count} failed out of {total_signals} signals"
        if new_ids:
            first_task = tm.get_task(new_ids[0])
            if first_task:
                first_task.add_log(summary_msg)
                if failed_details:
                    first_task.add_log(f"⚠️ Failed signals: {', '.join(failed_details[:10])}" + ("..." if len(failed_details) > 10 else ""))
        print(f"🎯 [PARSE] {summary_msg}")
        if failed_details:
            print(f"⚠️ First 10 failures: {', '.join(failed_details[:10])}")
    
    # 🔧 CRITICAL FIX: Update golden store so UI table sees newly created tasks immediately
    # This syncs tm.tasks (working storage) → golden_task_store_data (UI display source)
    global golden_task_store_data, golden_store_version
    with tm.lock:
        golden_task_store_data = list(tm.tasks.values())
        golden_store_version += 1  # Invalidate page caches to force refresh
    print(f"🔄 [PARSE] Golden store updated: {len(golden_task_store_data)} tasks, version={golden_store_version}")
    
    return new_ids, new_count


def _run_parse_background(parse_data):
    """Runs in background thread to parse large signal batches without blocking UI."""
    global current_tasks
    
    print(f"🔥 [PARSE THREAD] Started with {len(parse_data['signals'])} signals")
    sys.stdout.flush()
    
    # Extract parameters
    signals = parse_data['signals']
    period_type = parse_data['period_type']
    start_date = parse_data['start_date']
    end_date = parse_data['end_date']
    hours = parse_data['hours']
    tf = parse_data['tf']
    ow_flag = parse_data['ow_flag']
    analyze_beyond = parse_data['analyze_beyond']
    strat_disabled = parse_data['strat_disabled']
    imp_disabled = parse_data['imp_disabled']
    log_events = parse_data['log_events']
    hide_logs_val = parse_data['hide_logs_val']
    pre_buffer = parse_data['pre_buffer']
    existing_ids = parse_data['existing_ids']
    existing_count = parse_data['existing_count']
    
    total_signals = len(signals)
    step = max(1, total_signals // 50)
    print(f"🔥 [PARSE THREAD] Dynamic step calculated: {step} (total={total_signals})")
    sys.stdout.flush()
    
    new_ids = existing_ids.copy()
    new_count = existing_count
    processed_count = 0
    failed_count = 0
    failed_details = []
    
    # 🔧 CRITICAL FIX: Build tasks locally first, then atomic swap at end
    # This prevents spawning hundreds of concurrent downloads immediately
    local_tasks = {}
    
    for idx, sig in enumerate(signals):
        try:
            symbol = sig['symbol']
            signal_time = sig['time_ms']
            signal_price = sig['price']
            signal_direction = sig['direction']
            
            # Determine start/end based on period type
            if period_type == 'date':
                if not start_date or not end_date:
                    continue
                start_dt = datetime.fromisoformat(start_date)
                end_dt = datetime.fromisoformat(end_date)
            else:  # hours
                h = hours if hours else 1
                pre_buf_min = int(pre_buffer) if pre_buffer else 120
                pre_buffer_ms = pre_buf_min * 60 * 1000
                start_dt = datetime.fromtimestamp((signal_time - pre_buffer_ms) / 1000.0, tz=timezone.utc)
                end_dt = start_dt + timedelta(hours=h)
            
            # Create task
            tid = str(uuid.uuid4())
            hide_logs = "hide" in hide_logs_val if hide_logs_val else True
            task = DownloadTask(
                tid, [symbol], tf, 'period', start_date=start_dt, end_date=end_dt,
                overwrite=ow_flag, price_continuity_check=False,
                signal_time=signal_time, signal_price=signal_price,
                signal_symbol=symbol, signal_direction=signal_direction,
                analyze_beyond=analyze_beyond,
                enable_strategy=not strat_disabled,
                enable_impulse=not imp_disabled,
                pre_buffer_minutes=int(pre_buffer) if pre_buffer else 120,
                log_events=log_events,
                hide_logs=hide_logs
            )
            
            # 🔧 Store locally instead of adding to TaskManager immediately
            local_tasks[tid] = task
            
            # Log details
            task.add_log(f"Signal: {symbol} at {pd.to_datetime(signal_time, unit='ms', utc=True)} price={signal_price} direction={signal_direction}")
            if period_type == 'hours':
                task.add_log(f"Period: {h} hours from signal (with {pre_buf_min} min buffer)")
            else:
                task.add_log(f"Period: date range – from {start_dt.date()} to {end_dt.date()}")
            
            new_ids.append(tid)
            new_count += 1
            processed_count += 1
            
            # 🔧 CRITICAL: Update progress counter with DYNAMIC STEP
            if (idx + 1) % step == 0 or (idx + 1) == total_signals:
                print(f"🔥 [PARSE THREAD] Progress: {idx + 1}/{total_signals} (step={step})")
                sys.stdout.flush()
            
            # 🔧 HEARTBEAT: Every 10 tasks
            if (idx + 1) % max(10, step) == 0:
                print(f"💓 [PARSE THREAD] Heartbeat: Processing signal {idx + 1}/{total_signals}...")
                sys.stdout.flush()
                
        except Exception as e:
            failed_count += 1
            failed_details.append(f"Signal {idx} ({symbol}): {str(e)}")
            print(f"⚠️ [PARSE THREAD] Task {idx} error: {e} - continuing...")
            sys.stdout.flush()
            continue
    
    # 🔧 CRITICAL: Atomic swap - add all tasks at once after parsing complete
    # This prevents race conditions and uncontrolled concurrent downloads
    with tm.lock:
        tm.tasks.update(local_tasks)
    # Queue tasks for processing (worker threads will handle them sequentially)
    for task in local_tasks.values():
        tm.queue.put(task)
    
    # Update global RAM reference
    current_tasks = list(tm.tasks.values())
    
    # 🔧 CRITICAL FIX: Update golden store so UI table sees newly created tasks immediately (background thread)
    # This syncs tm.tasks (working storage) → golden_task_store_data (UI display source)
    global golden_task_store_data, golden_store_version
    with tm.lock:
        golden_task_store_data = list(tm.tasks.values())
        golden_store_version += 1  # Invalidate page caches to force refresh
    print(f"🔄 [PARSE THREAD] Golden store updated: {len(golden_task_store_data)} tasks, version={golden_store_version}")
    
    # Final summary
    summary_msg = f"✅ Parse complete: {processed_count} created, {failed_count} failed out of {total_signals} signals"
    if new_ids:
        first_task = tm.get_task(new_ids[0]) if new_ids else None
        if first_task:
            first_task.add_log(summary_msg)
            if failed_details:
                first_task.add_log(f"⚠️ Failed: {', '.join(failed_details[:10])}" + ("..." if len(failed_details) > 10 else ""))
    
    print(f"🎯 [PARSE THREAD] {summary_msg}")
    sys.stdout.flush()

# ----- Existing callbacks (unchanged) -----
@app.callback(
    Output("task-ids-store", "data", allow_duplicate=True),
    Input({"type": "remove-task", "index": ALL}, "n_clicks"),
    State("task-ids-store", "data"),
    prevent_initial_call=True
)
def remove_task(_, stored_ids):
    btn = ctx.triggered_id
    if not btn or not isinstance(btn, dict):
        return stored_ids
    tid = btn.get("index")
    if not tid:
        return stored_ids
    if stored_ids and tid in stored_ids:
        task = tm.get_task(tid)
        if task and hasattr(task, '_chart_cache'):
            task._chart_cache.clear()  # Free RAM before deletion
        tm.remove_task(tid)
        return [x for x in stored_ids if x != tid]
    return stored_ids

# Note: The JavaScript event listener at line 2578 handles DIV button clicks globally
# No need for a separate clientside_callback for remove-task buttons

# 🔧 CRITICAL: Clientside callback to handle DIV button clicks and trigger server-side callbacks
# This converts DIV clicks into store updates that server callbacks can listen to
clientside_callback(
    """
function(clickData) {
    // This is a dummy callback to enable DIV click handling via the existing JS event listener
    // The actual work is done by the JavaScript event listener at line 2578
    return window.dash_clientside.no_update;
}
""",
    Output("div-click-dummy-store", "data"),
    Input("div-click-trigger-store", "data"),
    prevent_initial_call=False
)

# 🔧 CRITICAL: Clientside callback to capture CustomEvent 'dash-chart-trigger' and update chart-button-trigger store
# This is the missing link that allows the chart button to work!
clientside_callback(
    """
function(n) {
    // This callback is triggered by the custom event via the window event listener below
    // The event detail is passed through the global window.dashChartEventData
    if (window.dashChartEventData) {
        return window.dashChartEventData;
    }
    return window.dash_clientside.no_update;
}
""",
    Output("chart-button-trigger", "data"),
    Input("chart-event-dummy", "n_clicks"),  # Dummy button that gets incremented by event listener
    prevent_initial_call=True
)

# 🔧 CRITICAL: Global event listeners for CustomEvents - these capture event details and update dummy counters
app.index_string = app.index_string.replace(
    '{%renderer%}',
    '''{%renderer%}
<script>
// Global event listeners for CustomEvents dispatched by button clicks
document.addEventListener('dash-chart-trigger', function(e) {
    window.dashChartEventData = e.detail;
    // Trigger a click on the hidden button to activate the clientside callback
    const dummyBtn = document.getElementById('chart-event-dummy');
    if (dummyBtn) dummyBtn.click();
});
document.addEventListener('dash-details-trigger', function(e) {
    window.dashDetailsEventData = e.detail;
    const dummyBtn = document.getElementById('details-event-dummy');
    if (dummyBtn) dummyBtn.click();
});
document.addEventListener('dash-impulse-trigger', function(e) {
    window.dashImpulseEventData = e.detail;
    const dummyBtn = document.getElementById('impulse-event-dummy');
    if (dummyBtn) dummyBtn.click();
});
</script>'''
)

# 🔧 CRITICAL: Clientside callback to capture CustomEvent 'dash-details-trigger' and update strategy-details-trigger store
# This enables the Details button to work
clientside_callback(
    """
function(n) {
    // This callback is triggered by the custom event via the window event listener
    // The event detail is passed through the global window.dashDetailsEventData
    if (window.dashDetailsEventData) {
        return window.dashDetailsEventData;
    }
    return window.dash_clientside.no_update;
}
""",
    Output("strategy-details-trigger", "data"),
    Input("details-event-dummy", "n_clicks"),  # Dummy button that gets incremented by event listener
    prevent_initial_call=True
)

# 🔧 CRITICAL: Clientside callback to capture CustomEvent 'dash-impulse-trigger' and update impulse-button-trigger store
# This enables the Impulse button to work
clientside_callback(
    """
function(n) {
    // This callback is triggered by the custom event via the window event listener
    // The event detail is passed through the global window.dashImpulseEventData
    if (window.dashImpulseEventData) {
        return window.dashImpulseEventData;
    }
    return window.dash_clientside.no_update;
}
""",
    Output("impulse-button-trigger", "data"),
    Input("impulse-event-dummy", "n_clicks"),  # Dummy button that gets incremented by event listener
    prevent_initial_call=True
)

@app.callback(
    Output({"type": "log", "index": ALL}, "value"),
    Output({"type": "progress", "index": ALL}, "value"),
    Output({"type": "progress-text", "index": ALL}, "children"),
    Input("progress-interval", "n_intervals"),
    State({"type": "task-store", "index": ALL}, "data")
)
def update_progress(_, stores):
    if not stores:
        return [], [], []
    logs, progs, texts = [], [], []
    for s in stores:
        tid = s.get("props", {}).get("data-task_id") if isinstance(s, dict) else None
        if not tid:
            tid = s.get("data", {}).get("task_id") if isinstance(s, dict) else None
        if not tid:
            logs.append("")
            progs.append("0")
            texts.append("0.0% 0/0/0")
            continue
        task = tm.get_task(tid)
        if task:
            logs.append("\n".join(task.log) if task.log else "No logs yet...")
            progs.append(str(task.progress))
            rem = max(0, task.total_candles - task.downloaded_candles) if task.total_candles else 0
            texts.append(f"{task.progress:.1f}%  {task.downloaded_candles}/{task.total_candles}/{rem}")
        else:
            logs.append("")
            progs.append("0")
            texts.append("0.0% 0/0/0")
    return logs, progs, texts

# ============================================================================
# 🔧 SPLIT CALLBACK #1: Summary Statistics Only (HEAVY - runs ONCE per data load)
# ============================================================================
@app.callback(
    Output("summary-stats-container", "children"),
    Input("golden-store-version", "data"),  # ✅ FIXED: Only trigger when data version changes (not on page clicks)
    Input("recalc-lock-store", "data")
)
def update_summary_stats_only(version, lock_state):
    """Calculate summary statistics ONLY when golden_store_version changes.
    Does NOT run on page navigation - this is the key fix for 10-minute freeze."""
    global golden_task_store_data, golden_store_version, recalculation_complete_timestamp
    
    # Validate global state
    if not hasattr(app, 'layout') or app.layout is None:
        return html.Div("", style={"display": "none"})
    
    # Get tasks from dcc.Store via callback context or fallback to global
    ctx = dash.callback_context
    if not ctx.triggered:
        return dash.no_update
        
    # Check if version changed (to avoid recalc on lock state changes alone)
    triggered_id = ctx.triggered[0]['prop_id'].split('.')[0]
    if triggered_id == "recalc-lock-store":
        return dash.no_update  # Don't recalc stats just because lock changed
        
    # Try to get data from store first, fallback to global
    try:
        # In a real dcc.Store setup, we'd get this from Input, but for now use global
        tasks = golden_task_store_data if golden_task_store_data else (list(tm.tasks.values()) if hasattr(tm, 'tasks') else [])
    except:
        tasks = []
    
    if not tasks:
        return html.Div("⏳ Initializing...", style={"textAlign": "center", "padding": "20px", "color": "#666"})
    
    # Lock check
    if lock_state and lock_state.get("locked", False):
        return html.Div([
            html.Div("⏳ Recalculating... Please wait", style={"textAlign": "center", "padding": "20px", "fontSize": "16px", "color": "#666"}),
            html.Div(lock_state.get("message", ""), style={"textAlign": "center", "fontSize": "12px", "color": "#999"})
        ])
    
    # Get tasks from Golden Store
    if golden_task_store_data is not None and len(golden_task_store_data) > 0:
        tasks = golden_task_store_data
    else:
        with tm.lock:
            tasks = list(tm.tasks.values())
        
    if not tasks:
        return "No tasks."
    
    # ✅ BASIC STATS: Clear separation of Completed vs Total Tasks
    total_tasks = len(tasks)
    completed_count = sum(1 for t in tasks if t.status == "completed")
    
    # ✅ FIXED: Removed page-specific averages from stats (they were causing confusion)
    # Stats now show GLOBAL averages across ALL tasks, not just visible page
    avg_adv = np.mean([t.max_adverse_move_pct for t in tasks if t.max_adverse_move_pct is not None and not is_na(t.max_adverse_move_pct)] or [0])
    avg_dd = np.mean([t.drawdown_before_level for t in tasks if t.drawdown_before_level is not None and not is_na(t.drawdown_before_level)] or [0])
    
    stats_rows = [
        html.Tr([html.Td("✅ Task Completed 100%"), html.Td(str(completed_count))]),
        html.Tr([html.Td("📦 Total Task"), html.Td(str(total_tasks))]),
        html.Tr([html.Td("📉 Avg Max Adverse (Global)"), html.Td(f"{avg_adv:.2f}%")]),
        html.Tr([html.Td("📉 Avg Drawdown Lvl (Global)"), html.Td(f"{avg_dd:.2f}%")])
    ]
    stats_table = html.Table([html.Tbody(stats_rows)], style={"border": "1px solid #ccc", "padding": "5px", "fontSize": "13px", "backgroundColor": "#f9f9f9"})
    
    # ✅ SIGNAL STATS: Calculated on ALL in-memory tasks (consistent denominator)
    reached_level_cnt = sum(1 for t in tasks if getattr(t, 'reached_level', False))
    reversed_dir_cnt = sum(1 for t in tasks if getattr(t, 'reversed_direction', False))
    hit_1_cnt = sum(1 for t in tasks if getattr(t, 'reached_level', False) and getattr(t, 'hit_1', False))
    hit_1_5_cnt = sum(1 for t in tasks if getattr(t, 'reached_level', False) and getattr(t, 'hit_1_5', False))
    hit_2_cnt = sum(1 for t in tasks if getattr(t, 'reached_level', False) and getattr(t, 'hit_2', False))
    
    def fmt_stat(stat_count, total):
        if total == 0: return "0 / 0 (0.0%)"
        return f"{stat_count} / {total} ({(stat_count/total)*100:.1f}%)"

    # ----- Max Adverse Distribution Stats -----
    def get_adverse_range_ui(pct):
        if pct is None or (isinstance(pct, float) and is_na(pct)):
            return None
        if 0 <= pct < 0.5: return "0-0.5%"
        elif 0.5 <= pct < 1: return "0.5-1%"
        elif 1 <= pct < 2: return "1-2%"
        elif 2 <= pct < 3: return "2-3%"
        elif 3 <= pct < 4: return "3-4%"
        elif 4 <= pct < 5: return "4-5%"
        elif 5 <= pct < 10: return "5-10%"
        elif 10 <= pct < 20: return "10-20%"
        elif 20 <= pct < 30: return "20-30%"
        elif pct >= 30: return ">30%"
        return None

    adverse_counts = {}
    for t in tasks:
        adv = getattr(t, 'max_adverse_move_pct', None)
        if t.reached_level and adv is not None and not (isinstance(adv, float) and is_na(adv)):
            range_key = get_adverse_range_ui(adv)
            if range_key:
                adverse_counts[range_key] = adverse_counts.get(range_key, 0) + 1

    ranges = ["0-0.5%", "0.5-1%", "1-2%", "2-3%", "3-4%", "4-5%", "5-10%", "10-20%", "20-30%", ">30%"]
    row1_adv = " | ".join([f"{r}:{adverse_counts.get(r,0)}" for r in ranges[:5]])
    row2_adv = " | ".join([f"{r}:{adverse_counts.get(r,0)}" for r in ranges[5:]])

    adv_05_plus_total = 0
    adv_4_plus_total = 0
    for t in tasks:
        adv = getattr(t, 'max_adverse_move_pct', None)
        if t.reached_level and adv is not None and not (isinstance(adv, float) and is_na(adv)):
            if adv >= 0.5:
                adv_05_plus_total += 1
            if adv >= 4.0:
                adv_4_plus_total += 1

    exp_counts = {}
    exp_05_plus_total = 0
    exp_4_plus_total = 0
    for t in tasks:
        exp = getattr(t, 'max_expected_move_pct', None)
        if t.reached_level and exp is not None and not (isinstance(exp, float) and is_na(exp)):
            range_key = get_adverse_range_ui(exp)
            if range_key:
                exp_counts[range_key] = exp_counts.get(range_key, 0) + 1
            if exp >= 0.5:
                exp_05_plus_total += 1
            if exp >= 4.0:
                exp_4_plus_total += 1
                
    row1_exp = " | ".join([f"{r}:{exp_counts.get(r,0)}" for r in ranges[:5]])
    row2_exp = " | ".join([f"{r}:{exp_counts.get(r,0)}" for r in ranges[5:]])

    td_style = {"fontSize": "13px", "fontWeight": "normal", "padding": "2px 5px"}
    
    adv_sgnl_counts = {}; exp_sgnl_counts = {}
    adv_sgnl_05 = 0; adv_sgnl_4 = 0; exp_sgnl_05 = 0; exp_sgnl_4 = 0
    for t in tasks:
        adv_s = getattr(t, 'max_adverse_sgnl_pct', None)
        if adv_s is not None and not (isinstance(adv_s, float) and is_na(adv_s)):
            r = get_adverse_range_ui(adv_s)
            if r: adv_sgnl_counts[r] = adv_sgnl_counts.get(r, 0) + 1
            if adv_s >= 0.5: adv_sgnl_05 += 1
            if adv_s >= 4.0: adv_sgnl_4 += 1
        exp_s = getattr(t, 'max_expected_sgnl_pct', None)
        if exp_s is not None and not (isinstance(exp_s, float) and is_na(exp_s)):
            r = get_adverse_range_ui(exp_s)
            if r: exp_sgnl_counts[r] = exp_sgnl_counts.get(r, 0) + 1
            if exp_s >= 0.5: exp_sgnl_05 += 1
            if exp_s >= 4.0: exp_sgnl_4 += 1
            
    row1_adv_s = " | ".join([f"{r}:{adv_sgnl_counts.get(r,0)}" for r in ranges[:5]])
    row2_adv_s = " | ".join([f"{r}:{adv_sgnl_counts.get(r,0)}" for r in ranges[5:]])
    row1_exp_s = " | ".join([f"{r}:{exp_sgnl_counts.get(r,0)}" for r in ranges[:5]])
    row2_exp_s = " | ".join([f"{r}:{exp_sgnl_counts.get(r,0)}" for r in ranges[5:]])
    
    delta_counts = {k: 0 for k in ranges}
    delta_05_plus_total = 0
    delta_4_plus_total = 0
    for t in tasks:
        dp = getattr(t, 'price_change_pct', None)
        if dp is not None and not (isinstance(dp, float) and is_na(dp)):
            val = abs(dp)
            r = get_adverse_range_ui(val)
            if r:
                delta_counts[r] += 1
            if val >= 0.5: delta_05_plus_total += 1
            if val >= 4.0: delta_4_plus_total += 1

    row1_delta = " | ".join([f"{r}:{delta_counts[r]}" for r in ranges[:5]])
    row2_delta = " | ".join([f"{r}:{delta_counts[r]}" for r in ranges[5:]])

    signal_stats_rows = [
        html.Tr([html.Td("Reached Level", style=td_style), html.Td(fmt_stat(reached_level_cnt, total_tasks), style=td_style)]),
        html.Tr([html.Td("Reversed Direction", style=td_style), html.Td(fmt_stat(reversed_dir_cnt, total_tasks), style=td_style)]),
        html.Tr([html.Td("Hit 1% (from level)", style=td_style), html.Td(fmt_stat(hit_1_cnt, total_tasks), style=td_style)]),
        html.Tr([html.Td("Hit 1.5% (from level)", style=td_style), html.Td(fmt_stat(hit_1_5_cnt, total_tasks), style=td_style)]),
        html.Tr([html.Td("Hit 2% (from level)", style=td_style), html.Td(fmt_stat(hit_2_cnt, total_tasks), style=td_style)]),
        html.Tr([html.Td("Max Adv 0-4% (lvl)", style=td_style), html.Td(row1_adv, style=td_style)]),
        html.Tr([html.Td("Max Adv 4%+ (lvl)", style=td_style), html.Td(row2_adv, style=td_style)]),
        html.Tr([html.Td("Max Adv 0.5%+ Total (lvl)", style=td_style), html.Td(str(adv_05_plus_total), style=td_style)]),
        html.Tr([html.Td("Max Adv 4%+ Total (lvl)", style=td_style), html.Td(str(adv_4_plus_total), style=td_style)]),
        html.Tr([html.Td("Max Exp 0-4% (lvl)", style=td_style), html.Td(row1_exp, style=td_style)]),
        html.Tr([html.Td("Max Exp 4%+ (lvl)", style=td_style), html.Td(row2_exp, style=td_style)]),
        html.Tr([html.Td("Max Exp 0.5%+ Total (lvl)", style=td_style), html.Td(str(exp_05_plus_total), style=td_style)]),
        html.Tr([html.Td("Max Exp 4%+ Total (lvl)", style=td_style), html.Td(str(exp_4_plus_total), style=td_style)]),
        html.Tr([html.Td("Max Adv 0-4% (sgnl)", style=td_style), html.Td(row1_adv_s, style=td_style)]),
        html.Tr([html.Td("Max Adv 4%+ (sgnl)", style=td_style), html.Td(row2_adv_s, style=td_style)]),
        html.Tr([html.Td("Max Adv 0.5%+ Total (sgnl)", style=td_style), html.Td(str(adv_sgnl_05), style=td_style)]),
        html.Tr([html.Td("Max Adv 4%+ Total (sgnl)", style=td_style), html.Td(str(adv_sgnl_4), style=td_style)]),
        html.Tr([html.Td("Max Exp 0-4% (sgnl)", style=td_style), html.Td(row1_exp_s, style=td_style)]),
        html.Tr([html.Td("Max Exp 4%+ (sgnl)", style=td_style), html.Td(row2_exp_s, style=td_style)]),
        html.Tr([html.Td("Max Exp 0.5%+ Total (sgnl)", style=td_style), html.Td(str(exp_sgnl_05), style=td_style)]),
        html.Tr([html.Td("Max Exp 4%+ Total (sgnl)", style=td_style), html.Td(str(exp_sgnl_4), style=td_style)]),
        html.Tr([html.Td("Delta Price 0-4%", style=td_style), html.Td(row1_delta, style=td_style)]),
        html.Tr([html.Td("Delta Price 4%+", style=td_style), html.Td(row2_delta, style=td_style)]),
        html.Tr([html.Td("Delta Price 0.5%+ Total", style=td_style), html.Td(str(delta_05_plus_total), style=td_style)]),
        html.Tr([html.Td("Delta Price 4%+ Total", style=td_style), html.Td(str(delta_4_plus_total), style=td_style)]),
    ]
    signal_stats_table = html.Table([html.Tbody(signal_stats_rows)], style={"border": "1px solid #4a90e2", "padding": "5px", "marginTop": "10px", "backgroundColor": "#f0f7ff"})
    
    return html.Div([
        stats_table,
        html.H5("Signal Performance Summary", style={"marginTop": "15px", "marginBottom": "5px"}),
        signal_stats_table,
        html.P(
            "ℹ️ Hit % metrics measure price movement ≥1%/1.5%/2% **in the EXPECTED direction** from the signal level base. "
            "Resistance: Price moves UP ≥X% from level. Support: Price moves DOWN ≥X% from level. "
            "Hits are only counted if the price actually touched the level first.",
            style={"fontSize": "11px", "color": "#777", "marginTop": "6px", "marginBottom": "0", "fontStyle": "italic"}
        )
    ])


# ============================================================================
# 🔧 SPLIT CALLBACK #2: Task Table Only (LIGHT - runs on every page click)
# ============================================================================

# ⚡ CRITICAL OPTIMIZATION: Page-level HTML cache
# Stores pre-rendered HTML rows for each page to avoid re-rendering on navigation
_page_html_cache = {}
_cached_golden_version = None

@app.callback(
    Output("task-table-container", "children"),
    Input("task-page-store", "data"),
    Input("golden-store-version", "data"),
    Input("recalc-lock-store", "data"),
    Input("analysis-complete-trigger", "data"),  # 🔧 NEW: Trigger UI refresh after recalculation completes
    prevent_initial_call=False
)
def update_task_table_only(current_page, version, lock_state, analysis_trigger):
    """Render task table ONLY. Uses aggressive caching to skip HTML generation on page changes."""
    global golden_task_store_data, golden_store_version, _page_html_cache, _cached_golden_version, cached_signal_stats_html, cached_small_stats_data, stats_cache_version
    
    # Initialize timer for full trace
    timer = PerfTimer(f"Page {current_page} Render (v{version})").start()
    
    # Validate global state
    if not hasattr(app, 'layout') or app.layout is None:
        timer.check("Validation Failed").end()
        return html.Div("", style={"display": "none"})
    
    # Get triggered input
    ctx = dash.callback_context
    if not ctx.triggered:
        timer.check("No Trigger").end()
        return dash.no_update
        
    triggered_id = ctx.triggered[0]['prop_id'].split('.')[0]
    print(f"[DEBUG] 🔍 TRIGGER: {triggered_id} | version={version} | page={current_page}")
    timer.check(f"Trigger Detected: {triggered_id}")
    
    # If only lock changed, don't re-render table
    if triggered_id == "recalc-lock-store" and version == getattr(update_task_table_only, '_last_version', None):
        print(f"[TRACE] Skipping render - lock change only")
        timer.check("Lock Skip").end()
        return dash.no_update
    
    update_task_table_only._last_version = version
    print(f"[DEBUG] 📊 STATE: golden_store_version={golden_store_version}, cache_size={len(_page_html_cache)}")
    
    # Lock check
    if lock_state and lock_state.get("locked", False):
        timer.check("Lock Active").end()
        return html.Div("⏳ Recalculating... Please wait", style={"textAlign": "center", "padding": "20px", "fontSize": "16px", "color": "#666"})
    
    # Get tasks from Golden Store
    t0 = time.time()
    if golden_task_store_data is not None and len(golden_task_store_data) > 0:
        tasks = golden_task_store_data
        print(f"[TRACE] ✓ Loaded {len(tasks)} tasks from golden store")
    else:
        with tm.lock:
            tasks = list(tm.tasks.values())
        print(f"[TRACE] ✓ Loaded {len(tasks)} tasks from task_manager")
    timer.check(f"Step 1: Get Data ({len(tasks)} tasks)")
    
    if not tasks:
        print("[TRACE] ✗ No tasks found")
        timer.end()
        return "No tasks."
    
    # CRITICAL CACHE CHECK
    current_golden_version = golden_store_version
    print(f"[TRACE] Version check: cached={_cached_golden_version}, current={current_golden_version}")
    
    # Invalidate cache if data changed
    if _cached_golden_version != current_golden_version:
        print(f"[TRACE] 🔄 Cache invalidated: {_cached_golden_version} -> {current_golden_version}")
        _page_html_cache.clear()
        _cached_golden_version = current_golden_version
        timer.check("Cache Invalidated")
    
    # ⚡ CRITICAL FIX: Cache MUST use version in key to avoid stale data
    cache_key = f"page_{current_page}_v{current_golden_version}"
    
    # Return cached page if available (INSTANT - no HTML generation)
    if cache_key in _page_html_cache:
        print(f"[TRACE] ⚡ CACHE HIT for key '{cache_key}'! Returning cached page {current_page}")
        timer.check("Cache Hit").end()
        return _page_html_cache[cache_key]
    
    print(f"[TRACE] ❌ CACHE MISS for key '{cache_key}'. Will generate rows.")
    timer.check("Cache Miss Confirmed")
    
    force_refresh = version is not None and version > 0
    
    # Pagination Slicing
    PAGE_SIZE = 300
    total_pages = max(1, (len(tasks) + PAGE_SIZE - 1) // PAGE_SIZE)
    current_page = max(0, min(current_page or 0, total_pages - 1))
    start_idx = current_page * PAGE_SIZE
    end_idx = start_idx + PAGE_SIZE
    visible_tasks = tasks[start_idx:end_idx]
    print(f"[TRACE] ✂️ Sliced tasks [{start_idx}:{end_idx}] → {len(visible_tasks)} visible")
    timer.check(f"Step 2: Pagination Slice")
    
    # Detect if this is ONLY a page navigation (no data change)
    prev_golden_version = getattr(update_task_table_only, '_last_golden_version', None)
    is_page_only_nav = (triggered_id == "task-page-store") and (prev_golden_version is not None) and (current_golden_version == prev_golden_version)
    
    # 🔧 CRITICAL FIX: Also treat analysis_trigger as a data change (not page nav)
    # This ensures full stats are calculated after recalculation completes
    if triggered_id == "analysis-complete-trigger":
        is_page_only_nav = False
        print(f"[TRACE] 🔄 Analysis trigger detected - forcing full stats recalculation")
    
    print(f"[TRACE] Navigation detection: triggered={triggered_id}, prev_ver={prev_golden_version}, curr_ver={current_golden_version} → is_page_only_nav={is_page_only_nav}")
    timer.check("Navigation Detection")
    
    # Store current state for next comparison
    update_task_table_only._last_golden_version = current_golden_version
    update_task_table_only._last_page = current_page
    
    # Pre-calculate helper functions ONCE - OPTIMIZED with native datetime (NO pandas)
    from datetime import datetime, timezone
    import math
    
    # Use global is_na function instead of local definition for consistency
    # Local is_na removed to avoid shadowing and ensure np.floating support
    
    def fmt_time(ts):
        """⚡ ULTRA-FAST timestamp formatting - NO pandas calls"""
        if ts is None:
            return "-"
        try:
            # Check for NA using native method
            if isinstance(ts, float) and math.isnan(ts):
                return "-"
            # Handle datetime objects directly
            if isinstance(ts, datetime):
                return ts.strftime("%Y-%m-%d %H:%M")
            if isinstance(ts, str):
                # ⚡ FAST PATH: Handle ISO-8601 strings directly (85x faster than pandas)
                ts_clean = ts.strip()
                if ts_clean.endswith('Z'):
                    ts_clean = ts_clean[:-1]
                if 'T' in ts_clean:
                    # ISO format: 2024-01-15T10:30:45.123
                    if '.' in ts_clean:
                        dt = datetime.strptime(ts_clean.split('.')[0], "%Y-%m-%dT%H:%M:%S")
                    else:
                        dt = datetime.strptime(ts_clean, "%Y-%m-%dT%H:%M:%S")
                    return dt.strftime("%Y-%m-%d %H:%M")
                # Try numeric string
                try:
                    ts_num = float(ts_clean)
                    return datetime.fromtimestamp(ts_num / 1000.0, tz=timezone.utc).strftime("%Y-%m-%d %H:%M")
                except ValueError:
                    pass
            # Numeric timestamp (milliseconds)
            if isinstance(ts, (int, float)):
                return datetime.fromtimestamp(ts / 1000.0, tz=timezone.utc).strftime("%Y-%m-%d %H:%M")
        except Exception:
            return "-"
        # Fallback (should rarely happen)
        try:
            return datetime.fromtimestamp(float(ts) / 1000.0, tz=timezone.utc).strftime("%Y-%m-%d %H:%M")
        except Exception:
            return "-"
    
    def fmt_dd(val):
        if val is None or is_na(val):
            return "-"
        try:
            return f"{float(val):.2f}%"
        except Exception:
            return "-"
    
    timer.check("Step 3: Helper Functions Setup")
    
    # Generate rows for visible tasks ONLY (300 max)
    # ⚡ PERFORMANCE OPTIMIZATION: Use render_task_table_row() helper which returns raw HTML strings
    # This avoids creating 15,600+ nested Python objects (300 rows × 52 columns)
    print(f"[TRACE] 🚀 Starting row generation for {len(visible_tasks)} tasks using optimized HTML string renderer...")
    t_row_start = time.time()
    
    # 🔧 CRITICAL FIX: Call render_task_table_row() which now returns raw HTML strings (<tr>...</tr>)
    # instead of html.Tr objects. This eliminates Dash serialization overhead.
    rows = [render_task_table_row(t) for t in visible_tasks]
    row_count = len(rows)
    
    row_elapsed = time.time() - t_row_start
    print(f"[TRACE] ✓ Generated {row_count} rows in {row_elapsed:.2f}s ({row_elapsed/row_count*1000:.1f}ms per row) - USING RAW HTML STRINGS")
    timer.check(f"Step 4: Row Generation ({row_count} rows)")
    
    # Build table HTML as raw string
    t_table_start = time.time()
    
    # 🔧 HEADER: Build table header as raw HTML string
    header_cells = [
        "<th style=\"min-width:80px\">ID</th>",
        "<th style=\"min-width:80px\">Status</th>",
        "<th style=\"min-width:70px\">Progress</th>",
        "<th style=\"min-width:100px\">Symbols</th>",
        "<th style=\"min-width:70px\">Mode</th>",
        "<th style=\"min-width:80px\">Direction</th>",
        "<th style=\"min-width:120px\">Signal Time</th>",
        "<th style=\"min-width:120px\">First Event</th>",
        "<th style=\"min-width:60px\">Pin?</th>",
        "<th style=\"min-width:80px\">Price Δ% (sgnl-lvl)</th>",
        "<th style=\"min-width:70px\">Reached</th>",
        "<th style=\"min-width:70px\">Reversed</th>",
        "<th style=\"min-width:50px\">Hit 1% (lvl-fwd.dir)</th>",
        "<th style=\"min-width:60px\">Hit 1.5% (lvl-fwd.dir)</th>",
        "<th style=\"min-width:50px\">Hit 2% (lvl-fwd.dir)</th>",
        "<th style=\"min-width:50px\">1st 1% Exp</th>",
        "<th style=\"min-width:140px\">Time 1% Exp</th>",
        "<th style=\"min-width:60px\">1st 1.5% Exp</th>",
        "<th style=\"min-width:140px\">Time 1.5% Exp</th>",
        "<th style=\"min-width:50px\">1st 2% Exp</th>",
        "<th style=\"min-width:140px\">Time 2% Exp</th>",
        "<th style=\"min-width:50px\">1st 1% Opp</th>",
        "<th style=\"min-width:140px\">Time 1% Opp</th>",
        "<th style=\"min-width:60px\">1st 1.5% Opp</th>",
        "<th style=\"min-width:140px\">Time 1.5% Opp</th>",
        "<th style=\"min-width:50px\">1st 2% Opp</th>",
        "<th style=\"min-width:140px\">Time 2% Opp</th>",
        "<th style=\"min-width:100px\">Max Adv %(lvl)</th>",
        "<th style=\"min-width:140px\">Max Adv T(lvl)</th>",
        "<th style=\"min-width:100px\">Max Exp %(lvl)</th>",
        "<th style=\"min-width:140px\">Max Exp T(lvl)</th>",
        "<th style=\"min-width:100px\">Max Adv %(sgnl)</th>",
        "<th style=\"min-width:140px\">Max Adv T(sgnl)</th>",
        "<th style=\"min-width:100px\">Max Exp %(sgnl)</th>",
        "<th style=\"min-width:140px\">Max Exp T(sgnl)</th>",
        "<th style=\"min-width:140px\">Max Adv %(bef ret lvl)</th>",
        "<th style=\"min-width:140px\">Time (bef ret lvl)</th>",
        "<th style=\"min-width:140px\">Max Adv %(bef ret sgnl)</th>",
        "<th style=\"min-width:140px\">Time (bef ret sgnl)</th>",
        "<th style=\"min-width:80px\">DD% (Lvl)</th>",
        "<th style=\"min-width:140px\">DD Time (Lvl)</th>",
        "<th style=\"min-width:80px\">DD% (1%)</th>",
        "<th style=\"min-width:140px\">DD Time (1%)</th>",
        "<th style=\"min-width:80px\">DD% (1.5%)</th>",
        "<th style=\"min-width:140px\">DD Time (1.5%)</th>",
        "<th style=\"min-width:80px\">DD% (2%)</th>",
        "<th style=\"min-width:140px\">DD Time (2%)</th>",
        "<th style=\"min-width:120px\">Strategy</th>",
        "<th style=\"min-width:80px\">Confidence</th>",
        "<th style=\"min-width:80px\">Impulse #</th>",
        "<th style=\"min-width:200px\">Log</th>",
        "<th style=\"min-width:180px\">Actions</th>"
    ]
    header_html = "<thead style=\"position:sticky;top:0;background-color:#f0f0f0;z-index:10\"><tr>" + "".join(header_cells) + "</tr></thead>"
    
    # 🔧 BODY: Join all row HTML strings (each row is already a <tr>...</tr> string from render_task_table_row)
    body_html = "<tbody>" + "".join(rows) + "</tbody>"
    
    # 🔧 TABLE: Assemble complete table as raw HTML string
    table_html = f"<table style=\"width:100%;border-collapse:collapse\">{header_html}{body_html}</table>"
    
    print(f"[TRACE] ✓ Built table HTML string in {time.time() - t_table_start:.2f}s")
    timer.check("Step 5: Build Table HTML")



    # ⚡ PERFORMANCE: Skip heavy stats calculation on page-only navigation
    # This is the CRITICAL FIX - stats are calculated ONLY when version changes (data reload/recalc)
    if is_page_only_nav:
        # Return minimal stats for page navigation (no heavy iteration over all tasks)
        # But we still need to show basic stats from ALL tasks (consistent across pages)
        total_tasks = len(tasks)
        completed_count = sum(1 for t in tasks if t.status == "completed")
        
        # ALL-task averages (still fast - just iterating, not generating HTML) - NO pandas
        avg_adv = np.mean([t.max_adverse_move_pct for t in tasks if t.max_adverse_move_pct is not None and not is_na(t.max_adverse_move_pct)] or [0])
        avg_dd = np.mean([t.drawdown_before_level for t in tasks if t.drawdown_before_level is not None and not is_na(t.drawdown_before_level)] or [0])
        
        stats_rows = [
            html.Tr([html.Td("✅ Task Completed (Total)"), html.Td(str(completed_count))]),
            html.Tr([html.Td("📦 Total Tasks"), html.Td(str(total_tasks))]),
            html.Tr([html.Td("📉 Avg Max Adverse (All)"), html.Td(fmt_dd(avg_adv))]),
            html.Tr([html.Td("📉 Avg Drawdown Lvl (All)"), html.Td(fmt_dd(avg_dd))])
        ]
        stats_table = html.Table([html.Tbody(stats_rows)], style={"border": "1px solid #ccc", "padding": "5px", "fontSize": "13px", "backgroundColor": "#f9f9f9"})
        
        # 🔧 FIX: Use cached signal stats from ALL tasks (calculated once per version)
        print(f"[DEBUG] ⏭️ USING CACHED SIGNAL STATS")
        stats_elapsed = 0.0
        # Access global cache (already declared at function level)
        signal_stats_table = cached_signal_stats_html if cached_signal_stats_html else html.Div("ℹ️ Stats loading...", style={"textAlign": "center", "padding": "10px", "color": "#555", "fontStyle": "italic"})
    else:
        # 🔧 CRITICAL: Calculate signal stats on ALL tasks when data loads/recalculates
        print(f"[DEBUG] 🚀 CALCULATING SIGNAL STATS for {len(tasks)} tasks...")
        
        t_stats_start = time.time()

        # ✅ BASIC STATS: Calculate only when data changes (not on page nav) - NOW USES ALL TASKS
        total_tasks = len(tasks)
        completed_count = sum(1 for t in tasks if t.status == "completed")

        # ALL-task averages (consistent across all pages)
        avg_adv = np.mean([t.max_adverse_move_pct for t in tasks if t.max_adverse_move_pct is not None and not is_na(t.max_adverse_move_pct)] or [0])
        avg_dd = np.mean([t.drawdown_before_level for t in tasks if t.drawdown_before_level is not None and not is_na(t.drawdown_before_level)] or [0])

        stats_rows = [
            html.Tr([html.Td("✅ Task Completed (Total)"), html.Td(str(completed_count))]),
            html.Tr([html.Td("📦 Total Tasks"), html.Td(str(total_tasks))]),
            html.Tr([html.Td("📉 Avg Max Adverse (All)"), html.Td(fmt_dd(avg_adv))]),
            html.Tr([html.Td("📉 Avg Drawdown Lvl (All)"), html.Td(fmt_dd(avg_dd))])
        ]
        stats_table = html.Table([html.Tbody(stats_rows)], style={"border": "1px solid #ccc", "padding": "5px", "fontSize": "13px", "backgroundColor": "#f9f9f9"})

        # ✅ SIGNAL STATS: Calculated on ALL in-memory tasks (consistent denominator)
        reached_level_cnt = sum(1 for t in tasks if t.reached_level)
        reversed_dir_cnt = sum(1 for t in tasks if t.reversed_direction)
        hit_1_cnt = sum(1 for t in tasks if t.reached_level and t.hit_1)
        hit_1_5_cnt = sum(1 for t in tasks if t.reached_level and t.hit_1_5)
        hit_2_cnt = sum(1 for t in tasks if t.reached_level and t.hit_2)
        
        def fmt_stat(stat_count, total):
            if total == 0: return "0 / 0 (0.0%)"
            return f"{stat_count} / {total} ({(stat_count/total)*100:.1f}%)"

        # ----- Max Adverse Distribution Stats (compact format) -----
        def get_adverse_range(pct):
            if pct is None or (isinstance(pct, float) and is_na(pct)):
                return None
            if 0 <= pct < 0.5: return "0-0.5%"
            elif 0.5 <= pct < 1: return "0.5-1%"
            elif 1 <= pct < 2: return "1-2%"
            elif 2 <= pct < 3: return "2-3%"
            elif 3 <= pct < 4: return "3-4%"
            elif 4 <= pct < 5: return "4-5%"
            elif 5 <= pct < 10: return "5-10%"
            elif 10 <= pct < 20: return "10-20%"
            elif 20 <= pct < 30: return "20-30%"
            elif pct >= 30: return ">30%"
            return None

        # Count tasks in each adverse range (only for reached_level tasks)
        adverse_counts = {}
        for t in tasks:
            adv = t.max_adverse_move_pct
            if t.reached_level and adv is not None and not (isinstance(adv, float) and is_na(adv)):
                range_key = get_adverse_range(adv)
                if range_key:
                    adverse_counts[range_key] = adverse_counts.get(range_key, 0) + 1

        # Format as two compact rows (5 ranges each) to save vertical space
        ranges = ["0-0.5%", "0.5-1%", "1-2%", "2-3%", "3-4%", "4-5%", "5-10%", "10-20%", "20-30%", ">30%"]
        row1_adv = " | ".join([f"{r}:{adverse_counts.get(r,0)}" for r in ranges[:5]])
        row2_adv = " | ".join([f"{r}:{adverse_counts.get(r,0)}" for r in ranges[5:]])

        # 🔧 Calculate cumulative totals for Max Adverse
        adv_05_plus_total = 0
        adv_4_plus_total = 0
        for t in tasks:
            adv = t.max_adverse_move_pct
            if t.reached_level and adv is not None and not (isinstance(adv, float) and is_na(adv)):
                if adv >= 0.5:
                    adv_05_plus_total += 1
                if adv >= 4.0:
                    adv_4_plus_total += 1

        # 🔧 NEW: Calculate distribution & cumulative totals for Max Expected
        exp_counts = {}
        exp_05_plus_total = 0
        exp_4_plus_total = 0
        for t in tasks:
            exp = t.max_expected_move_pct
            if t.reached_level and exp is not None and not (isinstance(exp, float) and is_na(exp)):
                range_key = get_adverse_range(exp)
                if range_key:
                    exp_counts[range_key] = exp_counts.get(range_key, 0) + 1
                if exp >= 0.5:
                    exp_05_plus_total += 1
                if exp >= 4.0:
                    exp_4_plus_total += 1
                
        row1_exp = " | ".join([f"{r}:{exp_counts.get(r,0)}" for r in ranges[:5]])
        row2_exp = " | ".join([f"{r}:{exp_counts.get(r,0)}" for r in ranges[5:]])

        # Define uniform style for all cells in the summary table
        td_style = {"fontSize": "13px", "fontWeight": "normal", "padding": "2px 5px"}
        
        # Calculate (sgnl) statistics for Adverse & Expected - OPTIMIZED with direct attribute access
        adv_sgnl_counts = {}; exp_sgnl_counts = {}
        adv_sgnl_05 = 0; adv_sgnl_4 = 0; exp_sgnl_05 = 0; exp_sgnl_4 = 0
        for t in tasks:
            adv_s = t.max_adverse_sgnl_pct
            if adv_s is not None and not (isinstance(adv_s, float) and is_na(adv_s)):
                r = get_adverse_range(adv_s)
                if r: adv_sgnl_counts[r] = adv_sgnl_counts.get(r, 0) + 1
                if adv_s >= 0.5: adv_sgnl_05 += 1
                if adv_s >= 4.0: adv_sgnl_4 += 1
            exp_s = t.max_expected_sgnl_pct
            if exp_s is not None and not (isinstance(exp_s, float) and is_na(exp_s)):
                r = get_adverse_range(exp_s)
                if r: exp_sgnl_counts[r] = exp_sgnl_counts.get(r, 0) + 1
                if exp_s >= 0.5: exp_sgnl_05 += 1
                if exp_s >= 4.0: exp_sgnl_4 += 1
                
        row1_adv_s = " | ".join([f"{r}:{adv_sgnl_counts.get(r,0)}" for r in ranges[:5]])
        row2_adv_s = " | ".join([f"{r}:{adv_sgnl_counts.get(r,0)}" for r in ranges[5:]])
        row1_exp_s = " | ".join([f"{r}:{exp_sgnl_counts.get(r,0)}" for r in ranges[:5]])
        row2_exp_s = " | ".join([f"{r}:{exp_sgnl_counts.get(r,0)}" for r in ranges[5:]])
        
        # Delta Price (sgnl to lvl) Distribution
        delta_counts = {k: 0 for k in ranges}
        delta_05_plus_total = 0
        delta_4_plus_total = 0
        for t in tasks:
            dp = t.price_change_pct
            if dp is not None and not (isinstance(dp, float) and is_na(dp)):
                val = abs(dp)
                r = get_adverse_range(val)
                if r:
                    delta_counts[r] += 1
                if val >= 0.5: delta_05_plus_total += 1
                if val >= 4.0: delta_4_plus_total += 1

        row1_delta = " | ".join([f"{r}:{delta_counts[r]}" for r in ranges[:5]])
        row2_delta = " | ".join([f"{r}:{delta_counts[r]}" for r in ranges[5:]])

        signal_stats_rows = [
            html.Tr([html.Td("Reached Level", style=td_style), html.Td(fmt_stat(reached_level_cnt, total_tasks), style=td_style)]),
            html.Tr([html.Td("Reversed Direction", style=td_style), html.Td(fmt_stat(reversed_dir_cnt, total_tasks), style=td_style)]),
            html.Tr([html.Td("Hit 1% (from level)", style=td_style), html.Td(fmt_stat(hit_1_cnt, total_tasks), style=td_style)]),
            html.Tr([html.Td("Hit 1.5% (from level)", style=td_style), html.Td(fmt_stat(hit_1_5_cnt, total_tasks), style=td_style)]),
            html.Tr([html.Td("Hit 2% (from level)", style=td_style), html.Td(fmt_stat(hit_2_cnt, total_tasks), style=td_style)]),
            # Max Adverse (lvl) Rows
            html.Tr([html.Td("Max Adv 0-4% (lvl)", style=td_style), html.Td(row1_adv, style=td_style)]),
            html.Tr([html.Td("Max Adv 4%+ (lvl)", style=td_style), html.Td(row2_adv, style=td_style)]),
            html.Tr([html.Td("Max Adv 0.5%+ Total (lvl)", style=td_style), html.Td(str(adv_05_plus_total), style=td_style)]),
            html.Tr([html.Td("Max Adv 4%+ Total (lvl)", style=td_style), html.Td(str(adv_4_plus_total), style=td_style)]),
            # Max Expected (lvl) Rows
            html.Tr([html.Td("Max Exp 0-4% (lvl)", style=td_style), html.Td(row1_exp, style=td_style)]),
            html.Tr([html.Td("Max Exp 4%+ (lvl)", style=td_style), html.Td(row2_exp, style=td_style)]),
            html.Tr([html.Td("Max Exp 0.5%+ Total (lvl)", style=td_style), html.Td(str(exp_05_plus_total), style=td_style)]),
            html.Tr([html.Td("Max Exp 4%+ Total (lvl)", style=td_style), html.Td(str(exp_4_plus_total), style=td_style)]),
            # Max Adverse (sgnl) Rows
            html.Tr([html.Td("Max Adv 0-4% (sgnl)", style=td_style), html.Td(row1_adv_s, style=td_style)]),
            html.Tr([html.Td("Max Adv 4%+ (sgnl)", style=td_style), html.Td(row2_adv_s, style=td_style)]),
            html.Tr([html.Td("Max Adv 0.5%+ Total (sgnl)", style=td_style), html.Td(str(adv_sgnl_05), style=td_style)]),
            html.Tr([html.Td("Max Adv 4%+ Total (sgnl)", style=td_style), html.Td(str(adv_sgnl_4), style=td_style)]),
            # Max Expected (sgnl) Rows
            html.Tr([html.Td("Max Exp 0-4% (sgnl)", style=td_style), html.Td(row1_exp_s, style=td_style)]),
            html.Tr([html.Td("Max Exp 4%+ (sgnl)", style=td_style), html.Td(row2_exp_s, style=td_style)]),
            html.Tr([html.Td("Max Exp 0.5%+ Total (sgnl)", style=td_style), html.Td(str(exp_sgnl_05), style=td_style)]),
            html.Tr([html.Td("Max Exp 4%+ Total (sgnl)", style=td_style), html.Td(str(exp_sgnl_4), style=td_style)]),
            # Delta Price Rows
            html.Tr([html.Td("Delta Price 0-4%", style=td_style), html.Td(row1_delta, style=td_style)]),
            html.Tr([html.Td("Delta Price 4%+", style=td_style), html.Td(row2_delta, style=td_style)]),
            html.Tr([html.Td("Delta Price 0.5%+ Total", style=td_style), html.Td(str(delta_05_plus_total), style=td_style)]),
            html.Tr([html.Td("Delta Price 4%+ Total", style=td_style), html.Td(str(delta_4_plus_total), style=td_style)]),
        ]
        signal_stats_table = html.Table([html.Tbody(signal_stats_rows)], style={"border": "1px solid #4a90e2", "padding": "5px", "marginTop": "10px", "backgroundColor": "#f0f7ff"})
        
        # Cache the stats for ALL tasks (calculated once per version)
        cached_signal_stats_html = signal_stats_table
        cached_small_stats_data = {"completed": completed_count, "total": total_tasks, "avg_adv": avg_adv, "avg_dd": avg_dd}
        stats_cache_version = golden_store_version
        
        stats_elapsed = time.time() - t_stats_start
        print(f"[DEBUG] ✅ SIGNAL STATS COMPLETE in {stats_elapsed:.2f}s (cached for version {stats_cache_version})")
    
    # 🔧 PAGINATION NAVIGATION
    nav_buttons = []
    nav_buttons.append(html.Button("<< Prev", id={"type":"page-nav","index":"prev"}, disabled=(current_page==0), style={"margin":"2px"}))
    for p in range(total_pages):
        btn_style = {"margin":"2px", "padding":"2px 6px", "fontWeight":"bold" if p==current_page else "normal"}
        nav_buttons.append(html.Button(str(p+1), id={"type":"page-nav","index":p}, style=btn_style))
    nav_buttons.append(html.Button("Next >>", id={"type":"page-nav","index":"next"}, disabled=(current_page==total_pages-1), style={"margin":"2px"}))
    nav_container = html.Div(nav_buttons, style={"display":"flex", "alignItems":"center", "marginBottom":"8px", "justifyContent":"center"})
    timer.check("Step 7: Build Pagination Nav")

    result = html.Div([
        html.H4("Task Summary"),
        nav_container,
        dcc.Markdown(table_html, dangerously_allow_html=True, style={"overflow-x": "auto", "overflow-y": "auto", "max-height": "75vh", "width": "100%"}),
        html.P(f"📄 Page {current_page+1} of {total_pages} | Showing tasks {start_idx+1}-{min(end_idx, len(tasks))} of {len(tasks)}", style={"textAlign":"center", "fontSize":"12px", "color":"#555"}),
        stats_table,
        html.H5("Signal Performance Summary", style={"marginTop": "15px", "marginBottom": "5px"}),
        signal_stats_table,
        html.P(
            "ℹ️ Hit % metrics measure price movement ≥1%/1.5%/2% **in the EXPECTED direction** from the signal level base. "
            "Resistance: Price moves UP ≥X% from level. Support: Price moves DOWN ≥X% from level. "
            "Hits are only counted if the price actually touched the level first.",
            style={"fontSize": "11px", "color": "#777", "marginTop": "6px", "marginBottom": "0", "fontStyle": "italic"}
        )
    ])
    timer.check("Step 8: Build Final Result Div")
    
    # ⚡ CACHE THE RESULT with version key for instant page switching (ALWAYS cache, regardless of stats)
    # The table HTML is the same whether we calculated full stats or page-only stats
    _page_html_cache[cache_key] = result
    timer.check("Step 9: Cache Result")
    
    # Print final timing
    timer.end()
    print(f"[TRACE] <<< COMPLETE Page {current_page} rendered in {timer.last_time - timer.start_time:.4f}s | Cache Size: {len(_page_html_cache)}")
    print(f"[TRACE] ✓✓✓ RETURNING RESULT TO DASH UI ✓✓✓")
    

    return result

def render_task_table_row(t):
    """Render a single task row for the table. Returns RAW HTML STRING (<tr>...</tr>) for performance."""
    # Extract and format display variables from task attributes
    direction_display = t.signal_direction if t.signal_direction else '-'
    signal_time_display = fmt_time_ui(t.signal_time) if t.signal_time else '-'
    first_event_display = fmt_time_ui(t.first_event_time) if t.first_event_time else '-'
    pin_display = "Yes" if t.first_event_is_pin else "No"
    price_change_display = fmt_dd_ui(t.price_change_pct) if t.price_change_pct is not None else '-'
    reached_display = "Yes" if t.reached_level else "No"
    
    # Lock check
    reversed_display = "Yes" if t.reversed_direction else "No"
    hit_1_display = "Yes" if t.hit_1 else "No"
    hit_1_5_display = "Yes" if t.hit_1_5 else "No"
    hit_2_display = "Yes" if t.hit_2 else "No"
    
    strategy_display = t.strategy_log_summary if t.strategy_log_summary else '-'
    strategy_conf = t.strategy_confidence if t.strategy_confidence else 0
    confidence_display = f"{strategy_conf:.1f}%" if strategy_conf else "-"
    
    # Count impulses
    impulse_count = sum(1 for sig in t.strategy_signals if sig.get('type') == 'impulse')
    impulse_display = str(impulse_count)
    
    # Format log display based on hide_logs setting - RETURN AS TEXT FOR HTML STRING
    if t.hide_logs:
        log_html = '<span style="color:#888;font-style:italic;font-size:12px">Logs are hidden</span>'
    else:
        log_text = "\n".join(t.log) if t.log else "No logs yet..."
        # Escape HTML special characters in log text
        import html as html_lib
        log_escaped = html_lib.escape(log_text)
        log_html = f'<div style="width:100%;max-height:100px;min-height:50px;font-family:monospace;font-size:11px;overflow-y:auto;white-space:pre-wrap;word-wrap:break-word;padding:4px;border:1px solid #ddd;border-radius:3px;background-color:#fafafa">{log_escaped}</div>'
    
    # Build action buttons as HTML strings
    task_id_str = str(t.task_id)
    is_completed = t.status == "completed"
    btn_disabled = "not-allowed" if not is_completed else "pointer"
    btn_opacity = "0.6" if not is_completed else "1"
    
    stop_btn = f'<div data-action="stop" data-task-id="{task_id_str}" style="margin:2px;padding:4px 8px;background-color:#ffcccc;border-radius:3px;cursor:pointer;display:inline-block;font-size:11px" class="interactive-button">Stop</div>'
    
    pause_label = "Resume" if t.paused else "Pause"
    pause_bg = "#fff3cd" if t.paused else "#d1ecf1"
    pause_btn = f'<div data-action="pause" data-task-id="{task_id_str}" style="margin:2px;padding:4px 8px;background-color:{pause_bg};border-radius:3px;cursor:pointer;display:inline-block;font-size:11px" class="interactive-button">{pause_label}</div>'
    
    chart_bg = "#d4edda" if is_completed else "#e9ecef"
    chart_btn = f'<div data-action="chart" data-task-id="{task_id_str}" style="margin:2px;padding:4px 8px;background-color:{chart_bg};border-radius:3px;cursor:{btn_disabled};display:inline-block;font-size:11px;opacity:{btn_opacity}" class="interactive-button">Chart</div>'
    
    details_bg = "#d4edda" if is_completed else "#e9ecef"
    details_btn = f'<div data-action="details" data-task-id="{task_id_str}" style="margin:2px;padding:4px 8px;background-color:{details_bg};border-radius:3px;cursor:{btn_disabled};display:inline-block;font-size:11px;opacity:{btn_opacity}" class="interactive-button">Details</div>'
    
    impulse_has_data = is_completed and impulse_count > 0
    impulse_bg = "#d4edda" if impulse_has_data else "#e9ecef"
    impulse_cursor = "pointer" if impulse_has_data else "not-allowed"
    impulse_opac = "1" if impulse_has_data else "0.6"
    impulse_btn = f'<div data-action="impulse" data-task-id="{task_id_str}" style="margin:2px;padding:4px 8px;background-color:{impulse_bg};border-radius:3px;cursor:{impulse_cursor};display:inline-block;font-size:11px;opacity:{impulse_opac}" class="interactive-button">Impulse</div>'
    
    rerun_strat_bg = "#d4edda" if is_completed else "#e9ecef"
    rerun_strat_btn = f'<div data-action="rerun-strat" data-task-id="{task_id_str}" style="margin:2px;padding:3px 6px;background-color:{rerun_strat_bg};border-radius:3px;cursor:{btn_disabled};display:inline-block;font-size:9px;opacity:{btn_opacity}" class="interactive-button">Re‑run Strategy</div>'
    
    rerun_impulse_bg = "#d4edda" if is_completed else "#e9ecef"
    rerun_impulse_btn = f'<div data-action="rerun-impulse" data-task-id="{task_id_str}" style="margin:2px;padding:3px 6px;background-color:{rerun_impulse_bg};border-radius:3px;cursor:{btn_disabled};display:inline-block;font-size:9px;opacity:{btn_opacity}" class="interactive-button">Re‑run Impulse</div>'
    
    # TV Button
    symbol = t.symbols[0] if t.symbols else ""
    tv_url = f"https://www.tradingview.com/chart/?symbol=BYBIT:{symbol}&interval={t.timeframe}"
    tv_btn = f'<a href="{tv_url}" target="_blank" title="Open TradingView Chart"><div style="margin:2px;padding:4px 8px;background-color:#e7f3ff;border-radius:3px;cursor:pointer;display:inline-block;font-size:11px">TV</div></a>'

    button_html = f'<div>{stop_btn}{pause_btn}{chart_btn}{details_btn}{impulse_btn}{rerun_strat_btn}{rerun_impulse_btn}{tv_btn}</div>'

    # Build and return RAW HTML STRING for the entire row
    return f"""<tr>
        <td style="min-width:80px">{task_id_str[:8]}</td>
        <td style="min-width:80px">{t.status}</td>
        <td style="min-width:70px">{t.progress:.1f}%</td>
        <td style="min-width:100px">{", ".join(t.symbols)}</td>
        <td style="min-width:70px">{t.mode}</td>
        <td style="min-width:80px">{direction_display}</td>
        <td style="min-width:120px">{signal_time_display}</td>
        <td style="min-width:120px">{first_event_display}</td>
        <td style="min-width:60px">{pin_display}</td>
        <td style="min-width:80px">{price_change_display}</td>
        <td style="min-width:70px">{reached_display}</td>
        <td style="min-width:70px">{reversed_display}</td>
        <td style="min-width:50px">{hit_1_display}</td>
        <td style="min-width:60px">{hit_1_5_display}</td>
        <td style="min-width:50px">{hit_2_display}</td>
        <td style="min-width:50px">{"Yes" if t.first_hit_1_expected else "No"}</td>
        <td style="min-width:140px">{fmt_time_ui(t.first_hit_1_expected_time)}</td>
        <td style="min-width:60px">{"Yes" if t.first_hit_1_5_expected else "No"}</td>
        <td style="min-width:140px">{fmt_time_ui(t.first_hit_1_5_expected_time)}</td>
        <td style="min-width:50px">{"Yes" if t.first_hit_2_expected else "No"}</td>
        <td style="min-width:140px">{fmt_time_ui(t.first_hit_2_expected_time)}</td>
        <td style="min-width:50px">{"Yes" if t.first_hit_1_opposite else "No"}</td>
        <td style="min-width:140px">{fmt_time_ui(t.first_hit_1_opposite_time)}</td>
        <td style="min-width:60px">{"Yes" if t.first_hit_1_5_opposite else "No"}</td>
        <td style="min-width:140px">{fmt_time_ui(t.first_hit_1_5_opposite_time)}</td>
        <td style="min-width:50px">{"Yes" if t.first_hit_2_opposite else "No"}</td>
        <td style="min-width:140px">{fmt_time_ui(t.first_hit_2_opposite_time)}</td>
        <td style="min-width:100px" class="{'strike-through' if not t.reached_level else ''}">{fmt_dd_ui(t.max_adverse_move_pct)}</td>
        <td style="min-width:140px" class="{'strike-through' if not t.reached_level else ''}">{fmt_time_ui(t.max_adverse_time)}</td>
        <td style="min-width:100px" class="{'strike-through' if not t.reached_level else ''}">{fmt_dd_ui(t.max_expected_move_pct)}</td>
        <td style="min-width:140px" class="{'strike-through' if not t.reached_level else ''}">{fmt_time_ui(t.max_expected_time)}</td>
        <td style="min-width:140px">{"Not returned" if not t.returned_to_signal else fmt_dd_ui(t.max_adverse_before_return_pct)}</td>
        <td style="min-width:140px">{fmt_time_ui(t.max_adverse_before_return_time) if t.returned_to_signal else "-"}</td>
        <td style="min-width:100px">{fmt_dd_ui(t.max_adverse_sgnl_pct)}</td>
        <td style="min-width:140px">{fmt_time_ui(t.max_adverse_sgnl_time)}</td>
        <td style="min-width:140px">{"Not returned" if not t.returned_to_sgnl else fmt_dd_ui(t.max_adverse_before_return_sgnl_pct)}</td>
        <td style="min-width:140px">{fmt_time_ui(t.max_adverse_before_return_sgnl_time) if t.returned_to_sgnl else "-"}</td>
        <td style="min-width:100px">{fmt_dd_ui(t.max_expected_sgnl_pct)}</td>
        <td style="min-width:140px">{fmt_time_ui(t.max_expected_sgnl_time)}</td>
        <td style="min-width:80px">{fmt_dd_ui(t.drawdown_before_level)}</td>
        <td style="min-width:140px">{fmt_time_ui(t.drawdown_before_level_time)}</td>
        <td style="min-width:80px">{fmt_dd_ui(t.drawdown_before_1pct)}</td>
        <td style="min-width:140px">{fmt_time_ui(t.drawdown_before_1pct_time)}</td>
        <td style="min-width:80px">{fmt_dd_ui(t.drawdown_before_1_5pct)}</td>
        <td style="min-width:140px">{fmt_time_ui(t.drawdown_before_1_5pct_time)}</td>
        <td style="min-width:80px">{fmt_dd_ui(t.drawdown_before_2pct)}</td>
        <td style="min-width:140px">{fmt_time_ui(t.drawdown_before_2pct_time)}</td>
        <td style="min-width:120px">{strategy_display}</td>
        <td style="min-width:80px">{confidence_display}</td>
        <td style="min-width:80px">{impulse_display}</td>
        <td style="min-width:200px">{log_html}</td>
        <td style="min-width:180px">{button_html}</td>
    </tr>"""


def render_task_table_header():
    """
    Render the table header with all column titles.
    Output: html.Thead component with sticky positioning
    """
    return html.Thead(html.Tr([
        html.Th("ID", style={"minWidth": "80px"}),
        html.Th("Status", style={"minWidth": "80px"}),
        html.Th("Progress", style={"minWidth": "70px"}),
        html.Th("Symbols", style={"minWidth": "100px"}),
        html.Th("Mode", style={"minWidth": "70px"}),
        html.Th("Direction", style={"minWidth": "80px"}),
        html.Th("Signal Time", style={"minWidth": "120px"}),
        html.Th("First Event", style={"minWidth": "120px"}),
        html.Th("Pin?", style={"minWidth": "60px"}),
        html.Th("Price Δ% (sgnl-lvl)", style={"minWidth": "80px"}),
        html.Th("Reached", style={"minWidth": "70px"}),
        html.Th("Reversed", style={"minWidth": "70px"}),
        html.Th("Hit 1% (lvl-fwd.dir)", style={"minWidth": "50px"}),
        html.Th("Hit 1.5% (lvl-fwd.dir)", style={"minWidth": "60px"}),
        html.Th("Hit 2% (lvl-fwd.dir)", style={"minWidth": "50px"}),
        html.Th("1st 1% Exp", style={"minWidth": "50px"}),
        html.Th("Time 1% Exp", style={"minWidth": "140px"}),
        html.Th("1st 1.5% Exp", style={"minWidth": "60px"}),
        html.Th("Time 1.5% Exp", style={"minWidth": "140px"}),
        html.Th("1st 2% Exp", style={"minWidth": "50px"}),
        html.Th("Time 2% Exp", style={"minWidth": "140px"}),
        html.Th("1st 1% Opp", style={"minWidth": "50px"}),
        html.Th("Time 1% Opp", style={"minWidth": "140px"}),
        html.Th("1st 1.5% Opp", style={"minWidth": "60px"}),
        html.Th("Time 1.5% Opp", style={"minWidth": "140px"}),
        html.Th("1st 2% Opp", style={"minWidth": "50px"}),
        html.Th("Time 2% Opp", style={"minWidth": "140px"}),
        html.Th("Max Adv %(lvl)", style={"minWidth": "100px"}),
        html.Th("Max Adv T(lvl)", style={"minWidth": "140px"}),
        html.Th("Max Exp %(lvl)", style={"minWidth": "100px"}),
        html.Th("Max Exp T(lvl)", style={"minWidth": "140px"}),
        html.Th("Max Adv %(sgnl)", style={"minWidth": "100px"}),
        html.Th("Max Adv T(sgnl)", style={"minWidth": "140px"}),
        html.Th("Max Exp %(sgnl)", style={"minWidth": "100px"}),
        html.Th("Max Exp T(sgnl)", style={"minWidth": "140px"}),           
        html.Th("Max Adv %(bef ret lvl)", style={"minWidth": "140px"}),
        html.Th("Time (bef ret lvl)", style={"minWidth": "140px"}),
        html.Th("Max Adv %(bef ret sgnl)", style={"minWidth": "140px"}),
        html.Th("Time (bef ret sgnl)", style={"minWidth": "140px"}),
        html.Th("DD% (Lvl)", style={"minWidth": "80px"}),
        html.Th("DD Time (Lvl)", style={"minWidth": "140px"}),
        html.Th("DD% (1%)", style={"minWidth": "80px"}),
        html.Th("DD Time (1%)", style={"minWidth": "140px"}),
        html.Th("DD% (1.5%)", style={"minWidth": "80px"}),
        html.Th("DD Time (1.5%)", style={"minWidth": "140px"}),
        html.Th("DD% (2%)", style={"minWidth": "80px"}),
        html.Th("DD Time (2%)", style={"minWidth": "140px"}),
        html.Th("Strategy", style={"minWidth": "120px"}),
        html.Th("Confidence", style={"minWidth": "80px"}),
        html.Th("Impulse #", style={"minWidth": "80px"}),
        html.Th("Log", style={"minWidth": "200px"}),
        html.Th("Actions", style={"minWidth": "180px"})
    ]), style={'position': 'sticky', 'top': 0, 'backgroundColor': '#f0f0f0', 'zIndex': 10})


def render_pagination_nav(current_page, total_pages):
    """
    Render pagination navigation buttons.
    Input: Current page number (0-indexed), total pages count
    Output: html.Div with navigation buttons
    """
    nav_buttons = []
    nav_buttons.append(html.Button("<< Prev", id={"type":"page-nav","index":"prev"}, disabled=(current_page==0), style={"margin":"2px"}))
    for p in range(total_pages):
        btn_style = {"margin":"2px", "padding":"2px 6px", "fontWeight":"bold" if p==current_page else "normal"}
        nav_buttons.append(html.Button(str(p+1), id={"type":"page-nav","index":p}, style=btn_style))
    nav_buttons.append(html.Button("Next >>", id={"type":"page-nav","index":"next"}, disabled=(current_page==total_pages-1), style={"margin":"2px"}))
    return html.Div(nav_buttons, style={"display":"flex", "alignItems":"center", "marginBottom":"8px", "justifyContent":"center"})


def render_basic_stats_table(completed_count, total_tasks, avg_adv, avg_dd):
    """
    Render basic statistics table (completion rate, averages).
    Input: Pre-calculated statistics
    Output: html.Table with basic stats
    """
    stats_rows = [
        html.Tr([html.Td("✅ Task Completed (Total)"), html.Td(str(completed_count))]),
        html.Tr([html.Td("📦 Total Tasks"), html.Td(str(total_tasks))]),
        html.Tr([html.Td("📉 Avg Max Adverse (All)"), html.Td(fmt_dd_ui(avg_adv))]),
        html.Tr([html.Td("📉 Avg Drawdown Lvl (All)"), html.Td(fmt_dd_ui(avg_dd))])
    ]
    return html.Table([html.Tbody(stats_rows)], style={"border": "1px solid #ccc", "padding": "5px", "fontSize": "13px", "backgroundColor": "#f9f9f9"})


def render_signal_stats_table(tasks):
    """
    Render detailed signal performance statistics table.
    Input: Full list of task objects (for iteration)
    Output: html.Table with comprehensive signal stats
    Note: This function DOES iterate and calculate stats from raw task data.
          This is intentional as it's a calculation function, not pure rendering.
          In future phases, this calculation logic will be extracted separately.
    """
    total_tasks = len(tasks)
    reached_level_cnt = sum(1 for t in tasks if t.reached_level)
    reversed_dir_cnt = sum(1 for t in tasks if t.reversed_direction)
    hit_1_cnt = sum(1 for t in tasks if t.reached_level and t.hit_1)
    hit_1_5_cnt = sum(1 for t in tasks if t.reached_level and t.hit_1_5)
    hit_2_cnt = sum(1 for t in tasks if t.reached_level and t.hit_2)
    
    def fmt_stat(stat_count, total):
        if total == 0: return "0 / 0 (0.0%)"
        return f"{stat_count} / {total} ({(stat_count/total)*100:.1f}%)"

    # ----- Max Adverse Distribution Stats (compact format) -----
    def get_adverse_range_ui(pct):
        if pct is None or (isinstance(pct, float) and is_na(pct)):
            return None
        if 0 <= pct < 0.5: return "0-0.5%"
        elif 0.5 <= pct < 1: return "0.5-1%"
        elif 1 <= pct < 2: return "1-2%"
        elif 2 <= pct < 3: return "2-3%"
        elif 3 <= pct < 4: return "3-4%"
        elif 4 <= pct < 5: return "4-5%"
        elif 5 <= pct < 10: return "5-10%"
        elif 10 <= pct < 20: return "10-20%"
        elif 20 <= pct < 30: return "20-30%"
        elif pct >= 30: return ">30%"
        return None

    # Count tasks in each adverse range (only for reached_level tasks)
    adverse_counts = {}
    for t in tasks:
        adv = t.max_adverse_move_pct
        if t.reached_level and adv is not None and not (isinstance(adv, float) and is_na(adv)):
            range_key = get_adverse_range_ui(adv)
            if range_key:
                adverse_counts[range_key] = adverse_counts.get(range_key, 0) + 1

    # Format as two compact rows (5 ranges each) to save vertical space
    ranges = ["0-0.5%", "0.5-1%", "1-2%", "2-3%", "3-4%", "4-5%", "5-10%", "10-20%", "20-30%", ">30%"]
    row1_adv = " | ".join([f"{r}:{adverse_counts.get(r,0)}" for r in ranges[:5]])
    row2_adv = " | ".join([f"{r}:{adverse_counts.get(r,0)}" for r in ranges[5:]])

    # Calculate cumulative totals for Max Adverse
    adv_05_plus_total = 0
    adv_4_plus_total = 0
    for t in tasks:
        adv = t.max_adverse_move_pct
        if t.reached_level and adv is not None and not (isinstance(adv, float) and is_na(adv)):
            if adv >= 0.5:
                adv_05_plus_total += 1
            if adv >= 4.0:
                adv_4_plus_total += 1

    # Calculate distribution & cumulative totals for Max Expected
    exp_counts = {}
    exp_05_plus_total = 0
    exp_4_plus_total = 0
    for t in tasks:
        exp = t.max_expected_move_pct
        if t.reached_level and exp is not None and not (isinstance(exp, float) and is_na(exp)):
            range_key = get_adverse_range_ui(exp)
            if range_key:
                exp_counts[range_key] = exp_counts.get(range_key, 0) + 1
            if exp >= 0.5:
                exp_05_plus_total += 1
            if exp >= 4.0:
                exp_4_plus_total += 1
                
    row1_exp = " | ".join([f"{r}:{exp_counts.get(r,0)}" for r in ranges[:5]])
    row2_exp = " | ".join([f"{r}:{exp_counts.get(r,0)}" for r in ranges[5:]])

    # Define uniform style for all cells in the summary table
    td_style = {"fontSize": "13px", "fontWeight": "normal", "padding": "2px 5px"}
    
    # Calculate (sgnl) statistics for Adverse & Expected
    adv_sgnl_counts = {}; exp_sgnl_counts = {}
    adv_sgnl_05 = 0; adv_sgnl_4 = 0; exp_sgnl_05 = 0; exp_sgnl_4 = 0
    for t in tasks:
        adv_s = t.max_adverse_sgnl_pct
        if adv_s is not None and not (isinstance(adv_s, float) and is_na(adv_s)):
            r = get_adverse_range_ui(adv_s)
            if r: adv_sgnl_counts[r] = adv_sgnl_counts.get(r, 0) + 1
            if adv_s >= 0.5: adv_sgnl_05 += 1
            if adv_s >= 4.0: adv_sgnl_4 += 1
        exp_s = t.max_expected_sgnl_pct
        if exp_s is not None and not (isinstance(exp_s, float) and is_na(exp_s)):
            r = get_adverse_range_ui(exp_s)
            if r: exp_sgnl_counts[r] = exp_sgnl_counts.get(r, 0) + 1
            if exp_s >= 0.5: exp_sgnl_05 += 1
            if exp_s >= 4.0: exp_sgnl_4 += 1
            
    row1_adv_s = " | ".join([f"{r}:{adv_sgnl_counts.get(r,0)}" for r in ranges[:5]])
    row2_adv_s = " | ".join([f"{r}:{adv_sgnl_counts.get(r,0)}" for r in ranges[5:]])
    row1_exp_s = " | ".join([f"{r}:{exp_sgnl_counts.get(r,0)}" for r in ranges[:5]])
    row2_exp_s = " | ".join([f"{r}:{exp_sgnl_counts.get(r,0)}" for r in ranges[5:]])
    
    # Delta Price (sgnl to lvl) Distribution
    delta_counts = {k: 0 for k in ranges}
    delta_05_plus_total = 0
    delta_4_plus_total = 0
    for t in tasks:
        dp = t.price_change_pct
        if dp is not None and not (isinstance(dp, float) and is_na(dp)):
            val = abs(dp)
            r = get_adverse_range_ui(val)
            if r:
                delta_counts[r] += 1
            if val >= 0.5: delta_05_plus_total += 1
            if val >= 4.0: delta_4_plus_total += 1

    row1_delta = " | ".join([f"{r}:{delta_counts[r]}" for r in ranges[:5]])
    row2_delta = " | ".join([f"{r}:{delta_counts[r]}" for r in ranges[5:]])

    signal_stats_rows = [
        html.Tr([html.Td("Reached Level", style=td_style), html.Td(fmt_stat(reached_level_cnt, total_tasks), style=td_style)]),
        html.Tr([html.Td("Reversed Direction", style=td_style), html.Td(fmt_stat(reversed_dir_cnt, total_tasks), style=td_style)]),
        html.Tr([html.Td("Hit 1% (from level)", style=td_style), html.Td(fmt_stat(hit_1_cnt, total_tasks), style=td_style)]),
        html.Tr([html.Td("Hit 1.5% (from level)", style=td_style), html.Td(fmt_stat(hit_1_5_cnt, total_tasks), style=td_style)]),
        html.Tr([html.Td("Hit 2% (from level)", style=td_style), html.Td(fmt_stat(hit_2_cnt, total_tasks), style=td_style)]),
        # Max Adverse (lvl) Rows
        html.Tr([html.Td("Max Adv 0-4% (lvl)", style=td_style), html.Td(row1_adv, style=td_style)]),
        html.Tr([html.Td("Max Adv 4%+ (lvl)", style=td_style), html.Td(row2_adv, style=td_style)]),
        html.Tr([html.Td("Max Adv 0.5%+ Total (lvl)", style=td_style), html.Td(str(adv_05_plus_total), style=td_style)]),
        html.Tr([html.Td("Max Adv 4%+ Total (lvl)", style=td_style), html.Td(str(adv_4_plus_total), style=td_style)]),
        # Max Expected (lvl) Rows
        html.Tr([html.Td("Max Exp 0-4% (lvl)", style=td_style), html.Td(row1_exp, style=td_style)]),
        html.Tr([html.Td("Max Exp 4%+ (lvl)", style=td_style), html.Td(row2_exp, style=td_style)]),
        html.Tr([html.Td("Max Exp 0.5%+ Total (lvl)", style=td_style), html.Td(str(exp_05_plus_total), style=td_style)]),
        html.Tr([html.Td("Max Exp 4%+ Total (lvl)", style=td_style), html.Td(str(exp_4_plus_total), style=td_style)]),
        # Max Adverse (sgnl) Rows
        html.Tr([html.Td("Max Adv 0-4% (sgnl)", style=td_style), html.Td(row1_adv_s, style=td_style)]),
        html.Tr([html.Td("Max Adv 4%+ (sgnl)", style=td_style), html.Td(row2_adv_s, style=td_style)]),
        html.Tr([html.Td("Max Adv 0.5%+ Total (sgnl)", style=td_style), html.Td(str(adv_sgnl_05), style=td_style)]),
        html.Tr([html.Td("Max Adv 4%+ Total (sgnl)", style=td_style), html.Td(str(adv_sgnl_4), style=td_style)]),
        # Max Expected (sgnl) Rows
        html.Tr([html.Td("Max Exp 0-4% (sgnl)", style=td_style), html.Td(row1_exp_s, style=td_style)]),
        html.Tr([html.Td("Max Exp 4%+ (sgnl)", style=td_style), html.Td(row2_exp_s, style=td_style)]),
        html.Tr([html.Td("Max Exp 0.5%+ Total (sgnl)", style=td_style), html.Td(str(exp_sgnl_05), style=td_style)]),
        html.Tr([html.Td("Max Exp 4%+ Total (sgnl)", style=td_style), html.Td(str(exp_sgnl_4), style=td_style)]),
        # Delta Price Rows
        html.Tr([html.Td("Delta Price 0-4%", style=td_style), html.Td(row1_delta, style=td_style)]),
        html.Tr([html.Td("Delta Price 4%+", style=td_style), html.Td(row2_delta, style=td_style)]),
        html.Tr([html.Td("Delta Price 0.5%+ Total", style=td_style), html.Td(str(delta_05_plus_total), style=td_style)]),
        html.Tr([html.Td("Delta Price 4%+ Total", style=td_style), html.Td(str(delta_4_plus_total), style=td_style)]),
    ]
    return html.Table([html.Tbody(signal_stats_rows)], style={"border": "1px solid #4a90e2", "padding": "5px", "marginTop": "10px", "backgroundColor": "#f0f7ff"})


# 🔧 REMOVED DUPLICATE: This was a duplicate function definition without @app.callback decorator
# The actual callback is defined at line 3695 with the proper @app.callback decorator
# def update_task_table_only(current_page, version, lock_state, analysis_trigger):
#     \"\"\"Render task table ONLY. Uses aggressive caching to skip HTML generation on page changes.\"\"\"
#     global golden_task_store_data, golden_store_version, _page_html_cache, _cached_golden_version, cached_signal_stats_html, cached_small_stats_data, stats_cache_version


    
    # Initialize timer for full trace
    timer = PerfTimer(f"Page {current_page} Render (v{version})").start()
    
    # Validate global state
    if not hasattr(app, 'layout') or app.layout is None:
        timer.check("Validation Failed").end()
        return html.Div("", style={"display": "none"})
    
    # Get triggered input
    ctx = dash.callback_context
    if not ctx.triggered:
        timer.check("No Trigger").end()
        return dash.no_update
        
    triggered_id = ctx.triggered[0]['prop_id'].split('.')[0]
    print(f"[DEBUG] 🔍 TRIGGER: {triggered_id} | version={version} | page={current_page}")
    timer.check(f"Trigger Detected: {triggered_id}")
    
    # If only lock changed, don't re-render table
    if triggered_id == "recalc-lock-store" and version == getattr(update_task_table_only, '_last_version', None):
        print(f"[TRACE] Skipping render - lock change only")
        timer.check("Lock Skip").end()
        return dash.no_update
    
    update_task_table_only._last_version = version
    print(f"[DEBUG] 📊 STATE: golden_store_version={golden_store_version}, cache_size={len(_page_html_cache)}")
    
    # Lock check
    if lock_state and lock_state.get("locked", False):
        timer.check("Lock Active").end()
        return html.Div("⏳ Recalculating... Please wait", style={"textAlign": "center", "padding": "20px", "fontSize": "16px", "color": "#666"})
    
    # Get tasks from Golden Store
    t0 = time.time()
    if golden_task_store_data is not None and len(golden_task_store_data) > 0:
        tasks = golden_task_store_data
        print(f"[TRACE] ✓ Loaded {len(tasks)} tasks from golden store")
    else:
        with tm.lock:
            tasks = list(tm.tasks.values())
        print(f"[TRACE] ✓ Loaded {len(tasks)} tasks from task_manager")
    timer.check(f"Step 1: Get Data ({len(tasks)} tasks)")
    
    if not tasks:
        print("[TRACE] ✗ No tasks found")
        timer.end()
        return "No tasks."
    
    # CRITICAL CACHE CHECK
    current_golden_version = golden_store_version
    print(f"[TRACE] Version check: cached={_cached_golden_version}, current={current_golden_version}")
    
    # Invalidate cache if data changed
    if _cached_golden_version != current_golden_version:
        print(f"[TRACE] 🔄 Cache invalidated: {_cached_golden_version} -> {current_golden_version}")
        _page_html_cache.clear()
        _cached_golden_version = current_golden_version
        timer.check("Cache Invalidated")
    
    # ⚡ CRITICAL FIX: Cache MUST use version in key to avoid stale data
    cache_key = f"page_{current_page}_v{current_golden_version}"
    
    # Return cached page if available (INSTANT - no HTML generation)
    if cache_key in _page_html_cache:
        print(f"[TRACE] ⚡ CACHE HIT for key '{cache_key}'! Returning cached page {current_page}")
        timer.check("Cache Hit").end()
        return _page_html_cache[cache_key]
    
    print(f"[TRACE] ❌ CACHE MISS for key '{cache_key}'. Will generate rows.")
    timer.check("Cache Miss Confirmed")
    
    force_refresh = version is not None and version > 0
    
    # Pagination Slicing
    PAGE_SIZE = 300
    total_pages = max(1, (len(tasks) + PAGE_SIZE - 1) // PAGE_SIZE)
    current_page = max(0, min(current_page or 0, total_pages - 1))
    start_idx = current_page * PAGE_SIZE
    end_idx = start_idx + PAGE_SIZE
    visible_tasks = tasks[start_idx:end_idx]
    print(f"[TRACE] ✂️ Sliced tasks [{start_idx}:{end_idx}] → {len(visible_tasks)} visible")
    timer.check(f"Step 2: Pagination Slice")
    
    # Detect if this is ONLY a page navigation (no data change)
    prev_golden_version = getattr(update_task_table_only, '_last_golden_version', None)
    is_page_only_nav = (triggered_id == "task-page-store") and (prev_golden_version is not None) and (current_golden_version == prev_golden_version)
    
    # 🔧 CRITICAL FIX: Also treat analysis_trigger as a data change (not page nav)
    # This ensures full stats are calculated after recalculation completes
    if triggered_id == "analysis-complete-trigger":
        is_page_only_nav = False
        print(f"[TRACE] 🔄 Analysis trigger detected - forcing full stats recalculation")
    
    print(f"[TRACE] Navigation detection: triggered={triggered_id}, prev_ver={prev_golden_version}, curr_ver={current_golden_version} → is_page_only_nav={is_page_only_nav}")
    timer.check("Navigation Detection")
    
    # Store current state for next comparison
    update_task_table_only._last_golden_version = current_golden_version
    update_task_table_only._last_page = current_page
    
    timer.check("Step 3: Helper Functions Setup")
    
    # Generate rows for visible tasks ONLY (300 max) using extracted UI function
    print(f"[TRACE] 🚀 Starting row generation for {len(visible_tasks)} tasks...")
    t_row_start = time.time()
    rows = [render_task_table_row(t) for t in visible_tasks]
    row_count = len(rows)
    
    row_elapsed = time.time() - t_row_start
    print(f"[TRACE] ✓ Generated {row_count} rows in {row_elapsed:.2f}s ({row_elapsed/row_count*1000:.1f}ms per row)")
    timer.check(f"Step 4: Row Generation ({row_count} rows)")
    
    # Build table HTML using extracted UI function
    t_table_start = time.time()
    table = html.Table([
        render_task_table_header(),
        html.Tbody(rows)
    ], style={"width": "100%", "borderCollapse": "collapse"})
    print(f"[TRACE] ✓ Built table HTML in {time.time() - t_table_start:.2f}s")
    timer.check("Step 5: Build Table HTML")

    # ⚡ PERFORMANCE: Skip heavy stats calculation on page-only navigation
    # This is the CRITICAL FIX - stats are calculated ONLY when version changes (data reload/recalc)
    if is_page_only_nav:
        # Return minimal stats for page navigation (no heavy iteration over all tasks)
        # But we still need to show basic stats from ALL tasks (consistent across pages)
        total_tasks = len(tasks)
        completed_count = sum(1 for t in tasks if t.status == "completed")
        
        # ALL-task averages (still fast - just iterating, not generating HTML)
        avg_adv = np.mean([t.max_adverse_move_pct for t in tasks if t.max_adverse_move_pct is not None and not is_na(t.max_adverse_move_pct)] or [0])
        avg_dd = np.mean([t.drawdown_before_level for t in tasks if t.drawdown_before_level is not None and not is_na(t.drawdown_before_level)] or [0])
        
        stats_rows = [
            html.Tr([html.Td("✅ Task Completed (Total)"), html.Td(str(completed_count))]),
            html.Tr([html.Td("📦 Total Tasks"), html.Td(str(total_tasks))]),
            html.Tr([html.Td("📉 Avg Max Adverse (All)"), html.Td(fmt_dd_ui(avg_adv))]),
            html.Tr([html.Td("📉 Avg Drawdown Lvl (All)"), html.Td(fmt_dd_ui(avg_dd))])
        ]
        stats_table = html.Table([html.Tbody(stats_rows)], style={"border": "1px solid #ccc", "padding": "5px", "fontSize": "13px", "backgroundColor": "#f9f9f9"})
        
        # 🔧 FIX: Use cached signal stats from ALL tasks (calculated once per version)
        print(f"[DEBUG] ⏭️ USING CACHED SIGNAL STATS")
        stats_elapsed = 0.0
        # Access global cache (already declared at function level)
        signal_stats_table = cached_signal_stats_html if cached_signal_stats_html else html.Div("ℹ️ Stats loading...", style={"textAlign": "center", "padding": "10px", "color": "#555", "fontStyle": "italic"})
    else:
        # 🔧 CRITICAL: Calculate signal stats on ALL tasks when data loads/recalculates
        print(f"[DEBUG] 🚀 CALCULATING SIGNAL STATS for {len(tasks)} tasks...")
        
        t_stats_start = time.time()

        # ✅ BASIC STATS: Calculate only when data changes (not on page nav) - NOW USES ALL TASKS
        total_tasks = len(tasks)
        completed_count = sum(1 for t in tasks if t.status == "completed")

        # ALL-task averages (consistent across all pages)
        avg_adv = np.mean([t.max_adverse_move_pct for t in tasks if t.max_adverse_move_pct is not None and not is_na(t.max_adverse_move_pct)] or [0])
        avg_dd = np.mean([t.drawdown_before_level for t in tasks if t.drawdown_before_level is not None and not is_na(t.drawdown_before_level)] or [0])

        stats_rows = [
            html.Tr([html.Td("✅ Task Completed (Total)"), html.Td(str(completed_count))]),
            html.Tr([html.Td("📦 Total Tasks"), html.Td(str(total_tasks))]),
            html.Tr([html.Td("📉 Avg Max Adverse (All)"), html.Td(fmt_dd_ui(avg_adv))]),
            html.Tr([html.Td("📉 Avg Drawdown Lvl (All)"), html.Td(fmt_dd_ui(avg_dd))])
        ]
        stats_table = html.Table([html.Tbody(stats_rows)], style={"border": "1px solid #ccc", "padding": "5px", "fontSize": "13px", "backgroundColor": "#f9f9f9"})

        # ✅ SIGNAL STATS: Calculated on ALL in-memory tasks (consistent denominator)
        reached_level_cnt = sum(1 for t in tasks if t.reached_level)
        reversed_dir_cnt = sum(1 for t in tasks if t.reversed_direction)
        hit_1_cnt = sum(1 for t in tasks if t.reached_level and t.hit_1)
        hit_1_5_cnt = sum(1 for t in tasks if t.reached_level and t.hit_1_5)
        hit_2_cnt = sum(1 for t in tasks if t.reached_level and t.hit_2)
        
        def fmt_stat(stat_count, total):
            if total == 0: return "0 / 0 (0.0%)"
            return f"{stat_count} / {total} ({(stat_count/total)*100:.1f}%)"

        # ----- Max Adverse Distribution Stats (compact format) -----
        def get_adverse_range_ui(pct):
            if pct is None or (isinstance(pct, float) and is_na(pct)):
                return None
            if 0 <= pct < 0.5: return "0-0.5%"
            elif 0.5 <= pct < 1: return "0.5-1%"
            elif 1 <= pct < 2: return "1-2%"
            elif 2 <= pct < 3: return "2-3%"
            elif 3 <= pct < 4: return "3-4%"
            elif 4 <= pct < 5: return "4-5%"
            elif 5 <= pct < 10: return "5-10%"
            elif 10 <= pct < 20: return "10-20%"
            elif 20 <= pct < 30: return "20-30%"
            elif pct >= 30: return ">30%"
            return None

        # Count tasks in each adverse range (only for reached_level tasks)
        adverse_counts = {}
        for t in tasks:
            adv = t.max_adverse_move_pct
            if t.reached_level and adv is not None and not (isinstance(adv, float) and is_na(adv)):
                range_key = get_adverse_range_ui(adv)
                if range_key:
                    adverse_counts[range_key] = adverse_counts.get(range_key, 0) + 1

        # Format as two compact rows (5 ranges each) to save vertical space
        ranges = ["0-0.5%", "0.5-1%", "1-2%", "2-3%", "3-4%", "4-5%", "5-10%", "10-20%", "20-30%", ">30%"]
        row1_adv = " | ".join([f"{r}:{adverse_counts.get(r,0)}" for r in ranges[:5]])
        row2_adv = " | ".join([f"{r}:{adverse_counts.get(r,0)}" for r in ranges[5:]])

        # 🔧 Calculate cumulative totals for Max Adverse
        adv_05_plus_total = 0
        adv_4_plus_total = 0
        for t in tasks:
            adv = t.max_adverse_move_pct
            if t.reached_level and adv is not None and not (isinstance(adv, float) and is_na(adv)):
                if adv >= 0.5:
                    adv_05_plus_total += 1
                if adv >= 4.0:
                    adv_4_plus_total += 1

        # 🔧 NEW: Calculate distribution & cumulative totals for Max Expected
        exp_counts = {}
        exp_05_plus_total = 0
        exp_4_plus_total = 0
        for t in tasks:
            exp = t.max_expected_move_pct
            if t.reached_level and exp is not None and not (isinstance(exp, float) and is_na(exp)):
                range_key = get_adverse_range_ui(exp)
                if range_key:
                    exp_counts[range_key] = exp_counts.get(range_key, 0) + 1
                if exp >= 0.5:
                    exp_05_plus_total += 1
                if exp >= 4.0:
                    exp_4_plus_total += 1
                
        row1_exp = " | ".join([f"{r}:{exp_counts.get(r,0)}" for r in ranges[:5]])
        row2_exp = " | ".join([f"{r}:{exp_counts.get(r,0)}" for r in ranges[5:]])

        # Define uniform style for all cells in the summary table
        td_style = {"fontSize": "13px", "fontWeight": "normal", "padding": "2px 5px"}
        
        # Calculate (sgnl) statistics for Adverse & Expected - OPTIMIZED with direct attribute access
        adv_sgnl_counts = {}; exp_sgnl_counts = {}
        adv_sgnl_05 = 0; adv_sgnl_4 = 0; exp_sgnl_05 = 0; exp_sgnl_4 = 0
        for t in tasks:
            adv_s = t.max_adverse_sgnl_pct
            if adv_s is not None and not (isinstance(adv_s, float) and is_na(adv_s)):
                r = get_adverse_range_ui(adv_s)
                if r: adv_sgnl_counts[r] = adv_sgnl_counts.get(r, 0) + 1
                if adv_s >= 0.5: adv_sgnl_05 += 1
                if adv_s >= 4.0: adv_sgnl_4 += 1
            exp_s = t.max_expected_sgnl_pct
            if exp_s is not None and not (isinstance(exp_s, float) and is_na(exp_s)):
                r = get_adverse_range_ui(exp_s)
                if r: exp_sgnl_counts[r] = exp_sgnl_counts.get(r, 0) + 1
                if exp_s >= 0.5: exp_sgnl_05 += 1
                if exp_s >= 4.0: exp_sgnl_4 += 1
                
        row1_adv_s = " | ".join([f"{r}:{adv_sgnl_counts.get(r,0)}" for r in ranges[:5]])
        row2_adv_s = " | ".join([f"{r}:{adv_sgnl_counts.get(r,0)}" for r in ranges[5:]])
        row1_exp_s = " | ".join([f"{r}:{exp_sgnl_counts.get(r,0)}" for r in ranges[:5]])
        row2_exp_s = " | ".join([f"{r}:{exp_sgnl_counts.get(r,0)}" for r in ranges[5:]])
        
        # Delta Price (sgnl to lvl) Distribution
        delta_counts = {k: 0 for k in ranges}
        delta_05_plus_total = 0
        delta_4_plus_total = 0
        for t in tasks:
            dp = t.price_change_pct
            if dp is not None and not (isinstance(dp, float) and is_na(dp)):
                val = abs(dp)
                r = get_adverse_range_ui(val)
                if r:
                    delta_counts[r] += 1
                if val >= 0.5: delta_05_plus_total += 1
                if val >= 4.0: delta_4_plus_total += 1

        row1_delta = " | ".join([f"{r}:{delta_counts[r]}" for r in ranges[:5]])
        row2_delta = " | ".join([f"{r}:{delta_counts[r]}" for r in ranges[5:]])

        signal_stats_rows = [
            html.Tr([html.Td("Reached Level", style=td_style), html.Td(fmt_stat(reached_level_cnt, total_tasks), style=td_style)]),
            html.Tr([html.Td("Reversed Direction", style=td_style), html.Td(fmt_stat(reversed_dir_cnt, total_tasks), style=td_style)]),
            html.Tr([html.Td("Hit 1% (from level)", style=td_style), html.Td(fmt_stat(hit_1_cnt, total_tasks), style=td_style)]),
            html.Tr([html.Td("Hit 1.5% (from level)", style=td_style), html.Td(fmt_stat(hit_1_5_cnt, total_tasks), style=td_style)]),
            html.Tr([html.Td("Hit 2% (from level)", style=td_style), html.Td(fmt_stat(hit_2_cnt, total_tasks), style=td_style)]),
            # Max Adverse (lvl) Rows
            html.Tr([html.Td("Max Adv 0-4% (lvl)", style=td_style), html.Td(row1_adv, style=td_style)]),
            html.Tr([html.Td("Max Adv 4%+ (lvl)", style=td_style), html.Td(row2_adv, style=td_style)]),
            html.Tr([html.Td("Max Adv 0.5%+ Total (lvl)", style=td_style), html.Td(str(adv_05_plus_total), style=td_style)]),
            html.Tr([html.Td("Max Adv 4%+ Total (lvl)", style=td_style), html.Td(str(adv_4_plus_total), style=td_style)]),
            # Max Expected (lvl) Rows
            html.Tr([html.Td("Max Exp 0-4% (lvl)", style=td_style), html.Td(row1_exp, style=td_style)]),
            html.Tr([html.Td("Max Exp 4%+ (lvl)", style=td_style), html.Td(row2_exp, style=td_style)]),
            html.Tr([html.Td("Max Exp 0.5%+ Total (lvl)", style=td_style), html.Td(str(exp_05_plus_total), style=td_style)]),
            html.Tr([html.Td("Max Exp 4%+ Total (lvl)", style=td_style), html.Td(str(exp_4_plus_total), style=td_style)]),
            # Max Adverse (sgnl) Rows
            html.Tr([html.Td("Max Adv 0-4% (sgnl)", style=td_style), html.Td(row1_adv_s, style=td_style)]),
            html.Tr([html.Td("Max Adv 4%+ (sgnl)", style=td_style), html.Td(row2_adv_s, style=td_style)]),
            html.Tr([html.Td("Max Adv 0.5%+ Total (sgnl)", style=td_style), html.Td(str(adv_sgnl_05), style=td_style)]),
            html.Tr([html.Td("Max Adv 4%+ Total (sgnl)", style=td_style), html.Td(str(adv_sgnl_4), style=td_style)]),
            # Max Expected (sgnl) Rows
            html.Tr([html.Td("Max Exp 0-4% (sgnl)", style=td_style), html.Td(row1_exp_s, style=td_style)]),
            html.Tr([html.Td("Max Exp 4%+ (sgnl)", style=td_style), html.Td(row2_exp_s, style=td_style)]),
            html.Tr([html.Td("Max Exp 0.5%+ Total (sgnl)", style=td_style), html.Td(str(exp_sgnl_05), style=td_style)]),
            html.Tr([html.Td("Max Exp 4%+ Total (sgnl)", style=td_style), html.Td(str(exp_sgnl_4), style=td_style)]),
            # Delta Price Rows
            html.Tr([html.Td("Delta Price 0-4%", style=td_style), html.Td(row1_delta, style=td_style)]),
            html.Tr([html.Td("Delta Price 4%+", style=td_style), html.Td(row2_delta, style=td_style)]),
            html.Tr([html.Td("Delta Price 0.5%+ Total", style=td_style), html.Td(str(delta_05_plus_total), style=td_style)]),
            html.Tr([html.Td("Delta Price 4%+ Total", style=td_style), html.Td(str(delta_4_plus_total), style=td_style)]),
        ]
        signal_stats_table = html.Table([html.Tbody(signal_stats_rows)], style={"border": "1px solid #4a90e2", "padding": "5px", "marginTop": "10px", "backgroundColor": "#f0f7ff"})
        
        # Cache the stats for ALL tasks (calculated once per version)
        cached_signal_stats_html = signal_stats_table
        cached_small_stats_data = {"completed": completed_count, "total": total_tasks, "avg_adv": avg_adv, "avg_dd": avg_dd}
        stats_cache_version = golden_store_version
        
        stats_elapsed = time.time() - t_stats_start
        print(f"[DEBUG] ✅ SIGNAL STATS COMPLETE in {stats_elapsed:.2f}s (cached for version {stats_cache_version})")
    
    # 🔧 PAGINATION NAVIGATION
    nav_buttons = []
    nav_buttons.append(html.Button("<< Prev", id={"type":"page-nav","index":"prev"}, disabled=(current_page==0), style={"margin":"2px"}))
    for p in range(total_pages):
        btn_style = {"margin":"2px", "padding":"2px 6px", "fontWeight":"bold" if p==current_page else "normal"}
        nav_buttons.append(html.Button(str(p+1), id={"type":"page-nav","index":p}, style=btn_style))
    nav_buttons.append(html.Button("Next >>", id={"type":"page-nav","index":"next"}, disabled=(current_page==total_pages-1), style={"margin":"2px"}))
    nav_container = html.Div(nav_buttons, style={"display":"flex", "alignItems":"center", "marginBottom":"8px", "justifyContent":"center"})
    timer.check("Step 7: Build Pagination Nav")

    result = html.Div([
        html.H4("Task Summary"),
        nav_container,
        dcc.Markdown(table_html, dangerously_allow_html=True, style={"overflow-x": "auto", "overflow-y": "auto", "max-height": "75vh", "width": "100%"}),
        html.P(f"📄 Page {current_page+1} of {total_pages} | Showing tasks {start_idx+1}-{min(end_idx, len(tasks))} of {len(tasks)}", style={"textAlign":"center", "fontSize":"12px", "color":"#555"}),
        stats_table,
        html.H5("Signal Performance Summary", style={"marginTop": "15px", "marginBottom": "5px"}),
        signal_stats_table,
        html.P(
            "ℹ️ Hit % metrics measure price movement ≥1%/1.5%/2% **in the EXPECTED direction** from the signal level base. "
            "Resistance: Price moves UP ≥X% from level. Support: Price moves DOWN ≥X% from level. "
            "Hits are only counted if the price actually touched the level first.",
            style={"fontSize": "11px", "color": "#777", "marginTop": "6px", "marginBottom": "0", "fontStyle": "italic"}
        )
    ])
    timer.check("Step 8: Build Final Result Div")
    
    # ⚡ CACHE THE RESULT with version key for instant page switching (ALWAYS cache, regardless of stats)
    # The table HTML is the same whether we calculated full stats or page-only stats
    _page_html_cache[cache_key] = result
    timer.check("Step 9: Cache Result")
    
    # Print final timing
    timer.end()
    print(f"[TRACE] <<< COMPLETE Page {current_page} rendered in {timer.last_time - timer.start_time:.4f}s | Cache Size: {len(_page_html_cache)}")
    print(f"[TRACE] ✓✓✓ RETURNING RESULT TO DASH UI ✓✓✓")
    
    return result

@app.callback(
    Output("task-page-store", "data"),
    Input({"type": "page-nav", "index": ALL}, "n_clicks"),
    State("task-count-store", "data"),
    State("task-page-store", "data"),
    prevent_initial_call=True
)
def handle_page_nav(n_clicks_list, count, current_page):
    triggered = ctx.triggered_id
    if not triggered or not isinstance(triggered, dict):
        return current_page
    action = triggered.get("index")
    total_tasks = int(count) if count else len(tm.get_all_tasks())
    total_pages = max(1, (total_tasks + PAGE_SIZE - 1) // PAGE_SIZE)
    
    if action == "prev":
        return max(0, current_page - 1)
    elif action == "next":
        return min(total_pages - 1, current_page + 1)
    elif isinstance(action, int):
        return action
    return current_page

@app.callback(
    Output("progress-interval", "disabled"),
    Output("analysis-interval", "disabled"),  # 🔧 Enable analysis-interval during recalc
    Input("progress-interval", "n_intervals"),
    prevent_initial_call=True
)
def auto_throttle_updates(_):
    """Keep interval always enabled. 
    The 'update_summary' callback handles performance by returning 'no_update' 
    when the table hasn't actually changed."""
    return False, False  # 🔧 Keep both intervals enabled

# ----- NEW: Callback for chart button using data-action pattern -----
# This callback listens to the hidden trigger that JS sets when chart button is clicked
@app.callback(
    Output("chart-task-id", "data"),
    Output("chart-click-store", "data"),
    Input("chart-button-trigger", "data"),  # Hidden trigger set by JS
    State("chart-click-store", "data"),
    prevent_initial_call=True
)
def set_chart_task_id(trigger_data, click_store):
    if not trigger_data:
        return no_update, no_update
    
    task_id = trigger_data.get("task_id")
    action = trigger_data.get("action")
    
    if not task_id or action != "chart":
        return no_update, no_update
    
    # Deduplication logic
    key = f"{task_id}_chart"
    current_time = time.time()
    old_time = click_store.get(key, 0)
    
    # Only process if this is a new click (within 0.5 seconds)
    if current_time - old_time < 0.5:
        return no_update, no_update
    
    click_store[key] = current_time
    return task_id, click_store

# ----- Modal display callback -----
@app.callback(
    Output("chart-modal", "style"),
    Input("chart-task-id", "data"),
    Input("close-chart-modal", "n_clicks"),
    prevent_initial_call=True
)
def toggle_chart_modal(task_id, close_clicks):
    triggered = ctx.triggered_id
    if triggered == "close-chart-modal":
        return {"display": "none"}
    if task_id:
        return {"display": "flex"}
    return no_update

@app.callback(
    Output("rsi-visible-store", "data"),
    Input("toggle-rsi-btn", "n_clicks"),
    State("rsi-visible-store", "data"),
    prevent_initial_call=True
)
def toggle_rsi(n_clicks, current):
    return not current

@app.callback(
    Output("strategy-visible-store", "data"),
    Input("toggle-strategy-btn", "n_clicks"),
    State("strategy-visible-store", "data"),
    prevent_initial_call=True
)
def toggle_strategy(n_clicks, current):
    return not current

# ----- Measurement tool callbacks -----
@app.callback(
    Output("measure-mode-store", "data"),
    Input("toggle-measure-btn", "n_clicks"),
    State("measure-mode-store", "data"),
    prevent_initial_call=True
)
def toggle_measure(n_clicks, current):
    return not current

@app.callback(
    Output("measure-points-store", "data"),
    Output("measure-result-store", "data"),
    Input("task-chart", "clickData"),
    State("measure-mode-store", "data"),
    State("measure-points-store", "data"),
    prevent_initial_call=True
)
def capture_click(clickData, measure_mode, points):
    if not measure_mode or not clickData:
        return dash.no_update, dash.no_update
    try:
        x_val = clickData['points'][0]['x']
        y_val = clickData['points'][0]['y']
        if points['first'] is None:
            # First click
            return {"first": {"x": x_val, "y": y_val}, "second": None}, None
        else:
            # Second click
            first = points['first']
            second = {"x": x_val, "y": y_val}
            price_diff = second['y'] - first['y']
            pct_change = (price_diff / first['y']) * 100
            result = f"📏 Δ Price: {price_diff:+.4f} ({pct_change:+.2f}%)"
            return {"first": None, "second": None}, result
    except Exception:
        return dash.no_update, dash.no_update

@app.callback(
    Output("measure-points-store", "data", allow_duplicate=True),
    Output("measure-result-store", "data", allow_duplicate=True),
    Input("measure-mode-store", "data"),
    prevent_initial_call=True
)
def reset_measure_on_mode_exit(mode):
    if not mode:
        return {"first": None, "second": None}, None
    return dash.no_update, dash.no_update

@app.callback(
    Output("measure-result", "children"),
    Input("measure-result-store", "data"),
    prevent_initial_call=True
)
def show_measure_result(result):
    if result:
        return result
    return ""

@app.callback(
    Output("measure-hint", "children"),
    Input("measure-mode-store", "data"),
    prevent_initial_call=True
)
def measure_hint(active):
    if active:
        return "📏 Measure mode active: click two points on the chart to measure price difference."
    return ""

# ----- Strategy details modal callbacks (using data-action pattern) -----
@app.callback(
    Output("strategy-details-task-id", "data"),
    Output("details-click-store", "data"),
    Input("strategy-details-trigger", "data"),  # Hidden trigger set by JS
    State("details-click-store", "data"),
    prevent_initial_call=True
)
def set_strategy_details_task_id(trigger_data, click_store):
    if not trigger_data:
        return no_update, no_update
    
    task_id = trigger_data.get("task_id")
    if not task_id:
        return no_update, no_update
    
    # Deduplication logic
    key = f"{task_id}_details"
    current_time = time.time()
    old_time = click_store.get(key, 0)
    
    if current_time - old_time < 0.5:
        return no_update, no_update
    
    click_store[key] = current_time
    return task_id, click_store

@app.callback(
    Output("strategy-details-modal", "style"),
    Output("strategy-details-title", "children"),
    Output("strategy-details-content", "children"),
    Input("strategy-details-task-id", "data"),
    Input("close-strategy-details-modal", "n_clicks"),
    prevent_initial_call=True
)
def toggle_strategy_details_modal(task_id, close_clicks):
    triggered = ctx.triggered_id
    if triggered == "close-strategy-details-modal":
        return {"display": "none"}, "", ""
    if task_id is None:
        return no_update, no_update, no_update
    task = tm.get_task(task_id)
    if not task or not task.strategy_signals:
        return {"display": "flex"}, f"Task {task_id[:8]} – No strategy signals", html.P("No strategy signals for this task.")
    # Build table of signals with entry/exit prices and times
    rows = []
    for sig in task.strategy_signals:
        entry_time = pd.to_datetime(sig['entry_time_ms'], unit='ms', utc=True).strftime("%Y-%m-%d %H:%M")
        exit_time = pd.to_datetime(sig['exit_time_ms'], unit='ms', utc=True).strftime("%Y-%m-%d %H:%M") if sig.get('exit_time_ms') else "-"
        pnl = sig.get('delta_pct')
        if pnl is None:
            pnl = 0.0
        pnl_color = "green" if pnl > 0 else "red" if pnl < 0 else "white"
        rows.append(html.Tr([
            html.Td(entry_time),
            html.Td(sig['type'].capitalize()),
            html.Td(sig['direction'].upper()),
            html.Td(f"{sig['entry_price']:.4f}"),
            html.Td(f"{sig['exit_price']:.4f}") if sig.get('exit_price') is not None else html.Td("-"),
            html.Td(exit_time),
            html.Td(f"{sig['confidence']:.0f}%"),
            html.Td(f"{pnl:+.2f}%", style={"color": pnl_color}),
            html.Td(sig.get('extra_info', '-'), style={"maxWidth": "200px", "fontSize": "12px"})  # new column
        ]))
    table = html.Table([
        html.Thead(html.Tr([
            html.Th("Entry Time (UTC)"), html.Th("Type"), html.Th("Dir"),
            html.Th("Entry Price"), html.Th("Exit Price"), html.Th("Exit Time (UTC)"),
            html.Th("Confidence"), html.Th("P&L %"), html.Th("Reason / Parameters")
        ])),
        html.Tbody(rows)
    ], style={"width": "100%", "border": "1px solid gray", "borderCollapse": "collapse"})
    # Win rates per strategy type
    from collections import defaultdict
    stats = defaultdict(lambda: {"total": 0, "win": 0})
    for sig in task.strategy_signals:
        t = sig['type']
        stats[t]["total"] += 1
        delta = sig.get('delta_pct')
        if delta is not None and delta > 0:
            stats[t]["win"] += 1
    stats_rows = []
    for t, data in stats.items():
        win_rate = (data["win"] / data["total"] * 100) if data["total"] > 0 else 0
        stats_rows.append(html.Tr([
            html.Td(t.capitalize()),
            html.Td(data["total"]),
            html.Td(data["win"]),
            html.Td(f"{win_rate:.1f}%")
        ]))
    stats_table = html.Table([
        html.Thead(html.Tr([html.Th("Strategy"), html.Th("Total"), html.Th("Wins"), html.Th("Win Rate")])),
        html.Tbody(stats_rows)
    ], style={"width": "50%", "border": "1px solid gray", "borderCollapse": "collapse", "marginTop": "10px"})
    content = html.Div([html.Div(table, style={"overflow-x": "auto"}), stats_table])
    title = f"Strategy Signals – {task.symbols[0]} ({task.timeframe})"
    return {"display": "flex"}, title, content

# ----- Chart figure callback (light theme) -----
@app.callback(
    Output("task-chart", "figure"),
    Input("chart-task-id", "data"),
    Input("rsi-visible-store", "data"),
    Input("strategy-visible-store", "data"),
    Input("impulse-visible-store", "data"),
    Input("events-visible-store", "data"),
    prevent_initial_call=True
)
def update_task_chart(task_id, rsi_visible, strategy_visible, impulse_visible, events_visible):
    if not task_id:
        return go.Figure()
    task = tm.get_task(task_id)
    if not task or not task.signal_time:
        return go.Figure()
    # Load data
    sym = task.symbols[0]
    path = symbol_timeframe_path(sym, task.timeframe)
    fp = os.path.join(path, "data.parquet")
    if not os.path.exists(fp):
        return go.Figure()
    df = pd.read_parquet(fp)
    if df.empty:
        return go.Figure()
    # Filter period
    start_ms = int(task.start_date.replace(tzinfo=timezone.utc).timestamp() * 1000) if task.start_date else 0
    end_ms = int(task.end_date.replace(tzinfo=timezone.utc).timestamp() * 1000) if task.end_date else df['timestamp'].max()
    df = df[(df['timestamp'] >= start_ms) & (df['timestamp'] <= end_ms)].copy()
    if df.empty:
        return go.Figure()
    # UTC datetime conversion
    def ms_to_utc_datetime(ms):
        return datetime.fromtimestamp(ms / 1000.0, tz=timezone.utc)
    df['x'] = df['timestamp'].apply(ms_to_utc_datetime)
    signal_dt = ms_to_utc_datetime(task.signal_time)
    # RSI calculation
    def compute_rsi(series, period=14):
        delta = series.diff()
        gain = delta.clip(lower=0)
        loss = -delta.clip(upper=0)
        avg_gain = gain.rolling(window=period, min_periods=period).mean()
        avg_loss = loss.rolling(window=period, min_periods=period).mean()
        rs = avg_gain / avg_loss
        rsi = 100 - (100 / (1 + rs))
        return rsi
    # Low-spec chart cache: compute RSI once per period view
    cache_key = (start_ms, end_ms)
    if cache_key not in task._chart_cache:
        df['rsi'] = compute_rsi(df['close'])
        task._chart_cache.clear()  # Keep only 1 view in RAM
        task._chart_cache[cache_key] = df.copy()
    else:
        df = task._chart_cache[cache_key]
    # Create figure
    if rsi_visible:
        fig = make_subplots(rows=2, cols=1, shared_xaxes=True,
                            vertical_spacing=0.05, row_heights=[0.7, 0.3])
        # Candlestick
        fig.add_trace(go.Candlestick(
            x=df['x'], open=df['open'], high=df['high'],
            low=df['low'], close=df['close'], name="OHLC",
            increasing_line_color='#26a69a', decreasing_line_color='#ef5350'
        ), row=1, col=1)
        # RSI line
        fig.add_trace(go.Scatter(
            x=df['x'], y=df['rsi'], mode='lines', name='RSI (14)',
            line=dict(color='purple', width=1.5), connectgaps=True
        ), row=2, col=1)
        # Helper trace on RSI (ensures hover line works – kept for consistency)
        fig.add_trace(go.Scatter(
            x=df['x'], y=[50]*len(df), mode='lines',
            name='_spike_helper_rsi', showlegend=False, hoverinfo='skip',
            line=dict(width=1, color='rgba(0,0,0,0.01)')
        ), row=2, col=1)
        # RSI levels
        fig.add_hline(y=70, line_dash="dash", line_color="red", row=2, col=1)
        fig.add_hline(y=30, line_dash="dash", line_color="green", row=2, col=1)
        fig.update_yaxes(title_text="RSI", row=2, col=1, range=[0, 100])
    else:
        fig = make_subplots(rows=1, cols=1, shared_xaxes=True)
        fig.add_trace(go.Candlestick(
            x=df['x'], open=df['open'], high=df['high'],
            low=df['low'], close=df['close'], name="OHLC",
            increasing_line_color='#26a69a', decreasing_line_color='#ef5350'
        ))
        # Helper trace on main chart (ensures hover line works – kept)
        y_mid = (df['high'].max() + df['low'].min()) / 2
        fig.add_trace(go.Scatter(
            x=df['x'], y=[y_mid]*len(df), mode='lines',
            name='_spike_helper_main', showlegend=False, hoverinfo='skip',
            line=dict(width=1, color='rgba(0,0,0,0.01)')
        ), row=1, col=1)
    # Signal level
    signal_price = task.signal_price
    fig.add_hline(y=signal_price, line_dash="dash", line_color="yellow",
                  annotation_text="Signal Level", annotation_position="top right",
                  row=1, col=1)
    # Event markers (only if toggled on)
    if events_visible and hasattr(task, 'events') and task.events:
        for ev in task.events:
            ts = ev['timestamp']
            event_dt = ms_to_utc_datetime(ts)
            event_type = ev['type']
            color = 'magenta' if 'pin' in event_type else \
                'cyan' if 'touch' in event_type else \
                'orange' if 'bounce' in event_type else \
                'red' if 'breakthrough' in event_type else 'white'
            fig.add_trace(go.Scatter(
                x=[event_dt], y=[ev.get('close', signal_price)],
                mode='markers', marker=dict(size=10, color=color),
                name=event_type, showlegend=False
            ), row=1, col=1)
    # Y-range for main chart (with padding)
    y_min = df['low'].min()
    y_max = df['high'].max()
    y_padding = (y_max - y_min) * 0.05
    y_min -= y_padding
    y_max += y_padding
    # Signal vertical line (fixed white dashed line at signal time)
    fig.add_trace(go.Scatter(
        x=[signal_dt, signal_dt], y=[y_min, y_max],
        mode='lines', line=dict(dash='dash', color='white', width=1),
        name='Signal Time', showlegend=False
    ), row=1, col=1)
    # Signal diamond marker
    fig.add_trace(go.Scatter(
        x=[signal_dt], y=[task.signal_price],
        mode='markers',
        marker=dict(size=10, color='white', symbol='diamond', line=dict(width=1, color='yellow')),
        name='Signal Time Marker', showlegend=False
    ), row=1, col=1)
    # ----- Strategy markers (separate: impulse vs other) -----
    if hasattr(task, 'strategy_signals') and task.strategy_signals:
        # Non‑impulse signals (bounce, retest, momentum) – only if strategy_visible is True
        if strategy_visible:
            for sig in task.strategy_signals:
                if sig['type'] == 'impulse':
                    continue
                sig_time = ms_to_utc_datetime(sig['entry_time_ms'])
                if sig['direction'] == 'buy':
                    marker = dict(symbol='triangle-up', size=12, color='lime')
                else:
                    marker = dict(symbol='triangle-down', size=12, color='red')
                fig.add_trace(go.Scatter(
                    x=[sig_time], y=[sig['entry_price']],
                    mode='markers', marker=marker,
                    name=f"{sig['type']} {sig['direction']}",
                    showlegend=False
                ), row=1, col=1)
        # Impulse signals – only if impulse_visible is True
        if impulse_visible:
            for sig in task.strategy_signals:
                if sig['type'] != 'impulse':
                    continue
                sig_time = ms_to_utc_datetime(sig['entry_time_ms'])
                marker = dict(symbol='diamond', size=14, color='purple')
                fig.add_trace(go.Scatter(
                    x=[sig_time], y=[sig['entry_price']],
                    mode='markers', marker=marker,
                    name=f"Impulse {sig['direction']}",
                    showlegend=False,
                    text=sig.get('extra_info', ''),
                    hoverinfo='text+y'
                ), row=1, col=1)
    # Layout (light theme)
    fig.update_layout(
        title=f"{sym} – {task.timeframe}  (Signal at {pd.to_datetime(task.signal_time, unit='ms')})",
        xaxis_rangeslider_visible=False,
        template="plotly_white",
        hovermode="x unified",
        height=700 if rsi_visible else 500,
        margin=dict(l=50, r=50, t=50, b=50)
    )
    # X-axis tick format
    fig.update_xaxes(tickformat="%H:%M", ticklabelmode="period", ticks="outside")
    return fig

# =============================================================================
# NOTE: Database-related callbacks have been moved to database.py
# and are registered via register_database_callbacks(app) below.
# This includes: verification controls, chart updates, delete operations,
# download functions, and database maintenance callbacks.
# =============================================================================

# ----- Impulse callbacks -----
@app.callback(
    Output("impulse-task-selector", "options"),
    Input("progress-interval", "n_intervals")
)
def update_impulse_task_selector(_):
    tasks = tm.get_all_tasks()
    return [{"label": f"{t.task_id[:8]} - {t.symbols[0]} ({t.timeframe})", "value": t.task_id} for t in tasks if t.status == "completed"]

@app.callback(
    Output("impulse-apply-status", "children"),
    Input("apply-impulse-params", "n_clicks"),
    State("impulse-task-selector", "value"),
    State("impulse-range-mult", "value"),
    State("impulse-vol-mult", "value"),
    State("impulse-body-ratio", "value"),
    State("impulse-wick-ratio", "value"),
    State("impulse-next-confirm", "value"),
    State("impulse-rsi-divergence", "value"),
    State("impulse-rsi-extreme", "value"),
    State("impulse-base-candle", "value"),
    State("impulse-vol-accel", "value"),
    State("impulse-use-retracement", "value"),
    prevent_initial_call=True
)
def apply_impulse_params(n_clicks, task_id, range_mult, vol_mult, body_ratio, wick_ratio,
                         next_confirm, rsi_div, rsi_extreme, base_candle, vol_accel, use_retracement):
    if not task_id:
        return "No task selected."
    task = tm.get_task(task_id)
    if not task:
        return "Task not found."
    params = {
        'range_mult': range_mult,
        'vol_mult': vol_mult,
        'body_ratio': body_ratio,
        'wick_ratio': wick_ratio,
        'use_next_candle_confirmation': 'confirm' in next_confirm if next_confirm else False,
        'use_rsi_divergence': 'div' in rsi_div if rsi_div else False,
        'rsi_extreme': rsi_extreme,
        'use_base_candle': 'base' in base_candle if base_candle else False,
        'use_volume_acceleration': 'accel' in vol_accel if vol_accel else False,
    }
    try:
        from impulse import backtest_impulse, detect_impulse_retracement, set_impulse_params
        set_impulse_params(params)
        sym = task.symbols[0]
        path = symbol_timeframe_path(sym, task.timeframe)
        fp = os.path.join(path, "data.parquet")
        if not os.path.exists(fp):
            return "Data file not found."
        full_df = pd.read_parquet(fp)
        buffer_ms = task.pre_buffer_minutes * 60 * 1000
        start_ms = max(0, task.signal_time - buffer_ms)
        if task.start_date and task.end_date:
            window_len_ms = int(task.end_date.replace(tzinfo=timezone.utc).timestamp() * 1000) - int(task.start_date.replace(tzinfo=timezone.utc).timestamp() * 1000)
            cutoff_time = task.signal_time + window_len_ms
            df_limited = full_df[(full_df['timestamp'] >= start_ms) & (full_df['timestamp'] <= cutoff_time)].copy()
        else:
            df_limited = full_df[full_df['timestamp'] >= start_ms].copy()
        if df_limited.empty:
            return "No data in selected period."
        use_retrace = "retrace" in (use_retracement or [])
        if use_retrace:
            # Use the pre-buffer value stored in the task (from task creation)
            buf = getattr(task, 'pre_buffer_minutes', 120)
            trades = detect_impulse_retracement(
                df_limited, task.signal_price, task.signal_direction, task.signal_time,
                pre_buffer_minutes=buf, verbose=False
            )
        else:
            res = backtest_impulse(
                df_limited, task.signal_price, task.signal_direction, task.signal_time,
                params=params, verbose=False
            )
            trades = res['trades']
        task.strategy_signals = [s for s in task.strategy_signals if s.get('type') != 'impulse']
        for trade in trades:
            task.add_strategy_signal(
                'impulse', trade['direction'], trade['entry_price'], trade['entry_time_ms'],
                exit_price=trade['exit_price'], exit_time_ms=trade['exit_time_ms'],
                confidence=trade.get('confidence', 60),
                extra_info=trade.get('parameters_log', trade.get('extra_info', ''))
            )
        task.add_log(f"Impulse detection completed: {len(trades)} signals (retracement={use_retrace})")
        return f"Applied. Impulse signals: {len(trades)} (retracement={use_retrace})"
    except Exception as e:
        return f"Error: {str(e)}"

@app.callback(
    Output("impulse-apply-all-status", "children"),
    Input("apply-impulse-all", "n_clicks"),
    State("impulse-range-mult", "value"),
    State("impulse-vol-mult", "value"),
    State("impulse-body-ratio", "value"),
    State("impulse-wick-ratio", "value"),
    State("impulse-next-confirm", "value"),
    State("impulse-rsi-divergence", "value"),
    State("impulse-rsi-extreme", "value"),
    State("impulse-base-candle", "value"),
    State("impulse-vol-accel", "value"),
    prevent_initial_call=True
)
def apply_impulse_to_all(n_clicks, range_mult, vol_mult, body_ratio, wick_ratio,
                         next_confirm, rsi_div, rsi_extreme, base_candle, vol_accel):
    if n_clicks == 0:
        return ""
    params = {
        'range_mult': range_mult,
        'vol_mult': vol_mult,
        'body_ratio': body_ratio,
        'wick_ratio': wick_ratio,
        'use_next_candle_confirmation': 'confirm' in next_confirm if next_confirm else False,
        'use_rsi_divergence': 'div' in rsi_div if rsi_div else False,
        'rsi_extreme': rsi_extreme,
        'use_base_candle': 'base' in base_candle if base_candle else False,
        'use_volume_acceleration': 'accel' in vol_accel if vol_accel else False,
    }
    tasks = tm.get_all_tasks()
    completed = [t for t in tasks if t.status == "completed"]
    if not completed:
        return "No completed tasks."
    success = 0
    total_impulse = 0
    for task in completed:
        try:
            cnt = task.run_impulse_detection(params=params, verbose=False)
            total_impulse += cnt
            success += 1
        except Exception as e:
            task.add_log(f"Impulse batch error: {e}")
    return f"Applied to {success} tasks. Total impulse signals: {total_impulse}"

@app.callback(
    Output("impulse-details-modal", "style"),
    Output("impulse-details-title", "children"),
    Output("impulse-details-content", "children"),
    Input({"type": "impulse-details-btn", "index": ALL}, "n_clicks"),
    State("details-click-store", "data"),
    prevent_initial_call=True
)
def show_impulse_details(n_clicks_list, click_store):
    triggered = ctx.triggered_id
    if not triggered or not isinstance(triggered, dict):
        return no_update, no_update, no_update
    task_id = triggered.get("index")
    trig = ctx.triggered[0]
    new_clicks = trig.get('value', 0) or 0
    key = f"{task_id}_impulse"
    old_clicks = click_store.get(key, 0)
    if new_clicks <= old_clicks:
        return no_update, no_update, no_update
    click_store[key] = new_clicks
    task = tm.get_task(task_id)
    if not task or not task.strategy_signals:
        return {"display": "flex"}, f"Task {task_id[:8]} – No impulse signals", html.P("No impulse signals for this task.")
    impulse_signals = [s for s in task.strategy_signals if s['type'] == 'impulse']
    if not impulse_signals:
        return {"display": "flex"}, f"Task {task_id[:8]} – No impulse signals", html.P("No impulse signals.")
    rows = []
    for sig in impulse_signals:
        entry_time = pd.to_datetime(sig['entry_time_ms'], unit='ms').strftime("%Y-%m-%d %H:%M")
        exit_time = pd.to_datetime(sig['exit_time_ms'], unit='ms').strftime("%Y-%m-%d %H:%M") if sig.get('exit_time_ms') else "-"
        pnl = sig.get('delta_pct') if sig.get('delta_pct') is not None else 0.0
        pnl_color = "green" if pnl > 0 else "red" if pnl < 0 else "white"
        extra = sig.get('extra_info', '-')
        rows.append(html.Tr([
            html.Td(entry_time),
            html.Td(sig['direction'].upper()),
            html.Td(f"{sig['entry_price']:.5f}"),
            html.Td(f"{sig['exit_price']:.5f}") if sig.get('exit_price') is not None else html.Td("-"),
            html.Td(exit_time),
            html.Td(f"{sig['confidence']:.0f}%"),
            html.Td(f"{pnl:+.2f}%", style={"color": pnl_color}),
            html.Td(extra, style={"maxWidth": "250px", "fontSize": "12px"})
        ]))
    table = html.Table([
        html.Thead(html.Tr([
            html.Th("Entry Time"), html.Th("Dir"), html.Th("Entry Price"), html.Th("Exit Price"),
            html.Th("Exit Time"), html.Th("Confidence"), html.Th("P&L %"), html.Th("Parameters")
        ])),
        html.Tbody(rows)
    ], style={"width": "100%", "border": "1px solid gray", "borderCollapse": "collapse"})
    stats = {}
    for sig in impulse_signals:
        t = sig['type']
        stats.setdefault(t, {"total": 0, "win": 0})
        stats[t]["total"] += 1
        if sig.get('delta_pct', 0) > 0:
            stats[t]["win"] += 1
    stats_rows = []
    for t, data in stats.items():
        win_rate = (data["win"] / data["total"] * 100) if data["total"] > 0 else 0
        stats_rows.append(html.Tr([html.Td(t.capitalize()), html.Td(data["total"]), html.Td(data["win"]), html.Td(f"{win_rate:.1f}%")]))
    stats_table = html.Table([
        html.Thead(html.Tr([html.Th("Strategy"), html.Th("Total"), html.Th("Wins"), html.Th("Win Rate")])),
        html.Tbody(stats_rows)
    ], style={"width": "50%", "border": "1px solid gray", "borderCollapse": "collapse", "marginTop": "10px"})
    content = html.Div([table, stats_table])
    title = f"Impulse Signals – {task.symbols[0]} ({task.timeframe})"
    return {"display": "flex"}, title, content

@app.callback(
    Output("impulse-details-modal", "style", allow_duplicate=True),
    Input("close-impulse-details-modal", "n_clicks"),
    prevent_initial_call=True
)
def close_impulse_modal(n_clicks):
    return {"display": "none"}

@app.callback(
    Output("download-impulse-csv", "data"),
    Input("export-impulse-csv", "n_clicks"),
    State("impulse-details-title", "children"),
    prevent_initial_call=True
)
def export_impulse_csv(n_clicks, title):
    if not title:
        return None
    import re
    match = re.search(r"– (.+?) \(", title)
    if not match:
        return None
    sym = match.group(1).strip()
    tasks = tm.get_all_tasks()
    task = next((t for t in tasks if t.symbols[0] == sym), None)
    if not task:
        return None
    impulse_signals = [s for s in task.strategy_signals if s['type'] == 'impulse']
    if not impulse_signals:
        return None
    data = []
    for sig in impulse_signals:
        data.append({
            'Entry Time (UTC)': pd.to_datetime(sig['entry_time_ms'], unit='ms'),
            'Exit Time (UTC)': pd.to_datetime(sig['exit_time_ms'], unit='ms') if sig.get('exit_time_ms') else None,
            'Direction': sig['direction'],
            'Entry Price': sig['entry_price'],
            'Exit Price': sig.get('exit_price'),
            'Confidence': sig['confidence'],
            'P&L %': sig.get('delta_pct', 0),
            'Parameters': sig.get('extra_info', ''),
            'Exit Reason': sig.get('exit_reason', '')
        })
    df = pd.DataFrame(data)
    return dcc.send_data_frame(df.to_csv, f"impulse_signals_{sym}.csv", index=False)

@app.callback(
    Output("impulse-visible-store", "data"),
    Input("toggle-impulses-btn", "n_clicks"),
    State("impulse-visible-store", "data"),
    prevent_initial_call=True
)
def toggle_impulses(n_clicks, current):
    return not current

@app.callback(
    Output("events-visible-store", "data"),
    Input("toggle-events-btn", "n_clicks"),
    State("events-visible-store", "data"),
    prevent_initial_call=True
)
def toggle_events(n_clicks, current):
    return not current

@app.callback(
Output("impulse-results", "children"),
Output("processing-ops-store", "data", allow_duplicate=True),
Input("run-grid-search", "n_clicks"),
Input({"type": "grid-poll", "index": ALL}, "n_intervals"),
State("impulse-task-selector", "value"),
State("impulse-range-mult", "value"),
State("impulse-vol-mult", "value"),
State("impulse-body-ratio", "value"),
State("impulse-wick-ratio", "value"),
State("impulse-next-confirm", "value"),
State("impulse-rsi-divergence", "value"),
State("impulse-rsi-extreme", "value"),
State("impulse-base-candle", "value"),
State("impulse-vol-accel", "value"),
State("processing-ops-store", "data"),
prevent_initial_call=True
)
def run_grid_search_and_poll(n_clicks, poll_intervals, task_id, range_mult, vol_mult, body_ratio, wick_ratio, next_confirm, rsi_div, rsi_extreme, base_candle, vol_accel, processing_ops):
    triggered = ctx.triggered_id
    
    # 1. Handle Button Click (Start Grid Search)
    if triggered == "run-grid-search":
        if not task_id:
            return html.Div([html.H5("⚠️ Select a task first.", style={"color":"red"})]), processing_ops
            
        op_key = f"grid_{task_id}"
        if processing_ops.get(op_key):
            return html.Div([html.H5("⏳ Already running for this task...")]), processing_ops
            
        # Prepare params & data
        task = tm.get_task(task_id)
        if not task:
            return html.Div([html.H5("❌ Task not found.", style={"color":"red"})]), processing_ops
            
        param_grid = {'range_mult': [0.7, 1.0, 1.3], 'vol_mult': [1.2, 1.5], 'body_ratio': [0.4, 0.5], 'wick_ratio': [0.3, 0.4], 'use_next_candle_confirmation': [True, False], 'use_rsi_divergence': [False], 'use_base_candle': [False], 'use_volume_acceleration': [False]}
        processing_ops[op_key] = True
        from impulse import grid_search  # ✅ ADD THIS LINE
        try:
            fp = os.path.join(symbol_timeframe_path(task.symbols[0], task.timeframe), "data.parquet")
            # 🔧 CRITICAL: Clear cache before loading to ensure fresh data after recalc
            clear_parquet_cache()
            full_df = load_task_data_cached(task)
            buffer_ms = SIGNAL_BUFFER_MINUTES * 60 * 1000
            start_ms = max(0, task.signal_time - buffer_ms)
            if task.start_date and task.end_date:
                window_len_ms = int(task.end_date.replace(tzinfo=timezone.utc).timestamp() * 1000) - int(task.start_date.replace(tzinfo=timezone.utc).timestamp() * 1000)
                df_limited = full_df[(full_df['timestamp'] >= start_ms) & (full_df['timestamp'] <= task.signal_time + window_len_ms)].copy()
            else:
                df_limited = full_df[full_df['timestamp'] >= start_ms].copy()
                
            if df_limited.empty:
                processing_ops.pop(op_key, None)
                return html.Div([html.H5("❌ No data in period.", style={"color":"red"})]), processing_ops
                
            job_id = f"grid_{task_id}"
            optimizer_mgr.submit(job_id, grid_search, df_limited, task.signal_price, task.signal_direction, task.signal_time, param_grid, verbose=False)
            
            return html.Div([
                html.H5("⏳ Grid Search Running: Testing 96 combinations..."),
                dcc.Interval(id={"type": "grid-poll", "index": task_id}, interval=1000, max_intervals=300),
                dcc.Store(id={"type": "grid-job-id", "index": task_id}, data=job_id)
            ]), processing_ops
        except Exception as e:
            processing_ops.pop(op_key, None)
            return html.Div([html.H5(f"❌ Error starting search: {e}", style={"color":"red"})]), processing_ops

    # 2. Handle Polling Interval
    if isinstance(triggered, dict) and triggered.get("type") == "grid-poll":
        task_id = triggered.get("index")
        job_id = f"grid_{task_id}"
        status = optimizer_mgr.get_status(job_id)
        
        if status['status'] == 'running':
            return html.Div([html.H5("⏳ Grid Search Running...")]), processing_ops
        if status['status'] == 'error':
            processing_ops.pop(job_id, None)
            return html.Div([html.H5(f"❌ Grid search failed: {status['error']}", style={"color":"red"})]), processing_ops
            
        processing_ops.pop(job_id, None)
        results_df = status['result']
        if results_df is None or results_df.empty:
            return html.Div([html.H5("⚠️ No impulse trades found in any combination.", style={"color":"orange"})]), processing_ops
            
        results_df = results_df.sort_values('total_pnl', ascending=False).head(5)
        table_rows = [html.Tr([
            html.Td(f"{r['range_mult']:.1f}"), html.Td(f"{r['vol_mult']:.1f}"), html.Td(f"{r['body_ratio']:.2f}"), html.Td(f"{r['wick_ratio']:.2f}"),
            html.Td("✓" if r['use_next_candle_confirmation'] else "✗"), html.Td("✓" if r['use_rsi_divergence'] else "✗"),
            html.Td("✓" if r['use_base_candle'] else "✗"), html.Td("✓" if r['use_volume_acceleration'] else "✗"),
            html.Td(f"{r['count']}"), html.Td(f"{r['win_rate']:.1f}%"), html.Td(f"{r['total_pnl']:.2f}%"), html.Td(f"{r['profit_factor']:.2f}"),
        ]) for _, r in results_df.iterrows()]
        
        return html.Div([
            html.H5("✅ Grid Search Complete (Top 5 Results)"),
            html.Table([html.Thead(html.Tr([html.Th("Range"), html.Th("Vol"), html.Th("Body"), html.Th("Wick"), html.Th("Next"), html.Th("Div"), html.Th("Base"), html.Th("Accel"), html.Th("Trades"), html.Th("Win%"), html.Th("P&L%"), html.Th("PF")])), html.Tbody(table_rows)], style={"width": "100%", "border": "1px solid gray", "borderCollapse": "collapse", "fontSize": "12px"})
        ]), processing_ops
        
    return no_update, processing_ops

@app.callback(
    Output("impulse-results", "children", allow_duplicate=True),
    Output("processing-ops-store", "data", allow_duplicate=True),
    Input({"type": "grid-poll", "index": ALL}, "n_intervals"),
    State("processing-ops-store", "data"),
    prevent_initial_call=True
)
def poll_grid_result(n_intervals, processing_ops):
    triggered = ctx.triggered_id
    if not triggered or not isinstance(triggered, dict):
        return no_update, processing_ops
    task_id = triggered.get("index")
    job_id = f"grid_{task_id}"
    status = optimizer_mgr.get_status(job_id)
    if status['status'] == 'running':
        return html.Div([html.H5("⏳ Grid search running...")]), processing_ops
    if status['status'] == 'error':
        processing_ops.pop(job_id, None)
        return html.Div([html.H5("❌ Grid search failed", style={"color":"red"}), html.Pre(status['error'])]), processing_ops
    processing_ops.pop(job_id, None)
    results_df = status['result']
    if results_df is None or results_df.empty:
        return html.Div([html.H5("⚠️ No impulse trades found", style={"color":"orange"})]), processing_ops
    results_df = results_df.sort_values('total_pnl', ascending=False).head(5)
    table_rows = [html.Tr([
        html.Td(f"{r['range_mult']:.1f}"), html.Td(f"{r['vol_mult']:.1f}"),
        html.Td(f"{r['body_ratio']:.2f}"), html.Td(f"{r['wick_ratio']:.2f}"),
        html.Td("✓" if r['use_next_candle_confirmation'] else "✗"),
        html.Td("✓" if r['use_rsi_divergence'] else "✗"),
        html.Td("✓" if r['use_base_candle'] else "✗"),
        html.Td("✓" if r['use_volume_acceleration'] else "✗"),
        html.Td(f"{r['count']}"), html.Td(f"{r['win_rate']:.1f}%"),
        html.Td(f"{r['total_pnl']:.2f}%"), html.Td(f"{r['profit_factor']:.2f}"),
    ]) for _, r in results_df.iterrows()]
    table = html.Table([
        html.Thead(html.Tr([html.Th("Range"), html.Th("Vol"), html.Th("Body"), html.Th("Wick"),
                            html.Th("Next"), html.Th("Div"), html.Th("Base"), html.Th("Accel"),
                            html.Th("Trades"), html.Th("Win%"), html.Th("Total P&L%"), html.Th("PF")])),
        html.Tbody(table_rows)
    ], style={"width": "100%", "border": "1px solid gray", "borderCollapse": "collapse", "fontSize": "12px"})
    return html.Div([html.H5("Grid Search Results (Top 5)"), table]), processing_ops

@app.callback(
    Output("impulse-results", "children", allow_duplicate=True),
    Input("run-walk-forward", "n_clicks"),
    State("impulse-task-selector", "value"),
    State("impulse-range-mult", "value"),
    State("impulse-vol-mult", "value"),
    State("impulse-body-ratio", "value"),
    State("impulse-wick-ratio", "value"),
    State("impulse-next-confirm", "value"),
    State("impulse-rsi-divergence", "value"),
    State("impulse-rsi-extreme", "value"),
    State("impulse-base-candle", "value"),
    State("impulse-vol-accel", "value"),
    prevent_initial_call=True
)
def run_walk_forward(n_clicks, task_id, range_mult, vol_mult, body_ratio, wick_ratio,
                     next_confirm, rsi_div, rsi_extreme, base_candle, vol_accel):
    if n_clicks == 0 or not task_id:
        return "Select a task and click Run Walk‑Forward."
    task = tm.get_task(task_id)
    if not task:
        return "Task not found."
    # WIDER, LOWER param grid to find impulses
    param_grid = {
        'range_mult': [0.5, 0.7, 0.9, 1.2],
        'vol_mult': [1.0, 1.2, 1.5],
        'body_ratio': [0.4, 0.5, 0.6],
        'wick_ratio': [0.3, 0.4, 0.5],
        'use_next_candle_confirmation': [True, False],
        'use_rsi_divergence': [True, False],
        'use_base_candle': [True, False],
        'use_volume_acceleration': [True, False],
    }
    try:
        from impulse import walk_forward
        # Load data (same as in apply_impulse_params)
        # 🔧 CRITICAL: Clear cache before loading to ensure fresh data after recalc
        clear_parquet_cache()
        full_df = load_task_data_cached(task)
        if full_df.empty:
            return "Data file not found or empty."
        buffer_ms = SIGNAL_BUFFER_MINUTES * 60 * 1000
        start_ms = max(0, task.signal_time - buffer_ms)
        if task.start_date and task.end_date:
            window_len_ms = int(task.end_date.replace(tzinfo=timezone.utc).timestamp() * 1000) - int(task.start_date.replace(tzinfo=timezone.utc).timestamp() * 1000)
            cutoff_time = task.signal_time + window_len_ms
            df_limited = full_df[(full_df['timestamp'] >= start_ms) & (full_df['timestamp'] <= cutoff_time)].copy()
        else:
            df_limited = full_df[full_df['timestamp'] >= start_ms].copy()
        if df_limited.empty:
            return "No data in the selected period."
        # Run walk‑forward (percentage split works for any data length)
        results_df = walk_forward(df_limited, task.signal_price, task.signal_direction, task.signal_time,
                                  in_sample_pct=0.7, out_sample_pct=0.3, param_grid=param_grid, verbose=False)
        if results_df.empty:
            return "No walk‑forward results (insufficient data)."
        # Format the results as a table with readable timestamps
        table_rows = []
        for _, row in results_df.iterrows():
            in_range = f"{pd.to_datetime(row['in_start'], unit='ms').strftime('%Y-%m-%d %H:%M')} to {pd.to_datetime(row['in_end'], unit='ms').strftime('%Y-%m-%d %H:%M')}"
            out_range = f"{pd.to_datetime(row['out_start'], unit='ms').strftime('%Y-%m-%d %H:%M')} to {pd.to_datetime(row['out_end'], unit='ms').strftime('%Y-%m-%d %H:%M')}"
            params_str = ", ".join([f"{k}={v}" for k, v in row['best_params'].items()])
            table_rows.append(html.Tr([
                html.Td(in_range),
                html.Td(out_range),
                html.Td(params_str, style={"maxWidth": "200px", "fontSize": "11px"}),
                html.Td(f"{row['out_trades']}"),
                html.Td(f"{row['out_win_rate']:.1f}%"),
                html.Td(f"{row['out_total_pnl']:.2f}%"),
            ]))
        table = html.Table([
            html.Thead(html.Tr([
                html.Th("In‑Sample Range"), html.Th("Out‑Sample Range"),
                html.Th("Best Params"), html.Th("Trades"), html.Th("Win%"), html.Th("Total P&L%")
            ])),
            html.Tbody(table_rows)
        ], style={"width": "100%", "border": "1px solid gray", "borderCollapse": "collapse", "fontSize": "12px"})
        return html.Div([html.H5("Walk‑Forward Results (70% train, 30% test)"), table])
    except Exception as e:
        return f"Walk‑forward error: {str(e)}"

@app.callback(
    Input({"type": "rerun-strat-btn", "index": ALL}, "n_clicks"),
    prevent_initial_call=True
)
def rerun_strategy(n_clicks_list):
    # FIX: Stop phantom triggers caused by table re-rendering (resetting n_clicks to None/0)
    if not any(n_clicks_list):
        return no_update

    triggered = ctx.triggered_id
    if not triggered or not isinstance(triggered, dict):
        return no_update
    task_id = triggered.get("index")
    task = tm.get_task(task_id)
    if not task or task.status != "completed":
        return no_update
    try:
        # Reload data and re-run detect_strategies
        sym = task.symbols[0]
        path = symbol_timeframe_path(sym, task.timeframe)
        fp = os.path.join(path, "data.parquet")
        if not os.path.exists(fp):
            task.add_log("Re‑run Strategy: data file not found")
            return no_update
        full_df = pd.read_parquet(fp)
        buffer_ms = SIGNAL_BUFFER_MINUTES * 60 * 1000
        start_ms = max(0, task.signal_time - buffer_ms)
        if task.start_date and task.end_date:
            window_len_ms = int(task.end_date.replace(tzinfo=timezone.utc).timestamp() * 1000) - int(task.start_date.replace(tzinfo=timezone.utc).timestamp() * 1000)
            cutoff_time = task.signal_time + window_len_ms
            df_limited = full_df[(full_df['timestamp'] >= start_ms) & (full_df['timestamp'] <= cutoff_time)].copy()
        else:
            df_limited = full_df[full_df['timestamp'] >= start_ms].copy()
        if df_limited.empty:
            task.add_log("Re‑run Strategy: no data after filtering")
            return no_update
        signals = detect_strategies(df_limited, task.signal_price, task.signal_direction, task.signal_time, verbose=False)
        # Replace all signals
        task.strategy_signals = []
        for sig in signals:
            task.add_strategy_signal(
                sig['type'], sig['direction'], sig['entry_price'], sig['entry_time_ms'],
                exit_price=sig.get('exit_price'), exit_time_ms=sig.get('exit_time_ms'),
                stop_loss=sig.get('stop_loss'), take_profit=sig.get('take_profit_1'),
                confidence=sig['confidence']
            )
        # Update best summary
        if task.strategy_signals:
            best = max(task.strategy_signals, key=lambda x: x['delta_pct'] if x.get('delta_pct') is not None else -999)
            task.strategy_log_summary = f"{best['type'].capitalize()} {best['direction'].upper()} ({best.get('delta_pct', 0):.1f}%)"
            task.strategy_confidence = best['confidence']
        else:
            task.strategy_log_summary = "No valid signal"
        task.add_log("Manual strategy re‑run completed")
        return no_update
    except Exception as e:
        task.add_log(f"Manual strategy re‑run error: {e}")
        return no_update

@app.callback(
    Input({"type": "rerun-impulse-btn", "index": ALL}, "n_clicks"),
    prevent_initial_call=True
)
def rerun_impulse(n_clicks_list):
    # FIX: Stop phantom triggers caused by table re-rendering
    if not any(n_clicks_list):
        return no_update

    triggered = ctx.triggered_id
    if not triggered or not isinstance(triggered, dict):
        return no_update
    task_id = triggered.get("index")
    task = tm.get_task(task_id)
    if not task or task.status != "completed":
        return no_update
    try:
        task.run_impulse_detection(verbose=False)
        task.add_log("Manual impulse re‑run completed")
        return no_update
    except Exception as e:
        task.add_log(f"Manual impulse re‑run error: {e}")
        return no_update

@app.callback(
    Output("impulse-apply-all-status", "children", allow_duplicate=True),
    Input("rerun-strat-all", "n_clicks"),
    State("impulse-range-mult", "value"),
    State("impulse-vol-mult", "value"),
    State("impulse-body-ratio", "value"),
    State("impulse-wick-ratio", "value"),
    State("impulse-next-confirm", "value"),
    State("impulse-rsi-divergence", "value"),
    State("impulse-rsi-extreme", "value"),
    State("impulse-base-candle", "value"),
    State("impulse-vol-accel", "value"),
    prevent_initial_call=True
)
def rerun_strategy_on_all(n_clicks, range_mult, vol_mult, body_ratio, wick_ratio,
                          next_confirm, rsi_div, rsi_extreme, base_candle, vol_accel):
    if n_clicks == 0:
        return ""
    tasks = tm.get_all_tasks()
    completed = [t for t in tasks if t.status == "completed"]
    if not completed:
        return "No completed tasks."
    success = 0
    for task in completed:
        try:
            # Re‑load data (same logic as in rerun_strategy)
            sym = task.symbols[0]
            path = symbol_timeframe_path(sym, task.timeframe)
            fp = os.path.join(path, "data.parquet")
            if not os.path.exists(fp):
                continue
            full_df = pd.read_parquet(fp)
            buffer_ms = task.pre_buffer_minutes * 60 * 1000
            start_ms = max(0, task.signal_time - buffer_ms)
            if task.start_date and task.end_date:
                window_len_ms = int(task.end_date.replace(tzinfo=timezone.utc).timestamp() * 1000) - int(task.start_date.replace(tzinfo=timezone.utc).timestamp() * 1000)
                cutoff_time = task.signal_time + window_len_ms
                df_limited = full_df[(full_df['timestamp'] >= start_ms) & (full_df['timestamp'] <= cutoff_time)].copy()
            else:
                df_limited = full_df[full_df['timestamp'] >= start_ms].copy()
            if df_limited.empty:
                continue
            signals = detect_strategies(df_limited, task.signal_price, task.signal_direction, task.signal_time, verbose=False)
            task.strategy_signals = []
            for sig in signals:
                task.add_strategy_signal(
                    sig['type'], sig['direction'], sig['entry_price'], sig['entry_time_ms'],
                    exit_price=sig.get('exit_price'), exit_time_ms=sig.get('exit_time_ms'),
                    stop_loss=sig.get('stop_loss'), take_profit=sig.get('take_profit_1'),
                    confidence=sig['confidence']
                )
            # Update best summary
            if task.strategy_signals:
                best = max(task.strategy_signals, key=lambda x: x['delta_pct'] if x.get('delta_pct') is not None else -999)
                task.strategy_log_summary = f"{best['type'].capitalize()} {best['direction'].upper()} ({best.get('delta_pct', 0):.1f}%)"
                task.strategy_confidence = best['confidence']
            else:
                task.strategy_log_summary = "No valid signal"
            success += 1
        except Exception as e:
            task.add_log(f"Re‑run Strategy on All error: {e}")
    return f"Re‑run Strategy completed on {success} tasks."

@app.callback(
    Output("impulse-apply-all-status", "children", allow_duplicate=True),
    Input("rerun-impulse-all", "n_clicks"),
    State("impulse-range-mult", "value"),
    State("impulse-vol-mult", "value"),
    State("impulse-body-ratio", "value"),
    State("impulse-wick-ratio", "value"),
    State("impulse-next-confirm", "value"),
    State("impulse-rsi-divergence", "value"),
    State("impulse-rsi-extreme", "value"),
    State("impulse-base-candle", "value"),
    State("impulse-vol-accel", "value"),
    prevent_initial_call=True
)
def rerun_impulse_on_all(n_clicks, range_mult, vol_mult, body_ratio, wick_ratio,
                         next_confirm, rsi_div, rsi_extreme, base_candle, vol_accel):
    if n_clicks == 0:
        return ""
    tasks = tm.get_all_tasks()
    completed = [t for t in tasks if t.status == "completed"]
    if not completed:
        return "No completed tasks."
    params = {
        'range_mult': range_mult,
        'vol_mult': vol_mult,
        'body_ratio': body_ratio,
        'wick_ratio': wick_ratio,
        'use_next_candle_confirmation': 'confirm' in next_confirm if next_confirm else False,
        'use_rsi_divergence': 'div' in rsi_div if rsi_div else False,
        'rsi_extreme': rsi_extreme,
        'use_base_candle': 'base' in base_candle if base_candle else False,
        'use_volume_acceleration': 'accel' in vol_accel if vol_accel else False,
    }
    success = 0
    total_impulse = 0
    for task in completed:
        try:
            cnt = task.run_impulse_detection(params=params, verbose=False)
            total_impulse += cnt
            success += 1
        except Exception as e:
            task.add_log(f"Re‑run Impulse on All error: {e}")
    return f"Re‑run Impulse completed on {success} tasks. Total impulse signals: {total_impulse}"

# =============================================================================
# NOTE: Database Maintenance callbacks have been moved to database.py
# and are registered via register_database_callbacks(app) below.
# This includes: clean-symbol/timeframe options, delete operations,
# redownload functions, and database backup functionality.
# =============================================================================

# ----- Active Download Monitor Callbacks -----
@app.callback(
    Output("monitor-task-info", "children"),
    Output("monitor-progress", "value"),
    Output("monitor-pause-btn", "disabled"),
    Output("monitor-stop-btn", "disabled"),
    Input("progress-interval", "n_intervals"),
    prevent_initial_call=True
)
def update_download_monitor(_):
    running = [t for t in tm.get_all_tasks() if t.status == "running"]
    if not running:
        return "Idle", "0", True, True
    task = running[0]
    sym = task.symbols[0]
    info = f"{sym} | {task.timeframe} | {task.downloaded_candles}/{task.total_candles} candles"
    return info, str(int(task.progress)), False, False

@app.callback(
    Output("monitor-pause-btn", "children", allow_duplicate=True),
    Input("monitor-pause-btn", "n_clicks"),
    prevent_initial_call=True
)
def monitor_pause(n_clicks):
    if n_clicks is None:
        return "⏸ Pause"
    running = [t for t in tm.get_all_tasks() if t.status == "running"]
    if not running:
        return "⏸ Pause"
    task = running[0]
    tm.pause_task(task.task_id)
    return "▶ Resume" if task.paused else "⏸ Pause"

@app.callback(
    Output("monitor-stop-btn", "n_clicks", allow_duplicate=True),
    Input("monitor-stop-btn", "n_clicks"),
    prevent_initial_call=True
)
def monitor_stop(n_clicks):
    if n_clicks is None:
        return 0
    running = [t for t in tm.get_all_tasks() if t.status == "running"]
    if running:
        tm.stop_task(running[0].task_id)
    return 0

# ----- Re-download ALL Existing Data Callback -----
@app.callback(
    Output("redownload-all-status", "children"),
    Input("redownload-all-btn", "n_clicks"),
    prevent_initial_call=True
)
def redownload_all_existing(n_clicks):
    if n_clicks is None:
        return ""
    try:
        pairs = []
        for root, _, files in os.walk(MARKET_DATA_DIR):
            if "data.parquet" in files:
                rel = os.path.relpath(root, MARKET_DATA_DIR).split(os.sep)
                if len(rel) == 2:
                    sym, tf = rel
                    pairs.append((sym, tf))
        if not pairs:
            return "⚠️ No existing data found to re-download."
        queued = 0
        for sym, tf in pairs:
            path = symbol_timeframe_path(sym, tf)
            fp = os.path.join(path, "data.parquet")
            if os.path.exists(fp):
                os.remove(fp)
            tid = str(uuid.uuid4())
            task = DownloadTask(
                task_id=tid, symbols=[sym], timeframe=tf, mode='full',
                start_date=None, end_date=None, overwrite=True,
                price_continuity_check=False, signal_time=int(time.time()*1000),
                signal_price=0, signal_symbol=sym, signal_direction='resistance',
                analyze_beyond=False, enable_strategy=False, enable_impulse=False,
                pre_buffer_minutes=5
            )
            tm.add_task(task)
            queued += 1
            # Add immediate log so UI picks it up on next interval refresh
            task.add_log(f"🔄 Full history re-download queued for {sym} ({tf})")
        return f"✅ Queued {queued} full re-download tasks. Progress will appear in Tasks tab shortly."
    except Exception as e:
        return f"❌ Error: {str(e)}"

@app.callback(
    Output("bulk-rerun-status", "children", allow_duplicate=True),
    Input("bulk-rerun-events", "n_clicks"),
    Input("bulk-rerun-strategy", "n_clicks"),
    Input("bulk-rerun-impulse", "n_clicks"),
    prevent_initial_call=True
)
def bulk_rerun_all(ev_n, str_n, imp_n):
    triggered = ctx.triggered_id
    if not triggered:
        return no_update
    
    tasks = tm.get_all_tasks()
    completed = [t for t in tasks if t.status == "completed"]
    
    if not completed:
        return "⚠️ No completed tasks found to re-run."
        
    count = 0
    for t in completed:
        try:
            if triggered == "bulk-rerun-events":
                # Runs analyze_signal() which generates all detailed logs you need
                t.analyze_signal()
                
            elif triggered == "bulk-rerun-strategy":
                sym = t.symbols[0]
                path = symbol_timeframe_path(sym, t.timeframe)
                fp = os.path.join(path, "data.parquet")
                if os.path.exists(fp):
                    full_df = pd.read_parquet(fp)
                    buffer_ms = t.pre_buffer_minutes * 60 * 1000
                    start_ms = max(0, t.signal_time - buffer_ms)
                    
                    if t.start_date and t.end_date:
                        window_len_ms = int(t.end_date.replace(tzinfo=timezone.utc).timestamp() * 1000) - int(t.start_date.replace(tzinfo=timezone.utc).timestamp() * 1000)
                        cutoff_time = t.signal_time + window_len_ms
                        df_limited = full_df[(full_df['timestamp'] >= start_ms) & (full_df['timestamp'] <= cutoff_time)].copy()
                    else:
                        df_limited = full_df[full_df['timestamp'] >= start_ms].copy()
                        
                    if not df_limited.empty:
                        signals = detect_strategies(df_limited, t.signal_price, t.signal_direction, t.signal_time, verbose=False)
                        t.strategy_signals = []
                        for sig in signals:
                            t.add_strategy_signal(
                                sig['type'], sig['direction'], sig['entry_price'], sig['entry_time_ms'],
                                exit_price=sig.get('exit_price'),
                                exit_time_ms=sig.get('exit_time_ms'),
                                stop_loss=sig.get('stop_loss'),
                                take_profit=sig.get('take_profit_1'),
                                confidence=sig['confidence']
                            )
                    
                    if t.strategy_signals:
                        best = max(t.strategy_signals, key=lambda x: x.get('delta_pct') if x.get('delta_pct') is not None else -999)
                        dp = best.get('delta_pct')
                        dp_val = dp if dp is not None else 0.0
                        t.strategy_log_summary = f"{best['type'].capitalize()} {best['direction'].upper()} ({dp_val:.1f}%)"
                        t.strategy_confidence = best['confidence']
                        
            elif triggered == "bulk-rerun-impulse":
                t.run_impulse_detection(verbose=False)
            count += 1
        except Exception as e:
            t.add_log(f"Bulk rerun error: {e}")
            
    label = "Events" if triggered == "bulk-rerun-events" else "Strategy" if triggered == "bulk-rerun-strategy" else "Impulse"
    return f"✅ {label} re-run completed on {count} tasks. Table will refresh shortly."

# 1. Auto-refresh dropdown with existing JSON files
@app.callback(
    Output("json-file-select", "options"),
    Input("save-tasks-btn", "n_clicks"),
    Input("load-tasks-btn", "n_clicks"),
    prevent_initial_call=True
)
def refresh_json_dropdown(*_):
    if not os.path.exists(LOGS_DIR):
        return []
    files = sorted([f for f in os.listdir(LOGS_DIR) if f.endswith('.json')], reverse=True)
    return [{"label": f, "value": os.path.join(LOGS_DIR, f)} for f in files]

# 2. Save tasks to custom JSON filename (REWRITTEN: Reconstruction from Truth pattern)
@app.callback(
    Output("save-load-status", "children"),
    Output("save-filename-input", "value"),
    Input("save-tasks-btn", "n_clicks"),
    State("save-filename-input", "value"),
    prevent_initial_call=True
)
def save_tasks_to_json(n, filename):
    """
    Save tasks using the 'Reconstruction from Truth' pattern.
    
    This function implements the Serialization Bridge architecture:
    1. Source of Truth: Reads from live RAM objects (task_manager.tasks)
    2. Sanitization: Converts all types via sanitize_for_json()
    3. Graveyard Preservation: Invalid tasks are preserved from original JSON
    4. Atomic Save: Uses temp file + replace for crash safety
    
    Data Layers:
    - core_signal: Static configuration (symbol, timeframe, signal_text, etc.)
    - analysis_results: Dynamic calculations (drawdown, events, strategies)
    - system_meta: Technical metadata (version, timestamp, status)
    """
    if not filename:
        return "⚠️ Please enter a valid filename.", filename
    
    # Sanitize filename & ensure .json extension
    filename = re.sub(r'[^\w\-_.]', '_', filename.strip())
    if not filename.endswith('.json'):
        filename += '.json'
    
    # Ensure the task_logs directory exists
    os.makedirs(LOGS_DIR, exist_ok=True)
    
    filepath = os.path.join(LOGS_DIR, filename)
    
    # Get live tasks from RAM (Source of Truth)
    tasks = tm.get_all_tasks()
    
    # Build reconstructed data list
    serializable_data = []
    
    # Process all valid tasks from RAM
    if tasks:
        for t in tasks:
            d = {}
            # Iterate through all attributes, excluding non-serializable threading objects
            for k, v in t.__dict__.items():
                # Skip threading/synchronization objects and internal caches
                if k in ('stop_event', 'pause_event', 'state_lock', 'raw_batches', '_chart_cache', 'symbol_ranges'):
                    continue
                
                # Apply sanitize_for_json to ALL values (handles datetime, NumPy, NaN, etc.)
                d[k] = sanitize_for_json(v)
            
            # Debug: Verify critical fields are present
            if 'hit_1' not in d:
                print(f"WARNING: Task {t.task_id[:8]} missing 'hit_1' in save! Current value: {getattr(t, 'hit_1', 'MISSING')}")
            
            serializable_data.append(d)
    
    # 🔧 ATOMIC SAVE with sanitization (removed default=str fallback)
    temp_path = filepath + ".tmp"
    try:
        with open(temp_path, 'w', encoding='utf-8') as f:
            # All data is pre-sanitized, no need for default=str
            json.dump(serializable_data, f, indent=2)
        os.replace(temp_path, filepath)
        return f"✅ Saved {len(tasks)} tasks to {filename}", filename
    except Exception as e:
        if os.path.exists(temp_path):
            os.remove(temp_path)  # Delete broken temp file
        return f"❌ Save failed: {str(e)}", filename


# 3. Load tasks from selected JSON file (Optimized & Thread-Safe)
@app.callback(
    Output("save-load-status", "children", allow_duplicate=True),
    Output("task-ids-store", "data", allow_duplicate=True),
    Output("task-count-store", "data", allow_duplicate=True),
    Output("task-page-store", "data", allow_duplicate=True),
    Output("analysis-complete-trigger", "data", allow_duplicate=True), # 🔧 NEW
    Output("golden-store-version", "data", allow_duplicate=True), # 🔧 CRITICAL FIX: Update version store to trigger table refresh
    Input("load-tasks-btn", "n_clicks"),
    State("json-file-select", "value"),
    prevent_initial_call=True
)
def load_tasks_from_json(n, filepath):
    if not filepath or not os.path.exists(filepath):
        return "⚠️ Please select a valid JSON file.", [], 0, 0, 0, dash.no_update  # 🔧 Added 6th value
    try:
        with open(filepath, 'r', encoding='utf-8') as f:
            data = json.load(f)
        if not isinstance(data, list):
            return "❌ Invalid JSON format: expected a list of tasks.", [], 0, 0, 0, dash.no_update  # 🔧 Added 6th value
    except json.JSONDecodeError as e:
        return f"❌ JSON Syntax Error at line {e.lineno}, col {e.colno}: {e.msg}.", [], 0, 0, 0, dash.no_update  # 🔧 Added 6th value
    except Exception as e:
        return f"❌ Load failed: {str(e)}", [], 0, 0, 0, dash.no_update  # 🔧 Added 6th value
        
    loaded_ids = []
    skipped = 0
    new_tasks = {}
    seen_ids = set()  # P3 IMPROVEMENT: Track unique task IDs
    
    # 🔧 DATETIME FIELDS that need restoration on load
    datetime_fields = {'start_date', 'end_date', 'first_event_time', 'max_adverse_time',
                       'max_expected_time', 'max_adverse_sgnl_time', 'max_expected_sgnl_time',
                       'max_adverse_before_return_time', 'max_adverse_before_return_sgnl_time',
                       'drawdown_before_level_time', 'drawdown_before_1pct_time', 
                       'drawdown_before_1_5pct_time', 'drawdown_before_2pct_time'}
    
    # 🔧 Use global _parse_timestamp for UTC-aware datetime parsing
    # This ensures all timestamps are converted to UTC-aware datetime objects
    
    for d in data:
        try:
            # P3 IMPROVEMENT: Check for duplicate task IDs
            task_id_candidate = d.get('task_id')
            if not task_id_candidate:
                print(f"Skipping task without task_id: {d}")
                skipped += 1
                continue
            if task_id_candidate in seen_ids:
                print(f"Duplicate task_id detected: {task_id_candidate}, skipping")
                skipped += 1
                continue
            seen_ids.add(task_id_candidate)
            
            # 1. Initialize Task with Core Attributes
            init_kwargs = {k: d.get(k) for k in ['task_id', 'symbols', 'timeframe', 'mode', 'start_date', 'end_date',
                'overwrite', 'price_continuity_check', 'signal_time', 'signal_price',
                'signal_symbol', 'signal_direction', 'analyze_beyond', 'enable_strategy',
                'enable_impulse', 'pre_buffer_minutes', 'log_events', 'hide_logs']}

            # Parse Datetimes for Init
            for k in datetime_fields:
                if k in init_kwargs and isinstance(init_kwargs[k], str):
                    init_kwargs[k] = _parse_timestamp(init_kwargs[k])

            task = DownloadTask(**init_kwargs)

            # 2. Restore ALL Other Attributes from JSON
            for k, v in d.items():
                if hasattr(task, k) and k not in init_kwargs:
                    try:
                        if k in datetime_fields:
                            setattr(task, k, _parse_timestamp(v))
                        elif k in ['signal_time', 'signal_price']:
                            setattr(task, k, float(v))
                        else:
                            setattr(task, k, v)
                    except Exception:
                        # If an attribute fails to restore, skip it silently (robustness)
                        pass 

            new_tasks[task.task_id] = task
            loaded_ids.append(task.task_id)
        except Exception as e:
            print(f"Error loading task: {e}")
            skipped += 1
            
    # 🔧 ATOMIC & THREAD-SAFE MEMORY UPDATE
    with tm.lock:
        tm.tasks.clear()
        tm.tasks.update(new_tasks)

    # 🔧 CRITICAL: Reset Version to Force Stats & Table Re-render
    # Since we split the callback, we just increment the version to trigger both new callbacks
    global golden_store_version
    golden_store_version += 1
        
    count = len(loaded_ids)
    msg = f"✅ Loaded {count} tasks from {os.path.basename(filepath)}"
    if skipped > 0:
        msg += f" | ⚠️ Skipped {skipped} corrupted tasks"
    # 🔧 Increment trigger to force UI refresh after load
    import time
    trigger_val = int(time.time()) 
    
    return msg, loaded_ids, count, 0, trigger_val, golden_store_version

@app.callback(
    Output("save-load-status", "children", allow_duplicate=True),
    Output("task-ids-store", "data", allow_duplicate=True),
    Output("task-count-store", "data", allow_duplicate=True),
    Output("task-page-store", "data", allow_duplicate=True),
    Input("clear-all-tasks-btn", "n_clicks"),
    prevent_initial_call=True
)
def manual_clear_all(n):
    """Instantly wipes all tasks from RAM and resets UI stores."""
    global STOP_REQUESTED
    STOP_REQUESTED = True  # 🔧 Safely halt background recalc (sync with STOP_REQUESTED)
    recalc_bg["stop_flag"] = True  # 🔧 Also set recalc_bg flag for UI
    with tm.lock:
        tm.tasks.clear()
    return "🗑️ All tasks cleared.", [], 0, 0

@app.callback(
    Output("bulk-rerun-status", "children", allow_duplicate=True),
    Output("analysis-complete-trigger", "data", allow_duplicate=True), # 🔧 NEW
    Input("recalc-table-flags-btn", "n_clicks"),
    prevent_initial_call=True
)
def recalc_table_flags(n):
    """Recomputes ONLY the table column flags..."""
    global STOP_REQUESTED
    if not n: 
        return dash.no_update, dash.no_update  # 🔧 Return tuple
    
    # 🔧 CRITICAL: Reset stop flag before starting new recalculation
    STOP_REQUESTED = False
    
    if recalc_bg["running"]: 
        return "⏳ Recalculation already in progress...", dash.no_update  # 🔧 Return tuple
        
    tasks = [t for t in tm.get_all_tasks() if t.signal_time is not None and t.status == "completed"]
    if not tasks:
        return "⚠️ No completed tasks with signal data to recalc.", dash.no_update  # 🔧 Return tuple

    # 🔧 CRITICAL: Serialize tasks to dict format INSIDE the main thread (same logic as save_tasks_to_json)
    # This ensures all attributes are properly captured before passing to background thread
    import copy
    initial_tasks = []
    for t in tasks:
        d = {}
        for k, v in t.__dict__.items():
            # Skip non-serializable objects (locks, events, caches)
            if k in ('stop_event', 'pause_event', 'state_lock', 'raw_batches', '_chart_cache', 'symbol_ranges'):
                continue
            # Handle datetime objects
            if isinstance(v, (datetime, pd.Timestamp)):
                d[k] = v.isoformat()
            elif isinstance(v, (int, float, str, bool, type(None))):
                d[k] = v
            elif isinstance(v, (list, dict)):
                try:
                    json.dumps(v)
                    d[k] = v
                except (TypeError, ValueError):
                    continue
            else:
                try:
                    d[k] = str(v)
                except Exception:
                    continue
        initial_tasks.append(d)
    
    # 🔧 CRITICAL: Set global counters
    global recalc_total_tasks, is_recalculating_flag, recalc_progress_count
    recalc_total_tasks = len(initial_tasks)
    is_recalculating_flag = True
    recalc_progress_count = 0
    
    # 🔧 CRITICAL: Update recalc_bg status BEFORE starting thread
    recalc_bg["running"] = True
    recalc_bg["total"] = len(initial_tasks)
    recalc_bg["count"] = 0
    recalc_bg["stop_flag"] = False  # 🔧 Reset stop flag in recalc_bg dict
    recalc_bg["trigger_val"] = 0  # 🔧 Reset trigger value
    
    # 🔧 CRITICAL: Enable the poller to monitor completion
    global recalc_poller_enabled
    recalc_poller_enabled = True
    
    # 🔧 CRITICAL: Start background thread passing initial_tasks as argument
    import threading
    threading.Thread(target=_run_recalc_background, args=(initial_tasks,), daemon=True).start()

    # 🔧 Increment trigger to force UI refresh after recalc starts
    import time
    trigger_val = int(time.time())

    return f"🔄 Recalculation started in background. Checking {len(tasks)} existing tasks...", trigger_val  # 🔧 Already correct

def _run_recalc_background(tasks_list):
    """Runs in background thread to never block the UI."""
    global recalc_progress_count, is_recalculating_flag, recalculation_complete_timestamp, current_tasks, STOP_REQUESTED, recalc_bg
    
    # 🔧 CRITICAL: Create LOCAL ALIASES for modules to avoid global lookup issues in threads
    import sys as _sys
    import bisect as _bisect
    import numpy as np
    import pandas as pd
    
    # Create module-level aliases accessible throughout this function
    sys = _sys
    bisect = _bisect
    
    # 🔧 CRITICAL: DO NOT clear parquet cache - we use cached data from RAM for fast analysis
    # The original design was to avoid re-reading files when analyzing JSON-loaded tasks
    
    # 🔧 HEARTBEAT: Confirm thread started
    print(f"🔥 [RECALC THREAD] Started with {len(tasks_list)} tasks")
    sys.stdout.flush()
    
    total_tasks = len(tasks_list)
    
    # 🔧 DYNAMIC STEP CALCULATOR: Ensures ~50 progress updates regardless of batch size
    # For 10 tasks: step = max(1, 10//50) = 1 → updates every task (10 updates)
    # For 89 tasks: step = max(1, 89//50) = 1 → updates every task (89 updates)
    # For 3500 tasks: step = max(1, 3500//50) = 70 → updates every 70 tasks (50 updates)
    step = max(1, total_tasks // 50)
    print(f"🔥 [RECALC THREAD] Dynamic step calculated: {step} (total={total_tasks})")
    sys.stdout.flush()
    
    # 🔧 DATETIME FIELDS that need restoration from ISO strings
    datetime_fields = {'start_date', 'end_date', 'first_event_time', 'max_adverse_time',
                       'max_expected_time', 'max_adverse_sgnl_time', 'max_expected_sgnl_time',
                       'max_adverse_before_return_time', 'max_adverse_before_return_sgnl_time',
                       'drawdown_before_level_time', 'drawdown_before_1pct_time', 
                       'drawdown_before_1_5pct_time', 'drawdown_before_2pct_time'}
    
    # 🔧 Use global _parse_timestamp for UTC-aware datetime parsing
    # (Defined at module level for consistency across save/load operations)
    
    # 🔧 TRACK SUCCESS/FAILURE COUNTS
    success_count = 0
    error_count = 0
    
    for i, t_dict in enumerate(tasks_list):
        # 🛑 PATCH A: Check for stop request every iteration (check both flags)
        if STOP_REQUESTED or recalc_bg.get("stop_flag", False):
            print(f"⚠️ [RECALC THREAD] Stop requested at {i}/{total_tasks}. Finishing safely...")
            sys.stdout.flush()
            break
            
        try:
            # 🔧 RECONSTRUCT TASK OBJECT FROM DICTIONARY
            # Get task from memory if it exists, otherwise create a new one from dict
            task_id = t_dict.get('task_id')
            task_symbol = t_dict.get('symbols', ['UNKNOWN'])[0] if isinstance(t_dict.get('symbols'), list) else 'UNKNOWN'
            task_tf = t_dict.get('timeframe', 'unknown')
            
            print(f"🔍 [TASK {i+1}/{total_tasks}] Starting: {task_symbol} {task_tf} (ID: {task_id})")
            sys.stdout.flush()
            
            task = tm.get_task(task_id) if task_id else None
            
            if task is None:
                # Reconstruct task from dictionary
                init_kwargs = {k: t_dict.get(k) for k in ['task_id', 'symbols', 'timeframe', 'mode', 'start_date', 'end_date',
                    'overwrite', 'price_continuity_check', 'signal_time', 'signal_price',
                    'signal_symbol', 'signal_direction', 'analyze_beyond', 'enable_strategy',
                    'enable_impulse', 'pre_buffer_minutes', 'log_events', 'hide_logs']}
                
                # Parse Datetimes
                for k in datetime_fields:
                    if k in init_kwargs and isinstance(init_kwargs[k], str):
                        init_kwargs[k] = _parse_timestamp(init_kwargs[k])
                
                task = DownloadTask(**init_kwargs)
                
                # Restore ALL Other Attributes from Dictionary
                for k, v in t_dict.items():
                    if hasattr(task, k) and k not in init_kwargs:
                        try:
                            if k in datetime_fields:
                                setattr(task, k, _parse_timestamp(v))
                            elif k in ['signal_time', 'signal_price']:
                                setattr(task, k, float(v))
                            else:
                                setattr(task, k, v)
                        except Exception:
                            pass
            
            # Now process the reconstructed task object
            if task.signal_time is not None and task.status == "completed":
                print(f"📊 [TASK {i+1}/{total_tasks}] Running analyze_signal for {task_symbol} {task_tf}...")
                sys.stdout.flush()
                
                # 🔧 CRITICAL: Acquire state_lock before modifying strategy signals
                with task.state_lock:
                    task.analyze_signal()  # This is the slow part
                    
                print(f"✅ [TASK {i+1}/{total_tasks}] Completed analyze_signal for {task_symbol} {task_tf}")
                sys.stdout.flush()
                
                # 🔧 CRITICAL: Auto-save recalculated tasks to persist new data
                task.add_log("💾 Recalculation complete - data updated in memory")
                success_count += 1  # ✅ Track successful recalculation
            else:
                print(f"⏭️ [TASK {i+1}/{total_tasks}] Skipping (no signal_time or not completed): {task_symbol} {task_tf}")
                sys.stdout.flush()
                # Skipped tasks don't count as errors or successes
        except Exception as e:
            # ⚠️ WARNING ONLY: Continue processing even if task has errors (old Mac safe)
            import traceback
            print(f"❌ [TASK {i+1}/{total_tasks}] ERROR on {task_symbol if 'task_symbol' in locals() else 'UNKNOWN'} {task_tf if 'task_tf' in locals() else 'unknown'}: {e}")
            traceback.print_exc()
            sys.stdout.flush()
            error_count += 1  # ❌ Track failed recalculation
            try: 
                if task:
                    task.add_log(f"⚠️ Recalc error: {e}")
            except: pass

        # 🔧 CRITICAL: Update progress counter with DYNAMIC STEP for any batch size
        # This prevents freezing where small task counts would never reach the update threshold
        if (i + 1) % step == 0 or (i + 1) == total_tasks:
            recalc_progress_count = i + 1
            recalc_bg["count"] = i + 1  # 🔧 Update recalc_bg for UI polling
            print(f"🔥 [RECALC THREAD] Progress: {i + 1}/{total_tasks} (step={step})")
            sys.stdout.flush()
            
        # 🔧 HEARTBEAT: Every 10 seconds, print a heartbeat to confirm thread is alive
        if (i + 1) % max(10, step) == 0:
            print(f"💓 [RECALC THREAD] Heartbeat: Processing task {i + 1}/{total_tasks}...")
            sys.stdout.flush()

    # 🔧 CRITICAL: Update global RAM with processed tasks (atomic swap)
    with tm.lock:
        # Tasks were modified in-place during the loop, so they're already in tm.tasks
        # Just ensure current_tasks reflects the latest state
        current_tasks = list(tm.tasks.values())
    
    # 🔧 GOLDEN STORE: Populate pre-processed cache for instant pagination
    global golden_task_store_data, golden_store_version
    with tm.lock:
        golden_task_store_data = list(tm.tasks.values())
        golden_store_version += 1  # Increment version to invalidate page caches

    # 🔧 RECALC LOCK: Release lock to allow UI interaction
    global recalc_lock
    recalc_lock = {"locked": False, "message": "Recalculation complete"}
    
    # 🔧 CRITICAL: Update flags and timestamp (NO Auto-Save - user must press Save button)
    recalculation_complete_timestamp = time.time()
    is_recalculating_flag = False
    STOP_REQUESTED = False  # Reset stop flag for next run
    final_count = i + 1 if STOP_REQUESTED else total_tasks
    recalc_progress_count = final_count
    recalc_bg["count"] = final_count  # 🔧 Final count update
    recalc_bg["running"] = False  # 🔧 Signal completion to UI
    recalc_bg["trigger_val"] = int(time.time() * 1000)  # 🔧 NEW: Store trigger value for polling
    
    # 🔧 CRITICAL: Increment trigger to force UI refresh AFTER recalculation completes
    # This ensures task table and summary table show the updated data
    analysis_trigger_val = int(time.time() * 1000)  # Use milliseconds to ensure unique value

    if STOP_REQUESTED:
        print(f"⚠️ [RECALC THREAD] Recalculation stopped early: {final_count}/{total_tasks} tasks processed")
    elif error_count > 0:
        # 🚨 HONEST REPORTING: Show errors prominently
        print(f"🔴 [RECALC THREAD] Recalculation completed with ERRORS: {success_count} succeeded, {error_count} failed out of {total_tasks} tasks. FIX ERRORS before saving!")
    elif success_count == 0:
        # 🚨 HONEST REPORTING: No tasks were actually recalculated
        print(f"🔴 [RECALC THREAD] Recalculation completed but NOTHING WAS UPDATED: 0/{total_tasks} tasks recalculated. Check task status and signal data!")
    else:
        # ✅ Calculate how many tasks were skipped (no signal_time or not completed)
        skipped_count = total_tasks - success_count - error_count
        if skipped_count > 0:
            print(f"✅ [RECALC THREAD] Recalculation successful: {success_count}/{total_tasks} tasks updated.")
            print(f"ℹ️ [RECALC THREAD] Note: {skipped_count} task(s) were skipped (no signal time or incomplete status).")
            print(f"💾 [RECALC THREAD] Results in RAM - press 'Save New JSON' to persist.")
        else:
            print(f"✅ [RECALC THREAD] Recalculation successful: {success_count}/{total_tasks} tasks updated. Results in RAM - press 'Save New JSON' to persist.")
    sys.stdout.flush()
    
    # 🔧 CRITICAL: Return the trigger value so callback can update the store
    return analysis_trigger_val


@app.callback(
    Output("recalc-status-bar", "children"),
    Input("recalc-status-interval", "n_intervals"),
    prevent_initial_call=False
)
def update_status_bar(n):
    """Real-time status bar callback triggered every 1 second."""
    if is_recalculating_flag:
        # 🔧 FIX: Use recalc_bg["count"] for real-time progress instead of recalc_progress_count
        # which only updates in batches and can appear frozen
        current_count = recalc_bg.get("count", 0) if recalc_bg.get("running", False) else recalc_progress_count
        return f"⚙️ Checking: {current_count} / {recalc_total_tasks} tasks..."
    else:
        return "Ready"

@app.callback(
    Output("bulk-rerun-status", "children", allow_duplicate=True),
    Output("analysis-complete-trigger", "data", allow_duplicate=True), # 🔧 NEW: Also update trigger when polling detects completion
    Input("progress-interval", "n_intervals"),
    prevent_initial_call=True
)
def poll_recalc_progress(_):
    if not recalc_bg["running"]:
        # 🔧 FIX: Return a completion message instead of no_update
        # This ensures the UI shows "Done" instead of getting stuck on the last progress count
        if recalc_bg["total"] > 0:
            # 🔧 CRITICAL: Check if we have a trigger value from completed recalculation
            trigger_val = recalc_bg.get("trigger_val", 0)
            if trigger_val > 0:
                return f"✅ Recalculation complete. ({recalc_bg['count']}/{recalc_bg['total']} tasks updated)", trigger_val
            return f"✅ Recalculation complete. ({recalc_bg['count']}/{recalc_bg['total']} tasks updated)", dash.no_update
        else:
            # Only return no_update if recalculation never started
            if recalc_bg["count"] == 0:
                return no_update, dash.no_update
            # Otherwise show completion status even without total
            return f"✅ Recalculation complete. ({recalc_bg['count']} tasks updated)", dash.no_update
    return f"⏳ Recalculating... {recalc_bg['count']}/{recalc_bg['total']} completed", dash.no_update

# 🔧 NEW: Dedicated poller for triggering UI refresh after recalculation completes
@app.callback(
    Output("recalc-poller", "disabled"),
    Output("analysis-complete-trigger", "data", allow_duplicate=True),
    Input("recalc-poller", "n_intervals"),
    State("recalc-poller", "disabled"),
    prevent_initial_call=True
)
def trigger_ui_on_recalc_complete(n_intervals, is_disabled):
    """Polls every 1 second during recalculation and triggers UI refresh when complete."""
    global recalc_poller_enabled
    
    # Check if recalculation just finished
    if not recalc_bg["running"] and recalc_poller_enabled:
        # Recalculation just finished - trigger UI refresh
        trigger_val = recalc_bg.get("trigger_val", int(time.time() * 1000))
        print(f"🔥 [UI POLLER] Recalculation complete! Triggering UI refresh with value: {trigger_val}")
        # Reset poller state
        recalc_poller_enabled = False
        # Enable (disable=True) the poller until next recalculation
        return True, trigger_val
    elif recalc_bg["running"] and not recalc_poller_enabled:
        # Recalculation started - keep poller enabled (disabled=False)
        recalc_poller_enabled = True
        return False, dash.no_update
    # Keep current state
    return dash.no_update, dash.no_update

# Register database callbacks
register_database_callbacks(app)

if __name__ == "__main__":
    app.run(debug=True, port=8050)