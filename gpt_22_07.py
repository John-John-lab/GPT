"""
GPT 13.2 – rebuilt from gpt_11_07.py as the baseline application file.

Includes the latest strategy-task integrations by continuing to use the
current strategies.py detect_strategies implementation and impulse.py
impulse/backtesting implementation from this repository.

Bybit Downloader – Two Tabs + Summary + Optimized Buffering (10k candles)
with Database Verification Tool and Real‑time Integrity Checks.
Now with signal‑based downloading, candle analysis, and per‑task interactive charts.
"""

# =============================================================================
# 1. IMPORTS AND EXTERNAL INTEGRATIONS
# =============================================================================
# Keep imports centralized. Repository-local strategy/impulse/database imports are
# intentionally explicit so the main app can be reorganized without changing math.

import os, json, time, threading, queue, uuid, shutil, glob, hashlib, re, functools, sys, bisect, math
from collections import OrderedDict, deque
from datetime import datetime, timedelta, timezone
import dash
from dash import dcc, html, Input, Output, State, MATCH, ALL, no_update, ctx, clientside_callback as dash_clientside_callback
import pandas as pd
import numpy as np
import requests
import plotly.express as px
import plotly.graph_objects as go
from plotly.subplots import make_subplots
from flask import send_file, request, jsonify, g
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
    DUCKDB_AVAILABLE,
    em,
    validate_stored_candle_range,
)

# =============================================================================
# 2. UI FORMATTING HELPERS
# =============================================================================
# Presentation-only helpers. These functions may format or categorize values for
# display, but must not mutate tasks, publish Golden Store snapshots, or perform
# calculations that change saved analysis results.
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


# =============================================================================
# 3. MATH CONSTANTS AND TOWARD-LEVEL STRATEGY HELPERS
# =============================================================================
# Keep formulas and event/strategy math isolated from Dash callbacks. The helper
# below still mutates the task exactly as before; this section only makes the
# boundary explicit for future behavior-preserving extraction.
# =============================================================================

TOWARD_LEVEL_TARGET_PCTS = (0.5, 1.0, 1.5, 2.0, 3.0, 4.0)
TOWARD_LEVEL_STOP_LOSS_PCT = 0.12


def fmt_toward_level_target_ui(val):
    """Format the max reached target for the next-candle toward-level strategy."""
    if val is None or (isinstance(val, (float, np.floating)) and is_na(val)):
        return "-"
    try:
        val = float(val)
    except Exception:
        return "-"
    if val >= 4.0:
        return "4%+"
    return f"{val:g}%"


def reset_toward_level_strategy_fields(task):
    """Reset derived fields for the next-candle toward-level strategy."""
    task.toward_entry_direction = None
    task.toward_entry_price = None
    task.toward_entry_time = None
    task.toward_stop_loss_price = None
    task.toward_stop_loss_hit = False
    task.toward_stop_loss_time = None
    task.toward_max_reached_pct = None
    task.toward_level_reached = False
    task.toward_no_stop_returned_entry = False


def calculate_toward_level_strategy(task, df):
    """Calculate the user's next-candle entry strategy toward the parsed level.

    Logic used for counting: open on the first candle after signal_time using that
    candle open; buy toward resistance and sell toward support; stop loss is fixed
    at 0.12% from entry. We count the maximum target bucket reached before a stop
    loss. If price later falls back to a lower bucket and then reaches a higher
    bucket before the stop, the higher bucket is counted, because this best answers
    which take-profit level would have been available historically.
    """
    reset_toward_level_strategy_fields(task)
    if df is None or df.empty or task.signal_time is None or task.signal_price is None:
        return
    if task.signal_direction not in ("resistance", "support"):
        return

    df_sorted = df.sort_values('timestamp').reset_index(drop=True)
    entry_idx = df_sorted['timestamp'].searchsorted(float(task.signal_time), side='right')
    if entry_idx >= len(df_sorted):
        return

    entry_row = df_sorted.iloc[entry_idx]
    entry_price = entry_row.get('open', entry_row.get('close'))
    if entry_price is None or (isinstance(entry_price, (float, np.floating)) and is_na(entry_price)):
        return
    entry_price = float(entry_price)
    if entry_price <= 0:
        return

    direction = 'buy' if task.signal_direction == 'resistance' else 'sell'
    stop_loss_price = entry_price * (1 - TOWARD_LEVEL_STOP_LOSS_PCT / 100) if direction == 'buy' else entry_price * (1 + TOWARD_LEVEL_STOP_LOSS_PCT / 100)

    task.toward_entry_direction = direction
    task.toward_entry_price = entry_price
    task.toward_entry_time = entry_row['timestamp']
    task.toward_stop_loss_price = stop_loss_price

    max_move_pct = 0.0
    reached_targets = []
    returned_entry_after_favorable = False

    for _, row in df_sorted.iloc[entry_idx:].iterrows():
        high = float(row['high'])
        low = float(row['low'])
        ts = row['timestamp']

        if direction == 'buy':
            # Conservative same-candle rule: if stop and target are both inside the candle, count stop first.
            if low <= stop_loss_price:
                task.toward_stop_loss_hit = True
                task.toward_stop_loss_time = ts
                break
            move_pct = (high - entry_price) / entry_price * 100
            if high >= float(task.signal_price):
                task.toward_level_reached = True
        else:
            if high >= stop_loss_price:
                task.toward_stop_loss_hit = True
                task.toward_stop_loss_time = ts
                break
            move_pct = (entry_price - low) / entry_price * 100
            if low <= float(task.signal_price):
                task.toward_level_reached = True

        if move_pct > max_move_pct:
            max_move_pct = move_pct
            reached_targets = [pct for pct in TOWARD_LEVEL_TARGET_PCTS if move_pct >= pct]

        if max_move_pct > 0:
            if direction == 'buy' and low <= entry_price:
                returned_entry_after_favorable = True
            elif direction == 'sell' and high >= entry_price:
                returned_entry_after_favorable = True

        if task.toward_level_reached:
            break

    task.toward_max_reached_pct = max(reached_targets) if reached_targets else None
    task.toward_no_stop_returned_entry = bool(returned_entry_after_favorable and not task.toward_stop_loss_hit)

# =============================================================================
# 4. ANALYSIS THREAD-SAFETY ALIASES AND SHADOW VERIFICATION
# =============================================================================
# These aliases and comparison helpers support the existing vectorized analysis
# path. Preserve their behavior while gradually moving calculation details into
# smaller helpers inside this file.
# =============================================================================

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
# 5. JSON PERSISTENCE AND SNAPSHOT COMPATIBILITY
# =============================================================================
# Serialization Bridge for safe RAM ↔ disk conversion. This section owns JSON
# safety, timestamp parsing, task-field catalogs, and old snapshot compatibility.
# Be very careful when changing field names or runtime-field exclusions.
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


def task_to_serializable_dict(task):
    """Convert one task object to the current JSON-safe snapshot dictionary.

    This preserves the existing save behavior: iterate over live task attributes,
    skip runtime-only fields, sanitize every stored value, and keep the warning for
    missing critical derived fields.
    """
    d = {}
    # Iterate through all attributes, excluding non-serializable threading objects
    for k, v in task.__dict__.items():
        # Skip threading/synchronization objects and internal caches
        if k in RUNTIME_TASK_FIELDS:
            continue

        # Apply sanitize_for_json to ALL values (handles datetime, NumPy, NaN, etc.)
        d[k] = sanitize_for_json(v)

    # Debug: Verify critical fields are present
    if 'hit_1' not in d:
        print(f"WARNING: Task {task.task_id[:8]} missing 'hit_1' in save! Current value: {getattr(task, 'hit_1', 'MISSING')}")

    return d


def tasks_to_serializable_snapshot(tasks):
    """Convert live task objects into the list persisted by save_tasks_to_json()."""
    return [task_to_serializable_dict(t) for t in (tasks or [])]


def write_json_atomic(filepath, data):
    """Write JSON through a temp file and atomic replace, preserving crash safety."""
    temp_path = filepath + ".tmp"
    try:
        with open(temp_path, 'w', encoding='utf-8') as f:
            # All data is pre-sanitized, no need for default=str
            json.dump(data, f, indent=2)
        os.replace(temp_path, filepath)
    except Exception:
        if os.path.exists(temp_path):
            os.remove(temp_path)  # Delete broken temp file
        raise


# =============================================================================
# END JSON PERSISTENCE LAYER
# =============================================================================

# DuckDB availability is now imported from database module
# See: from database import DUCKDB_AVAILABLE

# =============================================================================
# 6. APPLICATION CONFIGURATION AND RUNTIME CONSTANTS
# =============================================================================
# Configuration remains in this file for now. Future refactors should move code
# toward smaller sections first, not new files, to preserve callback wiring.
# =============================================================================
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

# Keep verbose per-render tracing disabled by default. Printing dozens of trace
# lines on every page/table render can noticeably slow older machines and does
# not affect business logic. Set True only when profiling locally.
PERF_TRACE_ENABLED = False
# Informational only: used in optional chart tracing, never to reject or delay a render.
CHART_RENDER_PERF_BUDGET_SECONDS = 1.0
INTERACTION_TRACE_ENABLED = os.environ.get("GPT_INTERACTION_TRACE", "0").strip().lower() in {"1", "true", "yes", "on"}
# Always retain a small in-app diagnostic history; printing remains opt-in.
UI_INTERACTION_TRACE_EVENTS = deque(maxlen=120)


def interaction_trace(message):
    event = f"{datetime.now().strftime('%H:%M:%S')} | {message}"
    UI_INTERACTION_TRACE_EVENTS.append(event)
    if INTERACTION_TRACE_ENABLED:
        print(f"[UI-TRACE] {event}")


def perf_log(message):
    if PERF_TRACE_ENABLED:
        print(message)


class PerfTimer:
    """High-precision timer for optional performance tracing."""
    def __init__(self, label):
        self.label = label
        self.start_time = None
        self.last_time = None
        
    def start(self):
        self.start_time = time.perf_counter()
        self.last_time = self.start_time
        perf_log(f"[TRACE] ⏱️  START: {self.label}")
        return self
        
    def check(self, step_name):
        current = time.perf_counter()
        elapsed = current - self.last_time
        total = current - self.start_time
        perf_log(f"[TRACE]    └─ {step_name}: {elapsed:.4f}s (Total: {total:.4f}s)")
        self.last_time = current
        return self
        
    def end(self):
        if self.start_time:
            total = time.perf_counter() - self.start_time
            perf_log(f"[TRACE] ✅ END: {self.label} ({total:.4f}s)")
        return self


# =============================================================================
# 7. TASK FIELD CATALOG FOR JSON / RECALC DURABILITY
# =============================================================================
# Documentation-first catalog preserving current broad JSON snapshot behavior.
# Classify new task attributes here before changing save/load or recalculation.
# =============================================================================

# ---------- Task field catalog (documentation-first; preserves current behavior) ----------
# These groups make JSON/recalc changes safer by naming the field types in one
# place. They do not change formulas, event detection, downloading, validation,
# or the current broad JSON snapshot behavior. The catalog is intentionally
# evolvable: when new formulas/events/table columns add task attributes, classify
# them here so old JSON snapshots can still load and then be recalculated into a
# new JSON snapshot with the new derived data.
STATIC_TASK_FIELDS = {
    "task_id", "symbols", "timeframe", "mode", "start_date", "end_date",
    "overwrite", "price_continuity_check", "signal_time", "signal_price",
    "signal_symbol", "signal_direction", "analyze_beyond", "enable_strategy",
    "enable_impulse", "pre_buffer_minutes",
}

DERIVED_TASK_FIELDS = {
    "first_event_time", "first_event_type", "first_event_is_pin", "first_event_close",
    "price_change_pct", "reached_level", "reversed_direction", "events",
    "strategy_signals", "strategy_log_summary", "strategy_confidence",
    "hit_1", "hit_1_5", "hit_2",
    "first_hit_1_expected", "first_hit_1_5_expected", "first_hit_2_expected",
    "first_hit_1_expected_time", "first_hit_1_5_expected_time", "first_hit_2_expected_time",
    "first_hit_1_opposite", "first_hit_1_5_opposite", "first_hit_2_opposite",
    "first_hit_1_opposite_time", "first_hit_1_5_opposite_time", "first_hit_2_opposite_time",
    "drawdown_before_level", "drawdown_before_level_time",
    "drawdown_before_1pct", "drawdown_before_1pct_time",
    "drawdown_before_1_5pct", "drawdown_before_1_5pct_time",
    "drawdown_before_2pct", "drawdown_before_2pct_time",
    "max_adverse_move_pct", "max_adverse_time",
    "max_expected_move_pct", "max_expected_time",
    "max_adverse_before_return_pct", "max_adverse_before_return_time",
    "returned_to_signal", "max_adverse_sgnl_pct", "max_adverse_sgnl_time",
    "max_adverse_before_return_sgnl_pct", "max_adverse_before_return_sgnl_time",
    "drawdown_before_return_sgnl_pct", "drawdown_before_return_sgnl_time",
    "returned_to_sgnl", "max_expected_sgnl_pct", "max_expected_sgnl_time",
    "toward_entry_direction", "toward_entry_price", "toward_entry_time",
    "toward_stop_loss_price", "toward_stop_loss_hit", "toward_stop_loss_time",
    "toward_max_reached_pct", "toward_level_reached", "toward_no_stop_returned_entry",
}

# Internal state currently preserved by the broad JSON snapshot for backward
# compatibility. Do not move these into RUNTIME_TASK_FIELDS unless intentionally
# changing JSON/recalc persistence behavior.
INTERNAL_SNAPSHOT_TASK_FIELDS = {"_batches_since_flush"}

STATE_TASK_FIELDS = {
    "status", "progress", "log", "total_candles", "downloaded_candles",
    "paused", "last_ts", "last_count",
}

UI_TASK_FIELDS = {"log_events", "hide_logs"}

# Current JSON/recalc exclusion list. Keep this exact unless intentionally changing
# backward compatibility or runtime persistence behavior.
RUNTIME_TASK_FIELDS = {
    "stop_event", "pause_event", "state_lock", "raw_batches",
    "_chart_cache", "symbol_ranges",
    "_loaded_from_json", "_loaded_source_json", "_prepared_for_new_json",
}

TASK_DATETIME_FIELDS = {
    "start_date", "end_date", "first_event_time", "max_adverse_time",
    "max_expected_time", "max_adverse_sgnl_time", "max_expected_sgnl_time",
    "max_adverse_before_return_time", "max_adverse_before_return_sgnl_time",
    "drawdown_before_level_time", "drawdown_before_1pct_time",
    "drawdown_before_1_5pct_time", "drawdown_before_2pct_time",
}

TASK_INIT_FIELDS = (
    "task_id", "symbols", "timeframe", "mode", "start_date", "end_date",
    "overwrite", "price_continuity_check", "signal_time", "signal_price",
    "signal_symbol", "signal_direction", "analyze_beyond", "enable_strategy",
    "enable_impulse", "pre_buffer_minutes", "log_events", "hide_logs",
)

SERIALIZED_TASK_FIELDS = (
    STATIC_TASK_FIELDS
    | DERIVED_TASK_FIELDS
    | STATE_TASK_FIELDS
    | UI_TASK_FIELDS
    | INTERNAL_SNAPSHOT_TASK_FIELDS
)

TASK_KNOWN_FIELDS = SERIALIZED_TASK_FIELDS | RUNTIME_TASK_FIELDS


def get_unclassified_task_fields(tasks):
    """Return task attributes not covered by the field catalog. No behavior changes."""
    unknown = set()
    for task in tasks or []:
        if hasattr(task, "__dict__"):
            unknown.update(set(task.__dict__) - TASK_KNOWN_FIELDS)
    return unknown


def report_unclassified_task_fields(tasks, reason=""):
    """Log catalog gaps so future JSON/recalc changes can be made safely."""
    unknown = get_unclassified_task_fields(tasks)
    if unknown:
        print(f"⚠️ [FIELD CATALOG] {reason or '-'}: unclassified task fields: {sorted(unknown)}")
    return unknown

def _snapshot_field_names(item):
    """Return field names from a JSON dict or task object without mutating it."""
    if isinstance(item, dict):
        return set(item.keys())
    if hasattr(item, "__dict__"):
        return set(item.__dict__.keys())
    return set()


def audit_task_snapshot_compatibility(items, reason="", max_fields=8):
    """Summarize old-JSON/new-formula compatibility gaps without changing data.

    This intentionally inspects only field names. It does not calculate formulas,
    fill defaults, clear fields, publish Golden Store data, or touch task state.
    Missing derived fields are expected when opening an older JSON after adding a
    new formula/event/table column; recalculation can populate them later.
    """
    records = list(items or [])
    summary = {
        "reason": reason or "-",
        "total_items": len(records),
        "unknown_fields": [],
        "missing_static_fields": {},
        "missing_derived_fields": {},
        "recalc_recommended": False,
    }
    if not records:
        return summary

    unknown = set()
    missing_static = {}
    missing_derived = {}
    for item in records:
        fields = _snapshot_field_names(item)
        if not fields:
            continue
        unknown.update(fields - TASK_KNOWN_FIELDS)
        for field in STATIC_TASK_FIELDS:
            if field not in fields:
                missing_static[field] = missing_static.get(field, 0) + 1
        for field in DERIVED_TASK_FIELDS:
            if field not in fields:
                missing_derived[field] = missing_derived.get(field, 0) + 1

    summary["unknown_fields"] = sorted(unknown)
    summary["missing_static_fields"] = dict(sorted(missing_static.items()))
    summary["missing_derived_fields"] = dict(sorted(missing_derived.items()))
    summary["recalc_recommended"] = bool(missing_derived)

    label = reason or "-"
    if unknown:
        shown = sorted(unknown)[:max_fields]
        suffix = "..." if len(unknown) > max_fields else ""
        print(f"⚠️ [SNAPSHOT AUDIT] {label}: unknown fields not in catalog: {shown}{suffix}")
    if missing_static:
        shown = list(summary["missing_static_fields"].items())[:max_fields]
        suffix = "..." if len(missing_static) > max_fields else ""
        print(f"⚠️ [SNAPSHOT AUDIT] {label}: missing static fields: {shown}{suffix}")
    if missing_derived:
        shown_fields = list(summary["missing_derived_fields"].keys())[:max_fields]
        affected_count = max(missing_derived.values()) if missing_derived else 0
        suffix = ", ..." if len(missing_derived) > max_fields else ""
        print(
            f"ℹ️ [SNAPSHOT AUDIT] {label}: Loaded JSON is compatible. "
            f"{affected_count} task(s) are missing newer calculated field(s): "
            f"{', '.join(shown_fields)}{suffix}. "
            "Run recalculation only if you need these fields, then save a new JSON."
        )
    return summary


def format_snapshot_audit_note(audit):
    """Return a short UI-safe note for compatibility findings."""
    if not audit:
        return ""
    parts = []
    missing_derived = audit.get("missing_derived_fields") or {}
    unknown = audit.get("unknown_fields") or []
    if missing_derived:
        affected_count = max(missing_derived.values()) if missing_derived else 0
        fields = ", ".join(list(missing_derived.keys())[:4])
        suffix = ", ..." if len(missing_derived) > 4 else ""
        parts.append(
            f"ℹ️ Loaded JSON is compatible. {affected_count} task(s) are missing newer calculated field(s): "
            f"{fields}{suffix}. Run recalculation only if you need these fields, then save a new JSON."
        )
    if unknown:
        parts.append(f"⚠️ {len(unknown)} uncatalogued field(s) found; data was loaded unchanged.")
    return " | ".join(parts)


# =============================================================================
# 8. GOLDEN STORE, RECALC STATE, AND DISPLAY CACHE STATE
# =============================================================================
# Golden Store is the authoritative *in-memory display snapshot* for task
# table/stat callbacks. It is safe for UI refresh and background publication,
# but it is not durable storage across app restarts; JSON snapshots remain the
# durable persistence layer. Prefer publishing through
# publish_golden_task_snapshot() or bump_golden_store_version() so version bumps
# and cache resets stay synchronized. Recalc/display globals are documented here
# before deeper state-container refactors.
# =============================================================================

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

# Strategy-checkup source caches live with display caches because they are
# read-only views of the current Golden Store task/data snapshot. Keep these
# bounded: diagnostics should get faster on repeated parameter runs without
# becoming an unbounded in-memory database.
OSCILLATOR_REVERSAL_SOURCE_CACHE_MAX = 32
OSCILLATOR_REVERSAL_SOURCE_CACHE_MAX_BYTES = 192 * 1024 * 1024
oscillator_reversal_source_cache = OrderedDict()
oscillator_reversal_source_cache_bytes = 0

# Conservative chart caches for older machines: source entries are limited by
# both count and total DataFrame memory, never just by number of coin pairs.
# Entries are still invalidated by parquet mtime/size.
CHART_PARQUET_CACHE_MAX = 6
CHART_PARQUET_CACHE_MAX_BYTES = 192 * 1024 * 1024
chart_parquet_cache = OrderedDict()
chart_parquet_cache_bytes = 0
CHART_FILE_END_CACHE_MAX = 48
chart_file_end_cache = OrderedDict()
CHART_TASK_INDICATOR_CACHE_MAX = 2
chart_task_indicator_cache = OrderedDict()
# Warm one neighbouring range while the user studies the current chart. The
# source cache is byte-bounded, so this is safe on older Macs and makes the
# first Next/Previous action much faster. Set GPT_CHART_PREFETCH=0 to disable.
CHART_PREFETCH_ENABLED = os.environ.get("GPT_CHART_PREFETCH", "1") == "1"
# Let the foreground chart read claim an older SSD before optional neighbour
# warm-up begins.  Set to 0 only on machines with fast storage.
CHART_PREFETCH_DELAY_SECONDS = max(0.0, float(os.environ.get("GPT_CHART_PREFETCH_DELAY", "2.0")))
chart_prefetch_pending = set()
chart_prefetch_lock = threading.Lock()

def _chart_dataframe_bytes(df):
    """Return an accurate-enough in-memory size for a cached DataFrame."""
    try:
        return int(df.memory_usage(index=True, deep=True).sum())
    except Exception:
        return 0

def retain_chart_task_indicator_cache(task):
    """Keep lazy indicator data for only the active chart and one recent chart."""
    task_id = str(getattr(task, "task_id", ""))
    if not task_id:
        return
    chart_task_indicator_cache[task_id] = task
    chart_task_indicator_cache.move_to_end(task_id)
    while len(chart_task_indicator_cache) > CHART_TASK_INDICATOR_CACHE_MAX:
        _, evicted_task = chart_task_indicator_cache.popitem(last=False)
        if evicted_task is not task and hasattr(evicted_task, "_chart_cache"):
            evicted_task._chart_cache.clear()

def get_chart_file_end_timestamp(fp):
    """Return a parquet file's latest timestamp without rescanning it per task.

    Tasks for the same pair/timeframe often have no explicit end date.  The old
    chart path read the timestamp column every time the user pressed Next,
    even though the answer only changes when the parquet file changes.
    """
    stat = os.stat(fp)
    cache_key = (fp, stat.st_mtime_ns, stat.st_size)
    cached = chart_file_end_cache.get(cache_key)
    if cached is not None:
        chart_file_end_cache.move_to_end(cache_key)
        return cached

    # Retire cached bounds for an older version of this file.
    for old_key in [key for key in chart_file_end_cache if key[0] == fp and key != cache_key]:
        chart_file_end_cache.pop(old_key, None)
    timestamps = pd.read_parquet(fp, columns=["timestamp"])
    if timestamps.empty:
        return None
    latest = int(timestamps["timestamp"].max())
    chart_file_end_cache[cache_key] = latest
    chart_file_end_cache.move_to_end(cache_key)
    while len(chart_file_end_cache) > CHART_FILE_END_CACHE_MAX:
        chart_file_end_cache.popitem(last=False)
    return latest

def read_chart_parquet_cached(fp, start_ms=None, end_ms=None):
    """Read only the chart period, with a bounded mtime-aware cache.

    Market-data files can contain years of one-minute candles. Reading the
    entire file before slicing a task period made the first chart open compete
    with the UI and old SSD for several seconds. Parquet predicate filters keep
    the chart read-only and preserve the exact same inclusive time bounds while
    allowing PyArrow to skip unrelated row groups.
    """
    global chart_parquet_cache_bytes
    stat = os.stat(fp)
    cache_key = (fp, stat.st_mtime_ns, stat.st_size, start_ms, end_ms)
    cached = chart_parquet_cache.get(cache_key)
    if cached is not None:
        chart_parquet_cache.move_to_end(cache_key)
        return cached

    # Drop stale file versions, but retain other cached task ranges from the
    # current immutable parquet version for fast previous/next navigation.
    for old_key in [
        key for key in chart_parquet_cache
        if key[0] == fp and (key[1] != stat.st_mtime_ns or key[2] != stat.st_size)
    ]:
        stale_df = chart_parquet_cache.pop(old_key, None)
        chart_parquet_cache_bytes -= _chart_dataframe_bytes(stale_df) if stale_df is not None else 0

    filters = []
    if start_ms is not None:
        filters.append(("timestamp", ">=", int(start_ms)))
    if end_ms is not None:
        filters.append(("timestamp", "<=", int(end_ms)))
    df = pd.read_parquet(fp, filters=filters or None)
    df_bytes = _chart_dataframe_bytes(df)
    # A single oversized range is returned to the current chart but is not
    # retained, preventing one long history window from exhausting RAM.
    if df_bytes <= CHART_PARQUET_CACHE_MAX_BYTES:
        chart_parquet_cache[cache_key] = df
        chart_parquet_cache_bytes += df_bytes
        chart_parquet_cache.move_to_end(cache_key)
        while (len(chart_parquet_cache) > CHART_PARQUET_CACHE_MAX or
               chart_parquet_cache_bytes > CHART_PARQUET_CACHE_MAX_BYTES):
            _, evicted_df = chart_parquet_cache.popitem(last=False)
            chart_parquet_cache_bytes -= _chart_dataframe_bytes(evicted_df)
    return df

def prefetch_chart_source(task):
    """Warm one neighbouring task's source data without blocking the UI."""
    if not task or not getattr(task, "signal_time", None):
        return
    try:
        fp = os.path.join(symbol_timeframe_path(task.symbols[0], task.timeframe), "data.parquet")
        if not os.path.exists(fp):
            return
        start_ms = task_pre_signal_start_ms(task)
        end_ms = (int(task.end_date.replace(tzinfo=timezone.utc).timestamp() * 1000)
                  if task.end_date else get_chart_file_end_timestamp(fp))
        if end_ms is not None:
            read_chart_parquet_cached(fp, start_ms, end_ms)
    except Exception:
        # Prefetch is optional; it must never affect foreground navigation.
        return

def prefetch_chart_source_async(task):
    """Start at most one background warm-up for each task id."""
    if not CHART_PREFETCH_ENABLED:
        return
    task_id = str(getattr(task, "task_id", ""))
    if not task_id:
        return
    with chart_prefetch_lock:
        if task_id in chart_prefetch_pending:
            return
        chart_prefetch_pending.add(task_id)

    def _warm():
        try:
            # ``set_chart_task_id`` launches this at the same time Dash starts
            # the current chart callback. Without a short delay two parquet
            # reads can contend for a slow SSD and make *both* charts slower.
            if CHART_PREFETCH_DELAY_SECONDS:
                time.sleep(CHART_PREFETCH_DELAY_SECONDS)
            prefetch_chart_source(task)
        finally:
            with chart_prefetch_lock:
                chart_prefetch_pending.discard(task_id)

    threading.Thread(target=_warm, name="ChartPrefetch", daemon=True).start()

STRATEGY_SETTINGS_DIR = os.path.join(os.path.dirname(os.path.abspath(__file__)), "strategy_settings")
OSCILLATOR_SETTINGS_IDS = [
    "osc-stoch-14-level-input", "osc-stoch-14-condition-input", "osc-stoch-40-level-input", "osc-stoch-40-condition-input",
    "osc-stoch-60-level-input", "osc-stoch-60-condition-input", "osc-stoch-300-level-input", "osc-stoch-300-condition-input", "osc-rsi-level-input", "osc-rsi-condition-input",
    "osc-down-stoch-14-level-input", "osc-down-stoch-14-condition-input", "osc-down-stoch-40-level-input", "osc-down-stoch-40-condition-input",
    "osc-down-stoch-60-level-input", "osc-down-stoch-60-condition-input", "osc-down-stoch-300-level-input", "osc-down-stoch-300-condition-input", "osc-down-rsi-level-input", "osc-down-rsi-condition-input",
    "osc-reversal-sl-input", "osc-reversal-max-dd-input", "osc-reversal-tp-levels-input", "osc-reversal-trail-rules-input",
    "osc-reversal-sl-grid-input", "osc-entry-window-input", "osc-exit-window-input", "osc-exit-enabled-input",
    "osc-exit-sell-stoch-14-level-input", "osc-exit-sell-stoch-14-condition-input", "osc-exit-sell-stoch-40-level-input", "osc-exit-sell-stoch-40-condition-input",
    "osc-exit-sell-stoch-60-level-input", "osc-exit-sell-stoch-60-condition-input", "osc-exit-sell-stoch-300-level-input", "osc-exit-sell-stoch-300-condition-input", "osc-exit-buy-stoch-14-level-input", "osc-exit-buy-stoch-14-condition-input",
    "osc-exit-buy-stoch-40-level-input", "osc-exit-buy-stoch-40-condition-input", "osc-exit-buy-stoch-60-level-input", "osc-exit-buy-stoch-60-condition-input", "osc-exit-buy-stoch-300-level-input", "osc-exit-buy-stoch-300-condition-input",
    "osc-reversal-notional-input", "osc-reversal-cost-input", "osc-reversal-open-return-input",
    "osc-research-entry-windows-input", "osc-research-exit-windows-input", "osc-research-sl-grid-input", "osc-research-stop-presets-input",
    "osc-research-max-combos-input", "osc-research-top-input",
]

def _safe_strategy_settings_name(name):
    cleaned = re.sub(r"[^A-Za-z0-9_. -]+", "_", str(name or "")).strip().strip(".")
    return cleaned[:80] or None

def list_strategy_setting_names():
    os.makedirs(STRATEGY_SETTINGS_DIR, exist_ok=True)
    names = []
    for path in sorted(glob.glob(os.path.join(STRATEGY_SETTINGS_DIR, "*.json"))):
        names.append(os.path.splitext(os.path.basename(path))[0])
    return names

def strategy_setting_options():
    return [{"label": name, "value": name} for name in list_strategy_setting_names()]

def strategy_setting_path(name):
    safe_name = _safe_strategy_settings_name(name)
    if not safe_name:
        return None
    return os.path.join(STRATEGY_SETTINGS_DIR, f"{safe_name}.json")

# Global stats cache for ALL tasks (calculated once per data version)
cached_signal_stats_html = None  # Full Signal Performance Summary table
cached_toward_strategy_stats_html = None  # Separate toward-level strategy summary table
cached_small_stats_data = None   # Small summary stats dict
stats_cache_version = -1         # Version of data these stats belong to



def reset_display_caches(reason=""):
    """Clear UI-only rendered page, summary, and diagnostic source caches."""
    global _cached_golden_version, cached_signal_stats_html, cached_toward_strategy_stats_html, cached_small_stats_data, stats_cache_version, oscillator_reversal_source_cache_bytes
    if "_page_html_cache" in globals():
        _page_html_cache.clear()
    _cached_golden_version = None
    cached_signal_stats_html = None
    cached_toward_strategy_stats_html = None
    cached_small_stats_data = None
    stats_cache_version = -1
    if "oscillator_reversal_source_cache" in globals():
        oscillator_reversal_source_cache.clear()
        oscillator_reversal_source_cache_bytes = 0
    if reason:
        print(f"🔄 [GOLDEN] Display caches reset: {reason}")


def get_golden_store_version():
    """Return the current Golden Store version used by UI cache keys."""
    return golden_store_version


def has_golden_task_snapshot():
    """Return True when Golden Store currently has a non-empty task snapshot."""
    return golden_task_store_data is not None and len(golden_task_store_data) > 0


def get_golden_task_snapshot():
    """Return the current Golden Store snapshot without falling back to TaskManager."""
    return golden_task_store_data if golden_task_store_data is not None else []


def get_golden_task_count():
    """Return the number of tasks currently held by the Golden Store snapshot."""
    return len(golden_task_store_data) if golden_task_store_data is not None else 0




def bump_golden_store_version(reason="version_bump"):
    """Bump the in-memory Golden Store version and clear derived UI caches.

    Use this for cases where task objects were mutated in place and the existing
    Golden Store list still points at the same objects. Full snapshot replacement
    should continue to use publish_golden_task_snapshot().
    """
    global golden_store_version
    golden_store_version += 1
    reset_display_caches(reason or "version_bump")
    return golden_store_version

def publish_golden_task_snapshot(tasks, reason="", bump_version=True):
    """Publish the final task snapshot used by UI callbacks and reset display caches.

    This is intentionally small and behavior-preserving: it only centralizes the
    existing global Golden Store assignment, version bump, and cache clearing.
    """
    global golden_task_store_data, golden_store_version
    golden_task_store_data = list(tasks)
    report_unclassified_task_fields(golden_task_store_data, reason=f"publish:{reason or '-'}")
    if bump_version:
        bump_golden_store_version(reason or "publish")
    else:
        reset_display_caches(reason or "publish")
    print(f"🔄 [GOLDEN] Published {len(golden_task_store_data)} tasks, version={golden_store_version}, reason={reason or '-'}")
    return golden_store_version


def get_display_tasks_snapshot():
    """Return the Golden Store task snapshot, falling back to TaskManager if empty."""
    if has_golden_task_snapshot():
        return get_golden_task_snapshot()
    with tm.lock:
        return list(tm.tasks.values())

# =============================================================================
# 9. DATA ACCESS, PARQUET CACHE, AND MARKET API HELPERS
# =============================================================================
# Data I/O helpers stay separate from UI callbacks and math. They may load, write,
# merge, or fetch candles but should not render Dash components.
# =============================================================================

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
    try:
        df = _load_parquet_cached(fp, mtime).copy()
    except Exception as exc:
        # A partially written/corrupted parquet file (for example ZSTD
        # decompression failure) should not crash diagnostics or UI callbacks.
        # Clear the small LRU cache in case the failing reader state was cached,
        # report the affected file, and let callers treat this task as no-data.
        clear_parquet_cache()
        print(f"⚠️ [CACHE] Failed to read parquet for {sym} {task.timeframe}: {fp} ({exc})")
        return pd.DataFrame()
    
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


# ---------- Canonical task-window policy (chart, events, strategies, optimizers) ----------
def task_pre_signal_start_ms(task):
    """Return the requested history start without changing the task's end window."""
    signal_time = getattr(task, "signal_time", None)
    if signal_time is not None:
        minutes = max(0, int(getattr(task, "pre_buffer_minutes", 0) or 0))
        return max(0, int(float(signal_time)) - minutes * 60_000)
    start_date = getattr(task, "start_date", None)
    return int(start_date.replace(tzinfo=timezone.utc).timestamp() * 1000) if start_date else 0


def task_signal_window_bounds_ms(task, pre_signal_minutes=None):
    """Return the established inclusive strategy/impulse boundaries in milliseconds.

    This pure boundary helper is the maintenance point for future formulas and
    tests. ``pre_signal_minutes`` remains an explicit override for legacy callers
    that intentionally use ``SIGNAL_BUFFER_MINUTES`` rather than the task value.
    """
    if getattr(task, "signal_time", None) is None:
        return None, None
    minutes = (
        getattr(task, "pre_buffer_minutes", 0)
        if pre_signal_minutes is None
        else pre_signal_minutes
    )
    buffer_ms = minutes * 60 * 1000
    start_ms = max(0, task.signal_time - buffer_ms)
    cutoff_time = None
    if task.start_date and task.end_date:
        window_len_ms = (
            int(task.end_date.replace(tzinfo=timezone.utc).timestamp() * 1000)
            - int(task.start_date.replace(tzinfo=timezone.utc).timestamp() * 1000)
        )
        cutoff_time = task.signal_time + window_len_ms
    return start_ms, cutoff_time


def slice_task_signal_window(task, frame, pre_signal_minutes=None):
    """Slice an already-loaded frame using the canonical task window."""
    if frame is None or frame.empty:
        return frame.copy() if frame is not None else pd.DataFrame()
    start_ms, cutoff_time = task_signal_window_bounds_ms(task, pre_signal_minutes)
    if start_ms is None:
        return frame.iloc[0:0].copy()
    mask = frame["timestamp"] >= start_ms
    if cutoff_time is not None:
        mask &= frame["timestamp"] <= cutoff_time
    return frame.loc[mask].copy()


def read_task_signal_window(file_path, task, pre_signal_minutes=None):
    """Predicate-read only the canonical task window to protect slow disks and RAM."""
    start_ms, cutoff_time = task_signal_window_bounds_ms(task, pre_signal_minutes)
    if start_ms is None:
        return pd.DataFrame()
    filters = [("timestamp", ">=", start_ms)]
    if cutoff_time is not None:
        filters.append(("timestamp", "<=", cutoff_time))
    frame = pd.read_parquet(file_path, filters=filters)
    # Keep a defensive in-memory slice so correctness does not depend solely on
    # parquet-engine predicate behavior.
    return slice_task_signal_window(task, frame, pre_signal_minutes)

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

# =============================================================================
# 10. SIGNAL PARSING
# =============================================================================
# Parsing converts user/file text into normalized signal dictionaries only. It
# should not create tasks, mutate Golden Store, or render UI.
# =============================================================================

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

# =============================================================================
# 11. TASK MODEL AND TASK EXECUTION LOGIC
# =============================================================================
# DownloadTask currently owns task state, download execution, analysis, and logs.
# Keep original behavior intact; future internal refactors should split large
# methods into helpers before moving code to separate files.
# =============================================================================

# ---------- Task Model ----------
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
        reset_toward_level_strategy_fields(self)
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
                df_limited = read_task_signal_window(fp, self)
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
        df_limited = read_task_signal_window(fp, self)
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
        
        reset_toward_level_strategy_fields(self)
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

        calculate_toward_level_strategy(self, df)

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
            bump_golden_store_version("task_analysis_complete")
        except Exception:
            pass

from concurrent.futures import ThreadPoolExecutor, as_completed

# =============================================================================
# 12. TASK AND OPTIMIZER MANAGERS
# =============================================================================
# Runtime managers own queues/background jobs. Keep singleton creation explicit
# so callbacks continue to share the same task and optimizer state.
# =============================================================================

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

# =============================================================================
# 13. DASH APP, FLASK ROUTES, AND ROOT LAYOUT
# =============================================================================
# The app object and decorated callbacks/routes must stay after app creation.
# Component IDs in layout are part of the callback contract; do not rename them
# during organization-only refactors.
# =============================================================================

# ---------- Dash App ----------
app = dash.Dash(__name__, suppress_callback_exceptions=True, prevent_initial_callbacks='initial_duplicate')


@app.server.before_request
def start_chart_dash_response_timer():
    """Time the full Dash figure response, including JSON serialization."""
    if request.path != "/_dash-update-component":
        return
    payload = request.get_json(silent=True) or {}
    output = str(payload.get("output") or "")
    if "task-chart.figure" in output:
        g.chart_dash_output = output
        g.chart_dash_started_at = time.perf_counter()


@app.server.after_request
def trace_chart_dash_response(response):
    """Expose the gap between callback computation and the serialized response."""
    started_at = getattr(g, "chart_dash_started_at", None)
    if started_at is not None:
        elapsed_ms = round((time.perf_counter() - started_at) * 1000)
        size = response.calculate_content_length()
        interaction_trace(
            f"chart Dash response total_ms={elapsed_ms} bytes={size if size is not None else 'streamed'}"
        )
    return response

# Dash 4 can intermittently fail to resolve dynamically generated inline
# clientside callback functions after a hot reload ("undefined.apply" in the
# renderer). This application is running on an affected Dash 4 renderer, so
# do not register dynamically generated inline callbacks by default. Direct
# DOM handlers keep button/store updates and Measure draw mode available. Only
# opt in with GPT_ENABLE_INLINE_DASH_CALLBACKS=1 after validating the deployed
# Dash renderer version in a browser.
INLINE_DASH_CLIENTSIDE_CALLBACKS_ENABLED = os.environ.get("GPT_ENABLE_INLINE_DASH_CALLBACKS", "0").strip().lower() in {"1", "true", "yes", "on"}
# Legacy Stores remain authoritative during the migration. A live aggregation
# callback adds an extra Dash request to every toolbar click, so it is opt-in
# for future controls that genuinely consume the grouped snapshot.
CHART_UI_STATE_LEGACY_SYNC_ENABLED = os.environ.get("GPT_ENABLE_CHART_UI_STATE_SYNC", "0").strip().lower() in {"1", "true", "yes", "on"}
# Debug bundles use React's development renderer and are noticeably slow when
# replacing a large table or Plotly figure. Production mode is the safe default;
# developers can opt in locally with GPT_DASH_DEBUG=1.
DASH_DEBUG_ENABLED = os.environ.get("GPT_DASH_DEBUG", "0").strip().lower() in {"1", "true", "yes", "on"}

def register_browser_callback(*args, **kwargs):
    if INLINE_DASH_CLIENTSIDE_CALLBACKS_ENABLED:
        return dash_clientside_callback(*args, **kwargs)
    return None

@app.callback(
    Output("ui-trace-output", "children"),
    Input("ui-trace-interval", "n_intervals"),
    prevent_initial_call=False,
)
def render_ui_trace(_):
    """Show recent server-side chart interactions for non-technical debugging."""
    events = list(UI_INTERACTION_TRACE_EVENTS)
    return "\n".join(events[-40:]) if events else "No chart events yet. Open a chart or click a toolbar button."


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
def build_index_string():
    """Build the Dash HTML shell and client-side table/chart helpers.

    UI layout builder only: keep business logic, calculations, callbacks,
    Golden Store updates, and Dash component IDs out of this function.
    """
    return '''
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
/* Active chart row light blue – controlled by chart modal/navigation */
.chart-active-row td {
    background-color: #bbdefb !important;
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
.chart-button-strip {
    scrollbar-width: none;
    -ms-overflow-style: none;
}
.chart-button-strip::-webkit-scrollbar {
    display: none;
}
.chart-button-strip button {
    box-sizing: border-box;
    display: inline-flex;
    align-items: center;
    justify-content: center;
    flex: 0 0 max-content;
    width: max-content;
    min-width: max-content;
    max-width: none;
    min-height: 34px;
    height: auto;
    line-height: 1.2;
    overflow: visible;
    text-align: center;
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
// Keep this tiny diagnostic listener first. If later chart helper code throws,
// it still proves whether the page shell script reached the browser at all.
window.__gptIndexScriptLoaded = Date.now();
window.__gptEarlyBrowserTrace = [];
window.__gptUiBrowserTrace = [];
window.__gptRenderBrowserTrace = function() {
    const panel = document.getElementById('ui-client-trace-output');
    if (!panel) return;
    const lines = window.__gptEarlyBrowserTrace.concat(window.__gptUiBrowserTrace).slice(-40);
    panel.textContent = lines.join('\\n');
};
window.__gptEarlyTrace = function(message) {
    const line = new Date().toLocaleTimeString() + ' | EARLY | ' + message;
    window.__gptEarlyBrowserTrace.push(line);
    window.__gptRenderBrowserTrace();
};
window.__gptEarlyTrace('page shell script loaded');
document.addEventListener('click', function(event) {
    const target = event.target;
    const id = target && target.closest ? (target.closest('button, th, td') || {}).id : '';
    window.__gptEarlyTrace('capture click target=' + (target && target.tagName ? target.tagName : '?') + ' id=' + (id || '-'));
}, true);
window.setInterval(function() {
    window.__gptRenderBrowserTrace();
}, 500);
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
// Push an action payload into a Dash Store immediately.  The previous
// CustomEvent -> hidden button -> clientside callback bridge can miss clicks
// in some Dash/browser combinations, leaving Chart/Details/Impulse buttons
// visually clickable but with no Store update for the Python callback.
function pushDashStore(storeId, payload, fallbackEventName) {
    const eventPayload = Object.assign({ts: Date.now()}, payload);
    function publish() {
        if (!window.dash_clientside || typeof window.dash_clientside.set_props !== 'function') return false;
        try {
            window.dash_clientside.set_props(storeId, {data: eventPayload});
            return true;
        } catch (error) {
            console.error('Dash set_props failed for store:', storeId, error);
            return false;
        }
    }
    if (publish()) return;
    // Dash can expose set_props a few milliseconds after the page shell and
    // table HTML are visible. Retry once so a main-table Chart click is never
    // lost during startup/hot reload, while keeping the same unique payload.
    window.setTimeout(function() {
        if (!publish()) console.error('Dash set_props is unavailable; cannot update store:', storeId, fallbackEventName);
    }, 80);
}
const chartToggleStores = {
    'toggle-rsi-btn': ['rsi-visible-store', false],
    'toggle-stochastic-btn': ['stochastic-visible-store', false],
    'toggle-volume-btn': ['volume-visible-store', false],
    'toggle-adx-btn': ['adx-visible-store', false],
    'toggle-macd-btn': ['macd-visible-store', false],
    'toggle-disparity-btn': ['disparity-visible-store', false],
    'toggle-strategy-btn': ['strategy-visible-store', false],
    'toggle-chart-info-box-btn': ['chart-info-box-store', false],
    'toggle-oscillator-info-box-btn': ['oscillator-info-box-store', true],
    'toggle-oscillator-sync-info-btn': ['oscillator-sync-info-store', false],
    'toggle-chart-extend-x-btn': ['chart-extend-x-store', false],
    'toggle-chart-focus-entry-btn': ['chart-focus-entry-store', false],
    'toggle-measure-oscillator-range-btn': ['measure-oscillator-range-store', false],
    'toggle-measure-anchor-btn': ['measure-anchor-store', false],
    'toggle-measure-hover-btn': ['measure-hover-store', true],
    'toggle-impulses-btn': ['impulse-visible-store', false],
    'toggle-events-btn': ['events-visible-store', false],
    'toggle-measure-btn': ['measure-mode-store', false]
};
// Dash 4 exposes set_props even when dynamically registered clientside callbacks
// are disabled. Use it for immediate Store writes; a capture listener stops the
// native button event so the server fallback cannot toggle the Store twice.
window.__chartToolbarUsesServerCallbacks = false;
const chartToggleState = {};
function traceUi(message, details) {
    const text = new Date().toLocaleTimeString() + ' | ' + message + (details ? ' | ' + JSON.stringify(details) : '');
    const trace = window.__gptUiBrowserTrace || (window.__gptUiBrowserTrace = []);
    trace.push(text);
    if (trace.length > 30) trace.splice(0, trace.length - 30);
    if (window.__gptRenderBrowserTrace) window.__gptRenderBrowserTrace();
    if (window.localStorage && window.localStorage.getItem('gptTraceUi') === '1') {
        console.debug('[GPT UI TRACE]', message, details || '');
    }
}
traceUi('page script initialized', {loaded: window.__gptIndexScriptLoaded});
function markChartRenderRequested(kind) {
    window.__gptChartRenderRequest = {kind: kind, startedAt: performance.now()};
}
function installDashChartNetworkTrace() {
    if (window.__gptDashChartFetchTraceInstalled || typeof window.fetch !== 'function') return;
    window.__gptDashChartFetchTraceInstalled = true;
    const originalFetch = window.fetch.bind(window);
    window.fetch = function(input, init) {
        const url = typeof input === 'string' ? input : String((input && input.url) || '');
        let output = '';
        try {
            const body = init && init.body;
            if (typeof body === 'string') output = String((JSON.parse(body) || {}).output || '');
        } catch (_) {
            // Diagnostics must never interfere with Dash's request path.
        }
        const isChartFigure = url.indexOf('/_dash-update-component') >= 0 && output.indexOf('task-chart.figure') >= 0;
        const startedAt = isChartFigure ? performance.now() : 0;
        if (isChartFigure) traceUi('chart Dash request sent', {kind: (window.__gptChartRenderRequest || {}).kind || 'external'});
        return originalFetch(input, init).then(function(response) {
            if (isChartFigure) {
                traceUi('chart Dash response received', {
                    elapsed_ms: Math.round(performance.now() - startedAt),
                    bytes: response.headers.get('content-length') || 'chunked'
                });
            }
            return response;
        });
    };
}
installDashChartNetworkTrace();
function installChartBrowserRenderTrace() {
    function attach() {
        const root = document.getElementById('task-chart');
        const plot = root ? (root.querySelector('.js-plotly-plot') || root) : null;
        if (!plot || !window.Plotly || plot.__gptBrowserRenderTraceInstalled || typeof plot.on !== 'function') return;
        plot.__gptBrowserRenderTraceInstalled = true;
        plot.on('plotly_afterplot', function() {
            const request = window.__gptChartRenderRequest;
            const elapsedMs = request ? Math.round(performance.now() - request.startedAt) : null;
            // A figure may emit more than one afterplot event while Plotly
            // settles its layout. Report the first paint for this request.
            if (request) window.__gptChartRenderRequest = null;
            window.requestAnimationFrame(function() {
                traceUi('chart browser applied', {
                    kind: request ? request.kind : 'external',
                    elapsed_ms: elapsedMs,
                    traces: (plot.data || []).length
                });
            });
        });
    }
    attach();
    // Dash replaces the Plotly DOM node after a figure update. The short,
    // bounded poll only attaches an event listener and performs no rendering.
    window.setInterval(attach, 500);
}
installChartBrowserRenderTrace();
function applyLocalToolbarInteraction(button) {
    if (!button || !chartToggleStores[button.id]) return;
    const active = !Boolean(chartToggleState[button.id]);
    chartToggleState[button.id] = active;
    button.__gptOptimisticActive = active;
    // The server remains authoritative for chart panes. Update the control
    // immediately so a request queued behind a large Dash update is visible
    // to the user instead of looking like a lost click.
    button.setAttribute('aria-pressed', active ? 'true' : 'false');
    button.style.background = active ? '#e3f2fd' : 'transparent';
    button.style.borderWidth = active ? '2px' : '1px';
    button.style.fontWeight = active ? 'bold' : 'normal';
    if (chartToggleLabels[button.id]) {
        button.textContent = chartToggleLabels[button.id] + ': ' + (active ? 'On' : 'Off');
    }
    if (button.id !== 'toggle-measure-btn') {
        traceUi('local toolbar pending', {id: button.id, active: active});
        return;
    }
    const root = document.getElementById('task-chart');
    const plot = root ? (root.querySelector('.js-plotly-plot') || root) : null;
    if (plot && window.Plotly) {
        window.Plotly.relayout(plot, {dragmode: active ? 'drawrect' : 'pan'});
    }
    button.textContent = active ? '📐 Measuring' : '📐 Measure';
    traceUi('local measure mode', {active: active});
}
const chartToggleLabels = {
    'toggle-rsi-btn': 'RSI',
    'toggle-stochastic-btn': 'Stoch',
    'toggle-volume-btn': 'Volume',
    'toggle-adx-btn': 'ADX',
    'toggle-macd-btn': 'MACD',
    'toggle-disparity-btn': 'DIX',
    'toggle-strategy-btn': 'Strategy',
    'toggle-impulses-btn': 'Impulses',
    'toggle-events-btn': 'Events'
};
const measureExclusiveButtons = new Set([
    'toggle-rsi-btn', 'toggle-stochastic-btn', 'toggle-volume-btn',
    'toggle-adx-btn', 'toggle-macd-btn', 'toggle-disparity-btn',
    'toggle-strategy-btn', 'toggle-impulses-btn', 'toggle-events-btn',
    'toggle-chart-extend-x-btn', 'toggle-chart-focus-entry-btn',
    'toggle-chart-event-marks-btn'
]);
Object.keys(chartToggleStores).forEach(function(buttonId) {
    chartToggleState[buttonId] = chartToggleStores[buttonId][1];
});
function deactivateMeasureForChartAction() {
    if (!chartToggleState['toggle-measure-btn']) return;
    chartToggleState['toggle-measure-btn'] = false;
    if (window.dash_clientside && typeof window.dash_clientside.set_props === 'function') {
        window.dash_clientside.set_props('measure-mode-store', {data: false});
    }
    const measureButton = document.getElementById('toggle-measure-btn');
    if (measureButton) {
        measureButton.textContent = '📐 Measure';
        measureButton.setAttribute('aria-pressed', 'false');
        measureButton.style.background = 'transparent';
        measureButton.style.borderWidth = '1px';
        measureButton.style.fontWeight = 'normal';
    }
    const root = document.getElementById('task-chart');
    const plot = root ? (root.querySelector('.js-plotly-plot') || root) : null;
    if (plot && window.Plotly) {
        window.Plotly.relayout(plot, {dragmode: 'pan'});
    }
}
function applyChartToggleImmediately(button) {
    if (window.__chartToolbarUsesServerCallbacks) return false;
    const config = chartToggleStores[button.id];
    if (!config || !window.dash_clientside || typeof window.dash_clientside.set_props !== 'function') {
        return false;
    }
    const optimisticActive = button.__gptOptimisticActive;
    let active;
    if (typeof optimisticActive === 'boolean') {
        // applyLocalToolbarInteraction already changed the control appearance.
        // Reuse that value instead of inverting it a second time.
        active = optimisticActive;
        delete button.__gptOptimisticActive;
    } else {
        const label = String(button.textContent || '');
        if (button.id === 'toggle-measure-btn') chartToggleState[button.id] = label.indexOf('Measuring') >= 0;
        if (button.id === 'toggle-measure-anchor-btn') chartToggleState[button.id] = label.indexOf('Snap: On') >= 0;
        if (button.id === 'toggle-measure-hover-btn') chartToggleState[button.id] = label.indexOf('Hover: On') >= 0;
        if (button.id === 'toggle-chart-info-box-btn') chartToggleState[button.id] = label.indexOf('Candle Info: On') >= 0;
        if (button.id === 'toggle-oscillator-info-box-btn') chartToggleState[button.id] = label.indexOf('Osc Info: On') >= 0;
        if (button.id === 'toggle-oscillator-sync-info-btn') chartToggleState[button.id] = label.indexOf('Osc All: On') >= 0;
        if (button.id === 'toggle-chart-extend-x-btn') chartToggleState[button.id] = label.indexOf('Extend X: On') >= 0;
        if (button.id === 'toggle-chart-focus-entry-btn') chartToggleState[button.id] = label.indexOf('Focus Entry: On') >= 0;
        if (button.id === 'toggle-measure-oscillator-range-btn') chartToggleState[button.id] = label.indexOf('Osc Range: On') >= 0;
        if (chartToggleLabels[button.id]) chartToggleState[button.id] = label.indexOf(': On') >= 0;
        active = !Boolean(chartToggleState[button.id]);
    }
    chartToggleState[button.id] = active;
    markChartRenderRequested(button.id);
    window.dash_clientside.set_props(config[0], {data: active});
    button.setAttribute('aria-pressed', active ? 'true' : 'false');
    const warm = button.id === 'toggle-chart-info-box-btn' || button.id === 'toggle-measure-hover-btn';
    const green = button.id === 'toggle-measure-anchor-btn';
    button.style.background = active ? (warm ? '#fff8e1' : (green ? '#e8f5e9' : '#e3f2fd')) : 'transparent';
    button.style.borderWidth = active ? '2px' : '1px';
    if (button.id === 'toggle-measure-btn') {
        button.textContent = active ? '📐 Measuring' : '📐 Measure';
        button.style.fontWeight = active ? 'bold' : 'normal';
        const root = document.getElementById('task-chart');
        const plot = root ? (root.querySelector('.js-plotly-plot') || root) : null;
        if (plot && window.Plotly) {
            if (window.attachNativeMeasureOverlayListeners) window.attachNativeMeasureOverlayListeners(plot);
            window.Plotly.relayout(plot, {dragmode: active ? 'drawrect' : 'pan'});
        }
    }
    if (button.id === 'toggle-chart-info-box-btn') {
        button.textContent = active ? 'Candle Info: On' : 'Candle Info: Off';
        const root = document.getElementById('task-chart');
        const plot = root ? (root.querySelector('.js-plotly-plot') || root) : null;
        if (plot && window.Plotly) {
            (plot.data || []).forEach(function(trace, index) {
                if (!trace || trace.type !== 'candlestick') return;
                window.Plotly.restyle(plot, {
                    hoverinfo: active ? 'all' : 'skip',
                    hovertemplate: active ? '<b>%{x|%Y-%m-%d %H:%M}</b><br>Open: %{open}<br>High: %{high}<br>Low: %{low}<br>Close: %{close}<extra></extra>' : null
                }, [index]);
            });
        }
    }
    if (button.id === 'toggle-oscillator-info-box-btn') button.textContent = active ? 'Osc Info: On' : 'Osc Info: Off';
    if (button.id === 'toggle-oscillator-sync-info-btn') button.textContent = active ? 'Osc All: On' : 'Osc All: Off';
    if (button.id === 'toggle-chart-focus-entry-btn') button.textContent = active ? 'Focus Entry: On' : 'Focus Entry: Off';
    if (button.id === 'toggle-measure-oscillator-range-btn') {
        button.textContent = active ? 'Osc Range: On' : 'Osc Range: Off';
        window.__taskChartOscillatorRangeEnabled = active;
        if (window.showNativeMeasureResultAfterMouseup) window.showNativeMeasureResultAfterMouseup();
    }
    if (chartToggleLabels[button.id]) button.textContent = chartToggleLabels[button.id] + ': ' + (active ? 'On' : 'Off');
    return true;
}

// Dash 4's inline clientside callback registry is disabled by default for
// compatibility, so keep the full-height crosshair and Osc All values on a
// direct DOM listener. This is independent from Dash callback registration.
function installChartCrosshairFallback() {
    if (window.__taskChartCrosshairFallbackInstalled) return;
    window.__taskChartCrosshairFallbackInstalled = true;
    const line = document.createElement('div');
    line.id = 'task-chart-full-pane-crosshair';
    line.style.cssText = 'position:fixed;z-index:10050;display:none;width:0;border-left:1px dashed #666;pointer-events:none;';
    document.body.appendChild(line);
    function clearLabels(root) {
        if (root) root.querySelectorAll('[data-task-chart-oscillator-sync-label="true"]').forEach(function(node) { node.remove(); });
    }
    function asMillis(value) {
        if (value instanceof Date) return value.getTime();
        if (typeof value === 'number') return value;
        const parsed = Date.parse(value);
        return Number.isFinite(parsed) ? parsed : null;
    }
    function nearestIndex(values, target) {
        let best = 0, distance = Infinity;
        (values || []).forEach(function(value, index) {
            const stamp = asMillis(value);
            if (stamp === null) return;
            const nextDistance = Math.abs(stamp - target);
            if (nextDistance < distance) { best = index; distance = nextDistance; }
        });
        return Number.isFinite(distance) ? best : null;
    }
    document.addEventListener('mousemove', function(event) {
        const root = document.getElementById('task-chart');
        const plot = root ? (root.querySelector('.js-plotly-plot') || root) : null;
        if (!plot || !plot._fullLayout || !plot.data) { line.style.display = 'none'; return; }
        const rect = plot.getBoundingClientRect();
        if (event.clientX < rect.left || event.clientX > rect.right || event.clientY < rect.top || event.clientY > rect.bottom) {
            line.style.display = 'none'; clearLabels(root); return;
        }
        line.style.left = event.clientX + 'px'; line.style.top = rect.top + 'px'; line.style.height = rect.height + 'px'; line.style.display = 'block';
        if (!chartToggleState['toggle-oscillator-sync-info-btn']) { clearLabels(root); return; }
        const xaxis = plot._fullLayout.xaxis || {}, range = xaxis.range || [];
        const firstTrace = (plot.data || []).find(function(trace) { return trace && trace.x && trace.x.length; });
        if (!firstTrace || range.length !== 2) return;
        const start = asMillis(range[0]), end = asMillis(range[1]);
        if (start === null || end === null || start === end) return;
        const index = nearestIndex(firstTrace.x, start + (end - start) * ((event.clientX - rect.left) / Math.max(1, rect.width)));
        if (index === null) return;
        clearLabels(root);
        if (window.getComputedStyle(root).position === 'static') root.style.position = 'relative';
        const svg = plot.querySelector('.main-svg'), svgRect = svg ? svg.getBoundingClientRect() : rect, rootRect = root.getBoundingClientRect(), valuesByAxis = {};
        plot.data.forEach(function(trace) {
            const axisId = trace && trace.yaxis ? trace.yaxis : 'y';
            const name = trace && trace.name ? String(trace.name) : '';
            if (!trace || axisId === 'y' || !trace.y || index >= trace.y.length || trace.visible === false || name.startsWith('_')) return;
            const value = Number(trace.y[index]);
            if (!Number.isFinite(value)) return;
            (valuesByAxis[axisId] || (valuesByAxis[axisId] = [])).push((name || 'Value') + ': ' + value.toFixed(Math.abs(value) >= 100 ? 1 : 2));
        });
        Object.keys(valuesByAxis).forEach(function(axisId) {
            const axis = plot._fullLayout['yaxis' + axisId.slice(1)];
            if (!axis || !Number.isFinite(axis._offset)) return;
            const label = document.createElement('div');
            label.dataset.taskChartOscillatorSyncLabel = 'true'; label.textContent = valuesByAxis[axisId].join('\\n');
            label.style.cssText = 'position:absolute;z-index:10052;pointer-events:none;white-space:pre-line;background:rgba(255,255,255,.92);border:1px solid #90a4ae;border-radius:3px;color:#263238;font:11px sans-serif;line-height:1.3;padding:2px 5px;';
            label.style.left = Math.max(0, svgRect.left - rootRect.left + 8) + 'px'; label.style.top = Math.max(0, svgRect.top - rootRect.top + axis._offset + 4) + 'px'; root.appendChild(label);
        });
    }, true);
}
installChartCrosshairFallback();
// Chrome/Plotly compatibility fallback: older Plotly bundles can paint a
// drawrect shape before Dash publishes relayoutData. Read Plotly's own layout
// after mouseup and update the already-rendered result element immediately.
function refreshNativeMeasureResultSoon() {
    window.clearTimeout(window.__taskChartMeasureRefreshTimer);
    window.__taskChartMeasureRefreshTimer = window.setTimeout(function() {
        showNativeMeasureResultAfterMouseup();
    }, 40);
}

function measureShapeKey(shape) {
    if (!shape) return '';
    return [shape.type || 'rect', shape.xref || 'x', shape.yref || 'y', shape.x0, shape.x1, shape.y0, shape.y1]
        .map(function(value) { return String(value); }).join('|');
}

function uniqueMeasureShapes(shapes) {
    const seen = {};
    return (shapes || []).filter(function(shape) {
        if (!shape || (shape.type && shape.type !== 'rect') || shape.x0 == null || shape.x1 == null || shape.y0 == null || shape.y1 == null) return false;
        const key = measureShapeKey(shape);
        if (seen[key]) return false;
        seen[key] = true;
        return true;
    });
}

function selectMeasureShapeAtPointer(plot, event) {
    if (!plot || !plot.layout || !plot._fullLayout) return;
    const xaxis = plot._fullLayout.xaxis, yaxis = plot._fullLayout.yaxis;
    const svg = plot.querySelector('.main-svg');
    if (!xaxis || !yaxis || !svg || !xaxis.d2l || !yaxis.d2l || !xaxis.l2p || !yaxis.l2p) return;
    const base = Math.max(0, Number(plot.__dashBaseShapeCount || 0));
    const shapes = plot.layout.shapes || [];
    const svgRect = svg.getBoundingClientRect();
    let selected = '';
    let bestScore = Infinity;
    shapes.slice(base).forEach(function(shape) {
        if (!shape || (shape.type && shape.type !== 'rect')) return;
        const x0 = svgRect.left + xaxis._offset + xaxis.l2p(xaxis.d2l(shape.x0));
        const x1 = svgRect.left + xaxis._offset + xaxis.l2p(xaxis.d2l(shape.x1));
        const y0 = svgRect.top + yaxis._offset + yaxis.l2p(yaxis.d2l(shape.y0));
        const y1 = svgRect.top + yaxis._offset + yaxis.l2p(yaxis.d2l(shape.y1));
        if (![x0, x1, y0, y1].every(Number.isFinite)) return;
        const left = Math.min(x0, x1), right = Math.max(x0, x1), top = Math.min(y0, y1), bottom = Math.max(y0, y1);
        const tolerance = 8;
        if (event.clientX < left - tolerance || event.clientX > right + tolerance || event.clientY < top - tolerance || event.clientY > bottom + tolerance) return;
        const edgeScore = Math.min(Math.abs(event.clientX - left), Math.abs(event.clientX - right), Math.abs(event.clientY - top), Math.abs(event.clientY - bottom));
        if (edgeScore < bestScore) {
            bestScore = edgeScore;
            selected = measureShapeKey(shape);
        }
    });
    plot.__dashSelectedMeasureShapeKey = selected;
}

function attachNativeMeasureOverlayListeners(plot) {
    if (!plot || plot.__dashMeasureOverlayListenersAttached) return;
    plot.__dashMeasureOverlayListenersAttached = true;
    // Plotly shapes are data-anchored and move correctly by themselves. The
    // HTML labels are pixel-anchored, so redraw them after every zoom, pan,
    // and Extend X relayout to keep each label and pointer on its rectangle.
    if (typeof plot.on === 'function') {
        plot.on('plotly_relayout', refreshNativeMeasureResultSoon);
    }
    // Plotly does not expose a portable selected-shape API across the older
    // bundles we support. Record the clicked user rectangle ourselves so Delete
    // removes that exact box rather than an unrelated newest box.
    plot.addEventListener('mousedown', function(event) { selectMeasureShapeAtPointer(plot, event); }, true);
    if (typeof window.ResizeObserver === 'function') {
        plot.__dashMeasureResizeObserver = new window.ResizeObserver(refreshNativeMeasureResultSoon);
        plot.__dashMeasureResizeObserver.observe(plot);
    } else {
        window.addEventListener('resize', refreshNativeMeasureResultSoon);
    }
}

function showNativeMeasureResultAfterMouseup() {
    window.setTimeout(function() {
        const root = document.getElementById('task-chart');
        const plot = root ? (root.querySelector('.js-plotly-plot') || root) : null;
        if (!plot || !plot.layout) return;
        attachNativeMeasureOverlayListeners(plot);
        const shapes = (plot.layout && plot.layout.shapes) || (plot._fullLayout && plot._fullLayout.shapes) || [];
        const baseCount = Math.max(0, Number(plot.__dashBaseShapeCount || 0));
        // Preserve only user rectangles across indicator figure rebuilds.
        const userShapes = uniqueMeasureShapes(shapes.slice(baseCount));
        window.__taskChartMeasureShapes = userShapes.map(function(item) { return Object.assign({}, item); });
        const shape = userShapes[userShapes.length - 1];
        if (!shape) {
            root.querySelectorAll('[id^="task-chart-measure-label-"], [id^="task-chart-measure-pointer-"], [id^="task-chart-measure-osc-range-"]').forEach(function(node) { node.remove(); });
            return;
        }
        const y0 = Number(shape.y0), y1 = Number(shape.y1);
        if (!Number.isFinite(y0) || !Number.isFinite(y1)) return;
        const delta = y1 - y0, pct = y0 ? delta / y0 * 100 : 0;
        const start = Date.parse(shape.x0), end = Date.parse(shape.x1);
        let timeText = 'time n/a';
        if (Number.isFinite(start) && Number.isFinite(end)) {
            const seconds = Math.abs(end - start) / 1000;
            timeText = seconds < 60 ? Math.round(seconds) + 's' : (seconds < 3600 ? (seconds / 60).toFixed(1) + 'm' : (seconds < 86400 ? (seconds / 3600).toFixed(2) + 'h' : (seconds / 86400).toFixed(2) + 'd'));
        }
        const result = document.getElementById('measure-result');
        const text = '📦 Box ' + (delta >= 0 ? 'Up' : 'Down') + ': Δ Price ' + (delta >= 0 ? '+' : '') + delta.toPrecision(6) + ' (' + (pct >= 0 ? '+' : '') + pct.toFixed(2) + '%) | Δ Time: ' + timeText;
        if (result) result.textContent = text;
        // Attach the label to the chart container, not the browser viewport,
        // so it scrolls and moves with the measured rectangle.
        const xaxis = plot._fullLayout && plot._fullLayout.xaxis, yaxis = plot._fullLayout && plot._fullLayout.yaxis;
        const svg = plot.querySelector('.main-svg');
        if (xaxis && yaxis && svg && xaxis.d2l && yaxis.d2l && xaxis.l2p && yaxis.l2p) {
            const svgRect = svg.getBoundingClientRect();
            const rootRect = root.getBoundingClientRect();
            root.style.position = 'relative';
            const baseCount = Math.max(0, Number(plot.__dashBaseShapeCount || 0));
            const activeIds = {};
            shapes.forEach(function(measureShape, index) {
                if (index < baseCount || !measureShape || (measureShape.type && measureShape.type !== 'rect')) return;
                const my0 = Number(measureShape.y0), my1 = Number(measureShape.y1);
                if (!Number.isFinite(my0) || !Number.isFinite(my1)) return;
                const md = my1 - my0, mp = my0 ? md / my0 * 100 : 0;
                const ms = Date.parse(measureShape.x0), me = Date.parse(measureShape.x1);
                const mt = Number.isFinite(ms) && Number.isFinite(me) ? (Math.abs(me - ms) / 1000 < 60 ? Math.round(Math.abs(me - ms) / 1000) + 's' : (Math.abs(me - ms) / 60000).toFixed(1) + 'm') : 'time n/a';
                const labelId = 'task-chart-measure-label-' + index, pointerId = 'task-chart-measure-pointer-' + index;
                activeIds[labelId] = true; activeIds[pointerId] = true;
                const pointX = svgRect.left - rootRect.left + xaxis._offset + xaxis.l2p(xaxis.d2l(measureShape.x1));
                const pointY = svgRect.top - rootRect.top + yaxis._offset + yaxis.l2p(yaxis.d2l(measureShape.y1));
                const label = document.getElementById(labelId) || root.appendChild(document.createElement('div'));
                label.id = labelId; label.textContent = (md >= 0 ? '▲ ' : '▼ ') + (mp >= 0 ? '+' : '') + mp.toFixed(2) + '% | ' + mt;
                label.style.cssText = 'position:absolute;z-index:10051;pointer-events:none;background:rgba(25,118,210,.92);color:#fff;padding:3px 6px;border-radius:3px;font:11px sans-serif;white-space:nowrap;';
                label.style.left = (pointX + 18) + 'px'; label.style.top = (pointY - 30) + 'px';
                const pointer = document.getElementById(pointerId) || root.appendChild(document.createElement('div'));
                pointer.id = pointerId; const dx = 18, dy = -16, length = Math.sqrt(dx * dx + dy * dy);
                pointer.style.cssText = 'position:absolute;z-index:10050;pointer-events:none;height:1px;background:#1976d2;transform-origin:0 0;';
                pointer.style.left = pointX + 'px'; pointer.style.top = pointY + 'px'; pointer.style.width = length + 'px'; pointer.style.transform = 'rotate(' + Math.atan2(dy, dx) + 'rad)';
            });
            root.querySelectorAll('[id^="task-chart-measure-label-"], [id^="task-chart-measure-pointer-"]').forEach(function(node) { if (!activeIds[node.id]) node.remove(); });

            // A DOM overlay (rather than a Plotly shape) keeps oscillator range
            // highlighting separate from user measure rectangles. It therefore
            // cannot be deleted by Clear/Backspace or mistaken for a measure.
            const activeRangeIds = {};
            if (window.__taskChartOscillatorRangeEnabled) {
                const oscillatorAxes = Object.keys(plot._fullLayout || {}).map(function(key) {
                    return plot._fullLayout[key];
                }).filter(function(axis) {
                    return axis && axis._id && axis._id !== 'y' && /^y[0-9]+$/.test(axis._id) && axis.visible !== false && axis._length > 0;
                });
                shapes.forEach(function(measureShape, measureIndex) {
                    if (measureIndex < baseCount || !measureShape || (measureShape.type && measureShape.type !== 'rect')) return;
                    const leftValue = xaxis.l2p(xaxis.d2l(measureShape.x0));
                    const rightValue = xaxis.l2p(xaxis.d2l(measureShape.x1));
                    if (!Number.isFinite(leftValue) || !Number.isFinite(rightValue)) return;
                    const left = svgRect.left - rootRect.left + xaxis._offset + Math.min(leftValue, rightValue);
                    const width = Math.abs(rightValue - leftValue);
                    oscillatorAxes.forEach(function(axis) {
                        const rangeId = 'task-chart-measure-osc-range-' + measureIndex + '-' + axis._id;
                        activeRangeIds[rangeId] = true;
                        const range = document.getElementById(rangeId) || root.appendChild(document.createElement('div'));
                        range.id = rangeId;
                        range.style.cssText = 'position:absolute;z-index:10020;pointer-events:none;background:rgba(158,158,158,.20);border-left:1px solid rgba(117,117,117,.60);border-right:1px solid rgba(117,117,117,.60);';
                        range.style.left = left + 'px';
                        range.style.top = (svgRect.top - rootRect.top + axis._offset) + 'px';
                        range.style.width = Math.max(1, width) + 'px';
                        range.style.height = axis._length + 'px';
                    });
                });
            }
            root.querySelectorAll('[id^="task-chart-measure-osc-range-"]').forEach(function(node) { if (!activeRangeIds[node.id]) node.remove(); });
        }
    }, 80);
}
document.addEventListener('mouseup', showNativeMeasureResultAfterMouseup, true);
function openTableChartImmediately(button) {
    const rawId = String((button && button.id) || '');
    if (!rawId.startsWith('{') || !window.dash_clientside || typeof window.dash_clientside.set_props !== 'function') return false;
    try {
        const id = JSON.parse(rawId);
        if (id.type !== 'task-table-chart' || !id.task_id) return false;
        const taskId = String(id.task_id);
        markChartRenderRequested('main-table-chart');
        window.dash_clientside.set_props('chart-task-id', {data: taskId});
        window.dash_clientside.set_props('chart-click-store', {data: {[taskId + '_chart']: Date.now() / 1000}});
        window.dash_clientside.set_props('chart-event-context-store', {data: {source: 'main_table', events: [], index: 0, overlay: true}});
        traceUi('local chart open', {taskId: taskId});
        return true;
    } catch (error) {
        console.error('Immediate table chart open failed:', error);
        return false;
    }
}
function openAdjacentChartImmediately(button) {
    if (!button || button.getAttribute('data-direct-navigation') !== 'true') return false;
    const taskId = String(button.getAttribute('data-target-task-id') || '');
    if (!taskId || !window.dash_clientside || typeof window.dash_clientside.set_props !== 'function') return false;
    const direction = button.id === 'prev-chart-btn' ? 'previous' : 'next';
    markChartRenderRequested(button.id);
    window.dash_clientside.set_props('chart-task-id', {data: taskId});
    // The modal is already open; this store only preserves the existing
    // click/deduplication contract without asking Dash to resolve a target.
    window.dash_clientside.set_props('chart-click-store', {data: {[taskId + '_chart']: Date.now() / 1000}});
    traceUi('local chart navigation', {direction: direction, taskId: taskId});
    return true;
}
// Capture phase lets direct Store updates reach Dash before React queues the
// native n_click callback. If set_props is unavailable, normal bubbling keeps
// the server fallback fully functional.
// Existing button feedback - supports both BUTTON and DIV elements.
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
    traceUi('button click', {id: button.id, action: button.getAttribute('data-action')});
    if (openTableChartImmediately(button)) {
        e.preventDefault();
        e.stopPropagation();
        return;
    }
    applyLocalToolbarInteraction(button);

    // Indicator, overlay and range controls replace/reposition the figure.
    // They therefore leave drawing mode before their own action runs, so the
    // Measure appearance always agrees with the active chart interaction.
    if (measureExclusiveButtons.has(button.id)) deactivateMeasureForChartAction();

    // These are pure UI Store toggles. Updating through set_props avoids a
    // registered clientside callback lookup, which older Dash renderers can
    // fail with "undefined (reading apply)" after hot reloads/cache changes.
    if (applyChartToggleImmediately(button)) {
        e.preventDefault();
        e.stopPropagation();
        return;
    }

    if (button.id === 'clear-measure-btn') {
        const chartRoot = document.getElementById('task-chart');
        const plot = chartRoot ? (chartRoot.querySelector('.js-plotly-plot') || chartRoot) : null;
        // Clear native drawrect shapes locally.  The server callback below only
        // clears the small result Stores, so this cannot reload or reposition
        // the candle chart.
        if (plot && window.Plotly) {
            const keep = Math.max(0, Number(plot.__dashBaseShapeCount || 0));
            window.Plotly.relayout(plot, {shapes: (plot.layout.shapes || []).slice(0, keep)});
            window.__taskChartMeasureShapes = [];
        }
        if (chartRoot) {
            chartRoot.querySelectorAll('[id^="task-chart-measure-label-"], [id^="task-chart-measure-pointer-"], [id^="task-chart-measure-osc-range-"]').forEach(function(node) { node.remove(); });
        }
        return;
    }

    if (button.id === 'close-chart-modal') {
        applyChartRowHighlight(null);
        return;
    }
    if (button.id === 'prev-chart-btn' || button.id === 'next-chart-btn') {
        if (openAdjacentChartImmediately(button)) {
            e.preventDefault();
            e.stopPropagation();
            return;
        }
        markChartRenderRequested(button.id);
        traceUi('chart navigation requested', {direction: button.id === 'prev-chart-btn' ? 'previous' : 'next'});
        highlightAdjacentVisibleChartRow(button.id === 'prev-chart-btn' ? 'prev' : 'next');
        return;
    }
    
    try {
        // P1 IMPROVEMENT: Use data attributes instead of JSON parsing for better reliability
        let actionType = button.getAttribute('data-action');
        let taskId = button.getAttribute('data-task-id');
        
        // Fallback to old JSON parsing method for backward compatibility during transition
        if (!actionType || !taskId) {
            // Only the original pattern-ID controls use JSON IDs. Ordinary
            // Dash toolbar/app buttons have simple string IDs; parsing those
            // produced a noisy SyntaxError for every click.
            const rawId = String(button.id || '');
            if (!rawId.startsWith('{')) return;
            let idObj = JSON.parse(rawId);
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
                        applyChartRowHighlight(taskId);
                        // Show the shell immediately instead of waiting for a
                        // server callback and parquet/figure construction.
                        const chartModal = document.getElementById('chart-modal');
                        if (chartModal) chartModal.style.display = 'flex';
                        pushDashStore('chart-button-trigger', {task_id: taskId, action: actionType}, 'dash-chart-trigger');
                    } else if (actionType === 'details') {
                        pushDashStore('strategy-details-trigger', {task_id: taskId, action: actionType}, 'dash-details-trigger');
                    } else if (actionType === 'impulse') {
                        pushDashStore('impulse-button-trigger', {task_id: taskId, action: actionType}, 'dash-impulse-trigger');
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
}, true);
// Backspace removes the newest user-drawn rectangle while preserving figure
// shapes (notably the yellow Signal Level). Do not intercept text editing.
document.addEventListener('keydown', function(e) {
    const target = e.target;
    const editingText = target && typeof target.matches === 'function' && target.matches('input, textarea, [contenteditable="true"]');
    if ((e.key !== 'Backspace' && e.key !== 'Delete') || editingText) return;
    const root = document.getElementById('task-chart');
    const plot = root ? (root.querySelector('.js-plotly-plot') || root) : null;
    const shapes = plot && plot.layout ? (plot.layout.shapes || []) : [];
    const base = Math.max(0, Number(plot && plot.__dashBaseShapeCount || 0));
    if (!plot || !window.Plotly || shapes.length <= base) return;
    let removeIndex = shapes.length - 1;
    if (e.key === 'Delete' && plot.__dashSelectedMeasureShapeKey) {
        const selectedOffset = shapes.slice(base).findIndex(function(shape) {
            return measureShapeKey(shape) === plot.__dashSelectedMeasureShapeKey;
        });
        if (selectedOffset < 0) return;
        removeIndex = base + selectedOffset;
    }
    e.preventDefault();
    const remainingShapes = shapes.slice(0, removeIndex).concat(shapes.slice(removeIndex + 1));
    window.Plotly.relayout(plot, {shapes: remainingShapes});
    window.__taskChartMeasureShapes = uniqueMeasureShapes(remainingShapes.slice(base)).map(function(item) { return Object.assign({}, item); });
    plot.__dashSelectedMeasureShapeKey = '';
    if (remainingShapes.length <= base) {
        root.querySelectorAll('[id^="task-chart-measure-label-"], [id^="task-chart-measure-pointer-"], [id^="task-chart-measure-osc-range-"]').forEach(function(node) { node.remove(); });
    }
}, true);
// Toggle column highlight on header click
// Toggle row highlight on ANY cell click (not a button, not a header, not an interactive-button DIV)
// CRITICAL FIX: Must check if click originated from inside a table cell, not just any element
function handleTaskTableClick(e) {
    // CRITICAL: Check if we're clicking inside a TABLE first before checking for buttons
    // This ensures table clicks are handled even if they contain interactive elements
    let table = e.target.closest('table');
    
    // If we're NOT in a table, exit early (let button handler deal with it)
    if (!table) return;
    
    // Ignore clicks inside buttons OR interactive-button DIVs within the table
    if (e.target.closest('button') || e.target.closest('.interactive-button')) return;
    
    let cell = e.target.closest('th, td');
    if (!cell) return;
    traceUi('table cell click', {tag: cell.tagName, table: table.id || '(no-id)'});
    
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
}
// Dash can stop bubbling at its React root. Bind the normal table-click
// handler directly to every rendered HTML table, so summary and task tables
// retain immediate highlighting after any component refresh.
function bindRenderedTable(table) {
    if (!table || table.dataset.tableClickBound === 'true') return;
    table.dataset.tableClickBound = 'true';
    table.addEventListener('click', function(e) {
        if (e.__gptTableHighlightHandled) return;
        e.__gptTableHighlightHandled = true;
        handleTaskTableClick(e);
        // Do not interfere with Dash buttons or legacy action controls.
        if (!e.target.closest('button, .interactive-button, a, input, select, textarea')) {
            e.stopPropagation();
        }
    });
}

function bindTablesBelow(node) {
    if (!node || node.nodeType !== 1) return;
    if (node.tagName === 'TABLE') bindRenderedTable(node);
    if (node.querySelectorAll) node.querySelectorAll('table').forEach(bindRenderedTable);
}

function installTableRenderListener() {
    if (window.__tableRenderObserver || !document.body) return;
    document.querySelectorAll('table').forEach(bindRenderedTable);
    window.__tableRenderObserver = new MutationObserver(function(mutations) {
        let tableAdded = false;
        mutations.forEach(function(mutation) {
            mutation.addedNodes.forEach(function(node) {
                if (!node || node.nodeType !== 1) return;
                tableAdded = tableAdded || node.tagName === 'TABLE' || Boolean(node.querySelector && node.querySelector('table'));
                bindTablesBelow(node);
            });
        });
        // Reapply hidden columns only after Dash actually replaced a table;
        // Plotly and chart controls also mutate the page and must not trigger
        // table work on every interaction.
        if (tableAdded) applyHiddenColumns();
    });
    window.__tableRenderObserver.observe(document.body, {childList: true, subtree: true});
}
if (document.readyState === 'loading') {
    document.addEventListener('DOMContentLoaded', installTableRenderListener, {once: true});
} else {
    installTableRenderListener();
}
// Capture phase is a reliable fallback when Dash/React stops bubbling. Mark
// the event so a subsequently bound table handler never toggles it twice.
document.addEventListener('click', function(e) {
    if (e.__gptTableHighlightHandled) return;
    e.__gptTableHighlightHandled = true;
    handleTaskTableClick(e);
}, true);
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
function cssEscapeValue(value) {
    const strValue = String(value);
    if (window.CSS && typeof window.CSS.escape === 'function') {
        return window.CSS.escape(strValue);
    }
    return strValue.replace(/"/g, '\\22 ');
}
function applyChartRowHighlight(taskId) {
    // Keep this very cheap: table scrolling should not pay for a full-row scan.
    // The previous implementation queried every highlighted row on each sync.
    if (window.activeChartRow && window.activeChartRow.isConnected) {
        window.activeChartRow.classList.remove('chart-active-row');
    } else {
        const oldRow = document.querySelector('tr.chart-active-row');
        if (oldRow) oldRow.classList.remove('chart-active-row');
    }
    window.activeChartTaskId = taskId || null;
    window.activeChartRow = null;
    if (!taskId) return;
    const row = document.querySelector(`tr[data-task-row="${cssEscapeValue(taskId)}"]`);
    if (row) {
        row.classList.add('chart-active-row');
        window.activeChartRow = row;
    }
}
function highlightAdjacentVisibleChartRow(direction) {
    if (!window.activeChartTaskId) return;
    const rows = Array.from(document.querySelectorAll('#task-table-container tr[data-task-row]'));
    const currentIndex = rows.findIndex(row => row.getAttribute('data-task-row') === String(window.activeChartTaskId));
    if (currentIndex < 0) return;
    const step = direction === 'prev' ? -1 : 1;
    for (let i = currentIndex + step; i >= 0 && i < rows.length; i += step) {
        const chartButton = rows[i].querySelector('[data-action="chart"]');
        if (chartButton && chartButton.style.opacity !== '0.6') {
            applyChartRowHighlight(rows[i].getAttribute('data-task-row'));
            return;
        }
    }
}
window.applyChartRowHighlight = applyChartRowHighlight;
</script>
</footer>
</body>
</html>
'''

app.index_string = build_index_string()

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

# Canonical source profiles keep chart-open behaviour declarative.  They do
# not alter task/strategy math; they only describe chart presentation defaults.
CHART_SOURCE_PROFILES = {
    "main_table": {
        "navigation": "task",
        "focus": "signal",
        "default_panes": (),
        "default_overlays": (),
        "show_trade_details": False,
    },
    "dynamic_oscillator_summary": {
        "navigation": "event_group",
        "focus": "event_interval",
        "default_panes": ("rsi", "stochastic"),
        "default_overlays": ("event_marks", "trade_details"),
        "show_trade_details": True,
    },
    # Future strategy summaries can reuse this profile without adding another
    # chart-opening code path.  Their selected event supplies entry/exit/P&L.
    "strategy_summary": {
        "navigation": "event_group",
        "focus": "event_interval",
        "default_panes": (),
        "default_overlays": ("event_marks", "trade_details"),
        "show_trade_details": True,
    },
}


def make_chart_context(source="main_table", *, events=None, index=0, overlay=None, **extra):
    """Return normalized source context for every chart-opening path."""
    source = source if source in CHART_SOURCE_PROFILES else "main_table"
    profile = CHART_SOURCE_PROFILES[source]
    try:
        normalized_index = max(0, int(index or 0))
    except (TypeError, ValueError):
        normalized_index = 0
    context = {
        "source": source,
        "events": list(events or []),
        "index": normalized_index,
        "overlay": bool(profile["default_overlays"]) if overlay is None else bool(overlay),
    }
    context.update(extra)
    return context


def make_chart_request(task_id, context=None):
    """Build the canonical, UI-only chart request from task and source state."""
    context = dict(context or make_chart_context())
    source = context.get("source", "main_table")
    source = source if source in CHART_SOURCE_PROFILES else "main_table"
    profile = CHART_SOURCE_PROFILES[source]
    events = context.get("events") or []
    try:
        requested_index = int(context.get("index") or 0)
    except (TypeError, ValueError):
        requested_index = 0
    index = max(0, min(requested_index, len(events) - 1)) if events else 0
    selected_event = events[index] if events and 0 <= index < len(events) else None
    return {
        "task_id": str(task_id) if task_id else None,
        "source": source,
        "profile": profile,
        "context": {**context, "source": source, "index": index},
        # This is deliberately the original event payload so strategy-summary
        # charts retain entry, exit, reasons, and P&L for marks/tooltips.
        "selected_event": selected_event,
    }


# Phase 2 compatibility state: a single structured snapshot of chart controls.
# Existing Stores remain the writers during this migration, so current button
# behavior and chart math are unchanged while later phases gain one stable API.
def make_chart_ui_state(
    rsi=False, stochastic=False, volume=False, adx=False, macd=False,
    disparity=False, strategy=False, impulses=False, events=False,
    measure=False, measure_anchor=False, measure_hover=True,
    measure_oscillator_range=False, candle_info=False, oscillator_info=True,
    oscillator_sync=False, extend_x=False, focus_entry=False,
):
    return {
        "panes": {
            "rsi": bool(rsi), "stochastic": bool(stochastic),
            "volume": bool(volume), "adx": bool(adx), "macd": bool(macd),
            "disparity": bool(disparity),
        },
        "overlays": {
            "strategy": bool(strategy), "impulses": bool(impulses),
            "events": bool(events),
        },
        "measurement": {
            "enabled": bool(measure), "snap_to_candle": bool(measure_anchor),
            "show_hover": bool(measure_hover),
            "shade_oscillator_range": bool(measure_oscillator_range),
        },
        "information": {
            "candle": bool(candle_info), "oscillator": bool(oscillator_info),
            "oscillator_sync": bool(oscillator_sync),
        },
        "viewport": {"extend_x": bool(extend_x), "focus_entry": bool(focus_entry)},
    }


# Declarative registry for chart panes and overlays.  Values are UI/rendering
# metadata only; existing indicator calculations and Plotly trace functions
# remain unchanged in Phase 3.
CHART_INDICATOR_REGISTRY = {
    "rsi": {"requires_volume": False, "specs": (("rsi", None),)},
    "stochastic": {
        "requires_volume": False,
        "specs": (
            ("stoch", ("stoch_k_14_1_3", "stoch_d_14_1_3", "Stoch 14/1/3", "#1565c0")),
            ("stoch", ("stoch_k_40_1_4", "stoch_d_40_1_4", "Stoch 40/1/4", "#ef6c00")),
            ("stoch", ("stoch_k_60_1_10", "stoch_d_60_1_10", "Stoch 60/1/10", "#2e7d32")),
            ("stoch", ("stoch_k_300_1_10", "stoch_d_300_1_10", "Stoch 300/1/10", "#6a1b9a")),
        ),
    },
    "adx": {"requires_volume": False, "specs": (("adx", None),)},
    "macd": {"requires_volume": False, "specs": (("macd", None),)},
    "disparity": {"requires_volume": False, "specs": (("disparity", None),)},
    "volume": {"requires_volume": True, "specs": (("volume", None),)},
}

CHART_OVERLAY_REGISTRY = {
    "strategy": {"source_aware": False, "description": "Task strategy signals"},
    "impulses": {"source_aware": False, "description": "Task impulse signals"},
    "events": {"source_aware": False, "description": "Task price events"},
    "event_marks": {"source_aware": True, "description": "Source trade entry/exit marks"},
    "trade_details": {"source_aware": True, "description": "Entry/exit reason and P&L tooltips"},
}


def build_chart_indicator_specs(visibility, has_volume):
    """Return visible pane specs in stable registry order for the figure renderer."""
    specs = []
    for key, definition in CHART_INDICATOR_REGISTRY.items():
        if not visibility.get(key, False):
            continue
        if definition["requires_volume"] and not has_volume:
            continue
        specs.extend(definition["specs"])
    return specs


CHART_PANEL_STYLE = {
    "position": "relative",
    "width": "100%",
    "backgroundColor": "#f4f6f8",
    "justifyContent": "center",
    "alignItems": "stretch",
    "marginTop": "18px",
    "padding": "10px 0 24px 0",
    "borderTop": "2px solid #c8d2dc",
}


def build_root_layout():
    """Build the root Dash layout.

    UI layout builder only: this must only assemble Dash components and keep
    existing component IDs unchanged so callbacks remain wired exactly as before.
    """
    return html.Div([
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
    dcc.Store(id="chart-highlight-dummy", data=None),  # clientside row highlight sync
    dcc.Store(id="chart-event-context-store", data=make_chart_context()),
    # Canonical request used by future source-aware chart controls/renderers.
    dcc.Store(id="chart-request-store", data=make_chart_request(None)),
    dcc.Store(id="chart-ui-state-store", data=make_chart_ui_state()),
    # Future controls write declarative actions here; the bridge below applies
    # them to legacy Stores until all existing callbacks consume grouped state.
    dcc.Store(id="chart-ui-action-store", data=None),
    dcc.Store(id="chart-view-state-store", data={}),  # preserves user zoom/pan while toolbar buttons rebuild the chart
    dcc.Store(id="chart-dragmode-enforcer-store", data=None),  # keeps Measure draw-rectangle mode synced with Plotly modebar
    dcc.Store(id="chart-crosshair-listener-store", data=None),  # installs browser-side full-height chart crosshair overlay
    dcc.Store(id="osc-event-groups-store", data={}),
    dcc.Store(id="rsi-visible-store", data=False),   # default: RSI hidden
    dcc.Store(id="stochastic-visible-store", data=False),  # default: stochastic panes hidden
    dcc.Store(id="volume-visible-store", data=False),  # default: Volume hidden
    dcc.Store(id="adx-visible-store", data=False),  # default: ADX hidden
    dcc.Store(id="macd-visible-store", data=False),  # default: MACD hidden
    dcc.Store(id="disparity-visible-store", data=False),  # default: CMOa Disparity Index hidden
    dcc.Store(id="strategy-visible-store", data=False),
    # ---- Measurement tool stores ----
    dcc.Store(id="measure-mode-store", data=False),
    dcc.Store(id="measure-anchor-store", data=False),
    dcc.Store(id="measure-hover-store", data=True),
    dcc.Store(id="measure-oscillator-range-store", data=False),
    dcc.Store(id="chart-info-box-store", data=False),
    dcc.Store(id="oscillator-info-box-store", data=True),
    dcc.Store(id="oscillator-sync-info-store", data=False),
    dcc.Store(id="chart-extend-x-store", data=False),
    dcc.Store(id="chart-focus-entry-store", data=False),
    dcc.Store(id="measure-points-store", data={"first": None, "second": None}),
    dcc.Store(id="measure-result-store", data=None),
    # ---- Strategy details modal stores ----
    dcc.Store(id="strategy-details-task-id", data=None),
    dcc.Store(id="details-click-store", data={}),   # deduplication for details button
    # --------------------------------
    dcc.Store(id="impulse-visible-store", data=False),
    dcc.Store(id="events-visible-store", data=False),
    dcc.Store(id="impulse-params-store", data={}),
    # 🔧 CRITICAL: Hidden dummy buttons for CustomEvent-triggered callbacks (using html.Button which supports n_clicks)
    html.Button(id="chart-event-dummy", style={"display": "none"}, n_clicks=0),
    html.Button(id="details-event-dummy", style={"display": "none"}, n_clicks=0),
    html.Button(id="impulse-event-dummy", style={"display": "none"}, n_clicks=0),
    dcc.Interval(id="ui-trace-interval", interval=5000, n_intervals=0),
    html.Details([
        html.Summary("🩺 Chart diagnostics (click to open)", style={"cursor": "pointer", "fontWeight": "bold"}),
        html.Div("Use this panel when a chart button is slow or opens the wrong task. It records server-side chart and toolbar events. The blue area is read-only; use the test button below to verify browser click tracing.", style={"fontSize": "12px", "margin": "6px 0"}),
        html.Button("Test browser click tracing", id="ui-client-trace-test-btn", n_clicks=0, style={"fontSize": "12px", "marginBottom": "6px"}),
        html.Pre(id="ui-trace-output", children="No server chart events yet.", style={"maxHeight": "140px", "overflowY": "auto", "whiteSpace": "pre-wrap", "backgroundColor": "#111", "color": "#d7ffd9", "padding": "8px", "fontSize": "11px", "borderRadius": "4px"}),
        html.Pre(id="ui-client-trace-output", children="Browser click trace: waiting for page script.", style={"maxHeight": "100px", "overflowY": "auto", "whiteSpace": "pre-wrap", "backgroundColor": "#102027", "color": "#b2ebf2", "padding": "8px", "fontSize": "11px", "borderRadius": "4px", "marginTop": "6px"}),
    ], style={"margin": "8px 0", "padding": "6px", "border": "1px solid #90a4ae", "borderRadius": "4px", "backgroundColor": "#f5f7f8"}),
    dcc.Tabs(id="main-tabs", value="tab-tasks", children=[
        dcc.Tab(label="Tasks", value="tab-tasks"),
        dcc.Tab(label="Data Analysis", value="tab-analysis"),
    ]),
    # Permanent callback target: a background rerun/recalculation may finish
    # after the user has switched dynamic tabs. Do not place this target inside
    # tab-content, where Dash would remove it during the switch.
    html.Div(
        id="bulk-rerun-status",
        style={
            "color": "#1565c0",
            "fontFamily": "monospace",
        },
    ),
    html.Div(
        id="update-json-pre-signal-status",
        style={
            "color": "#1565c0",
            "fontFamily": "monospace",
        },
    ),
    html.Progress(
        id="json-period-update-progress",
        value="0",
        max=100,
        style={"width": "320px", "display": "block", "marginBottom": "6px"},
    ),
    html.Div(
        [
            html.Label("Prepared JSON filename: ", htmlFor="prepared-json-filename"),
            dcc.Input(
                id="prepared-json-filename",
                type="text",
                value="tasks_extended.json",
                placeholder="new_tasks_filename.json",
                debounce=True,
                style={"width": "250px", "marginRight": "8px"},
            ),
            html.Button(
                "💾 Save prepared JSON",
                id="save-prepared-json-btn",
                n_clicks=0,
                disabled=True,
                style={"backgroundColor": "#e8f5e9"},
            ),
        ],
        style={"display": "flex", "alignItems": "center", "marginBottom": "4px"},
    ),
    html.Div(
        id="prepared-json-save-status",
        style={"color": "#1565c0", "fontFamily": "monospace", "marginBottom": "6px"},
    ),
    html.Div(
        id="recalc-status-bar",
        style={
            "color": "#d84315",
            "fontFamily": "monospace",
            "fontWeight": "bold",
        },
    ),
    html.Div(id="tab-content"),
    # Inline chart panel. It intentionally follows tab-content in document flow
    # so a cold chart load never covers the task and summary tables.
    html.Div(
        id="chart-modal",
        style={**CHART_PANEL_STYLE, "display": "none"},
        children=[
            html.Div(
                style={
                    "backgroundColor": "#ffffff",   # white background
                    "width": "96%",
                    "minHeight": "720px",
                    "borderRadius": "8px",
                    "padding": "50px 20px 20px 20px",
                    "position": "relative",
                    "display": "flex",
                    "flexDirection": "column"
                },
                children=[
                    # Button row (Toggle RSI + Toggle Strategy + Measure + Close)
                    html.Div(
                        className="chart-button-strip",
                        style={
                            "position": "absolute",
                            "top": "10px",
                            "left": "10px",
                            "right": "10px",
                            "display": "flex",
                            "flexWrap": "nowrap",
                            "justifyContent": "flex-start",
                            "gap": "6px",
                            "overflowX": "auto",
                            "overflowY": "hidden",
                            "alignItems": "center",
                            "paddingBottom": "12px",
                            "maxWidth": "calc(100% - 20px)",
                            "whiteSpace": "nowrap",
                        },
                        children=[
                            html.Button("‹", id="prev-chart-btn", title="Previous task chart", n_clicks=0,
                                **{"data-target-task-id": "", "data-direct-navigation": "false"}, style={
                                "background": "transparent",
                                "color": "black",
                                "border": "1px solid black",
                                "padding": "6px 10px",
                                "cursor": "pointer",
                                "fontSize": "14px",
                                "minWidth": "34px",
                                "whiteSpace": "nowrap"
                            }),
                            html.Button("›", id="next-chart-btn", title="Next task chart", n_clicks=0,
                                **{"data-target-task-id": "", "data-direct-navigation": "false"}, style={
                                "background": "transparent",
                                "color": "black",
                                "border": "1px solid black",
                                "padding": "6px 10px",
                                "cursor": "pointer",
                                "fontSize": "14px",
                                "minWidth": "34px",
                                "whiteSpace": "nowrap"
                            }),
                            html.Button("RSI: Off", id="toggle-rsi-btn", style={
                                "background": "transparent",
                                "color": "black",
                                "border": "1px solid black",
                                "padding": "6px 10px",
                                "cursor": "pointer",
                                "fontSize": "12px",
                                "minWidth": "76px",
                                "whiteSpace": "nowrap"
                            }),
                            html.Button("Stoch: Off", id="toggle-stochastic-btn", style={
                                "background": "transparent",
                                "color": "black",
                                "border": "1px solid black",
                                "padding": "6px 10px",
                                "cursor": "pointer",
                                "fontSize": "12px",
                                "minWidth": "82px",
                                "whiteSpace": "nowrap"
                            }),
                            html.Button("Volume: Off", id="toggle-volume-btn", style={
                                "background": "transparent",
                                "color": "black",
                                "border": "1px solid black",
                                "padding": "6px 10px",
                                "cursor": "pointer",
                                "fontSize": "12px",
                                "minWidth": "86px",
                                "whiteSpace": "nowrap"
                            }),
                            html.Button("ADX: Off", id="toggle-adx-btn", style={
                                "background": "transparent",
                                "color": "black",
                                "border": "1px solid black",
                                "padding": "6px 10px",
                                "cursor": "pointer",
                                "fontSize": "12px",
                                "minWidth": "76px",
                                "whiteSpace": "nowrap"
                            }),
                            html.Button("MACD: Off", id="toggle-macd-btn", style={
                                "background": "transparent",
                                "color": "black",
                                "border": "1px solid black",
                                "padding": "6px 10px",
                                "cursor": "pointer",
                                "fontSize": "12px",
                                "minWidth": "88px",
                                "whiteSpace": "nowrap"
                            }),
                            html.Button("DIX: Off", id="toggle-disparity-btn", title="Toggle CMOa Disparity Index (EMA 50/25/9)", style={
                                "background": "transparent",
                                "color": "black",
                                "border": "1px solid black",
                                "padding": "6px 10px",
                                "cursor": "pointer",
                                "fontSize": "12px",
                                "minWidth": "84px",
                                "whiteSpace": "nowrap"
                            }),
                            html.Button("Strategy: Off", id="toggle-strategy-btn", style={
                                "background": "transparent",
                                "color": "black",
                                "border": "1px solid black",
                                "padding": "6px 10px",
                                "cursor": "pointer",
                                "fontSize": "12px",
                                "minWidth": "76px",
                                "whiteSpace": "nowrap"
                            }),
                            html.Button("📐 Measure", id="toggle-measure-btn", title="Measure price and time by drawing a rectangle", style={
                                "background": "transparent",
                                "color": "black",
                                "border": "1px solid black",
                                "padding": "6px 10px",
                                "cursor": "pointer",
                                "fontSize": "12px",
                                "minWidth": "76px",
                                "whiteSpace": "nowrap"
                            }),
                            html.Button("Osc Range: Off", id="toggle-measure-oscillator-range-btn", title="Shade every visible oscillator over each measured time range", style={
                                "background": "transparent",
                                "color": "black",
                                "border": "1px solid #999",
                                "padding": "6px 10px",
                                "cursor": "pointer",
                                "fontSize": "12px",
                                "minWidth": "104px",
                                "whiteSpace": "nowrap"
                            }),
                            html.Button("Snap: Off", id="toggle-measure-anchor-btn", title="Toggle measurement anchoring to close-price helper points", style={
                                "background": "transparent",
                                "color": "black",
                                "border": "1px solid #999",
                                "padding": "6px 10px",
                                "cursor": "pointer",
                                "fontSize": "12px",
                                "minWidth": "76px",
                                "whiteSpace": "nowrap"
                            }),
                            html.Button("Hover: On", id="toggle-measure-hover-btn", title="Toggle chart hover boxes and spike/crosshair lines while measuring", style={
                                "background": "#fff8e1",
                                "color": "black",
                                "border": "1px solid #f9a825",
                                "padding": "6px 10px",
                                "cursor": "pointer",
                                "fontSize": "12px",
                                "minWidth": "78px",
                                "whiteSpace": "nowrap"
                            }),
                            html.Button("Candle Info: Off", id="toggle-chart-info-box-btn", title="Toggle exact OHLC information for the main candle chart", style={
                                "background": "transparent",
                                "color": "black",
                                "border": "1px solid #f9a825",
                                "padding": "6px 10px",
                                "cursor": "pointer",
                                "fontSize": "12px",
                                "minWidth": "94px",
                                "whiteSpace": "nowrap"
                            }),
                            html.Button("Osc Info: On", id="toggle-oscillator-info-box-btn", title="Toggle exact hover values in every visible oscillator pane", style={
                                "background": "#fff8e1", "color": "black", "border": "1px solid #f9a825",
                                "padding": "6px 10px", "cursor": "pointer", "fontSize": "12px", "minWidth": "94px", "whiteSpace": "nowrap"
                            }),
                            html.Button("Osc All: Off", id="toggle-oscillator-sync-info-btn", title="Show synchronized values for every visible oscillator at the hovered time; never show main-chart values", style={
                                "background": "transparent", "color": "black", "border": "1px solid #999",
                                "padding": "6px 10px", "cursor": "pointer", "fontSize": "12px", "minWidth": "94px", "whiteSpace": "nowrap"
                            }),
                            html.Button("Extend X: Off", id="toggle-chart-extend-x-btn", title="Add TradingView-style empty space to the right side of the chart", style={
                                "background": "transparent",
                                "color": "black",
                                "border": "1px solid #999",
                                "padding": "6px 10px",
                                "cursor": "pointer",
                                "fontSize": "12px",
                                "minWidth": "94px",
                                "whiteSpace": "nowrap"
                            }),
                            html.Button("Focus Entry: Off", id="toggle-chart-focus-entry-btn", title="Center each newly opened chart on its signal entry with a practical zoom", style={
                                "background": "transparent",
                                "color": "black",
                                "border": "1px solid #999",
                                "padding": "6px 10px",
                                "cursor": "pointer",
                                "fontSize": "12px",
                                "minWidth": "104px",
                                "whiteSpace": "nowrap"
                            }),
                            html.Button("Clear Measure", id="clear-measure-btn", style={
                                "background": "transparent",
                                "color": "black",
                                "border": "1px solid #999",
                                "padding": "6px 10px",
                                "cursor": "pointer",
                                "fontSize": "12px",
                                "minWidth": "82px",
                                "whiteSpace": "nowrap"
                            }),
                            html.Button("Impulses: Off", id="toggle-impulses-btn", style={
                                "background": "transparent",
                                "color": "black",
                                "border": "1px solid black",
                                "padding": "6px 10px",
                                "cursor": "pointer",
                                "fontSize": "12px",
                                "minWidth": "76px",
                                "whiteSpace": "nowrap"
                            }),
                            html.Button("Event Marks: Off", id="toggle-chart-event-marks-btn", title="Toggle research entry/exit markers", style={
                                "background": "transparent",
                                "color": "black",
                                "border": "1px solid #999",
                                "padding": "6px 10px",
                                "cursor": "pointer",
                                "fontSize": "12px",
                                "minWidth": "108px",
                                "whiteSpace": "nowrap"
                            }),
                            html.Button("Events: Off", id="toggle-events-btn", style={
                                "background": "transparent",
                                "color": "black",
                                "border": "1px solid black",
                                "padding": "6px 10px",
                                "cursor": "pointer",
                                "fontSize": "12px",
                                "minWidth": "76px",
                                "whiteSpace": "nowrap"
                            }),
                            html.Button("✕", id="close-chart-modal", style={
                                "background": "transparent",
                                "color": "black",
                                "border": "none",
                                "fontSize": "16px",
                                "cursor": "pointer"
                            }),
                        ]
                    ),
                    # Keep the existing chart visible while controls update.
                    # A Loading wrapper replaces its child with a spinner for
                    # every figure/relayout callback, which made Measure hide
                    # the chart precisely when the user needed to select it.
                    dcc.Graph(
                        id="task-chart",
                        style={"flex": "1", "minHeight": "0"},
                        config={"scrollZoom": True, "displaylogo": False, "modeBarButtonsToAdd": ["drawrect", "eraseshape"]}
                    ),
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

app.layout = build_root_layout()



def build_tasks_tab_layout():
    """Build the Tasks tab layout.

    This is intentionally a layout-only extraction from render_tab so the main
    tab dispatcher stays small. Do not add parsing, download, event detection,
    or analysis math here; those flows remain in their dedicated callback and
    task sections below.
    """
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
                    options=[{"label": "Hide detailed logs in task table (faster)", "value": "hide"}],
                    value=["hide"]  # Default: checked
                ),
            ], style={"marginBottom": "10px"}),
            html.Div([
                html.Label("Main table view:", style={"fontWeight": "bold", "marginRight": "10px"}),
                dcc.RadioItems(
                    id="table-view-mode",
                    options=[
                        {"label": "Compact key columns (faster)", "value": "compact"},
                        {"label": "Full table", "value": "full"},
                    ],
                    value="compact",
                    inline=True,
                ),
            ], style={"marginBottom": "10px"}),
            html.Div([
                html.Label("Main table order:", style={"fontWeight": "bold", "marginRight": "10px"}),
                dcc.RadioItems(
                    id="table-sort-mode",
                    options=[
                        {"label": "Newest signal first", "value": "newest"},
                        {"label": "Original task order", "value": "original"},
                    ],
                    value="newest",
                    inline=True,
                ),
                html.Span(" UI-only; JSON and calculations are unchanged.", style={"fontSize": "12px", "color": "#666", "marginLeft": "8px"}),
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
            html.H5("Add persistent left-side minutes for a NEW JSON", style={"margin": "10px 0 5px"}),
            html.Div([
                dcc.Input(
                    id="update-json-pre-signal-minutes",
                    type="number",
                    min=0,
                    step=1,
                    placeholder="extra minutes to add",
                    style={"width": "205px", "marginRight": "10px"},
                ),
                html.Button(
                    "⬅️ Add minutes and prepare new JSON",
                    id="update-json-pre-signal-btn",
                    n_clicks=0,
                    title="Add this many earlier minutes to each task; verify/download safely, then use Save prepared JSON with a new filename.",
                ),
            ], style={"display": "flex", "alignItems": "center", "marginBottom": "6px"}),
            html.Div(
                "The number is additional, not the new total: a task with 120 minutes plus 30 becomes 150. Existing task results are not declared incorrect or re-parsed. Only the requested pre-signal candle range is checked; existing candles are reused and missing earlier candles are safely downloaded. If that range cannot be prepared, the task is listed as not prepared and keeps its original minutes. After Finished, rerun Events, Strategy and Impulse if wanted, then use the separate Prepared JSON filename and Save prepared JSON controls above. The button is enabled only after at least one task was prepared.",
                style={"fontSize": "12px", "color": "#666", "marginBottom": "5px"},
            ),
            html.Div(id="save-load-status", style={"minHeight": "20px", "color": "#1565c0", "fontFamily": "monospace", "marginBottom": "10px"}),
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
        # ----- Dynamic Toward-Level Strategy Checkup (on-demand diagnostics) -----
        html.Details([
            html.Summary("🧪 Dynamic Toward-Level Checkup – variable SL / TP / trailing stop", style={"fontWeight": "bold", "cursor": "pointer"}),
            html.Div([
                html.P(
                    "Runs an on-demand diagnostic over raw candle data without changing saved task fields. "
                    "Entry uses the first candle after signal time, buy toward resistance and sell toward support.",
                    style={"marginTop": "10px", "color": "#555"}
                ),
                html.Details([
                    html.Summary("ⓘ How to use SL grid, BE grid, TP levels, and dynamic stop rules", style={"cursor": "pointer", "color": "#0b63b6", "fontWeight": "bold"}),
                    html.Div([
                        html.P("Think of the controls as separate layers:", style={"marginBottom": "6px"}),
                        html.Ul([
                            html.Li("Initial stop loss % = where the first protective stop starts from entry; Initial stop events count trades closed by that stop before another exit type."),
                            html.Li("SL grid % = extra initial-stop values to test side by side, for example 0.12 / 0.25 / 0.5."),
                            html.Li("Take profit levels % = favorable-move checkpoints to count, such as 0.5 / 1 / 2 / 4."),
                            html.Li("Dynamic stop rules = not take-profit orders; they move the stop after price moves in your favor."),
                            html.Li("BE arm grid % = quick tests for moving the stop to entry after +0.25%, +0.5%, +1%, etc."),
                            html.Li("Max adverse DD grid % = optional adverse-move caps from entry tested side by side."),
                            html.Li("Net expectancy uses the simulated exit return minus your round-trip costs for every trade."),
                            html.Li("Money estimate multiplies each net return by your notional per trade, for example 1000 USD."),
                        ], style={"marginTop": 0}),
                        html.P("Dynamic stop rule format: trigger%:move-stop-to-profit%.", style={"fontWeight": "bold", "marginBottom": "4px"}),
                        html.Ul([
                            html.Li("0.5:0 means: after price moves +0.5% in your favor, move stop to breakeven / entry."),
                            html.Li("1:0.3 means: after price moves +1%, move stop to lock about +0.3% profit."),
                            html.Li("2:1.5 means: after price moves +2%, move stop to lock about +1.5% profit."),
                            html.Li("4:3 means: after price moves +4%, move stop to lock about +3% profit."),
                        ], style={"marginTop": 0}),
                        html.P(
                            "The dynamic summary table shows the selected scenario plus grid rows: SL grid scenarios, BE-after rows, "
                            "max adverse DD cap rows, TP hit rows, stop events, stop-after-TP, and dynamic-stop-moved counts.",
                            style={"marginBottom": 0}
                        ),
                    ], style={"fontSize": "13px", "lineHeight": "1.4", "padding": "8px", "backgroundColor": "#eef7ff", "border": "1px solid #cfe8ff", "borderRadius": "4px", "margin": "8px 0"})
                ], open=False),
                html.Div([
                    html.Label("Initial stop loss %:", style={"width": "180px", "display": "inline-block"}),
                    html.Span(" ⓘ", title="Loss distance from the simulated entry. Example: 0.12 means close if price moves 0.12% against the entry before a tighter dynamic stop is active.", style={"cursor": "help", "color": "#0b63b6"}),
                    dcc.Input(id="dynamic-check-sl-input", type="number", value=0.12, min=0, step=0.01, style={"width": "90px"}),
                    html.Label("Max adverse DD from entry % (positive):", style={"width": "210px", "display": "inline-block", "marginLeft": "20px"}),
                    html.Span(" ⓘ", title="Optional adverse-move cap measured from entry, always entered as a positive percent. It is an exit reason only if this cap is hit before the normal stop/trailing stop.", style={"cursor": "help", "color": "#0b63b6"}),
                    dcc.Input(id="dynamic-check-max-dd-input", type="number", value=None, min=0, step=0.1, placeholder="optional", style={"width": "110px"}),
                ], style={"marginBottom": "10px"}),
                html.Div([
                    html.Label("Take profit levels %:", style={"width": "180px", "display": "inline-block"}),
                    html.Span(" ⓘ", title="Favorable move checkpoints from entry. Example: 0.5, 1, 2, 4 counts candles that move at least those percentages in the trade direction.", style={"cursor": "help", "color": "#0b63b6"}),
                    dcc.Input(id="dynamic-check-tp-levels-input", type="text", value="0.5, 1, 2, 4", style={"width": "240px"}),
                    html.Span("Example: 0.5, 1, 2, 4", style={"marginLeft": "10px", "color": "#777"}),
                ], style={"marginBottom": "10px"}),
                html.Div([
                    html.Label("Dynamic stop rules:", style={"width": "180px", "display": "inline-block"}),
                    html.Span(" ⓘ", title="Comma-separated trigger:stop-profit pairs. Example 0.5:0 means: after price moves +0.5% in your favor, move the stop to breakeven. 1:0.3 means after +1%, lock +0.3% profit.", style={"cursor": "help", "color": "#0b63b6"}),
                    dcc.Input(id="dynamic-check-trail-rules-input", type="text", value="0.5:0, 1:0.5, 2:1, 4:2", style={"width": "320px"}),
                    html.Span("trigger%:move-stop-to-profit% pairs", style={"marginLeft": "10px", "color": "#777"}),
                ], style={"marginBottom": "10px"}),
                html.Div([
                    html.Label("SL grid %:", style={"width": "180px", "display": "inline-block"}),
                    html.Span(" ⓘ", title="Extra stop-loss values to test side-by-side in the summary. They reuse the same raw candle paths for faster comparison.", style={"cursor": "help", "color": "#0b63b6"}),
                    dcc.Input(id="dynamic-check-sl-grid-input", type="text", value="0.12, 0.15, 0.25, 0.35, 0.5", style={"width": "260px"}),
                    html.Label("BE arm grid %:", style={"width": "130px", "display": "inline-block", "marginLeft": "20px"}),
                    html.Span(" ⓘ", title="Breakeven-arm tests add a rule that moves stop to entry after this favorable move. Example 0.5 tests BE after +0.5%.", style={"cursor": "help", "color": "#0b63b6"}),
                    dcc.Input(id="dynamic-check-be-grid-input", type="text", value="0.25, 0.5, 0.75, 1", style={"width": "220px"}),
                ], style={"marginBottom": "10px"}),
                html.Div([
                    html.Label("Max adverse DD grid %:", style={"width": "180px", "display": "inline-block"}),
                    html.Span(" ⓘ", title="Extra adverse drawdown caps from entry to test side-by-side. A cap only counts when it becomes the actual exit before another stop.", style={"cursor": "help", "color": "#0b63b6"}),
                    dcc.Input(id="dynamic-check-dd-grid-input", type="text", value="0.25, 0.5, 0.75, 1", style={"width": "260px"}),
                    html.Span("Grid rows reuse raw candle paths built once per task for faster comparison.", style={"marginLeft": "10px", "color": "#777"}),
                ], style={"marginBottom": "10px"}),
                html.Div([
                    html.Label("Notional per trade USD:", style={"width": "180px", "display": "inline-block"}),
                    html.Span(" ⓘ", title="Diagnostic position size used only for estimated P/L. Example: 1000 means each simulated trade is counted as a 1000 USD notional trade.", style={"cursor": "help", "color": "#0b63b6"}),
                    dcc.Input(id="dynamic-check-notional-input", type="number", value=1000, min=0, step=100, style={"width": "110px"}),
                    html.Label("Round-trip costs %:", style={"width": "150px", "display": "inline-block", "marginLeft": "20px"}),
                    html.Span(" ⓘ", title="Estimated total entry+exit cost as percent of notional, including fees, spread, slippage, and funding if applicable. It is subtracted from every simulated trade.", style={"cursor": "help", "color": "#0b63b6"}),
                    dcc.Input(id="dynamic-check-cost-input", type="number", value=0.10, min=0, step=0.01, style={"width": "90px"}),
                    html.Label("Open/no-exit return %:", style={"width": "165px", "display": "inline-block", "marginLeft": "20px"}),
                    html.Span(" ⓘ", title="Fallback return for diagnostic paths that never hit SL, DD cap, or moved stop. Use 0 for conservative flat close, or another value if you have a forced end-of-window exit rule.", style={"cursor": "help", "color": "#0b63b6"}),
                    dcc.Input(id="dynamic-check-open-return-input", type="number", value=0, step=0.1, style={"width": "90px"}),
                ], style={"marginBottom": "10px"}),
                html.Button("Run Dynamic Checkup", id="dynamic-check-run-btn", n_clicks=0, style={"fontWeight": "bold"}),
                dcc.Loading(
                    type="circle",
                    children=[
                        html.Div(id="dynamic-check-status", style={"marginTop": "10px", "fontWeight": "bold"}),
                        html.Div(
                            id="dynamic-check-results",
                            style={
                                "marginTop": "10px",
                                "maxHeight": "420px",
                                "overflowY": "auto",
                                "border": "1px solid #ddd",
                                "borderRadius": "4px",
                                "padding": "8px",
                                "backgroundColor": "#fff",
                            }
                        ),
                    ],
                ),
            ], style={"padding": "10px", "backgroundColor": "#f7fbff", "borderRadius": "5px", "border": "1px solid #cfe8ff"})
        ], open=False, style={"marginBottom": "20px"}),
        # ----- Level-Reversal Strategy Checkup (on-demand diagnostics) -----
        html.Details([
            html.Summary("🧪 Level-Reversal Checkup – enter after signal level touch/overshoot", style={"fontWeight": "bold", "cursor": "pointer"}),
            html.Div([
                html.P(
                    "Tests the opposite idea: wait until price reaches the signal level (or overshoots it by a chosen percent), "
                    "then enter the reversal direction. Resistance becomes SELL; support becomes BUY. This is read-only and does not change saved task fields.",
                    style={"marginTop": "10px", "color": "#555"}
                ),
                html.Details([
                    html.Summary("ⓘ How the level-reversal checkup works", style={"cursor": "pointer", "color": "#9a5a00", "fontWeight": "bold"}),
                    html.Div([
                        html.P("This box tests a different entry idea from the first dynamic box:", style={"marginBottom": "6px"}),
                        html.Ul([
                            html.Li("Resistance signal: wait for price to touch/overshoot the resistance level, then simulate a SELL reversal."),
                            html.Li("Support signal: wait for price to touch/overshoot the support level, then simulate a BUY reversal."),
                            html.Li("Entry offset beyond level % = 0 means enter at the level; 0.25 waits for 0.25% overshoot beyond the level."),
                            html.Li("SL, TP levels, max adverse DD, and dynamic stop rules work the same way as the main dynamic checkup, but from this reversal entry."),
                            html.Li("Initial stop events count reversal entries that were closed by the initial or moved stop; they do not mean the task is bad/corrupted."),
                            html.Li("The summary is intentionally unified: it treats support/resistance as one concept — move toward the level, reject, then go back — instead of showing separate BUY/SELL cases."),
                            html.Li("Entry offset grid % tests how many tasks still trigger if you require extra overshoot before reversal entry."),
                            html.Li("Net expectancy and USD P/L rows use the same simulated exits, costs, and notional as the first dynamic box."),
                        ], style={"marginTop": 0}),
                        html.P("Examples:", style={"fontWeight": "bold", "marginBottom": "4px"}),
                        html.Ul([
                            html.Li("Offset 0%: enter reversal as soon as the signal level is touched."),
                            html.Li("Offset 0.25% on resistance: wait until high reaches resistance +0.25%, then test SELL reversal."),
                            html.Li("Offset 0.25% on support: wait until low reaches support -0.25%, then test BUY reversal."),
                            html.Li("Dynamic stop rule 1:0.3 still means: after +1% favorable reversal move, move stop to lock +0.3%."),
                        ], style={"marginTop": 0}),
                        html.P(
                            "The level-reversal summary table shows triggered entries, not-triggered entries, TP hit rows, SL events, "
                            "adverse-DD events, stop-after-TP, dynamic-stop-moved rows, SL grid rows, and entry-offset grid rows as one unified level-rejection strategy.",
                            style={"marginBottom": 0}
                        ),
                    ], style={"fontSize": "13px", "lineHeight": "1.4", "padding": "8px", "backgroundColor": "#fff4de", "border": "1px solid #f4d19b", "borderRadius": "4px", "margin": "8px 0"})
                ], open=False),
                html.Div([
                    html.Label("Entry offset beyond level %:", style={"width": "210px", "display": "inline-block"}),
                    html.Span(" ⓘ", title="0 means enter at the signal level. 0.2 means wait for 0.2% beyond resistance/support before entering the reversal trade.", style={"cursor": "help", "color": "#0b63b6"}),
                    dcc.Input(id="level-reversal-offset-input", type="number", value=0, min=0, step=0.05, style={"width": "90px"}),
                    html.Label("Initial stop loss %:", style={"width": "150px", "display": "inline-block", "marginLeft": "20px"}),
                    html.Span(" ⓘ", title="Loss distance from reversal entry. Resistance reversal is SELL, support reversal is BUY.", style={"cursor": "help", "color": "#0b63b6"}),
                    dcc.Input(id="level-reversal-sl-input", type="number", value=0.5, min=0, step=0.05, style={"width": "90px"}),
                    html.Label("Max adverse DD %:", style={"width": "140px", "display": "inline-block", "marginLeft": "20px"}),
                    dcc.Input(id="level-reversal-max-dd-input", type="number", value=None, min=0, step=0.1, placeholder="optional", style={"width": "110px"}),
                ], style={"marginBottom": "10px"}),
                html.Div([
                    html.Label("Take profit levels %:", style={"width": "210px", "display": "inline-block"}),
                    dcc.Input(id="level-reversal-tp-levels-input", type="text", value="0.5, 1, 2, 4", style={"width": "240px"}),
                    html.Label("Dynamic stop rules:", style={"width": "150px", "display": "inline-block", "marginLeft": "20px"}),
                    dcc.Input(id="level-reversal-trail-rules-input", type="text", value="0.5:0, 1:0.5, 2:1, 4:2", style={"width": "320px"}),
                ], style={"marginBottom": "10px"}),
                html.Div([
                    html.Label("SL grid %:", style={"width": "210px", "display": "inline-block"}),
                    dcc.Input(id="level-reversal-sl-grid-input", type="text", value="0.25, 0.5, 0.75, 1", style={"width": "260px"}),
                    html.Label("Entry offset grid %:", style={"width": "150px", "display": "inline-block", "marginLeft": "20px"}),
                    dcc.Input(id="level-reversal-offset-grid-input", type="text", value="0, 0.1, 0.25, 0.5", style={"width": "220px"}),
                ], style={"marginBottom": "10px"}),
                html.Div([
                    html.Label("Notional per trade USD:", style={"width": "210px", "display": "inline-block"}),
                    html.Span(" ⓘ", title="Diagnostic position size used only for estimated P/L. Example: 1000 means each triggered reversal entry is counted as a 1000 USD notional trade.", style={"cursor": "help", "color": "#0b63b6"}),
                    dcc.Input(id="level-reversal-notional-input", type="number", value=1000, min=0, step=100, style={"width": "110px"}),
                    html.Label("Round-trip costs %:", style={"width": "150px", "display": "inline-block", "marginLeft": "20px"}),
                    html.Span(" ⓘ", title="Estimated total entry+exit cost as percent of notional, including fees, spread, slippage, and funding if applicable. It is subtracted from every triggered reversal trade.", style={"cursor": "help", "color": "#0b63b6"}),
                    dcc.Input(id="level-reversal-cost-input", type="number", value=0.10, min=0, step=0.01, style={"width": "90px"}),
                    html.Label("Open/no-exit return %:", style={"width": "165px", "display": "inline-block", "marginLeft": "20px"}),
                    html.Span(" ⓘ", title="Fallback return for diagnostic paths that never hit SL, DD cap, or moved stop. Use 0 for conservative flat close unless you define a forced end-of-window exit rule.", style={"cursor": "help", "color": "#0b63b6"}),
                    dcc.Input(id="level-reversal-open-return-input", type="number", value=0, step=0.1, style={"width": "90px"}),
                ], style={"marginBottom": "10px"}),
                html.Button("Run Level-Reversal Checkup", id="level-reversal-run-btn", n_clicks=0, style={"fontWeight": "bold"}),
                dcc.Loading(
                    type="circle",
                    children=[
                        html.Div(id="level-reversal-status", style={"marginTop": "10px", "fontWeight": "bold"}),
                        html.Div(
                            id="level-reversal-results",
                            style={
                                "marginTop": "10px",
                                "maxHeight": "420px",
                                "overflowY": "auto",
                                "border": "1px solid #ddd",
                                "borderRadius": "4px",
                                "padding": "8px",
                                "backgroundColor": "#fff",
                            }
                        ),
                    ],
                ),
            ], style={"padding": "10px", "backgroundColor": "#fffaf2", "borderRadius": "5px", "border": "1px solid #f4d19b"})
        ], open=False, style={"marginBottom": "20px"}),
        # ----- Oscillator-confirmed Level-Reversal Checkup -----
        html.Details([
            html.Summary("🧪 Oscillator Level-Reversal Checkup – level cross + Stoch/RSI trigger", style={"fontWeight": "bold", "cursor": "pointer"}),
            html.Div([
                html.P(
                    "Waits for price to cross the signal level in the toward direction, then selects the UP-toward or DOWN-toward oscillator group. "
                    "When all enabled Stoch/RSI conditions in that group match, it enters the reverse side and runs the same SL/TP/DD/trailing-stop simulation.",
                    style={"marginTop": "10px", "color": "#555"}
                ),
                html.Details([
                    html.Summary("ⓘ Logic and examples", style={"cursor": "pointer", "color": "#4a148c", "fontWeight": "bold"}),
                    html.Div([
                        html.Ul([
                            html.Li("Resistance means the toward move is UP to resistance; the UP-toward group is used and the test enters SELL after confirmation."),
                            html.Li("Support means the toward move is DOWN to support; the DOWN-toward group is used and the test enters BUY after confirmation."),
                            html.Li("Use the UP-toward group for upper-limit logic, e.g. Stoch crossing down from 87 after price reaches resistance."),
                            html.Li("Use the DOWN-toward group for lower-limit logic, e.g. Stoch crossing up from 13 after price reaches support."),
                            html.Li("Stoch lines match the chart: K 14/1/3, K 40/1/4, K 60/1/10, K 300/1/10."),
                            html.Li("Cross down 87 means previous value was above 87 and current value is at/below 87; Cross up 13 means previous value was below 13 and current value is at/above 13."),
                            html.Li("RSI(14,14) means RSI(14) smoothed by a 14-candle average. Disable RSI if you only want Stochastic."),
                            html.Li("Speed note: candle paths and oscillator lines are cached per task snapshot, so changing only levels/conditions should be faster on repeated runs."),
                            html.Li("Exit note: TP levels in this table are favorable-move checkpoints, not real take-profit orders. Actual exits are original SL, moved/trailing stop, max-DD cap, stochastic close, or open/no-exit fallback."),
                            html.Li("Original SL hit means the first stop-loss set in the menu was reached before any moved stop or stochastic close. Moved-stop rows mean price first reached the trigger, then later closed by that adjusted stop."),
                            html.Li("The optional stochastic close section reports whether the trade closed by the four stochastic curves and buckets those realized returns so you can see losses vs profit ranges."),
                            html.Li("Condition windows broaden multi-oscillator checks: a window of 1 requires all enabled conditions on the same candle; a window of 3 allows each condition to occur within the current candle or previous 2 candles."),
                            html.Li("Maintenance note: this checkup is isolated in the strategy-checkup helper section so future curves can be added by extending oscillator specs instead of touching table/chart code."),
                        ], style={"marginTop": 0}),
                    ], style={"fontSize": "13px", "lineHeight": "1.4", "padding": "8px", "backgroundColor": "#f3e5f5", "border": "1px solid #ce93d8", "borderRadius": "4px", "margin": "8px 0"})
                ], open=False),
                html.Div([
                    html.H5("UP-toward oscillator group (resistance → reverse SELL)", style={"margin": "8px 0", "color": "#6a1b9a"}),
                    html.Label("Stoch 14/1/3:", style={"width": "120px", "display": "inline-block"}),
                    dcc.Input(id="osc-stoch-14-level-input", type="number", value=87, min=0, max=100, step=0.5, style={"width": "80px"}),
                    dcc.Dropdown(id="osc-stoch-14-condition-input", options=[{"label": "Cross down", "value": "cross_down"}, {"label": "Cross up", "value": "cross_up"}, {"label": "Above", "value": "above"}, {"label": "Below", "value": "below"}, {"label": "Disabled", "value": "disabled"}], value="cross_down", clearable=False, style={"width": "140px", "display": "inline-block", "verticalAlign": "middle", "marginLeft": "8px"}),
                    html.Label("Stoch 40/1/4:", style={"width": "120px", "display": "inline-block", "marginLeft": "18px"}),
                    dcc.Input(id="osc-stoch-40-level-input", type="number", value=87, min=0, max=100, step=0.5, style={"width": "80px"}),
                    dcc.Dropdown(id="osc-stoch-40-condition-input", options=[{"label": "Cross down", "value": "cross_down"}, {"label": "Cross up", "value": "cross_up"}, {"label": "Above", "value": "above"}, {"label": "Below", "value": "below"}, {"label": "Disabled", "value": "disabled"}], value="cross_down", clearable=False, style={"width": "140px", "display": "inline-block", "verticalAlign": "middle", "marginLeft": "8px"}),
                ], style={"marginBottom": "10px"}),
                html.Div([
                    html.Label("Stoch 60/1/10:", style={"width": "120px", "display": "inline-block"}),
                    dcc.Input(id="osc-stoch-60-level-input", type="number", value=87, min=0, max=100, step=0.5, style={"width": "80px"}),
                    dcc.Dropdown(id="osc-stoch-60-condition-input", options=[{"label": "Cross down", "value": "cross_down"}, {"label": "Cross up", "value": "cross_up"}, {"label": "Above", "value": "above"}, {"label": "Below", "value": "below"}, {"label": "Disabled", "value": "disabled"}], value="cross_down", clearable=False, style={"width": "140px", "display": "inline-block", "verticalAlign": "middle", "marginLeft": "8px"}),
                    html.Label("Stoch 300/1/10:", style={"width": "125px", "display": "inline-block", "marginLeft": "18px"}),
                    dcc.Input(id="osc-stoch-300-level-input", type="number", value=87, min=0, max=100, step=0.5, style={"width": "80px"}),
                    dcc.Dropdown(id="osc-stoch-300-condition-input", options=[{"label": "Cross down", "value": "cross_down"}, {"label": "Cross up", "value": "cross_up"}, {"label": "Above", "value": "above"}, {"label": "Below", "value": "below"}, {"label": "Disabled", "value": "disabled"}], value="cross_down", clearable=False, style={"width": "140px", "display": "inline-block", "verticalAlign": "middle", "marginLeft": "8px"}),
                ], style={"marginBottom": "10px"}),
                html.Div([
                    html.Label("RSI(14,14):", style={"width": "120px", "display": "inline-block"}),
                    dcc.Input(id="osc-rsi-level-input", type="number", value=70, min=0, max=100, step=0.5, style={"width": "80px"}),
                    dcc.Dropdown(id="osc-rsi-condition-input", options=[{"label": "Cross down", "value": "cross_down"}, {"label": "Cross up", "value": "cross_up"}, {"label": "Above", "value": "above"}, {"label": "Below", "value": "below"}, {"label": "Disabled", "value": "disabled"}], value="disabled", clearable=False, style={"width": "140px", "display": "inline-block", "verticalAlign": "middle", "marginLeft": "8px"}),
                ], style={"marginBottom": "12px"}),
                html.Div([
                    html.H5("DOWN-toward oscillator group (support → reverse BUY)", style={"margin": "8px 0", "color": "#1565c0"}),
                    html.Label("Stoch 14/1/3:", style={"width": "120px", "display": "inline-block"}),
                    dcc.Input(id="osc-down-stoch-14-level-input", type="number", value=13, min=0, max=100, step=0.5, style={"width": "80px"}),
                    dcc.Dropdown(id="osc-down-stoch-14-condition-input", options=[{"label": "Cross down", "value": "cross_down"}, {"label": "Cross up", "value": "cross_up"}, {"label": "Above", "value": "above"}, {"label": "Below", "value": "below"}, {"label": "Disabled", "value": "disabled"}], value="cross_up", clearable=False, style={"width": "140px", "display": "inline-block", "verticalAlign": "middle", "marginLeft": "8px"}),
                    html.Label("Stoch 40/1/4:", style={"width": "120px", "display": "inline-block", "marginLeft": "18px"}),
                    dcc.Input(id="osc-down-stoch-40-level-input", type="number", value=13, min=0, max=100, step=0.5, style={"width": "80px"}),
                    dcc.Dropdown(id="osc-down-stoch-40-condition-input", options=[{"label": "Cross down", "value": "cross_down"}, {"label": "Cross up", "value": "cross_up"}, {"label": "Above", "value": "above"}, {"label": "Below", "value": "below"}, {"label": "Disabled", "value": "disabled"}], value="cross_up", clearable=False, style={"width": "140px", "display": "inline-block", "verticalAlign": "middle", "marginLeft": "8px"}),
                ], style={"marginBottom": "10px"}),
                html.Div([
                    html.Label("Stoch 60/1/10:", style={"width": "120px", "display": "inline-block"}),
                    dcc.Input(id="osc-down-stoch-60-level-input", type="number", value=13, min=0, max=100, step=0.5, style={"width": "80px"}),
                    dcc.Dropdown(id="osc-down-stoch-60-condition-input", options=[{"label": "Cross down", "value": "cross_down"}, {"label": "Cross up", "value": "cross_up"}, {"label": "Above", "value": "above"}, {"label": "Below", "value": "below"}, {"label": "Disabled", "value": "disabled"}], value="cross_up", clearable=False, style={"width": "140px", "display": "inline-block", "verticalAlign": "middle", "marginLeft": "8px"}),
                    html.Label("Stoch 300/1/10:", style={"width": "125px", "display": "inline-block", "marginLeft": "18px"}),
                    dcc.Input(id="osc-down-stoch-300-level-input", type="number", value=13, min=0, max=100, step=0.5, style={"width": "80px"}),
                    dcc.Dropdown(id="osc-down-stoch-300-condition-input", options=[{"label": "Cross down", "value": "cross_down"}, {"label": "Cross up", "value": "cross_up"}, {"label": "Above", "value": "above"}, {"label": "Below", "value": "below"}, {"label": "Disabled", "value": "disabled"}], value="cross_up", clearable=False, style={"width": "140px", "display": "inline-block", "verticalAlign": "middle", "marginLeft": "8px"}),
                ], style={"marginBottom": "10px"}),
                html.Div([
                    html.Label("RSI(14,14):", style={"width": "120px", "display": "inline-block"}),
                    dcc.Input(id="osc-down-rsi-level-input", type="number", value=30, min=0, max=100, step=0.5, style={"width": "80px"}),
                    dcc.Dropdown(id="osc-down-rsi-condition-input", options=[{"label": "Cross down", "value": "cross_down"}, {"label": "Cross up", "value": "cross_up"}, {"label": "Above", "value": "above"}, {"label": "Below", "value": "below"}, {"label": "Disabled", "value": "disabled"}], value="disabled", clearable=False, style={"width": "140px", "display": "inline-block", "verticalAlign": "middle", "marginLeft": "8px"}),
                ], style={"marginBottom": "10px"}),
                html.Div([
                    html.Label("Initial SL %:", style={"width": "100px", "display": "inline-block"}), dcc.Input(id="osc-reversal-sl-input", type="number", value=0.5, min=0, step=0.05, style={"width": "90px"}),
                    html.Label("Max DD %:", style={"width": "85px", "display": "inline-block", "marginLeft": "20px"}), dcc.Input(id="osc-reversal-max-dd-input", type="number", value=None, min=0, step=0.1, placeholder="optional", style={"width": "110px"}),
                    html.Label("TP levels %:", style={"width": "95px", "display": "inline-block", "marginLeft": "20px"}), dcc.Input(id="osc-reversal-tp-levels-input", type="text", value="0.5, 1, 2, 4", style={"width": "220px"}),
                ], style={"marginBottom": "10px"}),
                html.Div([
                    html.Label("Stop rules:", style={"width": "100px", "display": "inline-block"}), dcc.Input(id="osc-reversal-trail-rules-input", type="text", value="0.5:0, 1:0.5, 2:1, 4:2", style={"width": "320px"}),
                    html.Label("SL grid %:", style={"width": "80px", "display": "inline-block", "marginLeft": "20px"}), dcc.Input(id="osc-reversal-sl-grid-input", type="text", value="0.25, 0.5, 0.75, 1", style={"width": "220px"}),
                ], style={"marginBottom": "10px"}),
                html.Div([
                    html.Label("Entry condition window:", style={"width": "150px", "display": "inline-block"}),
                    html.Span(" ⓘ", title="Number of candles where oscillator entry conditions may line up. 1 means all enabled conditions must be true on the same candle. 3 means each enabled condition may have occurred within the current candle or previous 2 candles.", style={"cursor": "help", "color": "#4a148c"}),
                    dcc.Input(id="osc-entry-window-input", type="number", value=1, min=1, step=1, style={"width": "70px"}),
                    html.Label("Close condition window:", style={"width": "150px", "display": "inline-block", "marginLeft": "20px"}),
                    html.Span(" ⓘ", title="Number of candles where stochastic close conditions may line up. Use 2-5 to avoid requiring Stoch 14/40/60/300 crosses on the exact same candle.", style={"cursor": "help", "color": "#4a148c"}),
                    dcc.Input(id="osc-exit-window-input", type="number", value=1, min=1, step=1, style={"width": "70px"}),
                    html.Span("1 = same candle; 3 = current + previous 2 candles", style={"marginLeft": "10px", "color": "#777"}),
                ], style={"marginBottom": "10px"}),
                html.Details([
                    html.Summary("Optional stochastic close confirmation", style={"cursor": "pointer", "color": "#4a148c", "fontWeight": "bold"}),
                    html.Div([
                        html.P("When enabled, the simulated position waits for these four stochastic conditions after entry and closes on that candle close. If they do not trigger first, the normal stop-loss / DD / moved-stop logic can still close the position.", style={"margin": "6px 0", "color": "#555"}),
                        html.Div([
                            dcc.Checklist(id="osc-exit-enabled-input", options=[{"label": "Enable stochastic close", "value": "enabled"}], value=[], style={"display": "inline-block", "marginRight": "20px"}),
                        ], style={"marginBottom": "8px"}),
                        html.Div([
                            html.H5("Close SELL positions (resistance entries)", style={"margin": "8px 0", "color": "#6a1b9a"}),
                            html.Label("Stoch 14/1/3:", style={"width": "120px", "display": "inline-block"}),
                            dcc.Input(id="osc-exit-sell-stoch-14-level-input", type="number", value=13, min=0, max=100, step=0.5, style={"width": "80px"}),
                            dcc.Dropdown(id="osc-exit-sell-stoch-14-condition-input", options=[{"label": "Cross down", "value": "cross_down"}, {"label": "Cross up", "value": "cross_up"}, {"label": "Above", "value": "above"}, {"label": "Below", "value": "below"}, {"label": "Disabled", "value": "disabled"}], value="cross_up", clearable=False, style={"width": "140px", "display": "inline-block", "verticalAlign": "middle", "marginLeft": "8px"}),
                            html.Label("Stoch 40/1/4:", style={"width": "120px", "display": "inline-block", "marginLeft": "18px"}),
                            dcc.Input(id="osc-exit-sell-stoch-40-level-input", type="number", value=13, min=0, max=100, step=0.5, style={"width": "80px"}),
                            dcc.Dropdown(id="osc-exit-sell-stoch-40-condition-input", options=[{"label": "Cross down", "value": "cross_down"}, {"label": "Cross up", "value": "cross_up"}, {"label": "Above", "value": "above"}, {"label": "Below", "value": "below"}, {"label": "Disabled", "value": "disabled"}], value="cross_up", clearable=False, style={"width": "140px", "display": "inline-block", "verticalAlign": "middle", "marginLeft": "8px"}),
                        ], style={"marginBottom": "8px"}),
                        html.Div([
                            html.Label("Stoch 60/1/10:", style={"width": "120px", "display": "inline-block"}),
                            dcc.Input(id="osc-exit-sell-stoch-60-level-input", type="number", value=13, min=0, max=100, step=0.5, style={"width": "80px"}),
                            dcc.Dropdown(id="osc-exit-sell-stoch-60-condition-input", options=[{"label": "Cross down", "value": "cross_down"}, {"label": "Cross up", "value": "cross_up"}, {"label": "Above", "value": "above"}, {"label": "Below", "value": "below"}, {"label": "Disabled", "value": "disabled"}], value="cross_up", clearable=False, style={"width": "140px", "display": "inline-block", "verticalAlign": "middle", "marginLeft": "8px"}),
                            html.Label("Stoch 300/1/10:", style={"width": "125px", "display": "inline-block", "marginLeft": "18px"}),
                            dcc.Input(id="osc-exit-sell-stoch-300-level-input", type="number", value=13, min=0, max=100, step=0.5, style={"width": "80px"}),
                            dcc.Dropdown(id="osc-exit-sell-stoch-300-condition-input", options=[{"label": "Cross down", "value": "cross_down"}, {"label": "Cross up", "value": "cross_up"}, {"label": "Above", "value": "above"}, {"label": "Below", "value": "below"}, {"label": "Disabled", "value": "disabled"}], value="cross_up", clearable=False, style={"width": "140px", "display": "inline-block", "verticalAlign": "middle", "marginLeft": "8px"}),
                        ], style={"marginBottom": "10px"}),
                        html.Div([
                            html.H5("Close BUY positions (support entries)", style={"margin": "8px 0", "color": "#1565c0"}),
                            html.Label("Stoch 14/1/3:", style={"width": "120px", "display": "inline-block"}),
                            dcc.Input(id="osc-exit-buy-stoch-14-level-input", type="number", value=87, min=0, max=100, step=0.5, style={"width": "80px"}),
                            dcc.Dropdown(id="osc-exit-buy-stoch-14-condition-input", options=[{"label": "Cross down", "value": "cross_down"}, {"label": "Cross up", "value": "cross_up"}, {"label": "Above", "value": "above"}, {"label": "Below", "value": "below"}, {"label": "Disabled", "value": "disabled"}], value="cross_down", clearable=False, style={"width": "140px", "display": "inline-block", "verticalAlign": "middle", "marginLeft": "8px"}),
                            html.Label("Stoch 40/1/4:", style={"width": "120px", "display": "inline-block", "marginLeft": "18px"}),
                            dcc.Input(id="osc-exit-buy-stoch-40-level-input", type="number", value=87, min=0, max=100, step=0.5, style={"width": "80px"}),
                            dcc.Dropdown(id="osc-exit-buy-stoch-40-condition-input", options=[{"label": "Cross down", "value": "cross_down"}, {"label": "Cross up", "value": "cross_up"}, {"label": "Above", "value": "above"}, {"label": "Below", "value": "below"}, {"label": "Disabled", "value": "disabled"}], value="cross_down", clearable=False, style={"width": "140px", "display": "inline-block", "verticalAlign": "middle", "marginLeft": "8px"}),
                        ], style={"marginBottom": "8px"}),
                        html.Div([
                            html.Label("Stoch 60/1/10:", style={"width": "120px", "display": "inline-block"}),
                            dcc.Input(id="osc-exit-buy-stoch-60-level-input", type="number", value=87, min=0, max=100, step=0.5, style={"width": "80px"}),
                            dcc.Dropdown(id="osc-exit-buy-stoch-60-condition-input", options=[{"label": "Cross down", "value": "cross_down"}, {"label": "Cross up", "value": "cross_up"}, {"label": "Above", "value": "above"}, {"label": "Below", "value": "below"}, {"label": "Disabled", "value": "disabled"}], value="cross_down", clearable=False, style={"width": "140px", "display": "inline-block", "verticalAlign": "middle", "marginLeft": "8px"}),
                            html.Label("Stoch 300/1/10:", style={"width": "125px", "display": "inline-block", "marginLeft": "18px"}),
                            dcc.Input(id="osc-exit-buy-stoch-300-level-input", type="number", value=87, min=0, max=100, step=0.5, style={"width": "80px"}),
                            dcc.Dropdown(id="osc-exit-buy-stoch-300-condition-input", options=[{"label": "Cross down", "value": "cross_down"}, {"label": "Cross up", "value": "cross_up"}, {"label": "Above", "value": "above"}, {"label": "Below", "value": "below"}, {"label": "Disabled", "value": "disabled"}], value="cross_down", clearable=False, style={"width": "140px", "display": "inline-block", "verticalAlign": "middle", "marginLeft": "8px"}),
                        ], style={"marginBottom": "4px"}),
                    ], style={"padding": "8px", "backgroundColor": "#f8edff", "border": "1px solid #ce93d8", "borderRadius": "4px", "margin": "8px 0"})
                ], open=False, style={"marginBottom": "10px"}),
                html.Div([
                    html.Label("Notional USD:", style={"width": "100px", "display": "inline-block"}), dcc.Input(id="osc-reversal-notional-input", type="number", value=1000, min=0, step=100, style={"width": "110px"}),
                    html.Label("Costs %:", style={"width": "70px", "display": "inline-block", "marginLeft": "20px"}), dcc.Input(id="osc-reversal-cost-input", type="number", value=0.10, min=0, step=0.01, style={"width": "90px"}),
                    html.Label("Open/no-exit %:", style={"width": "120px", "display": "inline-block", "marginLeft": "20px"}), dcc.Input(id="osc-reversal-open-return-input", type="number", value=0, step=0.1, style={"width": "90px"}),
                ], style={"marginBottom": "10px"}),
                html.Div([
                    html.Label("Settings name:", style={"width": "100px", "display": "inline-block"}),
                    dcc.Input(id="osc-settings-name-input", type="text", placeholder="my stochastic setup", style={"width": "220px"}),
                    html.Button("Save Settings", id="osc-settings-save-btn", n_clicks=0, style={"marginLeft": "8px"}),
                    html.Label("Open:", style={"marginLeft": "16px", "marginRight": "6px"}),
                    dcc.Dropdown(id="osc-settings-open-dropdown", options=strategy_setting_options(), value=None, placeholder="choose saved settings", clearable=False, style={"width": "260px", "display": "inline-block", "verticalAlign": "middle"}),
                    html.Button("Open Settings", id="osc-settings-open-btn", n_clicks=0, style={"marginLeft": "8px"}),
                    html.Div(id="osc-settings-status", style={"marginTop": "6px", "color": "#4a148c", "fontWeight": "bold"}),
                ], style={"marginBottom": "10px", "padding": "8px", "backgroundColor": "#f1e8ff", "border": "1px solid #ce93d8", "borderRadius": "4px"}),
                html.Button("Run Oscillator Reversal Checkup", id="osc-reversal-run-btn", n_clicks=0, style={"fontWeight": "bold"}),
                dcc.Loading(type="circle", children=[html.Div(id="osc-reversal-status", style={"marginTop": "10px", "fontWeight": "bold"}), html.Div(id="osc-reversal-results", style={"marginTop": "10px", "maxHeight": "420px", "overflowY": "auto", "border": "1px solid #ddd", "borderRadius": "4px", "padding": "8px", "backgroundColor": "#fff"})]),
                html.Details([
                    html.Summary("🔎 Research optimizer – compare oscillator/SL/stop combinations", style={"fontWeight": "bold", "cursor": "pointer", "color": "#4a148c", "marginTop": "14px"}),
                    html.Div([
                        html.P("Research mode runs multiple what-if combinations over historical candles and ranks them by net expectancy. It is for discovery/optimization, not a no-lookahead trading signal. After finding a candidate, validate it on a separate date range.", style={"color": "#555", "margin": "6px 0"}),
                        html.Details([html.Summary("ⓘ How research optimizer works", style={"cursor": "pointer", "color": "#4a148c", "fontWeight": "bold"}), html.Ul([
                            html.Li("It reuses the oscillator settings above as the base condition set."),
                            html.Li("Condition variants test Base, Relaxed, and Strict levels. Relaxed makes high-threshold groups easier and low-threshold groups easier; Strict does the opposite."),
                            html.Li("Window grids test whether conditions should align on the same candle or within several candles."),
                            html.Li("SL grid and stop-rule presets test risk management combinations side by side."),
                            html.Li("The ranked table includes entries, win-rate %, stop exits, stochastic exits, TP checkpoint success %, profit buckets, net expectancy, profit factor, and a plain-language advice column."),
                            html.Li("It does not magically know future live reversals; it researches historical candles to find which settings would have captured reversals with lower adverse movement and better net results."),
                        ], style={"fontSize": "13px", "lineHeight": "1.4"})], open=False),
                        html.Div([
                            html.Label("Entry windows:", style={"width": "110px", "display": "inline-block"}), dcc.Input(id="osc-research-entry-windows-input", type="text", value="1, 3, 5", style={"width": "140px"}),
                            html.Label("Close windows:", style={"width": "110px", "display": "inline-block", "marginLeft": "15px"}), dcc.Input(id="osc-research-exit-windows-input", type="text", value="1, 3, 5", style={"width": "140px"}),
                            html.Label("SL grid %:", style={"width": "80px", "display": "inline-block", "marginLeft": "15px"}), dcc.Input(id="osc-research-sl-grid-input", type="text", value="1, 1.5, 2, 2.5, 3", style={"width": "180px"}),
                        ], style={"marginBottom": "8px"}),
                        html.Div([
                            html.Label("Stop-rule presets:", style={"width": "120px", "display": "inline-block"}),
                            dcc.Textarea(id="osc-research-stop-presets-input", value="1:0.35, 1.5:0.75, 2:1, 3:2, 4:3 | 0.7:0.25, 1:0.5, 2:1, 3:2, 4:3 | 1:0.5, 2:1, 3:2, 4:3", style={"width": "640px", "height": "44px", "verticalAlign": "middle"}),
                            html.Span("Separate presets with |", style={"marginLeft": "8px", "color": "#777"}),
                        ], style={"marginBottom": "8px"}),
                        html.Div([
                            html.Label("Max combinations:", style={"width": "120px", "display": "inline-block"}), dcc.Input(id="osc-research-max-combos-input", type="number", value=120, min=1, max=500, step=1, style={"width": "90px"}),
                            html.Label("Top rows:", style={"width": "80px", "display": "inline-block", "marginLeft": "15px"}), dcc.Input(id="osc-research-top-input", type="number", value=20, min=5, max=100, step=1, style={"width": "80px"}),
                            html.Button("Run Research Optimizer", id="osc-research-run-btn", n_clicks=0, style={"fontWeight": "bold", "marginLeft": "15px"}),
                        ], style={"marginBottom": "8px"}),
                        dcc.Loading(type="circle", children=[html.Div(id="osc-research-status", style={"marginTop": "8px", "fontWeight": "bold"}), html.Div(id="osc-research-results", style={"marginTop": "10px", "maxHeight": "520px", "overflowY": "auto", "border": "1px solid #ddd", "borderRadius": "4px", "padding": "8px", "backgroundColor": "#fff"})]),
                    ], style={"padding": "8px", "backgroundColor": "#f6edff", "border": "1px solid #ce93d8", "borderRadius": "4px", "marginTop": "8px"}),
                ], open=False),
            ], style={"padding": "10px", "backgroundColor": "#fbf3ff", "borderRadius": "5px", "border": "1px solid #ce93d8"})
        ], open=False, style={"marginBottom": "20px"}),
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
        # Hidden target keeps the dedicated summary-stat cache callback active;
        # visible summaries remain embedded in the task table below.
        html.Div(id="summary-stats-container", style={"display": "none"}),
        html.Div(id="task-table-container", style={"width": "100%"}),
    ])


@app.callback(
    Output("tab-content", "children"),
    Input("main-tabs", "value")
)
def render_tab(tab):
    if tab == "tab-tasks":
        return build_tasks_tab_layout()
    else:
        # Data Analysis tab - now imported from database module
        return create_data_analysis_tab()

# =============================================================================
# 14. CALLBACKS: SIGNAL INPUT AND TASK CREATION
# =============================================================================
# These callbacks parse uploaded/pasted signals and create DownloadTask objects.
# They coordinate UI stores and Golden Store publication but should delegate math
# to task/analysis helpers.
# =============================================================================

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


def build_task_creation_options(ow, beyond_val, strat_val, imp_val, event_log_val, hide_logs_val, pre_buffer):
    """Normalize Create Tasks UI values into the flags used by existing logic."""
    return {
        'ow_flag': "overwrite" in ow if ow else False,
        'analyze_beyond': "beyond" in beyond_val if beyond_val else False,
        'strat_disabled': "disable" in strat_val if strat_val else False,
        'imp_disabled': "disable" in imp_val if imp_val else False,
        'log_events': "disable" not in event_log_val if event_log_val else True,
        'hide_logs_val': hide_logs_val,
        'pre_buffer': pre_buffer,
    }


def initialize_task_creation_state(stored_ids, count, autoclear_val):
    """Return the starting task id/count state for Create Tasks.

    This preserves the existing auto-clear behavior exactly, including clearing
    the task manager's in-memory task map before new task creation begins.
    """
    if autoclear_val and "autoclear" in autoclear_val:
        tm.tasks.clear()
        return [], 0
    return stored_ids.copy() if stored_ids else [], count


def build_background_parse_data(signals, period_type, start_date, end_date, hours, tf, task_options, new_ids, new_count):
    """Build the payload consumed by _run_parse_background using existing keys."""
    return {
        'signals': signals,
        'period_type': period_type,
        'start_date': start_date,
        'end_date': end_date,
        'hours': hours,
        'tf': tf,
        'ow_flag': task_options['ow_flag'],
        'analyze_beyond': task_options['analyze_beyond'],
        'strat_disabled': task_options['strat_disabled'],
        'imp_disabled': task_options['imp_disabled'],
        'log_events': task_options['log_events'],
        'hide_logs_val': task_options['hide_logs_val'],
        'pre_buffer': task_options['pre_buffer'],
        'existing_ids': list(new_ids),
        'existing_count': new_count
    }


@app.callback(
    Output("task-ids-store", "data", allow_duplicate=True),
    Output("task-count-store", "data", allow_duplicate=True),
    Output("task-page-store", "data", allow_duplicate=True),
    Output("golden-store-version", "data", allow_duplicate=True),
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
        return stored_ids, count, dash.no_update, dash.no_update
    
    task_options = build_task_creation_options(
        ow, beyond_val, strat_val, imp_val, event_log_val, hide_logs_val, pre_buffer
    )
    new_ids, new_count = initialize_task_creation_state(stored_ids, count, autoclear_val)
        
    buffer_ms = SIGNAL_BUFFER_MINUTES * 60 * 1000
    
    total_signals = len(signals)
    
    # 🔧 CRITICAL: For large batches (>100 signals), use background processing
    # This prevents UI freeze during parsing
    if total_signals > 100:
        print(f"🚀 Large batch detected ({total_signals} signals) - using background processing...")
        
        # 🔧 Prepare serialized data for background thread
        parse_data = build_background_parse_data(
            signals, period_type, start_date, end_date, hours, tf,
            task_options, new_ids, new_count
        )
        
        # 🔧 Start background thread
        import threading
        threading.Thread(target=_run_parse_background, args=(parse_data,), daemon=True).start()
        
        # 🔧 Return updated IDs immediately and reset the table to the first page.
        # The background thread publishes the final Golden Store snapshot; the
        # interval-based version sync below propagates that server-side version
        # bump back into the client store so the table refreshes when parsing is done.
        return new_ids, new_count, 0, get_golden_store_version()
    
    # 🔧 SMALL BATCH: Process synchronously (original logic with improved progress)
    return _process_signals_sync(signals, period_type, start_date, end_date, hours, tf,
                                  task_options['ow_flag'], task_options['analyze_beyond'],
                                  task_options['strat_disabled'], task_options['imp_disabled'],
                                  task_options['log_events'], task_options['hide_logs_val'],
                                  task_options['pre_buffer'], new_ids, new_count)


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
    with tm.lock:
        task_snapshot = list(tm.tasks.values())
    published_version = publish_golden_task_snapshot(task_snapshot, reason="parse_sync")
    
    # Reset to page 1 and bump the client-side Golden Store version so the
    # summary and task-table callbacks render the tasks created by this click.
    return new_ids, new_count, 0, published_version


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
    with tm.lock:
        task_snapshot = list(tm.tasks.values())
    publish_golden_task_snapshot(task_snapshot, reason="parse_background")
    
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

# Dash 4's ``set_props`` is used directly by the global click handler above.
# Do not retain legacy dummy clientside callbacks here: an inline callback that
# is not present after a hot reload is exactly what produces renderer-side
# ``undefined.apply`` errors in older Dash/Chrome combinations.

# Details and Impulse use the same direct ``set_props`` path as Chart.

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
            # Never ship an unbounded task log through the browser every ten
            # seconds. This periodic payload could monopolize Dash rendering
            # exactly when a chart control was clicked.
            logs.append("\n".join(task.log[-200:]) if task.log else "No logs yet...")
            progs.append(str(task.progress))
            rem = max(0, task.total_candles - task.downloaded_candles) if task.total_candles else 0
            texts.append(f"{task.progress:.1f}%  {task.downloaded_candles}/{task.total_candles}/{rem}")
        else:
            logs.append("")
            progs.append("0")
            texts.append("0.0% 0/0/0")
    return logs, progs, texts

# =============================================================================
# 15. CALLBACKS: SUMMARY STATISTICS AND TASK TABLE REFRESH
# =============================================================================
# Heavy summary rendering and lightweight table rendering are intentionally split
# for performance. Golden Store version changes are the primary refresh signal.
# =============================================================================

# ============================================================================
# 🔧 SPLIT CALLBACK #1: Summary Statistics Only (HEAVY - runs ONCE per data load)
# ============================================================================
def get_toward_entry_level_distance_pct(task):
    """Return absolute distance from toward entry to parsed level as percent."""
    entry_price = getattr(task, 'toward_entry_price', None)
    level_price = getattr(task, 'signal_price', None)
    try:
        if entry_price is None or level_price is None:
            return None
        entry_price = float(entry_price)
        level_price = float(level_price)
        if entry_price <= 0:
            return None
        return abs(level_price - entry_price) / entry_price * 100
    except Exception:
        return None


def get_toward_distance_bucket(distance_pct):
    """Bucket entry-to-level distance for toward-strategy diagnostics."""
    if distance_pct is None or (isinstance(distance_pct, float) and is_na(distance_pct)):
        return None
    if 0 <= distance_pct < 0.12:
        return "0-0.12%"
    if 0.12 <= distance_pct < 0.5:
        return "0.12-0.5%"
    if 0.5 <= distance_pct < 1:
        return "0.5-1%"
    if 1 <= distance_pct < 2:
        return "1-2%"
    if 2 <= distance_pct < 4:
        return "2-4%"
    if distance_pct >= 4:
        return "4%+"
    return None


def build_toward_strategy_summary_rows(tasks, td_style, fmt_stat):
    """Build transparent toward-strategy funnel/diagnostic rows without changing math."""
    toward_cases = [t for t in tasks if getattr(t, 'toward_entry_price', None) is not None]
    toward_total = len(toward_cases)
    toward_stop_losses = sum(1 for t in toward_cases if getattr(t, 'toward_stop_loss_hit', False))
    toward_no_sl_return = sum(1 for t in toward_cases if getattr(t, 'toward_no_stop_returned_entry', False))
    toward_level_reached = sum(1 for t in toward_cases if getattr(t, 'toward_level_reached', False))
    stopped_before_level = sum(
        1 for t in toward_cases
        if getattr(t, 'toward_stop_loss_hit', False) and not getattr(t, 'toward_level_reached', False)
    )
    reached_before_stop = sum(
        1 for t in toward_cases
        if getattr(t, 'toward_level_reached', False) and not getattr(t, 'toward_stop_loss_hit', False)
    )
    both_stop_and_level = sum(
        1 for t in toward_cases
        if getattr(t, 'toward_level_reached', False) and getattr(t, 'toward_stop_loss_hit', False)
    )
    neither_stop_nor_level = max(0, toward_total - stopped_before_level - reached_before_stop - both_stop_and_level)

    distance_ranges = ["0-0.12%", "0.12-0.5%", "0.5-1%", "1-2%", "2-4%", "4%+"]
    distance_counts = {r: 0 for r in distance_ranges}
    distance_reached_counts = {r: 0 for r in distance_ranges}
    for task in toward_cases:
        bucket = get_toward_distance_bucket(get_toward_entry_level_distance_pct(task))
        if bucket:
            distance_counts[bucket] += 1
            if getattr(task, 'toward_level_reached', False) and not getattr(task, 'toward_stop_loss_hit', False):
                distance_reached_counts[bucket] += 1
    distance_row_1 = " | ".join(f"{r}:{distance_counts.get(r, 0)}" for r in distance_ranges[:3])
    distance_row_2 = " | ".join(f"{r}:{distance_counts.get(r, 0)}" for r in distance_ranges[3:])

    def fmt_bucket_rate(bucket):
        total = distance_counts.get(bucket, 0)
        reached = distance_reached_counts.get(bucket, 0)
        pct = (reached / total * 100) if total else 0
        return f"{bucket}:{reached}/{total} ({pct:.1f}%)"

    distance_reach_row_1 = " | ".join(fmt_bucket_rate(r) for r in distance_ranges[:3])
    distance_reach_row_2 = " | ".join(fmt_bucket_rate(r) for r in distance_ranges[3:])

    tp05_found = sum(1 for t in toward_cases if (getattr(t, 'toward_max_reached_pct', None) or 0) >= 0.5)
    tp05_then_reached = sum(
        1 for t in toward_cases
        if (getattr(t, 'toward_max_reached_pct', None) or 0) >= 0.5
        and getattr(t, 'toward_level_reached', False)
        and not getattr(t, 'toward_stop_loss_hit', False)
    )
    tp05_then_stopped = sum(
        1 for t in toward_cases
        if (getattr(t, 'toward_max_reached_pct', None) or 0) >= 0.5
        and getattr(t, 'toward_stop_loss_hit', False)
        and not getattr(t, 'toward_level_reached', False)
    )
    fixed_sl_before_tp05 = sum(
        1 for t in toward_cases
        if getattr(t, 'toward_stop_loss_hit', False)
        and (getattr(t, 'toward_max_reached_pct', None) or 0) < 0.5
    )
    reached_level_before_tp05 = sum(
        1 for t in toward_cases
        if getattr(t, 'toward_level_reached', False)
        and not getattr(t, 'toward_stop_loss_hit', False)
        and (getattr(t, 'toward_max_reached_pct', None) or 0) < 0.5
    )

    def fmt_conditional(count, total):
        return f"{count} / {total} ({count / total * 100:.1f}%)" if total else "0 / 0 (0.0%)"

    def subtotal_for_buckets(buckets, counts):
        return sum(counts.get(bucket, 0) for bucket in buckets)

    dist_le_05_buckets = ["0-0.12%", "0.12-0.5%"]
    dist_le_1_buckets = ["0-0.12%", "0.12-0.5%", "0.5-1%"]
    dist_le_05_total = subtotal_for_buckets(dist_le_05_buckets, distance_counts)
    dist_le_05_reached = subtotal_for_buckets(dist_le_05_buckets, distance_reached_counts)
    dist_le_1_total = subtotal_for_buckets(dist_le_1_buckets, distance_counts)
    dist_le_1_reached = subtotal_for_buckets(dist_le_1_buckets, distance_reached_counts)

    def fmt_quick_expectancy(win_count, win_pct, loss_count, loss_pct):
        total = win_count + loss_count
        gross_pct = (win_count * win_pct) - (loss_count * loss_pct)
        avg_pct = gross_pct / total if total else 0.0
        return f"gross {gross_pct:.2f}% | avg {avg_pct:.3f}%/case before fees"

    tp1_found = sum(1 for t in toward_cases if (getattr(t, 'toward_max_reached_pct', None) or 0) >= 1.0)
    tp1_then_reached = sum(
        1 for t in toward_cases
        if (getattr(t, 'toward_max_reached_pct', None) or 0) >= 1.0
        and getattr(t, 'toward_level_reached', False)
        and not getattr(t, 'toward_stop_loss_hit', False)
    )
    tp1_then_stopped = sum(
        1 for t in toward_cases
        if (getattr(t, 'toward_max_reached_pct', None) or 0) >= 1.0
        and getattr(t, 'toward_stop_loss_hit', False)
        and not getattr(t, 'toward_level_reached', False)
    )
    tp05_loss_count = max(0, toward_total - tp05_found)

    toward_strategy_rows = [
        html.Tr([html.Td("Toward strategy cases", style=td_style), html.Td(str(toward_total), style=td_style)]),
        html.Tr([html.Td("Toward stop losses 0.12%", style=td_style), html.Td(fmt_stat(toward_stop_losses, toward_total), style=td_style)]),
        html.Tr([html.Td("Toward stopped before level", style=td_style), html.Td(fmt_stat(stopped_before_level, toward_total), style=td_style)]),
        html.Tr([html.Td("Toward reached level", style=td_style), html.Td(fmt_stat(toward_level_reached, toward_total), style=td_style)]),
        html.Tr([html.Td("Toward reached before stop", style=td_style), html.Td(fmt_stat(reached_before_stop, toward_total), style=td_style)]),
        html.Tr([html.Td("Toward both SL and level flags", style=td_style), html.Td(fmt_stat(both_stop_and_level, toward_total), style=td_style)]),
        html.Tr([html.Td("Toward no SL + returned entry", style=td_style), html.Td(fmt_stat(toward_no_sl_return, toward_total), style=td_style)]),
        html.Tr([html.Td("Toward neither SL nor level", style=td_style), html.Td(fmt_stat(neither_stop_nor_level, toward_total), style=td_style)]),
        html.Tr([html.Td("Entry→Level dist 0-1%", style=td_style), html.Td(distance_row_1, style=td_style)]),
        html.Tr([html.Td("Entry→Level dist 1%+", style=td_style), html.Td(distance_row_2, style=td_style)]),
        html.Tr([html.Td("Reach rate by dist 0-1%", style=td_style), html.Td(distance_reach_row_1, style=td_style)]),
        html.Tr([html.Td("Reach rate by dist 1%+", style=td_style), html.Td(distance_reach_row_2, style=td_style)]),
        html.Tr([html.Td("Entry dist ≤0.5% reached", style=td_style), html.Td(fmt_conditional(dist_le_05_reached, dist_le_05_total), style=td_style)]),
        html.Tr([html.Td("Entry dist ≤1% reached", style=td_style), html.Td(fmt_conditional(dist_le_1_reached, dist_le_1_total), style=td_style)]),
        html.Tr([html.Td("TP 0.5 arm before fixed SL", style=td_style), html.Td(fmt_stat(tp05_found, toward_total), style=td_style)]),
        html.Tr([html.Td("TP 0.5 arm → reached level", style=td_style), html.Td(fmt_conditional(tp05_then_reached, tp05_found), style=td_style)]),
        html.Tr([html.Td("TP 0.5 arm → fixed SL before level", style=td_style), html.Td(fmt_conditional(tp05_then_stopped, tp05_found), style=td_style)]),
        html.Tr([html.Td("Fixed SL before TP 0.5 arm", style=td_style), html.Td(fmt_stat(fixed_sl_before_tp05, toward_total), style=td_style)]),
        html.Tr([html.Td("Reached level before TP 0.5 arm", style=td_style), html.Td(fmt_stat(reached_level_before_tp05, toward_total), style=td_style)]),
        html.Tr([html.Td("BE-after-0.5 protected fixed-SL cases", style=td_style), html.Td(fmt_conditional(tp05_then_stopped, tp05_found), style=td_style)]),
        html.Tr([html.Td("TP 1.0 arm before fixed SL", style=td_style), html.Td(fmt_stat(tp1_found, toward_total), style=td_style)]),
        html.Tr([html.Td("TP 1.0 arm → reached level", style=td_style), html.Td(fmt_conditional(tp1_then_reached, tp1_found), style=td_style)]),
        html.Tr([html.Td("TP 1.0 arm → fixed SL before level", style=td_style), html.Td(fmt_conditional(tp1_then_stopped, tp1_found), style=td_style)]),
        html.Tr([html.Td("Quick exp: TP0.5 vs SL0.12", style=td_style), html.Td(fmt_quick_expectancy(tp05_found, 0.5, tp05_loss_count, 0.12), style=td_style)]),
        html.Tr([html.Td("Quick exp: TP0.5 vs SL0.15", style=td_style), html.Td(fmt_quick_expectancy(tp05_found, 0.5, tp05_loss_count, 0.15), style=td_style)]),
        html.Tr([html.Td("Quick exp: TP0.5 vs SL0.25", style=td_style), html.Td(fmt_quick_expectancy(tp05_found, 0.5, tp05_loss_count, 0.25), style=td_style)]),
    ]

    for pct in TOWARD_LEVEL_TARGET_PCTS:
        label = "4%+" if pct >= 4 else f"{pct:g}%"
        found = sum(1 for t in toward_cases if (getattr(t, 'toward_max_reached_pct', None) or 0) >= pct)
        found_reached = sum(
            1 for t in toward_cases
            if (getattr(t, 'toward_max_reached_pct', None) or 0) >= pct
            and getattr(t, 'toward_level_reached', False)
            and not getattr(t, 'toward_stop_loss_hit', False)
        )
        found_stopped = sum(
            1 for t in toward_cases
            if (getattr(t, 'toward_max_reached_pct', None) or 0) >= pct
            and getattr(t, 'toward_stop_loss_hit', False)
            and not getattr(t, 'toward_level_reached', False)
        )
        toward_strategy_rows.extend([
            html.Tr([html.Td(f"Toward TP {label} found", style=td_style), html.Td(fmt_stat(found, toward_total), style=td_style)]),
            html.Tr([html.Td(f"Toward TP {label} + reached level", style=td_style), html.Td(fmt_stat(found_reached, reached_before_stop), style=td_style)]),
            html.Tr([html.Td(f"Toward TP {label} + stopped before level", style=td_style), html.Td(fmt_stat(found_stopped, stopped_before_level), style=td_style)]),
        ])

    return toward_strategy_rows


@app.callback(
    Output("summary-stats-container", "children"),
    Input("golden-store-version", "data"),  # ✅ FIXED: Only trigger when data version changes (not on page clicks)
    Input("recalc-lock-store", "data")
)
def update_summary_stats_only(version, lock_state):
    """Calculate summary statistics ONLY when golden_store_version changes.
    Does NOT run on page navigation - this is the key fix for 10-minute freeze."""
    global golden_task_store_data, golden_store_version, recalculation_complete_timestamp, cached_signal_stats_html, cached_toward_strategy_stats_html, cached_small_stats_data, stats_cache_version
    
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
        tasks = get_display_tasks_snapshot() if hasattr(tm, 'tasks') else []
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
    tasks = get_display_tasks_snapshot()
        
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

    toward_strategy_rows = build_toward_strategy_summary_rows(tasks, td_style, fmt_stat)
    toward_strategy_table = html.Table([html.Tbody(toward_strategy_rows)], style={"border": "1px solid #2e7d32", "padding": "5px", "marginTop": "10px", "backgroundColor": "#f1fff1"})

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
    cached_signal_stats_html = signal_stats_table
    cached_toward_strategy_stats_html = toward_strategy_table
    cached_small_stats_data = {"completed": completed_count, "total": total_tasks, "avg_adv": avg_adv, "avg_dd": avg_dd}
    stats_cache_version = golden_store_version
    
    return html.Div([
        stats_table,
        html.H5("Signal Performance Summary", style={"marginTop": "15px", "marginBottom": "5px"}),
        signal_stats_table,
        html.H5("Toward-Level Next-Candle Strategy Summary", style={"marginTop": "15px", "marginBottom": "5px"}),
        toward_strategy_table,
        html.P(
            "ℹ️ Hit % metrics measure price movement ≥1%/1.5%/2% **in the EXPECTED direction** from the signal level base. "
            "Resistance: Price moves UP ≥X% from level. Support: Price moves DOWN ≥X% from level. "
            "Hits are only counted if the price actually touched the level first. "
            "Toward-level strategy counts the MAX target reached before the 0.12% stop; if price reaches 0.5%, later pulls back, then reaches 2% without stop, it is counted at 2% because that was the best available take-profit bucket.",
            style={"fontSize": "11px", "color": "#777", "marginTop": "6px", "marginBottom": "0", "fontStyle": "italic"}
        )
    ])


# ============================================================================
# 🔧 SPLIT CALLBACK #2: Task Table Only (LIGHT - runs on every page click)
# ============================================================================

# ⚡ CRITICAL OPTIMIZATION: Page-level HTML cache
# Stores pre-rendered HTML rows for each page to avoid re-rendering on navigation
_PAGE_HTML_CACHE_MAX_PAGES = 8
_page_html_cache = OrderedDict()
_cached_golden_version = None


def normalize_task_page(current_page, total_pages):
    """Clamp a requested page index to the available task-table page range."""
    try:
        page = int(current_page or 0)
    except (TypeError, ValueError):
        page = 0
    return max(0, min(page, max(1, total_pages) - 1))


def get_task_display_sort_key(task):
    """Return a UI-only sort key for newest-signal-first table display."""
    try:
        signal_time = getattr(task, "signal_time", None)
        if signal_time is None or is_na(signal_time):
            return -1.0
        return float(signal_time)
    except Exception:
        return -1.0


def sort_tasks_for_table_display(tasks, sort_mode="newest"):
    """Sort tasks for table display only; never mutate task data or JSON order."""
    task_list = list(tasks)
    if sort_mode == "newest":
        return sorted(task_list, key=get_task_display_sort_key, reverse=True)
    return task_list


def get_display_page_slice(current_page, page_size=PAGE_SIZE, tasks=None, sort_mode="newest"):
    """Return the Golden Store task snapshot and one visible page slice.

    This is UI pagination only: it keeps the 300-row page model, can apply a
    display-only sort, and does not calculate or mutate any task fields.
    """
    raw_task_list = get_display_tasks_snapshot() if tasks is None else tasks
    task_list = sort_tasks_for_table_display(raw_task_list, sort_mode=sort_mode)
    total_pages = max(1, (len(task_list) + page_size - 1) // page_size)
    page = normalize_task_page(current_page, total_pages)
    start_idx = page * page_size
    end_idx = start_idx + page_size
    return {
        "tasks": task_list,
        "visible_tasks": task_list[start_idx:end_idx],
        "total_pages": total_pages,
        "current_page": page,
        "start_idx": start_idx,
        "end_idx": end_idx,
    }


def should_show_table_logs(hide_logs_value):
    """Return True when the UI-only table log column should render logs."""
    return "hide" not in (hide_logs_value or ["hide"])


def make_task_page_cache_key(current_page, version, show_table_logs, table_view_mode="compact", table_sort_mode="newest"):
    """Build the versioned task-table page cache key used by the LRU cache."""
    log_cache_mode = "logs_on" if show_table_logs else "logs_off"
    safe_view_mode = table_view_mode if table_view_mode in ("compact", "full") else "compact"
    safe_sort_mode = table_sort_mode if table_sort_mode in ("newest", "original") else "newest"
    return f"page_{current_page}_v{version}_{log_cache_mode}_{safe_view_mode}_{safe_sort_mode}"


def build_cached_summary_panels(current_golden_version, tasks):
    """Return cached summary/stat UI for the table page without recalculating stats.

    The dedicated summary callback owns the heavy all-task aggregation. The
    task-table callback should only reuse cached panels or show lightweight
    placeholders while those caches are being refreshed.
    """
    if cached_small_stats_data and stats_cache_version == current_golden_version:
        stats_table = render_basic_stats_table(
            cached_small_stats_data.get("completed", 0),
            cached_small_stats_data.get("total", len(tasks)),
            cached_small_stats_data.get("avg_adv", 0),
            cached_small_stats_data.get("avg_dd", 0),
        )
    else:
        stats_table = html.Div(
            "ℹ️ Summary stats are updating...",
            style={"textAlign": "center", "padding": "8px", "color": "#555", "fontStyle": "italic"}
        )

    if cached_signal_stats_html and stats_cache_version == current_golden_version:
        signal_stats_table = cached_signal_stats_html
    else:
        signal_stats_table = html.Div(
            "ℹ️ Signal Performance Summary is updating...",
            style={"textAlign": "center", "padding": "10px", "color": "#555", "fontStyle": "italic"}
        )

    if cached_toward_strategy_stats_html and stats_cache_version == current_golden_version:
        toward_strategy_table = cached_toward_strategy_stats_html
    else:
        toward_strategy_table = html.Div(
            "ℹ️ Toward-Level Strategy Summary is updating...",
            style={"textAlign": "center", "padding": "10px", "color": "#555", "fontStyle": "italic"}
        )
    return stats_table, signal_stats_table, toward_strategy_table


def get_cached_task_page(cache_key):
    """Return a cached rendered task page and mark it recent, if present."""
    if cache_key not in _page_html_cache:
        return None
    _page_html_cache.move_to_end(cache_key)
    return _page_html_cache[cache_key]


def cache_task_page(cache_key, page):
    """Cache rendered task-table pages with a small LRU bound for slow machines."""
    _page_html_cache[cache_key] = page
    _page_html_cache.move_to_end(cache_key)
    while len(_page_html_cache) > _PAGE_HTML_CACHE_MAX_PAGES:
        evicted_key, _ = _page_html_cache.popitem(last=False)
        perf_log(f"[TRACE] 🧹 Evicted cached task page '{evicted_key}' to keep cache <= {_PAGE_HTML_CACHE_MAX_PAGES}")

@app.callback(
    Output("task-table-container", "children"),
    Input("task-page-store", "data"),
    Input("golden-store-version", "data"),
    Input("recalc-lock-store", "data"),
    Input("analysis-complete-trigger", "data"),  # 🔧 NEW: Trigger UI refresh after recalculation completes
    Input("hide-logs-checkbox", "value"),  # UI-only: live toggle for table log rendering
    Input("table-view-mode", "value"),  # UI-only: compact/full main table toggle
    Input("table-sort-mode", "value"),  # UI-only: newest/original task order toggle
    prevent_initial_call=False
)
def update_task_table_only(current_page, version, lock_state, analysis_trigger, hide_logs_value, table_view_mode, table_sort_mode):
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
    perf_log(f"[DEBUG] 🔍 TRIGGER: {triggered_id} | version={version} | page={current_page}")
    timer.check(f"Trigger Detected: {triggered_id}")
    
    # If only lock changed, don't re-render table
    if triggered_id == "recalc-lock-store" and version == getattr(update_task_table_only, '_last_version', None):
        perf_log(f"[TRACE] Skipping render - lock change only")
        timer.check("Lock Skip").end()
        return dash.no_update
    
    update_task_table_only._last_version = version
    perf_log(f"[DEBUG] 📊 STATE: golden_store_version={golden_store_version}, cache_size={len(_page_html_cache)}")
    
    # Lock check
    if lock_state and lock_state.get("locked", False):
        timer.check("Lock Active").end()
        return html.Div("⏳ Recalculating... Please wait", style={"textAlign": "center", "padding": "20px", "fontSize": "16px", "color": "#666"})
    
    table_sort_mode = table_sort_mode if table_sort_mode in ("newest", "original") else "newest"

    # Get tasks from Golden Store
    page_slice = get_display_page_slice(current_page, sort_mode=table_sort_mode)
    tasks = page_slice["tasks"]
    source = "golden store" if golden_task_store_data is not None and len(golden_task_store_data) > 0 else "task_manager"
    perf_log(f"[TRACE] ✓ Loaded {len(tasks)} tasks from {source}")
    timer.check(f"Step 1: Get Data ({len(tasks)} tasks)")
    
    if not tasks:
        perf_log("[TRACE] ✗ No tasks found")
        timer.end()
        return "No tasks."
    
    # CRITICAL CACHE CHECK
    current_golden_version = get_golden_store_version()
    perf_log(f"[TRACE] Version check: cached={_cached_golden_version}, current={current_golden_version}")
    
    # Invalidate cache if data changed
    if _cached_golden_version != current_golden_version:
        perf_log(f"[TRACE] 🔄 Cache invalidated: {_cached_golden_version} -> {current_golden_version}")
        _page_html_cache.clear()
        _cached_golden_version = current_golden_version
        timer.check("Cache Invalidated")
    
    # Pagination Slicing
    current_page = page_slice["current_page"]
    total_pages = page_slice["total_pages"]
    start_idx = page_slice["start_idx"]
    end_idx = page_slice["end_idx"]
    visible_tasks = page_slice["visible_tasks"]
    perf_log(f"[TRACE] ✂️ Sliced tasks [{start_idx}:{end_idx}] → {len(visible_tasks)} visible")
    timer.check(f"Step 2: Pagination Slice")

    # UI-only table log toggle. Checked means keep table rows lightweight.
    # This does not modify task.log, JSON, or the Disable event logs processing flag.
    show_table_logs = should_show_table_logs(hide_logs_value)
    table_view_mode = table_view_mode if table_view_mode in ("compact", "full") else "compact"

    # ⚡ CRITICAL FIX: Cache MUST use the normalized page, version, and log display mode.
    cache_key = make_task_page_cache_key(current_page, current_golden_version, show_table_logs, table_view_mode, table_sort_mode)

    # Return cached page if available (INSTANT - no HTML generation)
    cached_page = get_cached_task_page(cache_key)
    if cached_page is not None:
        perf_log(f"[TRACE] ⚡ CACHE HIT for key '{cache_key}'! Returning cached page {current_page}")
        timer.check("Cache Hit").end()
        return cached_page

    perf_log(f"[TRACE] ❌ CACHE MISS for key '{cache_key}'. Will generate rows.")
    timer.check("Cache Miss Confirmed")
    
    # Detect if this is ONLY a page navigation (no data change)
    prev_golden_version = getattr(update_task_table_only, '_last_golden_version', None)
    is_page_only_nav = (triggered_id == "task-page-store") and (prev_golden_version is not None) and (current_golden_version == prev_golden_version)
    
    # 🔧 CRITICAL FIX: Also treat analysis_trigger as a data change (not page nav)
    # This ensures full stats are calculated after recalculation completes
    if triggered_id == "analysis-complete-trigger":
        is_page_only_nav = False
        perf_log(f"[TRACE] 🔄 Analysis trigger detected - forcing full stats recalculation")
    
    perf_log(f"[TRACE] Navigation detection: triggered={triggered_id}, prev_ver={prev_golden_version}, curr_ver={current_golden_version} → is_page_only_nav={is_page_only_nav}")
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
    
    # Generate the visible table page ONLY (300 max) as Dash components.
    # Keep this presentation-only: it formats fields that are already present on tasks.
    perf_log(f"[TRACE] 🚀 Starting {table_view_mode} table generation for {len(visible_tasks)} tasks using Dash components...")
    t_table_start = time.time()
    table_component, row_count = render_task_table_component(visible_tasks, show_table_logs=show_table_logs, compact=(table_view_mode == "compact"))
    table_elapsed = time.time() - t_table_start
    per_row_ms = (table_elapsed / row_count * 1000) if row_count else 0
    perf_log(f"[TRACE] ✓ Generated {table_view_mode} table for {row_count} rows in {table_elapsed:.2f}s ({per_row_ms:.1f}ms per row)")
    timer.check(f"Step 4-5: Table Component Generation ({row_count} rows)")



    # ⚡ PERFORMANCE: the dedicated summary callback owns the full all-task
    # Signal Performance Summary. The task-table callback reuses cached panels
    # and never recalculates all-task stats on page navigation.
    stats_table, signal_stats_table, toward_strategy_table = build_cached_summary_panels(current_golden_version, tasks)
    # 🔧 PAGINATION NAVIGATION
    nav_container = render_pagination_nav(current_page, total_pages)
    timer.check("Step 7: Build Pagination Nav")

    result = html.Div([
        html.H4("Task Summary"),
        nav_container,
        table_component,
        html.P(f"📄 Page {current_page+1} of {total_pages} | Showing tasks {start_idx+1}-{min(end_idx, len(tasks))} of {len(tasks)}", style={"textAlign":"center", "fontSize":"12px", "color":"#555"}),
        stats_table,
        html.H5("Signal Performance Summary", style={"marginTop": "15px", "marginBottom": "5px"}),
        signal_stats_table,
        html.H5("Toward-Level Next-Candle Strategy Summary", style={"marginTop": "15px", "marginBottom": "5px"}),
        toward_strategy_table,
        html.P(
            "ℹ️ Hit % metrics measure price movement ≥1%/1.5%/2% **in the EXPECTED direction** from the signal level base. "
            "Resistance: Price moves UP ≥X% from level. Support: Price moves DOWN ≥X% from level. "
            "Hits are only counted if the price actually touched the level first. "
            "Toward-level strategy counts the MAX target reached before the 0.12% stop; if price reaches 0.5%, later pulls back, then reaches 2% without stop, it is counted at 2% because that was the best available take-profit bucket.",
            style={"fontSize": "11px", "color": "#777", "marginTop": "6px", "marginBottom": "0", "fontStyle": "italic"}
        )
    ])
    timer.check("Step 8: Build Final Result Div")
    
    # ⚡ CACHE THE RESULT with version key for instant page switching (ALWAYS cache, regardless of stats)
    # The table HTML is the same whether we calculated full stats or page-only stats
    cache_task_page(cache_key, result)
    timer.check("Step 9: Cache Result")
    
    # Print final timing
    timer.end()
    perf_log(f"[TRACE] <<< COMPLETE Page {current_page} rendered in {timer.last_time - timer.start_time:.4f}s | Cache Size: {len(_page_html_cache)}")
    perf_log(f"[TRACE] ✓✓✓ RETURNING RESULT TO DASH UI ✓✓✓")
    

    return result


TASK_TABLE_HEADERS = [
    ("ID", "80px"),
    ("Status", "80px"),
    ("Progress", "70px"),
    ("Symbols", "100px"),
    ("Mode", "70px"),
    ("Direction", "80px"),
    ("Signal Time", "120px"),
    ("First Event", "120px"),
    ("Pin?", "60px"),
    ("Price Δ% (sgnl-lvl)", "80px"),
    ("Reached", "70px"),
    ("Reversed", "70px"),
    ("Toward Dir", "80px"),
    ("Toward Entry", "110px"),
    ("Toward SL Hit 0.12%", "120px"),
    ("Toward Max TP (0.5–4%+)", "160px"),
    ("Toward Level Hit", "120px"),
    ("No-SL Ret Entry", "130px"),
    ("Hit 1% (lvl-fwd.dir)", "50px"),
    ("Hit 1.5% (lvl-fwd.dir)", "60px"),
    ("Hit 2% (lvl-fwd.dir)", "50px"),
    ("1st 1% Exp", "50px"),
    ("Time 1% Exp", "140px"),
    ("1st 1.5% Exp", "60px"),
    ("Time 1.5% Exp", "140px"),
    ("1st 2% Exp", "50px"),
    ("Time 2% Exp", "140px"),
    ("1st 1% Opp", "50px"),
    ("Time 1% Opp", "140px"),
    ("1st 1.5% Opp", "60px"),
    ("Time 1.5% Opp", "140px"),
    ("1st 2% Opp", "50px"),
    ("Time 2% Opp", "140px"),
    ("Max Adv %(lvl)", "100px"),
    ("Max Adv T(lvl)", "140px"),
    ("Max Exp %(lvl)", "100px"),
    ("Max Exp T(lvl)", "140px"),
    ("Max Adv %(bef ret lvl)", "140px"),
    ("Time (bef ret lvl)", "140px"),
    ("Max Adv %(sgnl)", "100px"),
    ("Max Adv T(sgnl)", "140px"),
    ("Max Adv %(bef ret sgnl)", "140px"),
    ("Time (bef ret sgnl)", "140px"),
    ("Max Exp %(sgnl)", "100px"),
    ("Max Exp T(sgnl)", "140px"),
    ("DD% (Lvl)", "80px"),
    ("DD Time (Lvl)", "140px"),
    ("DD% (1%)", "80px"),
    ("DD Time (1%)", "140px"),
    ("DD% (1.5%)", "80px"),
    ("DD Time (1.5%)", "140px"),
    ("DD% (2%)", "80px"),
    ("DD Time (2%)", "140px"),
    ("Strategy", "120px"),
    ("Confidence", "80px"),
    ("Impulse #", "80px"),
    ("Log", "200px"),
    ("Actions", "420px"),
]


TASK_TABLE_HEADER_HTML = (
    '<thead style="position:sticky;top:0;background-color:#f0f0f0;z-index:10"><tr>'
    + "".join(
        f'<th style="min-width:{width};white-space:nowrap;padding:4px 6px;border:1px solid #ddd">{label}</th>'
        for label, width in TASK_TABLE_HEADERS
    )
    + "</tr></thead>"
)


# =============================================================================
# 16. UI RENDERERS: TASK TABLE, PAGINATION, AND SUMMARY TABLES
# =============================================================================
# Renderer helpers convert already-calculated task fields into Dash/raw HTML. They
# should not change task state, Golden Store, JSON, or analysis results.
# =============================================================================

def render_task_table_header_html():
    """Return the prebuilt raw sticky table header HTML used by the fast task table."""
    return TASK_TABLE_HEADER_HTML


COMPACT_TASK_TABLE_HEADERS = [
    ("ID", "80px"),
    ("Status", "80px"),
    ("Progress", "70px"),
    ("Symbols", "100px"),
    ("Direction", "80px"),
    ("Signal Time", "120px"),
    ("Reached", "70px"),
    ("Toward Dir", "80px"),
    ("Toward Entry", "110px"),
    ("Toward SL", "80px"),
    ("Toward Max TP", "110px"),
    ("Toward Level", "100px"),
    ("Strategy", "120px"),
    ("Confidence", "80px"),
    ("Impulse #", "80px"),
    ("Actions", "280px"),
]


def render_task_action_buttons(t, compact=True):
    """Render task action buttons as Dash components so event delegation still works."""
    task_id_str = str(t.task_id)
    is_completed = t.status == "completed"
    btn_disabled = "not-allowed" if not is_completed else "pointer"
    btn_opacity = "0.6" if not is_completed else "1"
    impulse_count = sum(1 for sig in t.strategy_signals if sig.get('type') == 'impulse')

    def action_div(label, action, bg, cursor="pointer", opacity="1", font_size="11px"):
        return html.Div(
            label,
            **{"data-action": action, "data-task-id": task_id_str},
            style={
                "margin": "2px",
                "padding": "4px 8px",
                "backgroundColor": bg,
                "borderRadius": "3px",
                "cursor": cursor,
                "display": "inline-block",
                "fontSize": font_size,
                "opacity": opacity,
            },
            className="interactive-button",
        )

    chart_button = html.Button(
        "Chart",
        id={"type": "task-table-chart", "task_id": task_id_str},
        n_clicks=0,
        # Keep the original DIV behaviour: visual status does not suppress the
        # click, because older/imported tasks may use a different completion label.
        disabled=False,
        title="Open this task's chart",
        style={
            "margin": "2px", "padding": "4px 8px", "backgroundColor": "#d4edda" if is_completed else "#e9ecef",
            "border": "none", "borderRadius": "3px", "cursor": btn_disabled,
            "display": "inline-block", "fontSize": "11px", "opacity": btn_opacity,
        },
    )
    buttons = [
        action_div("Stop", "stop", "#ffcccc"),
        action_div("Resume" if t.paused else "Pause", "pause", "#fff3cd" if t.paused else "#d1ecf1"),
        chart_button,
        action_div("Details", "details", "#d4edda" if is_completed else "#e9ecef", btn_disabled, btn_opacity),
    ]
    if not compact:
        impulse_has_data = is_completed and impulse_count > 0
        buttons.extend([
            action_div("Impulse", "impulse", "#d4edda" if impulse_has_data else "#e9ecef", "pointer" if impulse_has_data else "not-allowed", "1" if impulse_has_data else "0.6"),
            action_div("Re-run Strategy", "rerun-strat", "#d4edda" if is_completed else "#e9ecef", btn_disabled, btn_opacity, "9px"),
            action_div("Re-run Impulse", "rerun-impulse", "#d4edda" if is_completed else "#e9ecef", btn_disabled, btn_opacity, "9px"),
        ])
    symbol = t.symbols[0] if t.symbols else ""
    tv_url = f"https://www.tradingview.com/chart/?symbol=BYBIT:{symbol}&interval={t.timeframe}"
    buttons.append(html.A(html.Div("TV", style={"margin": "2px", "padding": "4px 8px", "backgroundColor": "#e7f3ff", "borderRadius": "3px", "display": "inline-block", "fontSize": "11px"}), href=tv_url, target="_blank", title="Open TradingView Chart"))
    return html.Div(buttons)


def get_task_table_display_values(t, show_table_logs=False):
    """Return all full-table display values in TASK_TABLE_HEADERS order."""
    direction_display = t.signal_direction if t.signal_direction else '-'
    signal_time_display = fmt_time_ui(t.signal_time) if t.signal_time else '-'
    first_event_display = fmt_time_ui(t.first_event_time) if t.first_event_time else '-'
    strategy_conf = t.strategy_confidence if t.strategy_confidence else 0
    impulse_count = sum(1 for sig in t.strategy_signals if sig.get('type') == 'impulse')
    if not show_table_logs:
        log_value = html.Span(f"Logs hidden — {len(t.log) if getattr(t, 'log', None) else 0} lines", style={"color": "#888", "fontStyle": "italic", "fontSize": "12px"})
    else:
        log_value = html.Div("\n".join(t.log) if t.log else "No logs yet...", style={"width": "100%", "maxHeight": "100px", "minHeight": "50px", "fontFamily": "monospace", "fontSize": "11px", "overflowY": "auto", "whiteSpace": "pre-wrap", "padding": "4px", "border": "1px solid #ddd", "borderRadius": "3px", "backgroundColor": "#fafafa"})

    return [
        str(t.task_id)[:8],
        t.status,
        f"{t.progress:.1f}%",
        ", ".join(t.symbols),
        t.mode,
        direction_display,
        signal_time_display,
        first_event_display,
        "Yes" if t.first_event_is_pin else "No",
        fmt_dd_ui(t.price_change_pct) if t.price_change_pct is not None else '-',
        "Yes" if t.reached_level else "No",
        "Yes" if t.reversed_direction else "No",
        (getattr(t, 'toward_entry_direction', None) or '-').upper() if getattr(t, 'toward_entry_direction', None) else '-',
        f"{float(getattr(t, 'toward_entry_price')):.6g}" if getattr(t, 'toward_entry_price', None) is not None else '-',
        "Yes" if getattr(t, 'toward_stop_loss_hit', False) else "No",
        fmt_toward_level_target_ui(getattr(t, 'toward_max_reached_pct', None)),
        "Yes" if getattr(t, 'toward_level_reached', False) else "No",
        "Yes" if getattr(t, 'toward_no_stop_returned_entry', False) else "No",
        "Yes" if t.hit_1 else "No",
        "Yes" if t.hit_1_5 else "No",
        "Yes" if t.hit_2 else "No",
        "Yes" if t.first_hit_1_expected else "No",
        fmt_time_ui(t.first_hit_1_expected_time),
        "Yes" if t.first_hit_1_5_expected else "No",
        fmt_time_ui(t.first_hit_1_5_expected_time),
        "Yes" if t.first_hit_2_expected else "No",
        fmt_time_ui(t.first_hit_2_expected_time),
        "Yes" if t.first_hit_1_opposite else "No",
        fmt_time_ui(t.first_hit_1_opposite_time),
        "Yes" if t.first_hit_1_5_opposite else "No",
        fmt_time_ui(t.first_hit_1_5_opposite_time),
        "Yes" if t.first_hit_2_opposite else "No",
        fmt_time_ui(t.first_hit_2_opposite_time),
        fmt_dd_ui(t.max_adverse_move_pct),
        fmt_time_ui(t.max_adverse_time),
        fmt_dd_ui(t.max_expected_move_pct),
        fmt_time_ui(t.max_expected_time),
        "Not returned" if not t.returned_to_signal else fmt_dd_ui(t.max_adverse_before_return_pct),
        fmt_time_ui(t.max_adverse_before_return_time) if t.returned_to_signal else "-",
        fmt_dd_ui(t.max_adverse_sgnl_pct),
        fmt_time_ui(t.max_adverse_sgnl_time),
        "Not returned" if not t.returned_to_sgnl else fmt_dd_ui(t.max_adverse_before_return_sgnl_pct),
        fmt_time_ui(t.max_adverse_before_return_sgnl_time) if t.returned_to_sgnl else "-",
        fmt_dd_ui(t.max_expected_sgnl_pct),
        fmt_time_ui(t.max_expected_sgnl_time),
        fmt_dd_ui(t.drawdown_before_level),
        fmt_time_ui(t.drawdown_before_level_time),
        fmt_dd_ui(t.drawdown_before_1pct),
        fmt_time_ui(t.drawdown_before_1pct_time),
        fmt_dd_ui(t.drawdown_before_1_5pct),
        fmt_time_ui(t.drawdown_before_1_5pct_time),
        fmt_dd_ui(t.drawdown_before_2pct),
        fmt_time_ui(t.drawdown_before_2pct_time),
        t.strategy_log_summary if t.strategy_log_summary else '-',
        f"{strategy_conf:.1f}%" if strategy_conf else "-",
        str(impulse_count),
        log_value,
        render_task_action_buttons(t, compact=False),
    ]


def render_task_table_component(visible_tasks, show_table_logs=False, compact=True):
    """Render the task table as Dash components instead of Markdown/raw HTML."""
    headers = COMPACT_TASK_TABLE_HEADERS if compact else TASK_TABLE_HEADERS
    compact_indices = [0, 1, 2, 3, 5, 6, 10, 12, 13, 14, 15, 16, 53, 54, 55, 57]
    header_cells = [
        html.Th(label, style={"minWidth": width, "whiteSpace": "nowrap", "padding": "4px 6px", "border": "1px solid #ddd"})
        for label, width in headers
    ]
    rows = []
    for task in visible_tasks:
        values = get_task_table_display_values(task, show_table_logs=show_table_logs)
        row_values = [values[i] for i in compact_indices] if compact else values
        cells = [
            html.Td(value, style={"minWidth": headers[idx][1], "whiteSpace": "nowrap", "padding": "4px 6px", "border": "1px solid #ddd", "verticalAlign": "top"})
            for idx, value in enumerate(row_values)
        ]
        rows.append(html.Tr(cells, **{"data-task-row": str(task.task_id)}))

    table = html.Table(
        [html.Thead(html.Tr(header_cells), style={"position": "sticky", "top": 0, "backgroundColor": "#f0f0f0", "zIndex": 10}), html.Tbody(rows)],
        id="task-summary-table",
        style={"width": "max-content", "minWidth": "100%", "borderCollapse": "collapse", "tableLayout": "auto", "fontSize": "12px"},
    )
    return html.Div(table, style={"overflowX": "auto", "overflowY": "auto", "maxHeight": "75vh", "width": "100%"}), len(visible_tasks)


def render_task_table_html(visible_tasks, show_table_logs=False):
    """Render one already-sliced task-table page as raw HTML plus row count.

    This helper is intentionally presentation-only: it receives the 300-row page
    slice from the callback and only formats fields that already exist on each
    task, preserving the Golden Store/data-flow and calculation logic.
    The show_table_logs flag is a UI-only display mode; it never changes saved logs.
    """
    row_count = len(visible_tasks)
    body_html = "<tbody>" + "".join(
        render_task_table_row(t, show_table_logs=show_table_logs) for t in visible_tasks
    ) + "</tbody>"
    table_html = (
        '<style>'
        '#task-summary-table th,#task-summary-table td{white-space:nowrap;padding:4px 6px;border:1px solid #ddd;vertical-align:top;}'
        '#task-summary-table td:nth-last-child(2){white-space:normal;}'
        '</style>'
        '<table id="task-summary-table" style="width:max-content;min-width:100%;border-collapse:collapse;table-layout:auto">'
        + render_task_table_header_html()
        + body_html
        + "</table>"
    )
    return table_html, row_count

def render_task_table_row(t, show_table_logs=False):
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
    toward_dir_display = (getattr(t, 'toward_entry_direction', None) or '-').upper() if getattr(t, 'toward_entry_direction', None) else '-'
    toward_entry_display = f"{float(getattr(t, 'toward_entry_price')):.6g}" if getattr(t, 'toward_entry_price', None) is not None else '-'
    toward_sl_display = "Yes" if getattr(t, 'toward_stop_loss_hit', False) else "No"
    toward_max_display = fmt_toward_level_target_ui(getattr(t, 'toward_max_reached_pct', None))
    toward_level_display = "Yes" if getattr(t, 'toward_level_reached', False) else "No"
    toward_return_display = "Yes" if getattr(t, 'toward_no_stop_returned_entry', False) else "No"
    
    strategy_display = t.strategy_log_summary if t.strategy_log_summary else '-'
    strategy_conf = t.strategy_confidence if t.strategy_confidence else 0
    confidence_display = f"{strategy_conf:.1f}%" if strategy_conf else "-"
    
    # Count impulses
    impulse_count = sum(1 for sig in t.strategy_signals if sig.get('type') == 'impulse')
    impulse_display = str(impulse_count)
    
    # Format log display for the table only. When hidden, do not join/pass full
    # task logs into row HTML; this keeps the 300-row page lightweight.
    log_count = len(t.log) if getattr(t, "log", None) else 0
    if not show_table_logs:
        log_html = (
            '<span style="color:#888;font-style:italic;font-size:12px">'
            f'Logs hidden — {log_count} lines'
            '</span>'
        )
    else:
        import html as html_lib
        log_text = "\n".join(t.log) if t.log else "No logs yet..."
        log_escaped = html_lib.escape(log_text).replace("\n", "<br>")
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
    row_html = f"""<tr data-task-row="{task_id_str}">
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
        <td style="min-width:80px">{toward_dir_display}</td>
        <td style="min-width:100px">{toward_entry_display}</td>
        <td style="min-width:80px">{toward_sl_display}</td>
        <td style="min-width:90px">{toward_max_display}</td>
        <td style="min-width:80px">{toward_level_display}</td>
        <td style="min-width:100px">{toward_return_display}</td>
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
        <td style="min-width:420px">{button_html}</td>
    </tr>"""
    # dcc.Markdown treats indented HTML lines as code blocks, which caused raw
    # <td> tags to display in the page. Compact the row so Markdown receives a
    # continuous raw-HTML block while preserving log line breaks as <br> tags.
    return "".join(line.strip() for line in row_html.splitlines())


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
        html.Th("Toward Dir", style={"minWidth": "80px"}),
        html.Th("Toward Entry", style={"minWidth": "100px"}),
        html.Th("Toward SL Hit 0.12%", style={"minWidth": "120px"}),
        html.Th("Toward Max TP (0.5–4%+)", style={"minWidth": "160px"}),
        html.Th("Toward Level Hit", style={"minWidth": "120px"}),
        html.Th("No-SL Ret Entry", style={"minWidth": "130px"}),
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
        html.Th("Max Adv %(bef ret lvl)", style={"minWidth": "140px"}),
        html.Th("Time (bef ret lvl)", style={"minWidth": "140px"}),
        html.Th("Max Adv %(sgnl)", style={"minWidth": "100px"}),
        html.Th("Max Adv T(sgnl)", style={"minWidth": "140px"}),
        html.Th("Max Adv %(bef ret sgnl)", style={"minWidth": "140px"}),
        html.Th("Time (bef ret sgnl)", style={"minWidth": "140px"}),
        html.Th("Max Exp %(sgnl)", style={"minWidth": "100px"}),
        html.Th("Max Exp T(sgnl)", style={"minWidth": "140px"}),
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
        html.Th("Actions", style={"minWidth": "420px"})
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

def get_ordered_tasks_for_navigation():
    """Return tasks in the same order used by the paginated table."""
    return list(get_display_tasks_snapshot())

def get_chartable_tasks_for_navigation():
    """Return tasks that should have usable charts, preserving table order."""
    tasks = get_ordered_tasks_for_navigation()
    chartable = [t for t in tasks if getattr(t, 'status', None) == "completed"]
    return tasks, chartable

def prefetch_chart_neighbors(task_id):
    """Warm immediate previous/next chart sources after a chart opens."""
    if not task_id or not CHART_PREFETCH_ENABLED:
        return
    _, chartable = get_chartable_tasks_for_navigation()
    ids = [str(t.task_id) for t in chartable]
    try:
        index = ids.index(str(task_id))
    except ValueError:
        return
    # A single adjacent source gives the best old-SSD tradeoff. Prefer Next,
    # because it is the common navigation direction.
    if index + 1 < len(chartable):
        prefetch_chart_source_async(chartable[index + 1])
    elif index > 0:
        prefetch_chart_source_async(chartable[index - 1])

def page_for_task(task_id, tasks):
    for idx, task in enumerate(tasks):
        if str(getattr(task, 'task_id', '')) == str(task_id):
            return idx // PAGE_SIZE
    return no_update

# =============================================================================
# 17. CALLBACKS: CHART MODAL, CHART NAVIGATION, AND VISIBILITY TOGGLES
# =============================================================================
# Chart callbacks/renderers should consume task data and display state only. Keep
# measurement, visibility, and modal state separate from analysis calculations.
# =============================================================================

@app.callback(
    Output("prev-chart-btn", "disabled"),
    Output("next-chart-btn", "disabled"),
    Output("prev-chart-btn", "data-target-task-id"),
    Output("next-chart-btn", "data-target-task-id"),
    Output("prev-chart-btn", "data-direct-navigation"),
    Output("next-chart-btn", "data-direct-navigation"),
    Input("chart-task-id", "data"),
    Input("golden-store-version", "data"),
    Input("chart-event-context-store", "data"),
    prevent_initial_call=False
)
def update_chart_nav_buttons(task_id, version, event_context):
    if isinstance(event_context, dict) and event_context.get("events"):
        idx = int(event_context.get("index") or 0)
        events = event_context.get("events") or []
        total = len(events)
        previous = str(events[idx - 1].get("task_id") or "") if idx > 0 else ""
        following = str(events[idx + 1].get("task_id") or "") if idx < total - 1 else ""
        # Summary-event navigation must also move the event index/context, so
        # it keeps the server navigation route instead of bypassing it.
        return idx <= 0, idx >= total - 1, previous, following, "false", "false"
    if not task_id:
        return True, True, "", "", "false", "false"
    _, chartable = get_chartable_tasks_for_navigation()
    chart_ids = [str(t.task_id) for t in chartable]
    if task_id not in chart_ids:
        return True, True, "", "", "false", "false"
    idx = chart_ids.index(task_id)
    previous = chart_ids[idx - 1] if idx > 0 else ""
    following = chart_ids[idx + 1] if idx < len(chart_ids) - 1 else ""
    # Main-table navigation needs only a new task id. Expose the already
    # resolved adjacent ids so the browser can skip the server n_click hop.
    return idx <= 0, idx >= len(chart_ids) - 1, previous, following, "true", "true"

def carry_chart_view_state_to_task(view_state, target_task_id):
    """Carry current zoom/pan ranges to a newly selected chart task."""
    if not isinstance(view_state, dict) or not view_state.get("axes") or not target_task_id:
        return no_update
    next_state = dict(view_state)
    next_state["task_id"] = str(target_task_id)
    next_state["carried_to_task_ts"] = time.time()
    return next_state

@app.callback(
    Output("chart-task-id", "data", allow_duplicate=True),
    Output("task-page-store", "data", allow_duplicate=True),
    Output("chart-click-store", "data", allow_duplicate=True),
    Output("chart-event-context-store", "data", allow_duplicate=True),
    Output("chart-view-state-store", "data", allow_duplicate=True),
    Input("prev-chart-btn", "n_clicks"),
    Input("next-chart-btn", "n_clicks"),
    State("chart-task-id", "data"),
    State("chart-event-context-store", "data"),
    State("chart-view-state-store", "data"),
    prevent_initial_call=True
)
def navigate_chart_task(prev_clicks, next_clicks, current_task_id, event_context, chart_view_state):
    triggered = ctx.triggered_id
    if triggered not in ("prev-chart-btn", "next-chart-btn") or not current_task_id:
        return no_update, no_update, no_update, no_update, no_update

    if isinstance(event_context, dict) and event_context.get("events"):
        events = event_context.get("events") or []
        current_idx = int(event_context.get("index") or 0)
        next_idx = current_idx - 1 if triggered == "prev-chart-btn" else current_idx + 1
        if next_idx < 0 or next_idx >= len(events):
            return no_update, no_update, no_update, no_update, no_update
        target_id = str(events[next_idx].get("task_id") or "")
        if not target_id:
            return no_update, no_update, no_update, no_update, no_update
        # Event-group navigation is opened from summary tables and can include many
        # rows.  Do not force the task table to jump pages here; that expensive
        # table rebuild made left/right chart navigation feel very slow.
        updated_context = dict(event_context, index=next_idx)
        warm_idx = next_idx - 1 if triggered == "prev-chart-btn" else next_idx + 1
        if 0 <= warm_idx < len(events):
            prefetch_chart_source_async(tm.get_task(str(events[warm_idx].get("task_id") or "")))
        interaction_trace(f"chart navigation target={target_id} direction={triggered} source=event_context")
        return target_id, no_update, {f"{target_id}_chart": time.time()}, updated_context, carry_chart_view_state_to_task(chart_view_state, target_id)

    _, chartable = get_chartable_tasks_for_navigation()
    chart_ids = [str(t.task_id) for t in chartable]
    if current_task_id not in chart_ids:
        return no_update, no_update, no_update, no_update, no_update

    current_idx = chart_ids.index(current_task_id)
    next_idx = current_idx - 1 if triggered == "prev-chart-btn" else current_idx + 1
    if next_idx < 0 or next_idx >= len(chartable):
        return no_update, no_update, no_update, no_update, no_update

    target_id = str(chartable[next_idx].task_id)
    # Keep chart navigation independent from the main task table.  Jumping the
    # table page here triggers an expensive table rebuild and makes the chart's
    # left/right buttons feel delayed on large task sets.
    warm_idx = next_idx - 1 if triggered == "prev-chart-btn" else next_idx + 1
    if 0 <= warm_idx < len(chartable):
        prefetch_chart_source_async(chartable[warm_idx])
    interaction_trace(f"chart navigation target={target_id} direction={triggered} source=main_table")
    return target_id, no_update, {f"{target_id}_chart": time.time()}, no_update, carry_chart_view_state_to_task(chart_view_state, target_id)

register_browser_callback(
    """
function(taskId, page) {
    function apply() {
        if (window.applyChartRowHighlight) {
            window.applyChartRowHighlight(taskId);
        }
    }
    apply();
    setTimeout(apply, 50);
    setTimeout(apply, 250);
    return {task_id: taskId || null, page: page, ts: Date.now()};
}
""",
    Output("chart-highlight-dummy", "data"),
    Input("chart-task-id", "data"),
    Input("task-page-store", "data"),
    prevent_initial_call=False
)

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
    Output("chart-event-context-store", "data"),
    Input("chart-button-trigger", "data"),
    Input({"type": "task-table-chart", "task_id": ALL}, "n_clicks"),
    State("chart-click-store", "data"),
    prevent_initial_call=True,
)
def set_chart_task_id(trigger_data, _table_chart_clicks, click_store):
    triggered = ctx.triggered_id
    if isinstance(triggered, dict) and triggered.get("type") == "task-table-chart":
        # Pattern-matching inputs can fire with n_clicks=0 when Dash inserts a
        # freshly rendered page of table rows. That is not a user click; without
        # this guard the first rendered task opens itself and queues stale charts.
        trigger_value = (ctx.triggered[0].get("value") if ctx.triggered else None)
        if not trigger_value:
            interaction_trace(f"ignored initial table chart input task={triggered.get('task_id')}")
            return no_update, no_update, no_update
        task_id = triggered.get("task_id")
    elif triggered == "chart-button-trigger" and trigger_data and trigger_data.get("action") == "chart":
        task_id = trigger_data.get("task_id")
    else:
        return no_update, no_update, no_update
    if not task_id:
        return no_update, no_update, no_update
    click_store = dict(click_store or {})
    key = f"{task_id}_chart"
    current_time = time.time()
    if current_time - float(click_store.get(key, 0) or 0) < 0.5:
        return no_update, no_update, no_update
    click_store[key] = current_time
    interaction_trace(f"chart open task={task_id} source=main_table")
    # Discovering neighbours can walk the full task snapshot. Keep it off the
    # click callback so the modal and figure callback are released immediately.
    threading.Thread(
        target=prefetch_chart_neighbors,
        args=(str(task_id),),
        name="ChartNeighbourPrefetch",
        daemon=True,
    ).start()
    return str(task_id), click_store, make_chart_context("main_table")

@app.callback(
    Output("chart-request-store", "data"),
    Input("chart-task-id", "data"),
    Input("chart-event-context-store", "data"),
    prevent_initial_call=False,
)
def sync_chart_request(task_id, event_context):
    """Publish one source-aware request without changing existing chart inputs."""
    # The direct browser chart-open path intentionally bypasses the legacy
    # n_click callback. Schedule the same optional neighbour warm-up here so
    # main-table opens and Next/Previous navigation share one cache strategy.
    if task_id:
        threading.Thread(
            target=prefetch_chart_neighbors,
            args=(str(task_id),),
            name="ChartRequestPrefetch",
            daemon=True,
        ).start()
    return make_chart_request(task_id, event_context)

def sync_chart_ui_state(*values):
    """Build a grouped snapshot from legacy control Stores when explicitly enabled."""
    return make_chart_ui_state(*values)


if CHART_UI_STATE_LEGACY_SYNC_ENABLED:
    app.callback(
        Output("chart-ui-state-store", "data"),
        Input("rsi-visible-store", "data"),
        Input("stochastic-visible-store", "data"),
        Input("volume-visible-store", "data"),
        Input("adx-visible-store", "data"),
        Input("macd-visible-store", "data"),
        Input("disparity-visible-store", "data"),
        Input("strategy-visible-store", "data"),
        Input("impulse-visible-store", "data"),
        Input("events-visible-store", "data"),
        Input("measure-mode-store", "data"),
        Input("measure-anchor-store", "data"),
        Input("measure-hover-store", "data"),
        Input("measure-oscillator-range-store", "data"),
        Input("chart-info-box-store", "data"),
        Input("oscillator-info-box-store", "data"),
        Input("oscillator-sync-info-store", "data"),
        Input("chart-extend-x-store", "data"),
        Input("chart-focus-entry-store", "data"),
        prevent_initial_call=False,
    )(sync_chart_ui_state)


# Explicit migration bridge: a new control can publish a small declarative
# action without adding another Store. The grouped state is then mirrored back
# to the existing Store inputs until every renderer/control has migrated.
# Disabled by default: current toolbar controls still write legacy Stores directly.
# Enable only when a newly added control publishes chart-ui-action-store actions.
CHART_UI_LEGACY_BRIDGE_ENABLED = os.environ.get("GPT_ENABLE_CHART_UI_BRIDGE", "0") == "1"

_CHART_UI_STATE_PATHS = {
    "rsi-visible-store": ("panes", "rsi"),
    "stochastic-visible-store": ("panes", "stochastic"),
    "volume-visible-store": ("panes", "volume"),
    "adx-visible-store": ("panes", "adx"),
    "macd-visible-store": ("panes", "macd"),
    "disparity-visible-store": ("panes", "disparity"),
    "strategy-visible-store": ("overlays", "strategy"),
    "impulse-visible-store": ("overlays", "impulses"),
    "events-visible-store": ("overlays", "events"),
    "measure-mode-store": ("measurement", "enabled"),
    "measure-anchor-store": ("measurement", "snap_to_candle"),
    "measure-hover-store": ("measurement", "show_hover"),
    "measure-oscillator-range-store": ("measurement", "shade_oscillator_range"),
    "chart-info-box-store": ("information", "candle"),
    "oscillator-info-box-store": ("information", "oscillator"),
    "oscillator-sync-info-store": ("information", "oscillator_sync"),
    "chart-extend-x-store": ("viewport", "extend_x"),
    "chart-focus-entry-store": ("viewport", "focus_entry"),
}


def reduce_chart_ui_action(ui_state, action):
    """Apply one future-facing set/toggle action to grouped chart UI state."""
    state = json.loads(json.dumps(ui_state or make_chart_ui_state()))
    if not isinstance(action, dict):
        return state
    section, key = action.get("section"), action.get("key")
    bucket = state.get(section) if isinstance(section, str) else None
    if not isinstance(bucket, dict) or key not in bucket:
        return state
    if action.get("type") == "set":
        bucket[key] = bool(action.get("value"))
    elif action.get("type") == "toggle":
        bucket[key] = not bool(bucket[key])
    return state


@app.callback(
    Output("chart-ui-state-store", "data", allow_duplicate=True),
    Input("chart-ui-action-store", "data"),
    State("chart-ui-state-store", "data"),
    prevent_initial_call=True,
)
def apply_chart_ui_action(action, ui_state):
    return reduce_chart_ui_action(ui_state, action)


@app.callback(
    *[Output(store_id, "data", allow_duplicate=True) for store_id in _CHART_UI_STATE_PATHS],
    Input("chart-ui-state-store", "data"),
    *[State(store_id, "data") for store_id in _CHART_UI_STATE_PATHS],
    prevent_initial_call=True,
)
def bridge_chart_ui_state_to_legacy(ui_state, *legacy_values):
    """Mirror grouped state to legacy writers without feedback-loop updates."""
    if not CHART_UI_LEGACY_BRIDGE_ENABLED:
        return tuple(no_update for _ in _CHART_UI_STATE_PATHS)
    state = ui_state or make_chart_ui_state()
    outputs = []
    for (section, key), legacy_value in zip(_CHART_UI_STATE_PATHS.values(), legacy_values):
        desired = bool((state.get(section) or {}).get(key, False))
        outputs.append(no_update if desired == bool(legacy_value) else desired)
    return tuple(outputs)


# ----- Modal display callback -----
@app.callback(
    Output("chart-modal", "style"),
    Input("chart-task-id", "data"),
    Input("chart-click-store", "data"),
    Input("close-chart-modal", "n_clicks"),
    prevent_initial_call=True
)
def toggle_chart_modal(task_id, click_store, close_clicks):
    triggered = ctx.triggered_id
    if triggered == "close-chart-modal":
        return {**CHART_PANEL_STYLE, "display": "none"}
    if task_id:
        return {**CHART_PANEL_STYLE, "display": "flex"}
    return no_update

@app.callback(
    Output("chart-task-id", "data", allow_duplicate=True),
    Output("chart-button-trigger", "data"),
    Output("chart-click-store", "data", allow_duplicate=True),
    Output("chart-event-context-store", "data", allow_duplicate=True),
    Input("close-chart-modal", "n_clicks"),
    prevent_initial_call=True
)
def clear_chart_context_on_close(_):
    """Drop the selected chart and click trigger history when the modal closes."""
    return None, None, {}, make_chart_context("main_table")

@app.callback(
    Output("chart-task-id", "data", allow_duplicate=True),
    Output("chart-click-store", "data", allow_duplicate=True),
    Output("chart-event-context-store", "data", allow_duplicate=True),
    Output("rsi-visible-store", "data", allow_duplicate=True),
    Output("stochastic-visible-store", "data", allow_duplicate=True),
    Input({"type": "osc-event-chart", "category": ALL}, "n_clicks"),
    State({"type": "osc-event-index", "category": ALL}, "value"),
    State({"type": "osc-event-index", "category": ALL}, "id"),
    State("osc-event-groups-store", "data"),
    prevent_initial_call=True,
)
def open_oscillator_event_chart(_clicks, requested_indices, requested_index_ids, event_groups):
    """Open the chart on a selected diagnostic event number and enable oscillator panes."""
    triggered = ctx.triggered_id
    if not isinstance(triggered, dict):
        return no_update, no_update, no_update, no_update, no_update
    category = triggered.get("category")
    events = (event_groups or {}).get(category) or []
    if not events:
        return no_update, no_update, no_update, no_update, no_update

    requested_number = 1
    for value, id_obj in zip(requested_indices or [], requested_index_ids or []):
        if isinstance(id_obj, dict) and id_obj.get("category") == category:
            requested_number = value or 1
            break
    try:
        event_index = int(requested_number) - 1
    except Exception:
        event_index = 0
    event_index = max(0, min(event_index, len(events) - 1))

    task_id = str(events[event_index].get("task_id") or "")
    if not task_id:
        return no_update, no_update, no_update, no_update, no_update
    context = make_chart_context("dynamic_oscillator_summary", category=category, events=events, index=event_index, overlay=True)
    return task_id, {f"{task_id}_chart": time.time()}, context, True, True

@app.callback(
    Output("chart-event-context-store", "data", allow_duplicate=True),
    Input("toggle-chart-event-marks-btn", "n_clicks"),
    State("chart-event-context-store", "data"),
    prevent_initial_call=True,
)
def toggle_chart_event_marks(_clicks, event_context):
    event_context = dict(event_context or {"events": [], "index": 0, "overlay": True})
    event_context["overlay"] = not bool(event_context.get("overlay", True))
    return event_context

@app.callback(
    Output("toggle-chart-event-marks-btn", "children"),
    Output("toggle-chart-event-marks-btn", "style"),
    Input("chart-event-context-store", "data"),
    prevent_initial_call=False,
)
def update_chart_event_marks_button(event_context):
    enabled = bool((event_context or {}).get("overlay", True))
    style = {
        "padding": "6px 10px", "backgroundColor": "#1976d2" if enabled else "#6c757d",
        "color": "white", "border": "none", "borderRadius": "4px", "cursor": "pointer", "fontSize": "12px"
    }
    return ("Event Marks: On" if enabled else "Event Marks: Off"), style

# Core toolbar controls must have a server-side Dash path.  Inline browser
# callbacks are intentionally disabled on some Dash 4 renderers, so relying
# only on window.dash_clientside.set_props makes every chart toggle inert.
_CHART_TOGGLE_BUTTONS = {
    "toggle-rsi-btn": "rsi-visible-store",
    "toggle-stochastic-btn": "stochastic-visible-store",
    "toggle-volume-btn": "volume-visible-store",
    "toggle-adx-btn": "adx-visible-store",
    "toggle-macd-btn": "macd-visible-store",
    "toggle-disparity-btn": "disparity-visible-store",
    "toggle-strategy-btn": "strategy-visible-store",
    "toggle-impulses-btn": "impulse-visible-store",
    "toggle-events-btn": "events-visible-store",
    "toggle-measure-btn": "measure-mode-store",
    "toggle-measure-anchor-btn": "measure-anchor-store",
    "toggle-measure-hover-btn": "measure-hover-store",
    "toggle-measure-oscillator-range-btn": "measure-oscillator-range-store",
    "toggle-chart-info-box-btn": "chart-info-box-store",
    "toggle-oscillator-info-box-btn": "oscillator-info-box-store",
    "toggle-oscillator-sync-info-btn": "oscillator-sync-info-store",
    "toggle-chart-extend-x-btn": "chart-extend-x-store",
    "toggle-chart-focus-entry-btn": "chart-focus-entry-store",
}

@app.callback(
    *[Output(store_id, "data") for store_id in _CHART_TOGGLE_BUTTONS.values()],
    *[Input(button_id, "n_clicks") for button_id in _CHART_TOGGLE_BUTTONS],
    *[State(store_id, "data") for store_id in _CHART_TOGGLE_BUTTONS.values()],
    prevent_initial_call=True,
)
def toggle_chart_control_server(*args):
    """Reliable Dash fallback for every chart toolbar toggle."""
    count = len(_CHART_TOGGLE_BUTTONS)
    current_values = args[count:]
    triggered = ctx.triggered_id
    if triggered not in _CHART_TOGGLE_BUTTONS:
        return tuple(no_update for _ in range(count))
    outputs = [no_update] * count
    target_store = _CHART_TOGGLE_BUTTONS[triggered]
    target_index = list(_CHART_TOGGLE_BUTTONS.values()).index(target_store)
    interaction_trace(f"toolbar click={triggered} store={target_store} old={current_values[target_index]!r}")
    outputs[target_index] = not bool(current_values[target_index])
    return tuple(outputs)

# ----- Measurement tool callbacks -----
@app.callback(
    Output("measure-mode-store", "data", allow_duplicate=True),
    Output("measure-points-store", "data", allow_duplicate=True),
    Output("measure-result-store", "data", allow_duplicate=True),
    Output("task-chart", "clickData", allow_duplicate=True),
    Output("task-chart", "selectedData", allow_duplicate=True),
    Output("task-chart", "relayoutData", allow_duplicate=True),
    Input("chart-task-id", "data"),
    Input("close-chart-modal", "n_clicks"),
    prevent_initial_call=True
)
def reset_measure_on_chart_context_change(task_id, close_clicks):
    """Clear measurement state whenever the chart is closed or switched.

    Measurement points are in the coordinate space of the currently displayed
    task.  If they survive closing the modal or opening another task, Plotly can
    autorange around stale x/y coordinates and make the next chart look shifted
    or show unexpected candles.  Clearing the measure state and volatile Graph
    click/selection data gives each chart open a clean ruler context.
    """
    triggered = ctx.triggered_id
    if triggered == "close-chart-modal" or (triggered == "chart-task-id" and task_id):
        return False, {"first": None, "second": None}, None, None, None, None
    return no_update, no_update, no_update, no_update, no_update, no_update

@app.callback(
    Output("toggle-measure-btn", "children"),
    Output("toggle-measure-btn", "style"),
    Input("measure-mode-store", "data"),
    prevent_initial_call=False
)
def update_measure_button(active):
    base_style = {
        "background": "#e3f2fd" if active else "transparent",
        "color": "black",
        "border": "2px solid #1976d2" if active else "1px solid black",
        "padding": "6px 10px",
        "cursor": "pointer",
        "fontSize": "12px",
        "minWidth": "76px",
        "whiteSpace": "nowrap",
        "fontWeight": "bold" if active else "normal"
    }
    return ("📐 Measuring" if active else "📐 Measure"), base_style

@app.callback(
    Output("toggle-measure-anchor-btn", "children"),
    Output("toggle-measure-anchor-btn", "style"),
    Input("measure-anchor-store", "data"),
    prevent_initial_call=False
)
def update_measure_anchor_button(anchor_enabled):
    base_style = {
        "background": "#e8f5e9" if anchor_enabled else "transparent",
        "color": "black",
        "border": "2px solid #2e7d32" if anchor_enabled else "1px solid #999",
        "padding": "6px 10px",
        "cursor": "pointer",
        "fontSize": "12px",
        "minWidth": "76px",
        "whiteSpace": "nowrap",
        "fontWeight": "bold" if anchor_enabled else "normal"
    }
    return ("Snap: On" if anchor_enabled else "Snap: Off"), base_style

@app.callback(
    Output("toggle-measure-hover-btn", "children"),
    Output("toggle-measure-hover-btn", "style"),
    Input("measure-hover-store", "data"),
    prevent_initial_call=False
)
def update_measure_hover_button(hover_enabled):
    base_style = {
        "background": "#fff8e1" if hover_enabled else "transparent",
        "color": "black",
        "border": "2px solid #f9a825" if hover_enabled else "1px solid #999",
        "padding": "6px 10px",
        "cursor": "pointer",
        "fontSize": "12px",
        "minWidth": "78px",
        "whiteSpace": "nowrap",
        "fontWeight": "bold" if hover_enabled else "normal"
    }
    return ("Hover: On" if hover_enabled else "Hover: Off"), base_style


@app.callback(
    Output("toggle-measure-oscillator-range-btn", "children"),
    Output("toggle-measure-oscillator-range-btn", "style"),
    Input("measure-oscillator-range-store", "data"),
    prevent_initial_call=False,
)
def update_measure_oscillator_range_button(enabled):
    style = {
        "background": "#eceff1" if enabled else "transparent",
        "color": "black",
        "border": "2px solid #78909c" if enabled else "1px solid #999",
        "padding": "6px 10px",
        "cursor": "pointer",
        "fontSize": "12px",
        "minWidth": "104px",
        "whiteSpace": "nowrap",
        "fontWeight": "bold" if enabled else "normal",
    }
    return ("Osc Range: On" if enabled else "Osc Range: Off"), style

@app.callback(
    Output("toggle-chart-info-box-btn", "children"),
    Output("toggle-chart-info-box-btn", "style"),
    Input("chart-info-box-store", "data"),
    prevent_initial_call=False
)
def update_chart_info_box_button(info_enabled):
    base_style = {
        "background": "#fff8e1" if info_enabled else "transparent",
        "color": "black",
        "border": "2px solid #f9a825" if info_enabled else "1px solid #999",
        "padding": "6px 10px",
        "cursor": "pointer",
        "fontSize": "12px",
        "minWidth": "94px",
        "whiteSpace": "nowrap",
        "fontWeight": "bold" if info_enabled else "normal"
    }
    return ("Candle Info: On" if info_enabled else "Candle Info: Off"), base_style

@app.callback(
    Output("toggle-oscillator-info-box-btn", "children"),
    Output("toggle-oscillator-info-box-btn", "style"),
    Input("oscillator-info-box-store", "data"),
    prevent_initial_call=False
)
def update_oscillator_info_box_button(info_enabled):
    style = {"background": "#fff8e1" if info_enabled else "transparent", "color": "black",
             "border": "2px solid #f9a825" if info_enabled else "1px solid #999", "padding": "6px 10px",
             "cursor": "pointer", "fontSize": "12px", "minWidth": "94px", "whiteSpace": "nowrap",
             "fontWeight": "bold" if info_enabled else "normal"}
    return ("Osc Info: On" if info_enabled else "Osc Info: Off"), style


@app.callback(
    Output("toggle-oscillator-sync-info-btn", "children"),
    Output("toggle-oscillator-sync-info-btn", "style"),
    Input("oscillator-sync-info-store", "data"),
    prevent_initial_call=False,
)
def update_oscillator_sync_info_button(sync_enabled):
    style = {"background": "#e3f2fd" if sync_enabled else "transparent", "color": "black",
             "border": "2px solid #1976d2" if sync_enabled else "1px solid #999", "padding": "6px 10px",
             "cursor": "pointer", "fontSize": "12px", "minWidth": "94px", "whiteSpace": "nowrap",
             "fontWeight": "bold" if sync_enabled else "normal"}
    return ("Osc All: On" if sync_enabled else "Osc All: Off"), style


def _chart_toggle_button(label, enabled):
    """Return one consistent, stateful appearance for chart-pane controls."""
    enabled = bool(enabled)
    style = {
        "background": "#e3f2fd" if enabled else "transparent",
        "color": "black",
        "border": "2px solid #1976d2" if enabled else "1px solid #999",
        "padding": "6px 10px",
        "cursor": "pointer",
        "fontSize": "12px",
        "minWidth": "76px",
        "whiteSpace": "nowrap",
        "fontWeight": "bold" if enabled else "normal",
    }
    return f"{label}: {'On' if enabled else 'Off'}", style


@app.callback(
    Output("toggle-rsi-btn", "children"), Output("toggle-rsi-btn", "style"),
    Output("toggle-stochastic-btn", "children"), Output("toggle-stochastic-btn", "style"),
    Output("toggle-volume-btn", "children"), Output("toggle-volume-btn", "style"),
    Output("toggle-adx-btn", "children"), Output("toggle-adx-btn", "style"),
    Output("toggle-macd-btn", "children"), Output("toggle-macd-btn", "style"),
    Output("toggle-disparity-btn", "children"), Output("toggle-disparity-btn", "style"),
    Output("toggle-strategy-btn", "children"), Output("toggle-strategy-btn", "style"),
    Output("toggle-impulses-btn", "children"), Output("toggle-impulses-btn", "style"),
    Output("toggle-events-btn", "children"), Output("toggle-events-btn", "style"),
    Input("rsi-visible-store", "data"),
    Input("stochastic-visible-store", "data"),
    Input("volume-visible-store", "data"),
    Input("adx-visible-store", "data"),
    Input("macd-visible-store", "data"),
    Input("disparity-visible-store", "data"),
    Input("strategy-visible-store", "data"),
    Input("impulse-visible-store", "data"),
    Input("events-visible-store", "data"),
    prevent_initial_call=False,
)
def update_chart_toggle_buttons(rsi, stochastic, volume, adx, macd, disparity, strategy, impulses, events):
    return (
        *_chart_toggle_button("RSI", rsi),
        *_chart_toggle_button("Stoch", stochastic),
        *_chart_toggle_button("Volume", volume),
        *_chart_toggle_button("ADX", adx),
        *_chart_toggle_button("MACD", macd),
        *_chart_toggle_button("DIX", disparity),
        *_chart_toggle_button("Strategy", strategy),
        *_chart_toggle_button("Impulses", impulses),
        *_chart_toggle_button("Events", events),
    )

@app.callback(
    Output("toggle-chart-extend-x-btn", "children"),
    Output("toggle-chart-extend-x-btn", "style"),
    Input("chart-extend-x-store", "data"),
    prevent_initial_call=False
)
def update_chart_extend_x_button(extend_enabled):
    base_style = {
        "background": "#e3f2fd" if extend_enabled else "transparent",
        "color": "black",
        "border": "2px solid #1976d2" if extend_enabled else "1px solid #999",
        "padding": "6px 10px",
        "cursor": "pointer",
        "fontSize": "12px",
        "minWidth": "94px",
        "whiteSpace": "nowrap",
        "fontWeight": "bold" if extend_enabled else "normal"
    }
    return ("Extend X: On" if extend_enabled else "Extend X: Off"), base_style


@app.callback(
    Output("toggle-chart-focus-entry-btn", "children"),
    Output("toggle-chart-focus-entry-btn", "style"),
    Input("chart-focus-entry-store", "data"),
    prevent_initial_call=False,
)
def update_chart_focus_entry_button(focus_enabled):
    style = {
        "background": "#e3f2fd" if focus_enabled else "transparent",
        "color": "black",
        "border": "2px solid #1976d2" if focus_enabled else "1px solid #999",
        "padding": "6px 10px",
        "cursor": "pointer",
        "fontSize": "12px",
        "minWidth": "104px",
        "whiteSpace": "nowrap",
        "fontWeight": "bold" if focus_enabled else "normal",
    }
    return ("Focus Entry: On" if focus_enabled else "Focus Entry: Off"), style


register_browser_callback(
    """
function(measureMode, measureHover, oscillatorRange, candleInfo, oscillatorInfo, oscillatorSyncInfo, extendX, focusEntry, figure, viewState, chartTaskId, chartUiState) {
    if (!figure || !figure.layout) {
        return window.dash_clientside.no_update;
    }
    const root = document.getElementById('task-chart');
    const plot = root ? (root.querySelector('.js-plotly-plot') || root) : null;
    if (!plot || !window.Plotly) return window.dash_clientside.no_update;
    // Legacy Stores remain authoritative; the grouped UI state supplies a
    // safe fallback for newly added source-aware controls and restored charts.
    const uiMeasurement = (chartUiState && chartUiState.measurement) || {};
    const effectiveMeasureMode = typeof measureMode === 'boolean' ? measureMode : Boolean(uiMeasurement.enabled);
    const effectiveMeasureHover = typeof measureHover === 'boolean' ? measureHover : Boolean(uiMeasurement.show_hover);
    const effectiveOscillatorRange = typeof oscillatorRange === 'boolean' ? oscillatorRange : Boolean(uiMeasurement.shade_oscillator_range);
    window.__taskChartOscillatorRangeEnabled = effectiveOscillatorRange;
    if (window.attachNativeMeasureOverlayListeners) window.attachNativeMeasureOverlayListeners(plot);
    // Remember shapes supplied by the figure itself. User measurements are
    // appended after these, so Clear/Backspace cannot delete Signal Level.
    plot.__dashBaseShapeCount = ((figure.layout && figure.layout.shapes) || []).length;

    // Do not deep-clone and return the complete chart. Large candle figures
    // made that old path serialize/reconcile every point for a UI-only toggle.
    const layoutUpdate = {dragmode: effectiveMeasureMode ? 'drawrect' : 'pan'};
    const showHover = (!effectiveMeasureMode || effectiveMeasureHover);
    layoutUpdate.hovermode = showHover ? 'x' : false;
    layoutUpdate.hoversubplots = showHover ? 'axis' : false;

    const meta = figure.layout.meta || {};
    const hasEventFocus = Array.isArray(meta.event_focus_xrange) && meta.event_focus_xrange.length === 2;
    const targetRange = hasEventFocus ? meta.event_focus_xrange : (focusEntry ? meta.entry_focus_xrange : (extendX ? meta.extended_xrange : meta.default_xrange));
    Object.keys(figure.layout).forEach(function(key) {
        if (/^xaxis[0-9]*$/.test(key)) {
            layoutUpdate[key + '.showspikes'] = false;
            layoutUpdate[key + '.spikemode'] = 'across+toaxis';
            layoutUpdate[key + '.spikecolor'] = '#666';
            layoutUpdate[key + '.spikethickness'] = 1;
            layoutUpdate[key + '.spikedash'] = 'dash';
            layoutUpdate[key + '.spikesnap'] = 'cursor';
            if ((extendX || focusEntry || hasEventFocus) && targetRange && targetRange.length === 2) {
                layoutUpdate[key + '.range'] = targetRange;
                layoutUpdate[key + '.autorange'] = false;
            }
        }
        if (/^yaxis[0-9]*$/.test(key)) {
            layoutUpdate[key + '.showspikes'] = false;
        }
    });
    if (!extendX && !focusEntry && !hasEventFocus && viewState && String(viewState.task_id || '') === String(chartTaskId || '')) {
        const axes = viewState.axes || {};
        Object.keys(axes).forEach(function(axisName) {
            if (/^yaxis[0-9]+$/.test(axisName)) return;
            const axisState = axes[axisName] || {};
            if (axisState.range && axisState.range.length === 2) {
                layoutUpdate[axisName + '.range'] = axisState.range.slice();
                layoutUpdate[axisName + '.autorange'] = false;
            } else if (axisState.autorange) {
                layoutUpdate[axisName + '.autorange'] = true;
            }
        });
    }
    window.Plotly.relayout(plot, layoutUpdate);
    if (measureMode) {
        // A server-rendered figure can arrive just after the Store becomes
        // active. Reassert drawrect after Plotly has reconciled that figure,
        // without registering a second callback for the same Dash output.
        function enforceDrawRect() {
            if (plot.layout && plot.layout.dragmode !== 'drawrect') {
                window.Plotly.relayout(plot, {dragmode: 'drawrect'});
            }
        }
        window.setTimeout(enforceDrawRect, 0);
        window.setTimeout(enforceDrawRect, 60);
        window.setTimeout(enforceDrawRect, 200);
    }
    const figureTaskId = String((figure.layout.meta || {}).task_id || chartTaskId || '');
    if (window.__taskChartMeasureTaskId && window.__taskChartMeasureTaskId !== figureTaskId) {
        window.__taskChartMeasureShapes = [];
        // Measurements belong to one coin/timeframe. Remove the previous
        // chart's DOM labels and oscillator highlights immediately instead of
        // waiting for a new rectangle to be drawn on the next/previous chart.
        root.querySelectorAll('[id^="task-chart-measure-label-"], [id^="task-chart-measure-pointer-"], [id^="task-chart-measure-osc-range-"]').forEach(function(node) { node.remove(); });
    }
    window.__taskChartMeasureTaskId = figureTaskId;
    const savedMeasureShapes = uniqueMeasureShapes(window.__taskChartMeasureShapes || []);
    window.__taskChartMeasureShapes = savedMeasureShapes.map(function(shape) { return Object.assign({}, shape); });
    if (savedMeasureShapes.length) {
        const baseShapes = (plot.layout.shapes || []).slice(0, plot.__dashBaseShapeCount);
        window.Plotly.relayout(plot, {shapes: baseShapes.concat(savedMeasureShapes)});
        window.setTimeout(function() { if (window.showNativeMeasureResultAfterMouseup) window.showNativeMeasureResultAfterMouseup(); }, 40);
    }

    const candleTemplate = '<b>%{x|%Y-%m-%d %H:%M}</b><br>Open: %{open}<br>High: %{high}<br>Low: %{low}<br>Close: %{close}<extra></extra>';
    const expectedTaskId = String((figure.layout.meta || {}).task_id || chartTaskId || '');
    function applyHoverVisibility(targetPlot) {
        if (!targetPlot || !window.Plotly) return;
        const actualTaskId = String(((targetPlot.layout || {}).meta || {}).task_id || '');
        // A navigation callback can run before React replaces the Plotly DOM.
        // Never restyle the old coin with settings intended for the new coin.
        if (expectedTaskId && actualTaskId && expectedTaskId !== actualTaskId) return;
        (targetPlot.data || []).forEach(function(trace, index) {
        const traceName = trace.name ? String(trace.name) : '';
        const isSpikeHoverHelper = traceName.startsWith('_spike_hover_');
        const isHelper = traceName.startsWith('_') && !isSpikeHoverHelper;
        const isDynamicStrategyEvent = traceName === 'Dynamic strategy entry' || traceName === 'Dynamic strategy exit';
        // Dynamic event traces already carry their full, server-built reason
        // hovertemplate. Do not overwrite it during a zoom/pan/toggle update.
        if (isDynamicStrategyEvent && showHover && !oscillatorSyncInfo) return;
        // Main-pane entry/exit markers are candle information, not oscillator
        // information. Keep the two toggles independent even at an entry x.
        const isMainPane = !trace.yaxis || trace.yaxis === 'y';
        let hoverinfo = null;
        let hovertemplate = null;
        if (!showHover || isHelper) {
            hoverinfo = 'skip';
        } else if (isSpikeHoverHelper) {
            // The dark gray crosshair already shows time. Suppress this
            // transparent helper's duplicate white timestamp tooltip.
            hoverinfo = 'skip';
        } else if (isMainPane && (oscillatorSyncInfo || (!candleInfo && !isDynamicStrategyEvent))) {
            hoverinfo = 'skip';
        } else if (!isMainPane && !(oscillatorInfo || oscillatorSyncInfo)) {
            hoverinfo = 'skip';
        } else {
            // Explicitly restore hover after an Osc Info/Osc All toggle. A
            // trace may previously have been set to skip, and leaving the
            // property unchanged would keep every synchronized box hidden.
            hoverinfo = 'all';
            if (trace.type === 'candlestick') {
                hovertemplate = candleTemplate;
            } else if (trace.name && String(trace.name).includes('Volume')) {
                hovertemplate = 'Volume: %{y:,.0f}<extra></extra>';
            } else if (trace.name && String(trace.name).includes('RSI')) {
                hovertemplate = 'RSI: %{y:.2f}<extra></extra>';
            } else if (trace.name && (String(trace.name).includes('%K') || String(trace.name).includes('%D'))) {
                const cleanName = String(trace.name).replace(' %K', '').replace(' %D', '');
                hovertemplate = cleanName + ': %{y:.2f}<extra></extra>';
            }
        }
            const update = {};
            if (hoverinfo !== null) update.hoverinfo = hoverinfo;
            if (hovertemplate !== null) update.hovertemplate = hovertemplate;
            if (Object.keys(update).length) window.Plotly.restyle(targetPlot, update, [index]);
        });
    }
    applyHoverVisibility(plot);
    // Figure replacement and Plotly trace creation are asynchronous. Reapply
    // the hover policy after those phases so Candle Info stays Off when an
    // oscillator, Focus Entry, or another figure-changing control is used.
    [0, 60, 200].forEach(function(delay) {
        window.setTimeout(function() {
            const currentRoot = document.getElementById('task-chart');
            const currentPlot = currentRoot ? (currentRoot.querySelector('.js-plotly-plot') || currentRoot) : null;
            applyHoverVisibility(currentPlot);
        }, delay);
    });
    if (window.showNativeMeasureResultAfterMouseup) window.showNativeMeasureResultAfterMouseup();
    return {ts: Date.now(), measure: Boolean(effectiveMeasureMode), hover: Boolean(showHover)};
}
""",
    Output("chart-dragmode-enforcer-store", "data"),
    Input("measure-mode-store", "data"),
    Input("measure-hover-store", "data"),
    Input("measure-oscillator-range-store", "data"),
    Input("chart-info-box-store", "data"),
    Input("oscillator-info-box-store", "data"),
    Input("oscillator-sync-info-store", "data"),
    Input("chart-extend-x-store", "data"),
    Input("chart-focus-entry-store", "data"),
    # A newly selected chart or a newly opened oscillator replaces the Plotly
    # figure. Listen to that replacement as well, otherwise its fresh traces
    # can briefly restore candle hover boxes despite Candle Info being off.
    Input("task-chart", "figure"),
    State("chart-view-state-store", "data"),
    State("chart-task-id", "data"),
    State("chart-ui-state-store", "data"),
    prevent_initial_call=True
)


register_browser_callback(
    """
function(figure, oscillatorSyncInfo, candleInfo) {
    const root = document.getElementById('task-chart');
    const plot = root ? (root.querySelector('.js-plotly-plot') || root) : null;
    if (!plot) {
        return window.dash_clientside.no_update;
    }
    plot.__dashOscillatorSyncInfo = Boolean(oscillatorSyncInfo);
    plot.__dashCandleInfoEnabled = Boolean(candleInfo);
    function clearOscillatorSyncLabels() {
        root.querySelectorAll('[data-task-chart-oscillator-sync-label="true"]').forEach(function(label) {
            label.remove();
        });
    }
    if (plot.__dashFullPaneCrosshairInstalled) {
        if (!plot.__dashOscillatorSyncInfo) clearOscillatorSyncLabels();
        return {installed: true, ts: Date.now()};
    }
    plot.__dashFullPaneCrosshairInstalled = true;
    let line = document.getElementById('task-chart-full-pane-crosshair');
    if (!line) {
        line = document.createElement('div');
        line.id = 'task-chart-full-pane-crosshair';
        line.style.position = 'fixed';
        line.style.width = '0px';
        line.style.borderLeft = '1px dashed #666';
        line.style.pointerEvents = 'none';
        line.style.display = 'none';
        line.style.zIndex = '10050';
        document.body.appendChild(line);
    }
    function getPlotAreaRect() {
        const svg = plot.querySelector('.main-svg');
        const plotBgs = Array.from(plot.querySelectorAll('.bglayer .bg'));
        if (svg && plotBgs.length) {
            const svgRect = svg.getBoundingClientRect();
            const rects = plotBgs.map(function(bg) { return bg.getBoundingClientRect(); })
                .filter(function(rect) { return rect && rect.width > 0 && rect.height > 0; });
            if (rects.length) {
                let left = rects[0].left;
                let right = rects[0].right;
                let top = rects[0].top;
                let bottom = rects[0].bottom;
                rects.slice(1).forEach(function(rect) {
                    if (rect.left < left) left = rect.left;
                    if (rect.right > right) right = rect.right;
                    if (rect.top < top) top = rect.top;
                    if (rect.bottom > bottom) bottom = rect.bottom;
                });
                return {left: left || svgRect.left, right: right || svgRect.right, top: top || svgRect.top, bottom: bottom || svgRect.bottom, height: bottom - top};
            }
        }
        return plot.getBoundingClientRect();
    }
    function hideLine() {
        line.style.display = 'none';
        clearOscillatorSyncLabels();
        if (window.Plotly && window.Plotly.Fx) {
            try { window.Plotly.Fx.unhover(plot); } catch (e) {}
        }
    }
    function toMillis(value) {
        if (value instanceof Date) return value.getTime();
        if (typeof value === 'number') return value;
        const parsed = Date.parse(value);
        return Number.isFinite(parsed) ? parsed : null;
    }
    function findNearestPointIndex(xValues, targetMs) {
        if (!xValues || !xValues.length || targetMs === null) return null;
        let bestIndex = 0;
        let bestDistance = Infinity;
        for (let i = 0; i < xValues.length; i += 1) {
            const ms = toMillis(xValues[i]);
            if (ms === null) continue;
            const distance = Math.abs(ms - targetMs);
            if (distance < bestDistance) {
                bestDistance = distance;
                bestIndex = i;
            }
            if (ms > targetMs && distance > bestDistance) break;
        }
        return Number.isFinite(bestDistance) ? bestIndex : null;
    }
    function formatOscillatorValue(value) {
        const numeric = Number(value);
        if (!Number.isFinite(numeric)) return null;
        const magnitude = Math.abs(numeric);
        if (magnitude !== 0 && (magnitude < 0.01 || magnitude >= 10000)) return numeric.toPrecision(5);
        return numeric.toFixed(magnitude >= 100 ? 1 : magnitude >= 1 ? 2 : 4);
    }
    function renderOscillatorSyncLabels(pointIndex) {
        clearOscillatorSyncLabels();
        if (!plot.__dashOscillatorSyncInfo || !plot._fullLayout || !plot.data) return;
        const svg = plot.querySelector('.main-svg');
        if (!svg) return;
        if (window.getComputedStyle(root).position === 'static') root.style.position = 'relative';
        const rootRect = root.getBoundingClientRect();
        const svgRect = svg.getBoundingClientRect();
        const valuesByAxis = {};
        plot.data.forEach(function(trace) {
            const traceName = trace && trace.name ? String(trace.name) : '';
            const axisId = trace && trace.yaxis ? trace.yaxis : 'y';
            if (!trace || axisId === 'y' || !trace.x || !trace.y || trace.x.length <= pointIndex || trace.visible === false || trace.visible === 'legendonly') return;
            if (traceName.startsWith('_') || traceName === 'Signal Time') return;
            if (trace.mode === 'markers' && trace.showlegend === false) return;
            const value = formatOscillatorValue(trace.y[pointIndex]);
            if (value === null) return;
            if (!valuesByAxis[axisId]) valuesByAxis[axisId] = [];
            valuesByAxis[axisId].push((traceName || 'Value') + ': ' + value);
        });
        Object.keys(valuesByAxis).forEach(function(axisId) {
            const axisKey = axisId === 'y' ? 'yaxis' : 'yaxis' + axisId.slice(1);
            const axis = plot._fullLayout[axisKey];
            if (!axis || !Number.isFinite(axis._offset)) return;
            const label = document.createElement('div');
            label.dataset.taskChartOscillatorSyncLabel = 'true';
            label.textContent = valuesByAxis[axisId].join('\\n');
            label.style.position = 'absolute';
            label.style.left = Math.max(0, svgRect.left - rootRect.left + 8) + 'px';
            label.style.top = Math.max(0, svgRect.top - rootRect.top + axis._offset + 4) + 'px';
            label.style.zIndex = '10052';
            label.style.pointerEvents = 'none';
            label.style.whiteSpace = 'pre-line';
            label.style.background = 'rgba(255,255,255,0.92)';
            label.style.border = '1px solid #90a4ae';
            label.style.borderRadius = '3px';
            label.style.color = '#263238';
            label.style.font = '11px sans-serif';
            label.style.lineHeight = '1.3';
            label.style.padding = '2px 5px';
            root.appendChild(label);
        });
    }
    function syncedHoverAt(event, rect) {
        if (!window.Plotly || !window.Plotly.Fx || !plot._fullLayout || !plot.data || !plot.data.length) return;
        const xaxis = plot._fullLayout.xaxis || {};
        const range = xaxis.range || [];
        if (range.length !== 2) return;
        const rangeStart = toMillis(range[0]);
        const rangeEnd = toMillis(range[1]);
        if (rangeStart === null || rangeEnd === null || rangeEnd === rangeStart) return;
        const ratio = Math.max(0, Math.min(1, (event.clientX - rect.left) / Math.max(1, rect.right - rect.left)));
        const targetMs = rangeStart + (rangeEnd - rangeStart) * ratio;
        let xValues = null;
        for (let i = 0; i < plot.data.length; i += 1) {
            const trace = plot.data[i] || {};
            if (trace.x && trace.x.length) {
                xValues = trace.x;
                break;
            }
        }
        const pointIndex = findNearestPointIndex(xValues, targetMs);
        if (pointIndex === null) return;
        const hoverPoints = [];
        plot.data.forEach(function(trace, curveNumber) {
            const traceName = trace && trace.name ? String(trace.name) : '';
            if (!trace || !trace.x || trace.x.length <= pointIndex || trace.visible === false || trace.visible === 'legendonly') return;
            if (traceName.startsWith('_') || traceName === 'Signal Time') return;
            if (trace.mode === 'markers' && trace.showlegend === false) return;
            const isMainPane = !trace.yaxis || trace.yaxis === 'y';
            if (isMainPane && !plot.__dashCandleInfoEnabled) return;
            if (plot.__dashOscillatorSyncInfo && isMainPane) return;
            hoverPoints.push({curveNumber: curveNumber, pointNumber: pointIndex});
        });
        if (hoverPoints.length) {
            try { window.Plotly.Fx.hover(plot, hoverPoints); } catch (e) {}
        }
        // Some older Plotly bundles do not render multi-subplot hover labels
        // reliably. Keep a small, pane-anchored fallback for Osc All so every
        // visible oscillator still reports its value at the current time.
        renderOscillatorSyncLabels(pointIndex);
    }
    function moveLine(event) {
        const rect = getPlotAreaRect();
        if (!rect || event.clientX < rect.left || event.clientX > rect.right || event.clientY < rect.top || event.clientY > rect.bottom) {
            hideLine();
            return;
        }
        line.style.left = event.clientX + 'px';
        line.style.top = rect.top + 'px';
        line.style.height = Math.max(0, rect.height) + 'px';
        line.style.display = 'block';
        syncedHoverAt(event, rect);
    }
    plot.addEventListener('mousemove', moveLine);
    plot.addEventListener('mouseleave', hideLine);
    window.addEventListener('scroll', hideLine, true);
    window.addEventListener('resize', hideLine);
    return {installed: true, ts: Date.now()};
}
""",
    Output("chart-crosshair-listener-store", "data"),
    Input("task-chart", "figure"),
    Input("oscillator-sync-info-store", "data"),
    Input("chart-info-box-store", "data"),
    prevent_initial_call=True,
)
# Keep the Measure button and Plotly's Pan / draw-rectangle modebar tools in
# agreement.  This is deliberately client-side so a modebar click never sends
# the candle figure back to Python or changes the current zoom/pan ranges.
register_browser_callback(
    """
function(relayoutData, currentMeasureMode) {
    if (!relayoutData || !Object.prototype.hasOwnProperty.call(relayoutData, 'dragmode')) {
        return window.dash_clientside.no_update;
    }
    if (relayoutData.dragmode === 'drawrect') {
        return currentMeasureMode ? window.dash_clientside.no_update : true;
    }
    // Pan, zoom, select and lasso are all non-measure Plotly interactions.
    // Treat every one as leaving Measure so the button never says Measuring
    // while another modebar tool owns the drag gesture.
    return currentMeasureMode ? false : window.dash_clientside.no_update;
}
""",
    Output("measure-mode-store", "data", allow_duplicate=True),
    Input("task-chart", "relayoutData"),
    State("measure-mode-store", "data"),
    prevent_initial_call=True,
)

register_browser_callback(
    """
function(relayoutData, taskId, currentView) {
    if (!relayoutData || !taskId) {
        return window.dash_clientside.no_update;
    }
    const axes = {};
    function ensureAxis(axisName) {
        if (!axes[axisName]) axes[axisName] = {};
        return axes[axisName];
    }
    Object.keys(relayoutData).forEach(function(key) {
        let match = key.match(/^(xaxis[0-9]*|yaxis[0-9]*)\\.range\\[(0|1)\\]$/);
        if (match) {
            const axis = ensureAxis(match[1]);
            axis.range = axis.range || [null, null];
            axis.range[Number(match[2])] = relayoutData[key];
            return;
        }
        match = key.match(/^(xaxis[0-9]*|yaxis[0-9]*)\\.range$/);
        if (match && Array.isArray(relayoutData[key]) && relayoutData[key].length === 2) {
            ensureAxis(match[1]).range = relayoutData[key].slice();
            return;
        }
        match = key.match(/^(xaxis[0-9]*|yaxis[0-9]*)\\.autorange$/);
        if (match && relayoutData[key]) {
            ensureAxis(match[1]).autorange = true;
            delete ensureAxis(match[1]).range;
        }
    });
    Object.keys(axes).forEach(function(axisName) {
        const axis = axes[axisName];
        if (axis.range && (axis.range[0] === null || axis.range[1] === null)) {
            delete axis.range;
        }
    });
    if (!Object.keys(axes).length) {
        return window.dash_clientside.no_update;
    }
    const nextView = Object.assign({}, currentView || {});
    const canMergeCurrent = currentView && String(currentView.task_id || '') === String(taskId || '');
    const mergedAxes = Object.assign({}, canMergeCurrent ? (currentView.axes || {}) : {});
    Object.keys(axes).forEach(function(axisName) {
        mergedAxes[axisName] = Object.assign({}, mergedAxes[axisName] || {}, axes[axisName]);
    });
    nextView.task_id = taskId;
    nextView.axes = mergedAxes;
    nextView.ts = Date.now();
    return nextView;
}
""",
    Output("chart-view-state-store", "data"),
    Input("task-chart", "relayoutData"),
    State("chart-task-id", "data"),
    State("chart-view-state-store", "data"),
    prevent_initial_call=True,
)

def _extract_measure_point(click_data, anchor_enabled=True):
    """Return {'x': ..., 'y': ...} from Plotly clickData.

    Plotly candlestick clicks do not consistently expose a `y` key.  The chart
    therefore also adds an invisible close-price scatter trace, and this parser
    accepts both normal `y` clicks and candlestick/customdata close values.
    """
    if not click_data or not click_data.get('points'):
        return None
    point = click_data['points'][0]
    x_val = point.get('x')
    y_val = point.get('y')

    # The close-price helper is the second trace (after OHLC).  With Snap Off,
    # reject clicks on that helper so the preference has a real effect without
    # requiring a chart rebuild to add/remove the trace.
    if not anchor_enabled and point.get('curveNumber') == 1:
        return None

    if y_val is None:
        if point.get('close') is not None:
            y_val = point.get('close')
        else:
            custom = point.get('customdata')
            if isinstance(custom, (list, tuple)) and custom:
                y_val = custom[0]
            elif isinstance(custom, dict):
                y_val = custom.get('close')

    if x_val is None or y_val is None:
        return None

    try:
        y_val = float(y_val)
    except (TypeError, ValueError):
        return None
    return {"x": x_val, "y": y_val}

def _format_measure_time_delta(first_x, second_x, timeframe=None):
    try:
        first_ts = pd.to_datetime(first_x, utc=True)
        second_ts = pd.to_datetime(second_x, utc=True)
        delta = second_ts - first_ts
        total_seconds = abs(delta.total_seconds())
    except Exception:
        return "time n/a", "bars n/a"

    if total_seconds < 60:
        time_text = f"{total_seconds:.0f}s"
    elif total_seconds < 3600:
        time_text = f"{total_seconds / 60:.1f}m"
    elif total_seconds < 86400:
        time_text = f"{total_seconds / 3600:.2f}h"
    else:
        time_text = f"{total_seconds / 86400:.2f}d"

    bars_text = "bars n/a"
    interval_ms = INTERVAL_MS.get(timeframe) if timeframe else None
    if interval_ms:
        bars = total_seconds * 1000 / interval_ms
        bars_text = f"{bars:.1f} candles"
    return time_text, bars_text


def _extract_measure_box(relayout_data):
    """Return a TradingView-style drawn rectangle from Plotly relayoutData."""
    if not isinstance(relayout_data, dict):
        return None

    shapes = relayout_data.get("shapes")
    if isinstance(shapes, list) and shapes:
        for shape in reversed(shapes):
            if not isinstance(shape, dict):
                continue
            if shape.get("type") in (None, "rect") and all(k in shape for k in ("x0", "x1", "y0", "y1")):
                return {k: shape[k] for k in ("x0", "x1", "y0", "y1")}

    # Plotly versions differ: a completed draw can arrive as the complete
    # shapes list, separate ``shapes[0].x0`` keys, or one ``shapes[0]`` dict.
    # Support the latter explicitly; without it the chart shows the rectangle
    # but the measurement callback has no box to calculate.
    indexed_shape_objects = []
    for key, value in relayout_data.items():
        match = re.match(r"^shapes\[(\d+)\]$", str(key))
        if match and isinstance(value, dict):
            indexed_shape_objects.append((int(match.group(1)), value))
    for _, shape in sorted(indexed_shape_objects, reverse=True):
        if shape.get("type") in (None, "rect") and all(k in shape for k in ("x0", "x1", "y0", "y1")):
            return {k: shape[k] for k in ("x0", "x1", "y0", "y1")}

    shape_indexes = []
    for key in relayout_data:
        match = re.match(r"shapes\[(\d+)\]\.", str(key))
        if match:
            shape_indexes.append(int(match.group(1)))
    for idx in sorted(set(shape_indexes), reverse=True):
        prefix = f"shapes[{idx}]."
        shape = {
            "x0": relayout_data.get(prefix + "x0"),
            "x1": relayout_data.get(prefix + "x1"),
            "y0": relayout_data.get(prefix + "y0"),
            "y1": relayout_data.get(prefix + "y1"),
            "type": relayout_data.get(prefix + "type", "rect"),
        }
        if shape["type"] in (None, "rect") and all(shape.get(k) is not None for k in ("x0", "x1", "y0", "y1")):
            return {k: shape[k] for k in ("x0", "x1", "y0", "y1")}
    return None


@app.callback(
    Output("measure-points-store", "data", allow_duplicate=True),
    Input("task-chart", "relayoutData"),
    State("measure-mode-store", "data"),
    State("chart-task-id", "data"),
    prevent_initial_call=True
)
def capture_measure_box(relayout_data, measure_mode, task_id):
    if not measure_mode or not relayout_data:
        return dash.no_update

    box = _extract_measure_box(relayout_data)
    if not box:
        return dash.no_update

    try:
        y0 = float(box["y0"])
        y1 = float(box["y1"])
    except (TypeError, ValueError):
        return dash.no_update

    first = {"x": box["x0"], "y": y0}
    second = {"x": box["x1"], "y": y1}
    # The result itself is calculated in the matching clientside callback so
    # it is visible immediately. Keep this server callback only for point
    # state, avoiding two callbacks with the same relayout input/output pair.
    return {"task_id": task_id, "first": first, "second": second}


@app.callback(
    Output("measure-points-store", "data"),
    Output("measure-result-store", "data"),
    Input("task-chart", "clickData"),
    State("measure-mode-store", "data"),
    State("measure-anchor-store", "data"),
    State("measure-points-store", "data"),
    State("chart-task-id", "data"),
    prevent_initial_call=True
)
def capture_click(clickData, measure_mode, measure_anchor, points, task_id):
    if not measure_mode or not clickData:
        return dash.no_update, dash.no_update

    clicked = _extract_measure_point(clickData, anchor_enabled=bool(measure_anchor))
    if clicked is None:
        return dash.no_update, {
            "text": "📏 Could not read that candle price. Try clicking near a candle body/close marker, or turn Snap back On.",
            "first": None,
            "second": None
        }

    points = points or {"first": None, "second": None, "task_id": task_id}

    # First click, a completed measurement, or a click after switching tasks starts
    # a fresh ruler for the current chart only.
    if points.get('task_id') != task_id or points.get('first') is None or points.get('second') is not None:
        result = {
            "text": f"📍 First point selected at {clicked['y']:.6g}. Click the second candle to measure price %, time, and candle distance.",
            "task_id": task_id,
            "first": clicked,
            "second": None
        }
        return {"task_id": task_id, "first": clicked, "second": None}, result

    first = points['first']
    second = clicked
    try:
        price_diff = second['y'] - first['y']
        pct_change = (price_diff / first['y']) * 100 if first['y'] else 0
    except Exception:
        return dash.no_update, dash.no_update

    task = tm.get_task(task_id) if task_id else None
    timeframe = task.timeframe if task else None
    time_text, bars_text = _format_measure_time_delta(first['x'], second['x'], timeframe)
    result = {
        "text": f"📏 Δ Price: {price_diff:+.6g} ({pct_change:+.2f}%) | Δ Time: {time_text} | Δ Candles: {bars_text}",
        "task_id": task_id,
        "first": first,
        "second": second,
        "price_diff": price_diff,
        "pct_change": pct_change,
        "time_text": time_text,
        "bars_text": bars_text
    }
    return {"task_id": task_id, "first": first, "second": second}, result

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
    Output("measure-points-store", "data", allow_duplicate=True),
    Output("measure-result-store", "data", allow_duplicate=True),
    Input("clear-measure-btn", "n_clicks"),
    prevent_initial_call=True
)
def clear_measure(_):
    return {"first": None, "second": None}, None

@app.callback(
    Output("measure-result", "children"),
    Input("measure-result-store", "data"),
    Input("task-chart", "relayoutData"),
    State("chart-task-id", "data"),
    prevent_initial_call=False,
)
def render_measure_result(result, relayout_data, task_id):
    """Render point and rectangle measurements through one reliable Dash output."""
    # Do not gate this on measure-mode-store. Plotly can emit a dragmode
    # relayout after a completed shape; that async Store update may briefly say
    # ``False`` even though the visible rectangle is valid.
    if ctx.triggered_id == "task-chart":
        box = _extract_measure_box(relayout_data)
        if box:
            try:
                y0, y1 = float(box["y0"]), float(box["y1"])
            except (TypeError, ValueError):
                return "📏 Measure box could not read its price values. Draw it again inside the candle pane."
            price_diff = y1 - y0
            pct_change = price_diff / y0 * 100 if y0 else 0
            task = tm.get_task(task_id) if task_id else None
            time_text, bars_text = _format_measure_time_delta(box["x0"], box["x1"], task.timeframe if task else None)
            direction = "Up" if price_diff >= 0 else "Down"
            return f"📦 Box {direction}: Δ Price {price_diff:+.6g} ({pct_change:+.2f}%) | Δ Time: {time_text} | Δ Candles: {bars_text}"
    if isinstance(result, dict):
        return result.get("text", "")
    return result or ""

@app.callback(
    Output("measure-hint", "children"),
    Input("measure-mode-store", "data"),
    Input("measure-anchor-store", "data"),
    Input("measure-hover-store", "data"),
    prevent_initial_call=False
)
def measure_hint(active, anchor_enabled, hover_enabled):
    if active:
        snap_text = "Snap On: clicks anchor to close-price helper points." if anchor_enabled else "Snap Off: close-price helper anchors are hidden; click directly on candle/trace points."
        hover_text = "Hover On: chart tooltips/spike lines still show." if hover_enabled else "Hover Off: chart tooltips and spike lines are hidden for clean measuring."
        return f"📏 Measure mode active: drag a rectangle/box on the chart like TradingView, or click two points. {snap_text} {hover_text}"
    return "Click Measure to enable the TradingView-style ruler."

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

def apply_chart_view_state_to_figure(fig, view_state, task_id):
    """Reapply the user's current Plotly zoom/pan ranges after a figure rebuild."""
    if not isinstance(view_state, dict) or str(view_state.get("task_id")) != str(task_id):
        return fig
    axes = view_state.get("axes") or {}
    for axis_name, axis_state in axes.items():
        if not isinstance(axis_state, dict):
            continue
        axis_range = axis_state.get("range")
        if axis_range and len(axis_range) == 2:
            try:
                if re.match(r"^xaxis[0-9]*$", axis_name):
                    # Shared x-axes should move together when the main x-axis is restored.
                    if axis_name == "xaxis":
                        fig.update_xaxes(range=list(axis_range), autorange=False)
                    else:
                        fig.layout[axis_name].range = list(axis_range)
                        fig.layout[axis_name].autorange = False
                elif re.match(r"^yaxis[0-9]*$", axis_name):
                    # Only the candle pane retains a manual vertical zoom.
                    # Oscillator ranges are indicator-specific (for example
                    # RSI/Stoch 0–100) and must keep fitting their own panes.
                    if axis_name == "yaxis":
                        fig.layout[axis_name].range = list(axis_range)
                        fig.layout[axis_name].autorange = False
            except Exception:
                continue
        elif axis_state.get("autorange"):
            try:
                fig.layout[axis_name].autorange = True
            except Exception:
                continue
    return fig

def load_chart_task_window(task):
    """Load one task's inclusive chart window; no Plotly/UI decisions here."""
    if not task or not getattr(task, "signal_time", None) or not getattr(task, "symbols", None):
        return None
    symbol = task.symbols[0]
    data_path = symbol_timeframe_path(symbol, task.timeframe)
    file_path = os.path.join(data_path, "data.parquet")
    if not os.path.exists(file_path):
        return None
    start_ms = task_pre_signal_start_ms(task)
    if task.end_date:
        end_ms = int(task.end_date.replace(tzinfo=timezone.utc).timestamp() * 1000)
    else:
        end_ms = get_chart_file_end_timestamp(file_path)
        if end_ms is None or end_ms < start_ms:
            return None
    # Record whether the exact mtime-aware range is already warm before the
    # read. This gives diagnostics a concrete cache hit/miss answer without
    # changing the cache or any chart data.
    try:
        stat = os.stat(file_path)
        cache_key = (file_path, stat.st_mtime_ns, stat.st_size, start_ms, end_ms)
        cache_hit = cache_key in chart_parquet_cache
    except OSError:
        cache_hit = False
    source_read_started = time.perf_counter()
    df_source = read_chart_parquet_cached(file_path, start_ms, end_ms)
    source_read_ms = round((time.perf_counter() - source_read_started) * 1000)
    if df_source.empty:
        return None
    # Keep the defensive inclusive slice used by the original callback.
    df = df_source[(df_source["timestamp"] >= start_ms) & (df_source["timestamp"] <= end_ms)].copy()
    if df.empty:
        return None
    df["x"] = pd.to_datetime(df["timestamp"], unit="ms", utc=True)
    return {
        "symbol": symbol,
        "file_path": file_path,
        "start_ms": start_ms,
        "end_ms": end_ms,
        "df": df,
        "cache_hit": cache_hit,
        "source_read_ms": source_read_ms,
        "source_rows": len(df_source),
    }


def build_chart_render_model(task, chart_window, pane_visibility, event_context, ui_state=None):
    """Make UI-only figure decisions from normalized data and source context."""
    has_volume = "volume" in chart_window["df"].columns
    source = (event_context or {}).get("source", "main_table")
    source = source if source in CHART_SOURCE_PROFILES else "main_table"
    return {
        "task_id": str(task.task_id),
        "source": source,
        "source_profile": CHART_SOURCE_PROFILES[source],
        "has_volume": has_volume,
        "ui_state": dict(ui_state or make_chart_ui_state()),
        "indicator_specs": build_chart_indicator_specs(pane_visibility, has_volume),
    }


def resolve_chart_request_context(task_id, chart_request, fallback_context):
    """Use the canonical request only when it belongs to this rendered task."""
    if isinstance(chart_request, dict) and str(chart_request.get("task_id")) == str(task_id):
        context = chart_request.get("context")
        if isinstance(context, dict):
            return context
    return dict(fallback_context or make_chart_context())


def get_active_chart_source_event(task_id, chart_context):
    """Return the selected source event only when its profile supports trades."""
    context = dict(chart_context or {})
    source = context.get("source", "main_table")
    profile = CHART_SOURCE_PROFILES.get(source, CHART_SOURCE_PROFILES["main_table"])
    if not context.get("overlay", True) or not profile.get("show_trade_details"):
        return None
    events = context.get("events") or []
    try:
        index = int(context.get("index") or 0)
    except (TypeError, ValueError):
        return None
    if not 0 <= index < len(events):
        return None
    event = events[index] or {}
    return event if str(event.get("task_id")) == str(task_id) else None


def build_source_trade_mark_specs(event):
    """Normalize source trade timestamps for synchronized pane guides."""
    if not isinstance(event, dict):
        return []
    marks = []
    for kind, time_key, color in (
        ("entry", "entry_time", "#00c853"),
        ("exit", "exit_time", "#d50000"),
    ):
        try:
            timestamp = float(event.get(time_key))
        except (TypeError, ValueError):
            continue
        if np.isfinite(timestamp):
            marks.append({"kind": kind, "timestamp": timestamp, "color": color})
    return marks


def build_source_trade_details(event):
    """Format source-trade labels/tooltips without touching figure state."""
    event = dict(event or {})
    exit_reason = str(event.get("exit_reason") or "open")
    exit_reason_label = {
        "oscillator_close": "Stochastic close",
        "stop": "Stop loss",
        "max_adverse_dd": "Max adverse DD",
        "open": "Still open",
    }.get(exit_reason, exit_reason.replace("_", " ").title())
    try:
        return_text = f"{float(event.get('return_pct')):+.2f}%"
    except (TypeError, ValueError):
        return_text = "n/a"
    try:
        entry_distance = f"{float(event.get('entry_level_distance_pct')):.2f}% from level"
    except (TypeError, ValueError):
        entry_distance = "level distance n/a"
    entry_conditions = str(event.get("entry_conditions") or "oscillator confirmation")
    entry_window = event.get("entry_condition_window") or 1
    entry_execution = str(event.get("entry_execution") or "entry after confirmation")
    return {
        "label": event.get("label") or event.get("category") or "Dynamic strategy event",
        "direction": str(event.get("direction") or "").upper(),
        "entry_reason": (f"Level condition reached; {entry_conditions}; window={entry_window} candle(s); "
                         f"{entry_execution}; {entry_distance}"),
        "exit_reason_label": exit_reason_label,
        "exit_conditions": str(event.get("exit_conditions") or exit_reason_label),
        "return_text": return_text,
        "is_tp_checkpoint": str(event.get("category") or "").startswith("tp_"),
    }


def add_source_trade_overlay(fig, event, to_datetime, y_min, y_max):
    """Render main-pane entry/exit markers and trade-detail tooltips."""
    if not event:
        return
    entry_time, exit_time = event.get("entry_time"), event.get("exit_time")
    entry_price, exit_price = event.get("entry_price"), event.get("exit_price")
    details = build_source_trade_details(event)
    if entry_time is not None and entry_price is not None:
        try:
            entry_dt, entry_value = to_datetime(float(entry_time)), float(entry_price)
        except (TypeError, ValueError):
            entry_dt = entry_value = None
        if entry_dt is not None:
            fig.add_trace(go.Scatter(
                x=[entry_dt], y=[entry_value], mode="markers+text",
                text=[f"ENTRY {details['direction']}".strip()], textposition="top center",
                marker=dict(size=14, color="#00c853", symbol="triangle-up", line=dict(width=2, color="white")),
                name="Dynamic strategy entry", showlegend=False,
                hovertemplate=(f"<b>{details['label']}</b><br>Entry {details['direction'] or 'trade'}: %{{y:.6g}}"
                               f"<br>Why entered: {details['entry_reason']}"
                               f"<br>Time: %{{x|%Y-%m-%d %H:%M}}<extra></extra>"),
            ), row=1, col=1)
            fig.add_trace(go.Scatter(
                x=[entry_dt, entry_dt], y=[y_min, y_max], mode="lines",
                line=dict(color="#00c853", width=1, dash="dot"),
                name="Entry time", showlegend=False, hoverinfo="skip",
            ), row=1, col=1)
    if exit_time is not None and exit_price is not None:
        try:
            exit_dt, exit_value = to_datetime(float(exit_time)), float(exit_price)
        except (TypeError, ValueError):
            exit_dt = exit_value = None
        if exit_dt is not None:
            exit_text = ("TP CHECKPOINT" if details["is_tp_checkpoint"]
                         else f"EXIT {details['exit_reason_label']}: {details['return_text']}")
            exit_color = "#ff9800" if details["is_tp_checkpoint"] else ("#00c853" if details["return_text"].startswith("+") else "#d50000")
            exit_hover = (f"{details['label']}<br>TP checkpoint: %{{y:.6g}}<br>%{{x|%Y-%m-%d %H:%M}}"
                          if details["is_tp_checkpoint"] else
                          f"<b>{details['label']}</b><br>Exit reason: {details['exit_reason_label']}"
                          f"<br>Why exited: {details['exit_conditions']}<br>Return: {details['return_text']}"
                          f"<br>Exit: %{{y:.6g}}<br>Time: %{{x|%Y-%m-%d %H:%M}}")
            fig.add_trace(go.Scatter(
                x=[exit_dt], y=[exit_value], mode="markers+text", text=[exit_text], textposition="bottom center",
                marker=dict(size=14, color=exit_color, symbol="x", line=dict(width=2, color="white")),
                name="Dynamic strategy exit", showlegend=False, hovertemplate=exit_hover + "<extra></extra>",
            ), row=1, col=1)
            fig.add_trace(go.Scatter(
                x=[exit_dt, exit_dt], y=[y_min, y_max], mode="lines",
                line=dict(color="#d50000", width=1, dash="dot"),
                name="Exit time", showlegend=False, hoverinfo="skip",
            ), row=1, col=1)


# ----- Chart figure callback (light theme) -----
@app.callback(
    Output("task-chart", "figure"),
    Input("chart-task-id", "data"),
    Input("rsi-visible-store", "data"),
    Input("stochastic-visible-store", "data"),
    Input("volume-visible-store", "data"),
    Input("adx-visible-store", "data"),
    Input("macd-visible-store", "data"),
    Input("disparity-visible-store", "data"),
    Input("strategy-visible-store", "data"),
    Input("impulse-visible-store", "data"),
    Input("events-visible-store", "data"),
    Input("chart-event-context-store", "data"),
    Input("chart-focus-entry-store", "data"),
    # Candle Info is a rendering input, not only clientside state. Keeping it
    # as an Input ensures Candle Info: Off is authoritative even when the
    # optional inline Dash callbacks are disabled for renderer compatibility.
    Input("chart-info-box-store", "data"),
    # During migration these are States: legacy inputs retain exact timing,
    # while render helpers can consume the canonical contracts safely.
    State("chart-request-store", "data"),
    State("chart-ui-state-store", "data"),
    State("chart-view-state-store", "data"),
    State("measure-mode-store", "data"),
    prevent_initial_call=True
)
def update_task_chart(task_id, rsi_visible, stochastic_visible, volume_visible, adx_visible, macd_visible, disparity_visible, strategy_visible, impulse_visible, events_visible, chart_event_context, focus_entry, candle_info_enabled, chart_request, chart_ui_state, chart_view_state, measure_mode):
    if not task_id:
        return go.Figure()
    task = tm.get_task(task_id)
    interaction_trace(f"chart render start task={task_id} request={getattr(chart_request, 'get', lambda *_: None)('source') if isinstance(chart_request, dict) else None}")
    timer = PerfTimer(f"Chart render {task_id}").start()
    chart_window = load_chart_task_window(task)
    if not chart_window:
        timer.check("Task window unavailable").end()
        return go.Figure()
    interaction_trace(
        "chart data "
        f"cache={'hit' if chart_window.get('cache_hit') else 'miss'} "
        f"read_ms={chart_window.get('source_read_ms')} "
        f"source_rows={chart_window.get('source_rows')} window_rows={len(chart_window['df'])}"
    )
    timer.check("Load task window")
    sym = chart_window["symbol"]
    fp = chart_window["file_path"]
    start_ms = chart_window["start_ms"]
    end_ms = chart_window["end_ms"]
    df = chart_window["df"]
    chart_event_context = resolve_chart_request_context(task_id, chart_request, chart_event_context)
    # Retain the canonical UI snapshot in the model for new render helpers;
    # legacy Inputs remain authoritative until the next migration step.
    chart_ui_state = chart_ui_state if isinstance(chart_ui_state, dict) else make_chart_ui_state()
    source_trade_event = get_active_chart_source_event(task_id, chart_event_context)
    source_trade_marks = build_source_trade_mark_specs(source_trade_event)
    # UTC conversion remains local because the figure renderer uses it for
    # source marks, signals, and tooltips.
    def ms_to_utc_datetime(ms):
        return datetime.fromtimestamp(ms / 1000.0, tz=timezone.utc)
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

    def compute_stochastic(high, low, close, k_length=14, d_length=1, smooth=3):
        lowest_low = low.rolling(window=k_length, min_periods=k_length).min()
        highest_high = high.rolling(window=k_length, min_periods=k_length).max()
        price_range = (highest_high - lowest_low).replace(0, np.nan)
        raw_k = (close - lowest_low) / price_range * 100
        k_line = raw_k.rolling(window=smooth, min_periods=smooth).mean()
        d_line = k_line.rolling(window=d_length, min_periods=d_length).mean()
        return k_line, d_line

    def compute_adx(high, low, close, di_length=14, adx_smoothing=1):
        high = pd.Series(high, dtype="float64")
        low = pd.Series(low, dtype="float64")
        close = pd.Series(close, dtype="float64")
        up_move = high.diff()
        down_move = -low.diff()
        plus_dm = pd.Series(np.where((up_move > down_move) & (up_move > 0), up_move, 0.0), index=high.index)
        minus_dm = pd.Series(np.where((down_move > up_move) & (down_move > 0), down_move, 0.0), index=high.index)
        tr = pd.concat([(high - low), (high - close.shift()).abs(), (low - close.shift()).abs()], axis=1).max(axis=1)
        tr_rma = tr.ewm(alpha=1 / di_length, adjust=False, min_periods=di_length).mean().replace(0, np.nan)
        plus_di = 100 * plus_dm.ewm(alpha=1 / di_length, adjust=False, min_periods=di_length).mean() / tr_rma
        minus_di = 100 * minus_dm.ewm(alpha=1 / di_length, adjust=False, min_periods=di_length).mean() / tr_rma
        dx = (100 * (plus_di - minus_di).abs() / (plus_di + minus_di).replace(0, np.nan))
        adx = dx.ewm(alpha=1 / max(int(adx_smoothing or 1), 1), adjust=False, min_periods=max(int(adx_smoothing or 1), 1)).mean()
        return adx, plus_di, minus_di

    def compute_macd(close, fast_length=12, slow_length=26, signal_length=9):
        close = pd.Series(close, dtype="float64")
        fast_ema = close.ewm(span=fast_length, adjust=False, min_periods=fast_length).mean()
        slow_ema = close.ewm(span=slow_length, adjust=False, min_periods=slow_length).mean()
        macd_line = fast_ema - slow_ema
        signal_line = macd_line.ewm(span=signal_length, adjust=False, min_periods=signal_length).mean()
        hist = macd_line - signal_line
        return macd_line, signal_line, hist

    def compute_disparity_index(close, length):
        close = pd.Series(close, dtype="float64")
        ema = close.ewm(span=length, adjust=False, min_periods=length).mean().replace(0, np.nan)
        return 100 * (close - ema) / ema

    has_volume = 'volume' in df.columns

    def add_main_candles(target_fig):
        target_fig.add_trace(go.Candlestick(
            x=df['x'], open=df['open'], high=df['high'],
            low=df['low'], close=df['close'], name="OHLC",
            customdata=df[['close', 'timestamp']].values,
            increasing_line_color='#26a69a', decreasing_line_color='#ef5350',
            hoverinfo='all' if candle_info_enabled else 'skip',
            # Plotly applies hovertemplate ahead of hoverinfo for some OHLC
            # bundles. Remove it entirely when Candle Info is off; otherwise
            # older Plotly/Dash combinations can still show an OHLC box.
            hovertemplate=(
                "<b>%{x|%Y-%m-%d %H:%M}</b><br>"
                "Open: %{open}<br>High: %{high}<br>Low: %{low}<br>Close: %{close}"
                "<extra></extra>"
            ) if candle_info_enabled else None
        ), row=1, col=1)
        # Keep the invisible close-price helper in every figure.  This makes
        # Snap a capture-only preference rather than a reason to rebuild a
        # potentially large candle chart.
        target_fig.add_trace(go.Scatter(
            x=df['x'], y=df['close'], mode='markers',
            name='_measure_click_points', showlegend=False, hoverinfo='skip',
            marker=dict(size=18, color='rgba(0,0,0,0)')
        ), row=1, col=1)

    def add_hover_spike_bar(target_fig, row, y0, y1, name):
        """Transparent full-pane hover target so x-spikes work anywhere in a subplot."""
        try:
            y0 = float(y0)
            y1 = float(y1)
        except Exception:
            y0, y1 = 0.0, 1.0
        if not np.isfinite(y0) or not np.isfinite(y1) or y0 == y1:
            y0, y1 = 0.0, 1.0
        low, high = (min(y0, y1), max(y0, y1))
        target_fig.add_trace(go.Bar(
            x=df['x'], y=[high - low] * len(df), base=[low] * len(df),
            name=name, showlegend=False, opacity=0.001, marker_color='rgba(0,0,0,0.001)',
            marker_line_width=0, hoverinfo='skip'
        ), row=row, col=1)

    def add_volume_trace(target_fig, row, title="Volume"):
        add_hover_spike_bar(target_fig, row, 0, float(df['volume'].max() or 1), f'_spike_hover_volume_{row}')
        colors = np.where(df['close'] >= df['open'], '#26a69a', '#ef5350')
        target_fig.add_trace(go.Bar(
            x=df['x'], y=df['volume'], name="Volume",
            marker_color=colors, showlegend=False,
            hovertemplate='Volume: %{y:,.0f}<extra></extra>'
        ), row=row, col=1)
        target_fig.update_yaxes(title_text=title, row=row, col=1)

    def add_rsi_trace(target_fig, row):
        add_hover_spike_bar(target_fig, row, 0, 100, f'_spike_hover_rsi_{row}')
        target_fig.add_trace(go.Scatter(
            x=df['x'], y=df['rsi'], mode='lines', name='RSI (14)',
            line=dict(color='purple', width=1.5), connectgaps=True,
            hovertemplate='RSI: %{y:.2f}<extra></extra>'
        ), row=row, col=1)
        target_fig.add_trace(go.Scatter(
            x=df['x'], y=[50] * len(df), mode='lines',
            name=f'_spike_helper_rsi_{row}', showlegend=False, hoverinfo='skip',
            line=dict(width=1, color='rgba(0,0,0,0.01)')
        ), row=row, col=1)
        target_fig.add_hline(y=70, line_dash="dash", line_color="red", row=row, col=1)
        target_fig.add_hline(y=30, line_dash="dash", line_color="green", row=row, col=1)
        target_fig.update_yaxes(title_text="RSI", row=row, col=1, range=[0, 100])

    def add_stochastic_trace(target_fig, row, k_col, d_col, title, color):
        add_hover_spike_bar(target_fig, row, 0, 100, f'_spike_hover_{title}_{row}')
        # Only the %D curve is visible and used for strategy checks.  Keep k_col
        # in the signature so existing indicator_specs tuples remain readable.
        target_fig.add_trace(go.Scatter(
            x=df['x'], y=df[d_col], mode='lines', name=f'{title} %D',
            line=dict(color=color, width=1.4), connectgaps=True,
            hovertemplate=f'{title} %D: %{{y:.2f}}<extra></extra>'
        ), row=row, col=1)
        target_fig.add_hline(y=80, line_dash="dash", line_color="red", row=row, col=1)
        target_fig.add_hline(y=20, line_dash="dash", line_color="green", row=row, col=1)
        target_fig.update_yaxes(title_text=title, row=row, col=1, range=[0, 100])

    def add_adx_trace(target_fig, row):
        add_hover_spike_bar(target_fig, row, 0, 100, f'_spike_hover_adx_{row}')
        target_fig.add_trace(go.Scatter(x=df['x'], y=df['adx_14_1'], mode='lines', name='ADX 14/1', line=dict(color='#6d4c41', width=1.4), connectgaps=True, hovertemplate='ADX: %{y:.2f}<extra></extra>'), row=row, col=1)
        target_fig.add_trace(go.Scatter(x=df['x'], y=df['plus_di_14'], mode='lines', name='+DI 14', line=dict(color='#2e7d32', width=1.0), connectgaps=True, hovertemplate='+DI: %{y:.2f}<extra></extra>'), row=row, col=1)
        target_fig.add_trace(go.Scatter(x=df['x'], y=df['minus_di_14'], mode='lines', name='-DI 14', line=dict(color='#c62828', width=1.0), connectgaps=True, hovertemplate='-DI: %{y:.2f}<extra></extra>'), row=row, col=1)
        target_fig.add_hline(y=25, line_dash="dash", line_color="#999", row=row, col=1)
        target_fig.update_yaxes(title_text="ADX", row=row, col=1, range=[0, 100])

    def add_macd_trace(target_fig, row):
        macd_min = float(pd.concat([df['macd_hist'], df['macd_line'], df['macd_signal']], axis=1).min().min())
        macd_max = float(pd.concat([df['macd_hist'], df['macd_line'], df['macd_signal']], axis=1).max().max())
        add_hover_spike_bar(target_fig, row, macd_min, macd_max, f'_spike_hover_macd_{row}')
        colors = np.where(df['macd_hist'] >= 0, '#26a69a', '#ef5350')
        target_fig.add_trace(go.Bar(x=df['x'], y=df['macd_hist'], name='MACD Hist', marker_color=colors, showlegend=False, hovertemplate='Hist: %{y:.6g}<extra></extra>'), row=row, col=1)
        target_fig.add_trace(go.Scatter(x=df['x'], y=df['macd_line'], mode='lines', name='MACD 12/26', line=dict(color='#1565c0', width=1.3), connectgaps=True, hovertemplate='MACD: %{y:.6g}<extra></extra>'), row=row, col=1)
        target_fig.add_trace(go.Scatter(x=df['x'], y=df['macd_signal'], mode='lines', name='Signal 9', line=dict(color='#ef6c00', width=1.1), connectgaps=True, hovertemplate='Signal: %{y:.6g}<extra></extra>'), row=row, col=1)
        target_fig.add_hline(y=0, line_dash="dash", line_color="#999", row=row, col=1)
        target_fig.update_yaxes(title_text="MACD", row=row, col=1)

    def add_disparity_trace(target_fig, row):
        dix_cols = ['disparity_50', 'disparity_25', 'disparity_9']
        dix_range = pd.concat([df[col] for col in dix_cols], axis=1)
        dix_min = float(dix_range.min().min())
        dix_max = float(dix_range.max().max())
        add_hover_spike_bar(target_fig, row, dix_min, dix_max, f'_spike_hover_disparity_{row}')
        target_fig.add_trace(go.Scatter(x=df['x'], y=df['disparity_50'], mode='lines', name='DIX 1 (EMA 50)', line=dict(color='red', width=1.3), connectgaps=True, hovertemplate='DIX 1: %{y:.4f}%<extra></extra>'), row=row, col=1)
        target_fig.add_trace(go.Scatter(x=df['x'], y=df['disparity_25'], mode='lines', name='DIX 2 (EMA 25)', line=dict(color='blue', width=1.3), connectgaps=True, hovertemplate='DIX 2: %{y:.4f}%<extra></extra>'), row=row, col=1)
        target_fig.add_trace(go.Scatter(x=df['x'], y=df['disparity_9'], mode='lines', name='DIX 3 (EMA 9)', line=dict(color='green', width=1.3), connectgaps=True, hovertemplate='DIX 3: %{y:.4f}%<extra></extra>'), row=row, col=1)
        target_fig.add_hline(y=0, line_dash="dot", line_color="yellow", row=row, col=1)
        target_fig.update_yaxes(title_text="CMOa DIX", row=row, col=1)

    # Low-spec chart cache: cache the period view and compute indicator columns
    # lazily.  Left/right chart navigation often uses only candles; computing
    # every oscillator on every newly opened task made navigation feel slow.
    # Including parquet mtime/size prevents stale chart data after database updates.
    try:
        source_stat = os.stat(fp)
        cache_key = ("chart_period_v4_lazy_indicators", start_ms, end_ms, source_stat.st_mtime_ns, source_stat.st_size)
    except OSError:
        cache_key = ("chart_period_v4_lazy_indicators", start_ms, end_ms)
    if cache_key not in task._chart_cache:
        task._chart_cache.clear()  # Keep only 1 view in RAM
        task._chart_cache[cache_key] = df.copy()
    df = task._chart_cache[cache_key]
    retain_chart_task_indicator_cache(task)

    if volume_visible and has_volume:
        df['volume'] = pd.to_numeric(df['volume'], errors='coerce').fillna(0)
    if rsi_visible and 'rsi' not in df.columns:
        df['rsi'] = compute_rsi(df['close'])
    if stochastic_visible:
        stochastic_columns = {
            ('stoch_k_14_1_3', 'stoch_d_14_1_3'): (14, 1, 3),
            ('stoch_k_40_1_4', 'stoch_d_40_1_4'): (40, 1, 4),
            ('stoch_k_60_1_10', 'stoch_d_60_1_10'): (60, 1, 10),
            ('stoch_k_300_1_10', 'stoch_d_300_1_10'): (300, 10, 1),
        }
        for (k_col, d_col), params in stochastic_columns.items():
            if k_col not in df.columns or d_col not in df.columns:
                df[k_col], df[d_col] = compute_stochastic(df['high'], df['low'], df['close'], *params)
    if adx_visible and not {'adx_14_1', 'plus_di_14', 'minus_di_14'}.issubset(df.columns):
        df['adx_14_1'], df['plus_di_14'], df['minus_di_14'] = compute_adx(df['high'], df['low'], df['close'], 14, 1)
    if macd_visible and not {'macd_line', 'macd_signal', 'macd_hist'}.issubset(df.columns):
        df['macd_line'], df['macd_signal'], df['macd_hist'] = compute_macd(df['close'], 12, 26, 9)
    if disparity_visible:
        if 'disparity_50' not in df.columns:
            df['disparity_50'] = compute_disparity_index(df['close'], 50)
        if 'disparity_25' not in df.columns:
            df['disparity_25'] = compute_disparity_index(df['close'], 25)
        if 'disparity_9' not in df.columns:
            df['disparity_9'] = compute_disparity_index(df['close'], 9)
    # Build a UI/render model after lazy calculations. This preserves the
    # existing formulas while separating source/data decisions from rendering.
    pane_visibility = {
        "rsi": rsi_visible, "stochastic": stochastic_visible,
        "volume": volume_visible, "adx": adx_visible, "macd": macd_visible,
        "disparity": disparity_visible,
    }
    timer.check("Lazy indicator preparation")
    chart_model = build_chart_render_model(
        task, {**chart_window, "df": df}, pane_visibility, chart_event_context, chart_ui_state
    )
    has_volume = chart_model["has_volume"]
    volume_enabled = bool(volume_visible and has_volume)
    indicator_specs = chart_model["indicator_specs"]
    timer.check(f"Render model source={chart_model['source']} panes={len(indicator_specs)}")

    total_rows = 1 + len(indicator_specs)
    if total_rows == 1:
        fig = make_subplots(rows=1, cols=1, shared_xaxes=True)
    else:
        indicator_height = 0.12 if stochastic_visible else 0.18
        row_heights = [max(0.42, 1.0 - indicator_height * len(indicator_specs))]
        row_heights.extend([indicator_height] * len(indicator_specs))
        fig = make_subplots(
            rows=total_rows, cols=1, shared_xaxes=True,
            vertical_spacing=0.035, row_heights=row_heights
        )
    add_main_candles(fig)

    current_row = 2
    for indicator_type, indicator_data in indicator_specs:
        if indicator_type == "rsi":
            add_rsi_trace(fig, current_row)
        elif indicator_type == "stoch":
            add_stochastic_trace(fig, current_row, *indicator_data)
        elif indicator_type == "adx":
            add_adx_trace(fig, current_row)
        elif indicator_type == "macd":
            add_macd_trace(fig, current_row)
        elif indicator_type == "disparity":
            add_disparity_trace(fig, current_row)
        elif indicator_type == "volume":
            add_volume_trace(fig, row=current_row)
        current_row += 1

    if volume_visible and not has_volume:
        fig.add_annotation(
            text="Volume data is not available in this parquet file.",
            xref="paper", yref="paper", x=0.5, y=0.02,
            showarrow=False, bgcolor="rgba(255,255,255,0.85)",
            bordercolor="#999", font=dict(color="#555", size=12)
        )

    # Y-range for main chart (with padding) is needed before any full-height
    # hover helpers or vertical signal/event guides are added.
    y_min = df['low'].min()
    y_max = df['high'].max()
    y_padding = (y_max - y_min) * 0.05
    y_min -= y_padding
    y_max += y_padding

    # Optional per-task entry focus. Use a balanced local candle window and a
    # symmetric price range around the recorded signal price so switching to a
    # different coin never reuses an unrelated coin's zoom or y-position.
    entry_focus_xrange = None
    entry_focus_yrange = None
    # Always provide this lightweight metadata. That lets the browser focus
    # the *currently displayed* chart immediately when the toggle is clicked,
    # before the normal figure callback finishes rebuilding it. The server
    # then applies the same range to every subsequently opened chart while
    # Focus Entry remains enabled.
    if len(df):
        timestamps = df['timestamp'].to_numpy()
        signal_ms = int(float(task.signal_time))
        entry_idx = int(np.searchsorted(timestamps, signal_ms, side='left'))
        entry_idx = max(0, min(entry_idx, len(df) - 1))
        # About 100 candles gives context without showing an entire history.
        left_idx = max(0, entry_idx - 50)
        right_idx = min(len(df) - 1, entry_idx + 50)
        entry_focus_xrange = [df['x'].iloc[left_idx], df['x'].iloc[right_idx]]
        focus_low = float(df['low'].iloc[left_idx:right_idx + 1].min())
        focus_high = float(df['high'].iloc[left_idx:right_idx + 1].max())
        try:
            entry_price = float(task.signal_price)
        except (TypeError, ValueError):
            entry_price = 0.0
        if np.isfinite(entry_price) and entry_price > 0:
            half_span = max(abs(entry_price - focus_low), abs(focus_high - entry_price), entry_price * 0.01) * 1.12
            entry_focus_yrange = [entry_price - half_span, entry_price + half_span]
        else:
            focus_padding = max((focus_high - focus_low) * 0.06, 1e-12)
            entry_focus_yrange = [focus_low - focus_padding, focus_high + focus_padding]

    # A chart opened from a Dynamic Oscillator summary has a concrete trade
    # interval. Focus that entry-to-exit interval (not the original signal)
    # using the already loaded task DataFrame; no additional parquet read or
    # indicator calculation is needed.
    event_focus_xrange = None
    event_focus_yrange = None
    if source_trade_event:
        selected_event = source_trade_event
        try:
            event_entry_ms = float(selected_event.get("entry_time"))
            event_exit_ms = float(selected_event.get("exit_time"))
            event_entry_price = float(selected_event.get("entry_price"))
            event_exit_price = float(selected_event.get("exit_price"))
            if len(df) and all(np.isfinite(value) for value in (event_entry_ms, event_exit_ms, event_entry_price, event_exit_price)):
                timestamps = df['timestamp'].to_numpy()
                start_idx = int(np.searchsorted(timestamps, min(event_entry_ms, event_exit_ms), side='left'))
                end_idx = int(np.searchsorted(timestamps, max(event_entry_ms, event_exit_ms), side='right')) - 1
                start_idx = max(0, min(start_idx, len(df) - 1))
                end_idx = max(start_idx, min(end_idx, len(df) - 1))
                left_idx = max(0, start_idx - 20)
                right_idx = min(len(df) - 1, end_idx + 20)
                event_focus_xrange = [df['x'].iloc[left_idx], df['x'].iloc[right_idx]]
                event_low = min(float(df['low'].iloc[left_idx:right_idx + 1].min()), event_entry_price, event_exit_price)
                event_high = max(float(df['high'].iloc[left_idx:right_idx + 1].max()), event_entry_price, event_exit_price)
                event_padding = max((event_high - event_low) * 0.08, abs(event_entry_price) * 0.01, 1e-12)
                event_focus_yrange = [event_low - event_padding, event_high + event_padding]
        except (TypeError, ValueError):
            pass
    # Do not place a transparent hover trace over the candle pane: it can steal
    # the OHLC hover label from candles. A browser-side crosshair overlay below
    # provides the always-visible vertical guide across the full chart instead.
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
                name=event_type, showlegend=False, hoverinfo='skip'
            ), row=1, col=1)
    # Signal vertical line (fixed white dashed line at signal time)
    fig.add_trace(go.Scatter(
        x=[signal_dt, signal_dt], y=[y_min, y_max],
        mode='lines', line=dict(dash='dash', color='white', width=1),
        name='Signal Time', showlegend=False, hoverinfo='skip'
    ), row=1, col=1)
    # Signal diamond marker
    fig.add_trace(go.Scatter(
        x=[signal_dt], y=[task.signal_price],
        mode='markers',
        marker=dict(size=10, color='white', symbol='diamond', line=dict(width=1, color='yellow')),
        name='Signal Time Marker', showlegend=False, hoverinfo='skip'
    ), row=1, col=1)
    # Source-aware main-pane entry/exit markers retain detailed reasons and P&L.
    add_source_trade_overlay(fig, source_trade_event, ms_to_utc_datetime, y_min, y_max)
    # Source-entry/exit guides are repeated in each visible oscillator pane.
    # This gives strategy-summary charts one aligned time reference without
    # changing oscillator values, calculations, or main-pane trade tooltips.
    if source_trade_marks and total_rows > 1:
        for mark in source_trade_marks:
            mark_time = ms_to_utc_datetime(mark["timestamp"])
            for row in range(2, total_rows + 1):
                fig.add_vline(
                    x=mark_time, row=row, col=1,
                    line=dict(color=mark["color"], width=1, dash="dot"),
                )

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
                    showlegend=False, hoverinfo='skip'
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
                    hoverinfo='skip'
                ), row=1, col=1)
    # The native Plotly rectangle remains in the browser, and measurement text
    # is updated independently.  Keeping it out of this callback avoids a full
    # parquet/figure rebuild for every drag or point measurement.

    timer.check("Figure traces and overlays")
    # Layout (light theme)
    fig.update_layout(
        title=f"{sym} – {task.timeframe}  (Signal at {pd.to_datetime(task.signal_time, unit='ms')})",
        xaxis_rangeslider_visible=False,
        template="plotly_white",
        hovermode="x",
        # Keep hover labels tied to nearby data points; the browser-side
        # crosshair overlay provides the always-visible vertical guide.
        hoverdistance=24,
        spikedistance=-1,
        clickmode="event+select",
        # Measure is a State, not an Input: clicking Measure stays clientside
        # and does not rebuild the figure, while any later genuine rebuild
        # still preserves the active ruler mode instead of reverting to pan.
        dragmode="drawrect" if measure_mode else "pan",
        newshape=dict(line_color="#1976d2", fillcolor="rgba(25,118,210,0.08)", opacity=0.35),
        height=980 if stochastic_visible else (780 if sum(bool(v) for v in (rsi_visible, volume_enabled, adx_visible, macd_visible, disparity_visible)) >= 2 else (700 if any(bool(v) for v in (rsi_visible, volume_enabled, adx_visible, macd_visible, disparity_visible)) else 500)),
        margin=dict(l=50, r=50, t=50, b=50),
        meta={
            "default_xrange": [df['x'].iloc[0], df['x'].iloc[-1]],
            "extended_xrange": None,
            "entry_focus_xrange": entry_focus_xrange,
            "event_focus_xrange": event_focus_xrange,
            "chart_open_source": (chart_event_context or {}).get("source", "main_table") if isinstance(chart_event_context, dict) else "main_table",
            "timeframe": task.timeframe,
            "task_id": str(task_id),
            "measurement": chart_model["ui_state"].get("measurement", {}),
        },
        # Keep Plotly zoom/pan stable while toggles, measuring, table refreshes,
        # or marker overlays rebuild this figure.  The key changes only when a
        # different task chart is opened, so a new task still starts from its
        # own default view.
        uirevision=f"task-chart-preserve-view-{task_id}"
    )
    # X-axis tick format. Native Plotly spikes are disabled because the
    # browser-side crosshair overlay supplies the single full-pane dashed line.
    fig.update_xaxes(
        tickformat="%H:%M",
        hoverformat="%Y-%m-%d %H:%M",
        ticklabelmode="period",
        ticks="outside",
        showspikes=False,
        spikemode="across+toaxis",
        spikecolor="#666",
        spikesnap="cursor",
        spikethickness=1,
        spikedash="dash"
    )
    fig.update_yaxes(showspikes=False)
    if total_rows > 1:
        # Keep each oscillator's vertical scale independent. The time axis is
        # intentionally shared with candles, but a drag/wheel zoom started in
        # the main pane must never rescale or distort oscillator values.
        for row in range(2, total_rows + 1):
            fig.update_yaxes(fixedrange=True, row=row, col=1)
    if len(df) > 1:
        candle_step = df['x'].iloc[-1] - df['x'].iloc[-2]
        if candle_step.total_seconds() > 0:
            right_padding_bars = max(20, min(120, int(len(df) * 0.25)))
            fig.layout.meta["extended_xrange"] = [df['x'].iloc[0], df['x'].iloc[-1] + candle_step * right_padding_bars]
    try:
        fig.update_layout(hoversubplots="axis")
    except ValueError:
        pass
    if event_focus_xrange and event_focus_yrange:
        fig.update_xaxes(range=event_focus_xrange, autorange=False)
        fig.update_yaxes(range=event_focus_yrange, autorange=False, row=1, col=1)
    elif focus_entry and entry_focus_xrange and entry_focus_yrange:
        fig.update_xaxes(range=entry_focus_xrange, autorange=False)
        fig.update_yaxes(range=entry_focus_yrange, autorange=False, row=1, col=1)
    else:
        apply_chart_view_state_to_figure(fig, chart_view_state, task_id)
    timer.check(f"Layout and view state traces={len(fig.data)}")
    elapsed = time.perf_counter() - timer.start_time
    if elapsed > CHART_RENDER_PERF_BUDGET_SECONDS:
        perf_log(f"[TRACE] ⚠️ Chart render exceeded {CHART_RENDER_PERF_BUDGET_SECONDS:.1f}s: {elapsed:.4f}s")
    interaction_trace(f"chart render complete task={task_id} elapsed={elapsed:.3f}s traces={len(fig.data)}")
    timer.end()
    return fig

# =============================================================================
# NOTE: Database-related callbacks have been moved to database.py
# and are registered via register_database_callbacks(app) below.
# This includes: verification controls, chart updates, delete operations,
# download functions, and database maintenance callbacks.
# =============================================================================

# ----- Impulse callbacks -----
# =============================================================================
# 18. CALLBACKS: IMPULSE / STRATEGY DETAILS AND OPTIMIZATION UI
# =============================================================================
# UI around strategy/impulse parameters, details, grid search, and walk-forward.
# Core detection remains in strategies.py / impulse.py or task analysis helpers.
# =============================================================================

def parse_dynamic_percent_levels(text, default_levels=(0.5, 1.0, 2.0, 4.0)):
    """Parse comma/space separated positive percent levels for dynamic diagnostics."""
    if text is None or str(text).strip() == "":
        return list(default_levels)
    levels = []
    for raw_part in re.split(r"[,;\s]+", str(text)):
        part = raw_part.strip().replace("%", "").replace("+", "")
        if not part:
            continue
        value = float(part)
        if value <= 0:
            raise ValueError("Percent levels must be greater than 0.")
        levels.append(value)
    if not levels:
        return list(default_levels)
    return sorted(set(levels))


def parse_dynamic_nonnegative_percent_levels(text, default_levels=(0.0,)):
    """Parse comma/space separated non-negative percent levels for offset grids."""
    if text is None or str(text).strip() == "":
        return list(default_levels)
    levels = []
    for raw_part in re.split(r"[,;\s]+", str(text)):
        part = raw_part.strip().replace("%", "").replace("+", "")
        if not part:
            continue
        value = float(part)
        if value < 0:
            raise ValueError("Percent levels must be 0 or greater.")
        levels.append(value)
    if not levels:
        return list(default_levels)
    return sorted(set(levels))


def parse_dynamic_stop_rules(text):
    """Parse trigger%:stop-profit% pairs for dynamic stop movement diagnostics."""
    if text is None or str(text).strip() == "":
        return []
    rules = []
    for raw_rule in re.split(r"[,;]+", str(text)):
        rule = raw_rule.strip()
        if not rule:
            continue
        if ":" not in rule:
            raise ValueError("Dynamic stop rules must use trigger:stop format, e.g. 1:0.5.")
        trigger_text, stop_text = rule.split(":", 1)
        trigger_pct = float(trigger_text.strip().replace("%", "").replace("+", ""))
        stop_profit_pct = float(stop_text.strip().replace("%", "").replace("+", ""))
        if trigger_pct <= 0:
            raise ValueError("Dynamic stop trigger levels must be greater than 0.")
        rules.append((trigger_pct, stop_profit_pct))
    return sorted(set(rules), key=lambda item: item[0])


# =============================================================================
# 18A. READ-ONLY STRATEGY CHECKUP HELPERS
# =============================================================================
# Keep experimental diagnostics here: parse UI settings -> build raw candle path
# -> evaluate a scenario -> render summary rows. These helpers should not mutate
# DownloadTask analysis fields. Future curves/strategies should extend the spec
# and source/path builders in this section rather than mixing diagnostics into
# chart rendering, task-table rendering, or DownloadTask.analyze_signal().
# =============================================================================

def fmt_dynamic_level_label(level):
    """Format dynamic diagnostic percent labels."""
    try:
        level = float(level)
    except Exception:
        return str(level)
    if level >= 4:
        return f"{level:g}%+"
    return f"{level:g}%"


def is_task_eligible_for_dynamic_checkup(task):
    """Return False before parquet access for tasks that are not ready for diagnostics.

    Important wording: incomplete tasks and older JSON records with missing newer
    derived fields are not "corrupted"; they are simply not eligible for this
    completed-task diagnostic until recalculation/download finishes.
    """
    if task is None:
        return False
    status = str(getattr(task, "status", "") or "").lower()
    if status != "completed":
        return False
    if any(token in status for token in ("corrupt", "failed", "error")):
        return False
    for flag_name in ("corrupted", "is_corrupted", "data_corrupted", "json_corrupted", "load_corrupted"):
        if bool(getattr(task, flag_name, False)):
            return False
    return True


def build_dynamic_checkup_path(task):
    """Load and normalize one task's raw candle path once for fast scenario grids."""
    if not is_task_eligible_for_dynamic_checkup(task):
        return None
    if task is None or getattr(task, "signal_time", None) is None or getattr(task, "signal_price", None) is None:
        return None
    if getattr(task, "signal_direction", None) not in ("resistance", "support"):
        return None
    df = load_task_data_cached(task)
    if df is None or df.empty:
        return None
    df_sorted = df.sort_values("timestamp").reset_index(drop=True)
    entry_idx = df_sorted["timestamp"].searchsorted(float(task.signal_time), side="right")
    if entry_idx >= len(df_sorted):
        return None
    entry_row = df_sorted.iloc[entry_idx]
    entry_price = entry_row.get("open", entry_row.get("close"))
    if entry_price is None or (isinstance(entry_price, (float, np.floating)) and is_na(entry_price)):
        return None
    entry_price = float(entry_price)
    signal_price = float(task.signal_price)
    if entry_price <= 0 or signal_price <= 0:
        return None
    path_df = df_sorted.iloc[entry_idx:][["high", "low"]].astype(float)
    return {
        "direction": "buy" if task.signal_direction == "resistance" else "sell",
        "entry_price": entry_price,
        "signal_price": signal_price,
        "highs": path_df["high"].to_numpy(copy=False),
        "lows": path_df["low"].to_numpy(copy=False),
        "entry_level_distance_pct": abs(signal_price - entry_price) / entry_price * 100,
    }


def evaluate_dynamic_checkup_path(path, stop_loss_pct, max_dd_pct, tp_levels, stop_rules, oscillator_exit_specs=None, oscillator_exit_window=1):
    """Evaluate one preloaded path for a specific SL/DD/trailing-stop/oscillator-close scenario."""
    result = {
        "valid": False,
        "level_reached": False,
        "stop_hit": False,
        "max_dd_hit": False,
        "stopped_before_level": False,
        "stop_after_tp": False,
        "tp_hits": set(),
        "tp_hit_indices": {},
        "stop_moves": set(),
        "entry_level_distance_pct": None,
        "max_move_pct": 0.0,
        "exit_return_pct": None,
        "exit_reason": "open",
        "stop_return_pct": None,
        "initial_stop_hit": False,
        "moved_stop_hit": False,
        "oscillator_exit_hit": False,
        "oscillator_exit_idx": None,
        "exit_idx": None,
        "exit_price": None,
    }
    if not path:
        return result

    direction = path["direction"]
    entry_price = path["entry_price"]
    signal_price = path["signal_price"]
    result["valid"] = True
    result["entry_level_distance_pct"] = path["entry_level_distance_pct"]

    stop_loss_pct = max(0.0, float(stop_loss_pct or 0.0))
    current_stop_return_pct = -stop_loss_pct
    stop_price = entry_price * (1 - stop_loss_pct / 100) if direction == "buy" else entry_price * (1 + stop_loss_pct / 100)
    max_dd_pct = float(max_dd_pct or 0.0)
    max_dd_price = None
    if max_dd_pct > 0:
        max_dd_price = entry_price * (1 - max_dd_pct / 100) if direction == "buy" else entry_price * (1 + max_dd_pct / 100)
    selected_exit_specs = select_exit_specs_for_path(path, oscillator_exit_specs)
    close_values = path.get("closes")

    for idx, (high, low) in enumerate(zip(path["highs"], path["lows"])):
        if direction == "buy":
            # If max-DD is tighter than the initial/trailing stop, classify the
            # adverse exit as DD cap first. This keeps scenario-grid counts
            # intuitive when users test max adverse DD below the stop-loss distance.
            max_dd_is_tighter = max_dd_price is not None and max_dd_price >= stop_price
            if max_dd_is_tighter and low <= max_dd_price:
                result["max_dd_hit"] = True
                result["exit_return_pct"] = -max_dd_pct
                result["exit_idx"] = idx
                result["exit_price"] = max_dd_price
                result["exit_reason"] = "max_adverse_dd"
                break
            if low <= stop_price:
                result["stop_hit"] = True
                result["exit_return_pct"] = current_stop_return_pct
                result["exit_idx"] = idx
                result["exit_price"] = stop_price
                result["stop_return_pct"] = current_stop_return_pct
                result["initial_stop_hit"] = abs(current_stop_return_pct + stop_loss_pct) < 1e-12
                result["moved_stop_hit"] = not result["initial_stop_hit"]
                result["exit_reason"] = "stop"
                break
            if max_dd_price is not None and low <= max_dd_price:
                result["max_dd_hit"] = True
                result["exit_return_pct"] = -max_dd_pct
                result["exit_idx"] = idx
                result["exit_price"] = max_dd_price
                result["exit_reason"] = "max_adverse_dd"
                break
            move_pct = (high - entry_price) / entry_price * 100
            if high >= signal_price:
                result["level_reached"] = True
        else:
            max_dd_is_tighter = max_dd_price is not None and max_dd_price <= stop_price
            if max_dd_is_tighter and high >= max_dd_price:
                result["max_dd_hit"] = True
                result["exit_return_pct"] = -max_dd_pct
                result["exit_idx"] = idx
                result["exit_price"] = max_dd_price
                result["exit_reason"] = "max_adverse_dd"
                break
            if high >= stop_price:
                result["stop_hit"] = True
                result["exit_return_pct"] = current_stop_return_pct
                result["exit_idx"] = idx
                result["exit_price"] = stop_price
                result["stop_return_pct"] = current_stop_return_pct
                result["initial_stop_hit"] = abs(current_stop_return_pct + stop_loss_pct) < 1e-12
                result["moved_stop_hit"] = not result["initial_stop_hit"]
                result["exit_reason"] = "stop"
                break
            if max_dd_price is not None and high >= max_dd_price:
                result["max_dd_hit"] = True
                result["exit_return_pct"] = -max_dd_pct
                result["exit_idx"] = idx
                result["exit_price"] = max_dd_price
                result["exit_reason"] = "max_adverse_dd"
                break
            move_pct = (entry_price - low) / entry_price * 100
            if low <= signal_price:
                result["level_reached"] = True

        result["max_move_pct"] = max(result["max_move_pct"], move_pct)
        for level in tp_levels:
            if move_pct >= level:
                result["tp_hits"].add(level)
                result["tp_hit_indices"].setdefault(level, idx)

        for trigger_pct, stop_profit_pct in stop_rules:
            if move_pct < trigger_pct:
                continue
            if direction == "buy":
                candidate_stop = entry_price * (1 + stop_profit_pct / 100)
                if candidate_stop > stop_price:
                    stop_price = candidate_stop
                    current_stop_return_pct = stop_profit_pct
                    result["stop_moves"].add(trigger_pct)
            else:
                candidate_stop = entry_price * (1 - stop_profit_pct / 100)
                if candidate_stop < stop_price:
                    stop_price = candidate_stop
                    current_stop_return_pct = stop_profit_pct
                    result["stop_moves"].add(trigger_pct)

        if selected_exit_specs and close_values is not None and idx > 0:
            oscillator_ready = True
            for spec in selected_exit_specs:
                condition = normalize_oscillator_condition(spec.get("condition"))
                if condition == "disabled":
                    continue
                column = spec.get("column")
                if column not in path or not oscillator_condition_met_within_window(path[column], idx, spec["level"], condition, oscillator_exit_window, min_idx=0):
                    oscillator_ready = False
                    break
            if oscillator_ready:
                close_price = float(close_values[idx])
                result["oscillator_exit_hit"] = True
                result["oscillator_exit_idx"] = idx
                result["exit_idx"] = idx
                result["exit_price"] = close_price
                result["exit_return_pct"] = ((close_price - entry_price) / entry_price * 100) if direction == "buy" else ((entry_price - close_price) / entry_price * 100)
                result["exit_reason"] = "oscillator_close"
                break

    result["stopped_before_level"] = bool((result["stop_hit"] or result["max_dd_hit"]) and not result["level_reached"])
    result["stop_after_tp"] = bool((result["stop_hit"] or result["max_dd_hit"]) and len(result["tp_hits"]) > 0)
    return result


def analyze_dynamic_path_milestones(path):
    """Read-only path milestones independent of the active SL/DD scenario."""
    result = {
        "valid": False,
        "tp05": False,
        "tp1": False,
        "dd05": False,
        "dd05_before_tp1": False,
        "tp1_before_dd05": False,
        "entry_return_after_tp05": False,
        "entry_return_after_tp1": False,
        "dd05_after_tp05": False,
        "dd05_after_tp1": False,
        "tp1_before_entry_return_after_tp05": False,
    }
    if not path:
        return result

    direction = path["direction"]
    entry_price = path["entry_price"]
    result["valid"] = True
    tp05_seen = False
    tp1_seen = False
    entry_return_after_tp05_seen = False

    for high, low in zip(path["highs"], path["lows"]):
        if direction == "buy":
            favorable_pct = (high - entry_price) / entry_price * 100
            adverse_pct = (entry_price - low) / entry_price * 100
            returned_entry = low <= entry_price
        else:
            favorable_pct = (entry_price - low) / entry_price * 100
            adverse_pct = (high - entry_price) / entry_price * 100
            returned_entry = high >= entry_price

        if adverse_pct >= 0.5:
            result["dd05"] = True
            if not tp1_seen:
                result["dd05_before_tp1"] = True
            if tp05_seen:
                result["dd05_after_tp05"] = True
            if tp1_seen:
                result["dd05_after_tp1"] = True

        if favorable_pct >= 0.5:
            result["tp05"] = True
            tp05_seen = True

        if tp05_seen and returned_entry:
            result["entry_return_after_tp05"] = True
            entry_return_after_tp05_seen = True

        if favorable_pct >= 1.0:
            result["tp1"] = True
            if not result["dd05"]:
                result["tp1_before_dd05"] = True
            if not entry_return_after_tp05_seen:
                result["tp1_before_entry_return_after_tp05"] = True
            tp1_seen = True

        if tp1_seen and returned_entry:
            result["entry_return_after_tp1"] = True

    return result


def simulate_dynamic_checkup_for_task(task, stop_loss_pct, max_dd_pct, tp_levels, stop_rules):
    """Run a read-only raw-candle diagnostic for one task without mutating task fields."""
    path = build_dynamic_checkup_path(task)
    return evaluate_dynamic_checkup_path(path, stop_loss_pct, max_dd_pct, tp_levels, stop_rules)


def normalize_expectancy_inputs(notional_usd, round_trip_cost_pct, open_return_pct):
    """Normalize diagnostic expectancy settings used by strategy checkups."""
    notional = max(0.0, float(notional_usd if notional_usd is not None else 1000.0))
    costs = max(0.0, float(round_trip_cost_pct if round_trip_cost_pct is not None else 0.0))
    open_return = float(open_return_pct if open_return_pct is not None else 0.0)
    return notional, costs, open_return


def get_diagnostic_net_return_pct(result, round_trip_cost_pct=0.0, open_return_pct=0.0):
    """Estimate net percent return for a simulated diagnostic result.

    TP levels in these checkups are checkpoints, not forced exits. Realized return
    therefore comes from SL/trailing-stop/DD-cap exits; still-open paths use the
    configurable open/no-exit fallback return. Round-trip costs are subtracted
    from every valid simulated trade.
    """
    if not result or not result.get("valid"):
        return None
    gross_return = result.get("exit_return_pct")
    if gross_return is None:
        gross_return = open_return_pct
    return float(gross_return) - float(round_trip_cost_pct or 0.0)


def build_expectancy_summary_rows(results, notional_usd, round_trip_cost_pct, open_return_pct, td_style, label_prefix="Estimated"):
    """Build copyable net-expectancy diagnostic rows for a strategy summary."""
    valid_results = [r for r in results if r and r.get("valid")]
    total = len(valid_results)

    def money(value):
        return f"${value:,.2f}"

    if not total:
        return [
            html.Tr([html.Td(f"{label_prefix} net expectancy", style=td_style), html.Td("0 / 0", style=td_style)]),
        ]

    net_returns = [get_diagnostic_net_return_pct(r, round_trip_cost_pct, open_return_pct) for r in valid_results]
    net_returns = [r for r in net_returns if r is not None]
    gross_returns = [float(r.get("exit_return_pct") if r.get("exit_return_pct") is not None else open_return_pct) for r in valid_results]
    gross_profit_pct = sum(r for r in gross_returns if r > 0)
    gross_loss_pct = abs(sum(r for r in gross_returns if r < 0))
    profit_factor = "∞" if gross_loss_pct == 0 and gross_profit_pct > 0 else (f"{gross_profit_pct / gross_loss_pct:.2f}" if gross_loss_pct else "n/a")

    avg_net_pct = sum(net_returns) / total
    total_net_pct = sum(net_returns)
    total_profit_usd = total_net_pct / 100 * notional_usd
    winners = sum(1 for r in net_returns if r > 0)
    losers = sum(1 for r in net_returns if r < 0)
    flat = total - winners - losers
    open_count = sum(1 for r in valid_results if r.get("exit_return_pct") is None)

    return [
        html.Tr([html.Td("— Net expectancy / money estimate —", style=td_style), html.Td("Diagnostic only; TP rows are checkpoints unless your dynamic stop closes later", style=td_style)]),
        html.Tr([html.Td("Notional per trade", style=td_style), html.Td(money(notional_usd), style=td_style)]),
        html.Tr([html.Td("Round-trip costs", style=td_style), html.Td(f"{round_trip_cost_pct:g}% subtracted from every trade", style=td_style)]),
        html.Tr([html.Td("Open/no-exit fallback", style=td_style), html.Td(f"{open_return_pct:g}% used for {open_count} open paths", style=td_style)]),
        html.Tr([html.Td(f"{label_prefix} avg net return / trade", style=td_style), html.Td(f"{avg_net_pct:.3f}%", style=td_style)]),
        html.Tr([html.Td(f"{label_prefix} total net return sum", style=td_style), html.Td(f"{total_net_pct:.2f}% across {total} trades", style=td_style)]),
        html.Tr([html.Td(f"{label_prefix} total net P/L", style=td_style), html.Td(money(total_profit_usd), style=td_style)]),
        html.Tr([html.Td("Net winners / losers / flat", style=td_style), html.Td(f"{winners} / {losers} / {flat}", style=td_style)]),
        html.Tr([html.Td("Gross profit factor before costs", style=td_style), html.Td(profit_factor, style=td_style)]),
    ]


def build_dynamic_checkup_summary_table(tasks, stop_loss_pct, max_dd_pct, tp_levels, stop_rules, sl_grid=None, be_grid=None, dd_grid=None, notional_usd=1000, round_trip_cost_pct=0.0, open_return_pct=0.0):
    """Build an on-demand summary table from raw dynamic-check diagnostic results."""
    td_style = {"padding": "4px 8px", "border": "1px solid #ddd"}
    notional_usd, round_trip_cost_pct, open_return_pct = normalize_expectancy_inputs(notional_usd, round_trip_cost_pct, open_return_pct)
    total_tasks = len(tasks)
    eligible_tasks = [t for t in tasks if is_task_eligible_for_dynamic_checkup(t)]
    paths = [build_dynamic_checkup_path(t) for t in eligible_tasks]
    valid_paths = [p for p in paths if p]
    results = [evaluate_dynamic_checkup_path(p, stop_loss_pct, max_dd_pct, tp_levels, stop_rules) for p in valid_paths]
    milestones = [analyze_dynamic_path_milestones(p) for p in valid_paths]
    valid_results = [r for r in results if r["valid"]]
    valid_milestones = [m for m in milestones if m["valid"]]
    valid_total = len(valid_results)

    def fmt_stat(count, total):
        return f"{count} / {total} ({count / total * 100:.1f}%)" if total else "0 / 0"

    def scenario_summary_row(label, scenario_results):
        scenario_total = len(scenario_results)
        reached = sum(1 for r in scenario_results if r["level_reached"])
        stopped = sum(1 for r in scenario_results if r["stop_hit"])
        max_dd = sum(1 for r in scenario_results if r["max_dd_hit"])
        tp05 = sum(1 for r in scenario_results if any(level >= 0.5 for level in r["tp_hits"]))
        stop_moved = sum(1 for r in scenario_results if r["stop_moves"])
        avg_net = 0.0
        total_net_usd = 0.0
        if scenario_total:
            scenario_net = [get_diagnostic_net_return_pct(r, round_trip_cost_pct, open_return_pct) for r in scenario_results]
            scenario_net = [r for r in scenario_net if r is not None]
            avg_net = sum(scenario_net) / scenario_total
            total_net_usd = sum(scenario_net) / 100 * notional_usd
        return html.Tr([
            html.Td(label, style=td_style),
            html.Td(
                f"level {fmt_stat(reached, scenario_total)} | "
                f"TP0.5 {fmt_stat(tp05, scenario_total)} | "
                f"SL {fmt_stat(stopped, scenario_total)} | "
                f"adverse DD cap {fmt_stat(max_dd, scenario_total)} | "
                f"stop moved {fmt_stat(stop_moved, scenario_total)} | "
                f"avg net {avg_net:.3f}% | "
                f"net P/L ${total_net_usd:,.2f}",
                style=td_style,
            ),
        ])

    stop_events = sum(1 for r in valid_results if r["stop_hit"])
    max_dd_events = sum(1 for r in valid_results if r["max_dd_hit"])
    level_reached = sum(1 for r in valid_results if r["level_reached"])
    stopped_before_level = sum(1 for r in valid_results if r["stopped_before_level"])
    stop_after_tp = sum(1 for r in valid_results if r["stop_after_tp"])
    stop_moved = sum(1 for r in valid_results if r["stop_moves"])
    raw_tp05 = sum(1 for m in valid_milestones if m["tp05"])
    raw_tp1 = sum(1 for m in valid_milestones if m["tp1"])
    raw_dd05 = sum(1 for m in valid_milestones if m["dd05"])
    raw_dd05_before_tp1 = sum(1 for m in valid_milestones if m["dd05_before_tp1"])
    raw_tp1_before_dd05 = sum(1 for m in valid_milestones if m["tp1_before_dd05"])
    raw_entry_return_after_tp05 = sum(1 for m in valid_milestones if m["entry_return_after_tp05"])
    raw_entry_return_after_tp1 = sum(1 for m in valid_milestones if m["entry_return_after_tp1"])
    raw_dd05_after_tp05 = sum(1 for m in valid_milestones if m["dd05_after_tp05"])
    raw_dd05_after_tp1 = sum(1 for m in valid_milestones if m["dd05_after_tp1"])
    raw_tp1_before_entry_return_after_tp05 = sum(1 for m in valid_milestones if m["tp1_before_entry_return_after_tp05"])

    distance_ranges = ["0-0.12%", "0.12-0.5%", "0.5-1%", "1-2%", "2-4%", "4%+"]
    distance_counts = {r: 0 for r in distance_ranges}
    for result in valid_results:
        bucket = get_toward_distance_bucket(result["entry_level_distance_pct"])
        if bucket:
            distance_counts[bucket] += 1

    rows = [
        html.Tr([html.Td("All tasks in snapshot", style=td_style), html.Td(str(total_tasks), style=td_style)]),
        html.Tr([html.Td("Completed tasks considered", style=td_style), html.Td(fmt_stat(len(eligible_tasks), total_tasks), style=td_style)]),
        html.Tr([html.Td("Valid dynamic cases with candle data", style=td_style), html.Td(fmt_stat(valid_total, len(eligible_tasks)), style=td_style)]),
        html.Tr([html.Td("Initial stop events", style=td_style), html.Td(fmt_stat(stop_events, valid_total), style=td_style)]),
        html.Tr([html.Td("Max adverse DD cap events", style=td_style), html.Td(fmt_stat(max_dd_events, valid_total), style=td_style)]),
        html.Tr([html.Td("Reached signal level", style=td_style), html.Td(fmt_stat(level_reached, valid_total), style=td_style)]),
        html.Tr([html.Td("Stopped before level", style=td_style), html.Td(fmt_stat(stopped_before_level, valid_total), style=td_style)]),
        html.Tr([html.Td("Stop after at least one TP", style=td_style), html.Td(fmt_stat(stop_after_tp, valid_total), style=td_style)]),
        html.Tr([html.Td("Dynamic stop moved", style=td_style), html.Td(fmt_stat(stop_moved, valid_total), style=td_style)]),
        html.Tr([html.Td("Entry→Level dist 0-1%", style=td_style), html.Td(" | ".join(f"{r}:{distance_counts[r]}" for r in distance_ranges[:3]), style=td_style)]),
        html.Tr([html.Td("Entry→Level dist 1%+", style=td_style), html.Td(" | ".join(f"{r}:{distance_counts[r]}" for r in distance_ranges[3:]), style=td_style)]),
    ]

    rows.extend(build_expectancy_summary_rows(valid_results, notional_usd, round_trip_cost_pct, open_return_pct, td_style, label_prefix="Dynamic scenario"))

    reached_results = [r for r in valid_results if r["level_reached"]]
    stopped_results = [r for r in valid_results if r["stopped_before_level"]]
    for level in tp_levels:
        label = fmt_dynamic_level_label(level)
        tp_found = sum(1 for r in valid_results if level in r["tp_hits"])
        tp_reached = sum(1 for r in reached_results if level in r["tp_hits"])
        tp_stopped = sum(1 for r in stopped_results if level in r["tp_hits"])
        rows.extend([
            html.Tr([html.Td(f"TP {label} found", style=td_style), html.Td(fmt_stat(tp_found, valid_total), style=td_style)]),
            html.Tr([html.Td(f"TP {label} conditional over reached level", style=td_style), html.Td(fmt_stat(tp_reached, len(reached_results)), style=td_style)]),
            html.Tr([html.Td(f"TP {label} while stopped before level", style=td_style), html.Td(fmt_stat(tp_stopped, len(stopped_results)), style=td_style)]),
        ])

    rows.extend([
        html.Tr([html.Td("Raw path touched adverse DD 0.5% from entry", style=td_style), html.Td(fmt_stat(raw_dd05, valid_total), style=td_style)]),
        html.Tr([html.Td("Raw path adverse DD 0.5% before TP1", style=td_style), html.Td(fmt_stat(raw_dd05_before_tp1, valid_total), style=td_style)]),
        html.Tr([html.Td("Raw path TP1 before adverse DD 0.5%", style=td_style), html.Td(fmt_stat(raw_tp1_before_dd05, valid_total), style=td_style)]),
        html.Tr([html.Td("After TP0.5 returned to entry", style=td_style), html.Td(fmt_stat(raw_entry_return_after_tp05, raw_tp05), style=td_style)]),
        html.Tr([html.Td("After TP1 returned to entry", style=td_style), html.Td(fmt_stat(raw_entry_return_after_tp1, raw_tp1), style=td_style)]),
        html.Tr([html.Td("After TP0.5 touched adverse DD 0.5%", style=td_style), html.Td(fmt_stat(raw_dd05_after_tp05, raw_tp05), style=td_style)]),
        html.Tr([html.Td("After TP1 touched adverse DD 0.5%", style=td_style), html.Td(fmt_stat(raw_dd05_after_tp1, raw_tp1), style=td_style)]),
        html.Tr([html.Td("TP1 before entry return after TP0.5", style=td_style), html.Td(fmt_stat(raw_tp1_before_entry_return_after_tp05, raw_tp05), style=td_style)]),
    ])

    for trigger_pct, stop_profit_pct in stop_rules:
        moved = sum(1 for r in valid_results if trigger_pct in r["stop_moves"])
        rows.append(html.Tr([
            html.Td(f"Stop moved at {fmt_dynamic_level_label(trigger_pct)} to {stop_profit_pct:g}% profit", style=td_style),
            html.Td(fmt_stat(moved, valid_total), style=td_style),
        ]))

    sl_grid = sl_grid or []
    if sl_grid:
        rows.append(html.Tr([html.Td("— SL grid scenarios —", style=td_style), html.Td("Same TP levels and dynamic stop rules; max adverse DD unchanged", style=td_style)]))
        for sl_pct in sl_grid:
            scenario_results = [evaluate_dynamic_checkup_path(p, sl_pct, max_dd_pct, tp_levels, stop_rules) for p in valid_paths]
            rows.append(scenario_summary_row(f"Initial SL {fmt_dynamic_level_label(sl_pct)}", scenario_results))

    be_grid = be_grid or []
    if be_grid:
        rows.append(html.Tr([html.Td("— Breakeven arm grid —", style=td_style), html.Td("Move stop to entry when favorable move reaches trigger; initial SL/max adverse DD unchanged", style=td_style)]))
        for arm_pct in be_grid:
            scenario_rules = sorted(set(list(stop_rules) + [(arm_pct, 0.0)]), key=lambda item: item[0])
            scenario_results = [evaluate_dynamic_checkup_path(p, stop_loss_pct, max_dd_pct, tp_levels, scenario_rules) for p in valid_paths]
            rows.append(scenario_summary_row(f"BE after {fmt_dynamic_level_label(arm_pct)}", scenario_results))

    dd_grid = dd_grid or []
    if dd_grid:
        rows.append(html.Tr([html.Td("— Max adverse DD cap grid —", style=td_style), html.Td("Initial SL, TP levels, and dynamic stop rules unchanged", style=td_style)]))
        for dd_pct in dd_grid:
            scenario_results = [evaluate_dynamic_checkup_path(p, stop_loss_pct, dd_pct, tp_levels, stop_rules) for p in valid_paths]
            rows.append(scenario_summary_row(f"Max adverse DD cap {fmt_dynamic_level_label(dd_pct)}", scenario_results))

    return html.Table(rows, style={"borderCollapse": "collapse", "width": "100%", "fontSize": "13px"})


def build_level_reversal_source(task):
    """Preload one task once for level-reversal offset/grid diagnostics."""
    if not is_task_eligible_for_dynamic_checkup(task):
        return None
    if task is None or getattr(task, "signal_time", None) is None or getattr(task, "signal_price", None) is None:
        return None
    if getattr(task, "signal_direction", None) not in ("resistance", "support"):
        return None

    df = load_task_data_cached(task)
    if df is None or df.empty:
        return None

    signal_price = float(task.signal_price)
    if signal_price <= 0:
        return None

    df_sorted = df.sort_values("timestamp").reset_index(drop=True)
    search_idx = df_sorted["timestamp"].searchsorted(float(task.signal_time), side="right")
    if search_idx >= len(df_sorted):
        return None
    path_df = df_sorted.iloc[search_idx:][["high", "low"]].astype(float)
    if path_df.empty:
        return None

    return {
        "level_kind": task.signal_direction,
        "direction": "sell" if task.signal_direction == "resistance" else "buy",
        "signal_price": signal_price,
        "highs": path_df["high"].to_numpy(copy=False),
        "lows": path_df["low"].to_numpy(copy=False),
    }


def build_level_reversal_path_from_source(source, entry_offset_pct=0.0):
    """Build one offset path from a preloaded level-reversal source."""
    if not source:
        return None
    entry_offset_pct = max(0.0, float(entry_offset_pct or 0.0))
    signal_price = float(source["signal_price"])
    if signal_price <= 0:
        return None

    if source["level_kind"] == "resistance":
        direction = "sell"
        entry_price = signal_price * (1 + entry_offset_pct / 100)
        trigger_mask = source["highs"] >= entry_price
    else:
        direction = "buy"
        entry_price = signal_price * (1 - entry_offset_pct / 100)
        trigger_mask = source["lows"] <= entry_price

    trigger_positions = np.flatnonzero(trigger_mask)
    if len(trigger_positions) == 0:
        return None

    trigger_idx = int(trigger_positions[0])
    highs = source["highs"][trigger_idx:]
    lows = source["lows"][trigger_idx:]
    if len(highs) == 0 or entry_price <= 0:
        return None

    return {
        "direction": direction,
        "entry_price": entry_price,
        "signal_price": signal_price,
        "highs": highs,
        "lows": lows,
        "entry_offset_pct": entry_offset_pct,
        "entry_level_distance_pct": entry_offset_pct,
    }


def build_level_reversal_path(task, entry_offset_pct=0.0):
    """Build a raw path for the opposite trade after level touch/overshoot."""
    return build_level_reversal_path_from_source(build_level_reversal_source(task), entry_offset_pct)



def compute_dynamic_rsi_series(close, period=14):
    """Compute RSI for diagnostic oscillator checkups."""
    close = pd.Series(close, dtype="float64")
    delta = close.diff()
    gain = delta.clip(lower=0)
    loss = -delta.clip(upper=0)
    avg_gain = gain.rolling(window=period, min_periods=period).mean()
    avg_loss = loss.rolling(window=period, min_periods=period).mean()
    rs = avg_gain / avg_loss.replace(0, np.nan)
    return 100 - (100 / (1 + rs))


def compute_dynamic_stochastic_series(high, low, close, k_length, d_length=1, smooth=3):
    """Compute the chart-style stochastic %K/%D diagnostic lines."""
    high = pd.Series(high, dtype="float64")
    low = pd.Series(low, dtype="float64")
    close = pd.Series(close, dtype="float64")
    lowest_low = low.rolling(window=k_length, min_periods=k_length).min()
    highest_high = high.rolling(window=k_length, min_periods=k_length).max()
    price_range = (highest_high - lowest_low).replace(0, np.nan)
    raw_k = (close - lowest_low) / price_range * 100
    k_line = raw_k.rolling(window=smooth, min_periods=smooth).mean()
    d_line = k_line.rolling(window=d_length, min_periods=d_length).mean()
    return k_line, d_line


def normalize_oscillator_condition(condition):
    allowed = {"cross_down", "cross_up", "above", "below", "disabled"}
    return condition if condition in allowed else "disabled"


def oscillator_condition_met(values, idx, level, condition):
    """Evaluate one oscillator condition at index idx."""
    condition = normalize_oscillator_condition(condition)
    if condition == "disabled":
        return True
    if idx < 0 or idx >= len(values):
        return False
    current = values[idx]
    if pd.isna(current):
        return False
    level = float(level if level is not None else 0.0)
    if condition == "above":
        return current >= level
    if condition == "below":
        return current <= level
    if idx == 0 or pd.isna(values[idx - 1]):
        return False
    previous = values[idx - 1]
    if condition == "cross_down":
        return previous > level and current <= level
    if condition == "cross_up":
        return previous < level and current >= level
    return False


def oscillator_condition_met_within_window(values, idx, level, condition, window=1, min_idx=0):
    """Return True when one oscillator condition matched within a recent past/current candle window."""
    window = max(1, int(window or 1))
    start_idx = max(int(min_idx or 0), idx - window + 1)
    return any(oscillator_condition_met(values, check_idx, level, condition) for check_idx in range(start_idx, idx + 1))


def oscillator_specs_met_within_window(values_by_column, specs, idx, window=1, min_idx=0):
    """Require every enabled oscillator spec to have matched within the same past/current window.

    ``values_by_column`` is prebuilt once per task source. Repeatedly calling
    DataFrame.to_numpy() inside the candle scan made long histories effectively
    quadratic and was the main reason the dynamic stochastic checkup stalled.
    """
    for spec in specs:
        condition = normalize_oscillator_condition(spec.get("condition"))
        if condition == "disabled":
            continue
        column = spec.get("column")
        values = values_by_column.get(column) if isinstance(values_by_column, dict) else None
        if values is None:
            return False
        if not oscillator_condition_met_within_window(values, idx, spec["level"], condition, window, min_idx=min_idx):
            return False
    return True


def build_oscillator_specs(stoch14_level, stoch14_condition, stoch40_level, stoch40_condition, stoch60_level, stoch60_condition, stoch300_level, stoch300_condition, rsi_level, rsi_condition, default_stoch_level=87.0, default_rsi_level=70.0):
    """Build normalized oscillator condition specs from UI values."""
    return [
        {"label": "Stoch 14/1/3", "column": "stoch_d_14_1_3", "level": float(stoch14_level if stoch14_level is not None else default_stoch_level), "condition": normalize_oscillator_condition(stoch14_condition)},
        {"label": "Stoch 40/1/4", "column": "stoch_d_40_1_4", "level": float(stoch40_level if stoch40_level is not None else default_stoch_level), "condition": normalize_oscillator_condition(stoch40_condition)},
        {"label": "Stoch 60/1/10", "column": "stoch_d_60_1_10", "level": float(stoch60_level if stoch60_level is not None else default_stoch_level), "condition": normalize_oscillator_condition(stoch60_condition)},
        {"label": "Stoch 300/1/10", "column": "stoch_d_300_1_10", "level": float(stoch300_level if stoch300_level is not None else default_stoch_level), "condition": normalize_oscillator_condition(stoch300_condition)},
        {"label": "RSI(14,14)", "column": "rsi_14_14", "level": float(rsi_level if rsi_level is not None else default_rsi_level), "condition": normalize_oscillator_condition(rsi_condition)},
    ]


def build_oscillator_spec_groups(up_inputs, down_inputs):
    """Build UP-toward and DOWN-toward oscillator specs without reading rendered table HTML."""
    return {
        "up": build_oscillator_specs(*up_inputs, default_stoch_level=87.0, default_rsi_level=70.0),
        "down": build_oscillator_specs(*down_inputs, default_stoch_level=13.0, default_rsi_level=30.0),
    }


def build_stochastic_exit_specs(stoch14_level, stoch14_condition, stoch40_level, stoch40_condition, stoch60_level, stoch60_condition, stoch300_level, stoch300_condition, default_stoch_level):
    """Build normalized stochastic-only exit specs using the same curve style as oscillator entries."""
    return [
        {"label": "Stoch 14/1/3", "column": "stoch_d_14_1_3", "level": float(stoch14_level if stoch14_level is not None else default_stoch_level), "condition": normalize_oscillator_condition(stoch14_condition)},
        {"label": "Stoch 40/1/4", "column": "stoch_d_40_1_4", "level": float(stoch40_level if stoch40_level is not None else default_stoch_level), "condition": normalize_oscillator_condition(stoch40_condition)},
        {"label": "Stoch 60/1/10", "column": "stoch_d_60_1_10", "level": float(stoch60_level if stoch60_level is not None else default_stoch_level), "condition": normalize_oscillator_condition(stoch60_condition)},
        {"label": "Stoch 300/1/10", "column": "stoch_d_300_1_10", "level": float(stoch300_level if stoch300_level is not None else default_stoch_level), "condition": normalize_oscillator_condition(stoch300_condition)},
    ]


def build_stochastic_exit_spec_groups(enabled_values, sell_inputs, buy_inputs):
    """Build optional stochastic close specs for SELL and BUY oscillator-reversal positions."""
    enabled = bool(enabled_values and "enabled" in enabled_values)
    if not enabled:
        return None
    groups = {
        "sell": build_stochastic_exit_specs(*sell_inputs, default_stoch_level=13.0),
        "buy": build_stochastic_exit_specs(*buy_inputs, default_stoch_level=87.0),
    }
    has_active_condition = any(spec["condition"] != "disabled" for specs in groups.values() for spec in specs)
    return groups if has_active_condition else None


def select_exit_specs_for_path(path, exit_specs):
    if not exit_specs or not path:
        return []
    return exit_specs.get(path.get("direction"), []) if isinstance(exit_specs, dict) else (exit_specs or [])


def select_oscillator_specs_for_source(source, oscillator_specs):
    """Select oscillator group by reliable task/source direction: resistance=up, support=down."""
    if isinstance(oscillator_specs, dict):
        group_key = source.get("toward_direction", "up") if source else "up"
        return oscillator_specs.get(group_key) or oscillator_specs.get("up") or []
    return oscillator_specs or []


def format_oscillator_specs(specs):
    if isinstance(specs, dict):
        preferred_labels = [("up", "UP-toward"), ("down", "DOWN-toward"), ("sell", "SELL close"), ("buy", "BUY close")]
        parts = [f"{label}: {format_oscillator_specs(specs.get(key, []))}" for key, label in preferred_labels if key in specs]
        extra_parts = [f"{key}: {format_oscillator_specs(value)}" for key, value in specs.items() if key not in {item[0] for item in preferred_labels}]
        return " | ".join(parts + extra_parts) if parts or extra_parts else "all oscillator filters disabled"
    parts = []
    for spec in specs:
        if spec["condition"] == "disabled":
            continue
        parts.append(f"{spec['label']} {spec['condition'].replace('_', ' ')} {spec['level']:g}")
    return "; ".join(parts) if parts else "all oscillator filters disabled"


def make_oscillator_reversal_source_cache_key(task):
    """Return a stable cache key for oscillator source data derived from one task snapshot."""
    return (
        "osc_source_v3_stoch_d_only",
        getattr(task, "task_id", None),
        getattr(task, "signal_time", None),
        getattr(task, "signal_price", None),
        getattr(task, "signal_direction", None),
        getattr(task, "start_date", None),
        getattr(task, "end_date", None),
        getattr(task, "pre_buffer_minutes", None),
        getattr(task, "status", None),
    )


def build_oscillator_reversal_source_uncached(task):
    """Preload candles and chart-matching oscillator lines for level-cross oscillator reversal diagnostics."""
    if not is_task_eligible_for_dynamic_checkup(task):
        return None
    if task is None or getattr(task, "signal_time", None) is None or getattr(task, "signal_price", None) is None:
        return None
    if getattr(task, "signal_direction", None) not in ("resistance", "support"):
        return None

    # Read only this task's needed candle window.  The generic task-data helper
    # caches a complete pair/timeframe parquet file, which made a first dynamic
    # stochastic checkup slow on older SSDs even when the task uses a short
    # period.  This mtime-aware predicate read shares the bounded chart cache.
    history_start_ms = task_pre_signal_start_ms(task)
    fp = os.path.join(symbol_timeframe_path(task.symbols[0], task.timeframe), "data.parquet")
    if not os.path.exists(fp):
        return None
    if task.end_date:
        history_end_ms = int(task.end_date.replace(tzinfo=timezone.utc).timestamp() * 1000)
    else:
        history_end_ms = get_chart_file_end_timestamp(fp)
    if history_end_ms is None or history_end_ms < history_start_ms:
        return None
    df = read_chart_parquet_cached(fp, history_start_ms, history_end_ms).copy()
    required = {"timestamp", "high", "low", "close"}
    if df.empty or not required.issubset(df.columns):
        return None
    # Preserve the inclusive boundary defensively even though the parquet read
    # already uses the same predicates.
    df = df[(df["timestamp"] >= history_start_ms) & (df["timestamp"] <= history_end_ms)]
    if df.empty:
        return None

    signal_price = float(task.signal_price)
    if signal_price <= 0:
        return None

    df_sorted = df.sort_values("timestamp").reset_index(drop=True).copy()
    for col in ["high", "low", "close"]:
        df_sorted[col] = pd.to_numeric(df_sorted[col], errors="coerce")
    df_sorted["stoch_k_14_1_3"], df_sorted["stoch_d_14_1_3"] = compute_dynamic_stochastic_series(df_sorted["high"], df_sorted["low"], df_sorted["close"], 14, 1, 3)
    df_sorted["stoch_k_40_1_4"], df_sorted["stoch_d_40_1_4"] = compute_dynamic_stochastic_series(df_sorted["high"], df_sorted["low"], df_sorted["close"], 40, 1, 4)
    df_sorted["stoch_k_60_1_10"], df_sorted["stoch_d_60_1_10"] = compute_dynamic_stochastic_series(df_sorted["high"], df_sorted["low"], df_sorted["close"], 60, 1, 10)
    # Keep calculation parameters aligned with the public column/UI name:
    # Stoch 300/1/10 means %K length 300, %D length 1, smoothing 10.
    df_sorted["stoch_k_300_1_10"], df_sorted["stoch_d_300_1_10"] = compute_dynamic_stochastic_series(df_sorted["high"], df_sorted["low"], df_sorted["close"], 300, 1, 10)
    df_sorted["rsi_14_14"] = compute_dynamic_rsi_series(df_sorted["close"], 14).rolling(window=14, min_periods=1).mean()

    search_idx = df_sorted["timestamp"].searchsorted(float(task.signal_time), side="right")
    if search_idx >= len(df_sorted):
        return None
    path_df = df_sorted.iloc[search_idx:].reset_index(drop=True)
    if path_df.empty:
        return None

    oscillator_columns = [
        "stoch_d_14_1_3", "stoch_d_40_1_4", "stoch_d_60_1_10",
        "stoch_d_300_1_10", "rsi_14_14",
    ]
    return {
        "task_id": str(getattr(task, "task_id", "")),
        "level_kind": task.signal_direction,
        "toward_direction": "up" if task.signal_direction == "resistance" else "down",
        "direction": "sell" if task.signal_direction == "resistance" else "buy",
        "signal_price": signal_price,
        "df": path_df,
        "oscillator_values": {
            column: path_df[column].to_numpy(dtype=float, copy=False)
            for column in oscillator_columns
        },
    }


def _oscillator_source_bytes(source):
    if not source or not isinstance(source, dict):
        return 0
    return _chart_dataframe_bytes(source.get("df"))

def build_oscillator_reversal_source(task):
    """Return a bounded cached oscillator source for fast repeated checkup runs."""
    global oscillator_reversal_source_cache_bytes
    cache_key = make_oscillator_reversal_source_cache_key(task)
    if cache_key in oscillator_reversal_source_cache:
        oscillator_reversal_source_cache.move_to_end(cache_key)
        return oscillator_reversal_source_cache[cache_key]
    source = build_oscillator_reversal_source_uncached(task)
    source_bytes = _oscillator_source_bytes(source)
    # Return a large source to this calculation, but do not retain it across
    # runs on a low-memory machine.
    if source_bytes <= OSCILLATOR_REVERSAL_SOURCE_CACHE_MAX_BYTES:
        oscillator_reversal_source_cache[cache_key] = source
        oscillator_reversal_source_cache_bytes += source_bytes
        oscillator_reversal_source_cache.move_to_end(cache_key)
        while (len(oscillator_reversal_source_cache) > OSCILLATOR_REVERSAL_SOURCE_CACHE_MAX or
               oscillator_reversal_source_cache_bytes > OSCILLATOR_REVERSAL_SOURCE_CACHE_MAX_BYTES):
            _, evicted_source = oscillator_reversal_source_cache.popitem(last=False)
            oscillator_reversal_source_cache_bytes -= _oscillator_source_bytes(evicted_source)
    return source


def build_oscillator_reversal_path_from_source(source, oscillator_specs, entry_condition_window=1):
    """Build a reversal path after level cross and oscillator confirmation."""
    if not source:
        return None
    df = source["df"]
    signal_price = float(source["signal_price"])
    if source["level_kind"] == "resistance":
        level_cross_mask = df["high"].to_numpy(dtype=float) >= signal_price
    else:
        level_cross_mask = df["low"].to_numpy(dtype=float) <= signal_price
    cross_positions = np.flatnonzero(level_cross_mask)
    if len(cross_positions) == 0:
        return None
    cross_idx = int(cross_positions[0])

    selected_specs = select_oscillator_specs_for_source(source, oscillator_specs)
    oscillator_idx = None
    for idx in range(cross_idx, len(df)):
        if oscillator_specs_met_within_window(source["oscillator_values"], selected_specs, idx, entry_condition_window, min_idx=cross_idx):
            oscillator_idx = idx
            break
    if oscillator_idx is None:
        return None

    entry_price = float(df.iloc[oscillator_idx]["close"])
    if entry_price <= 0:
        return None
    # The oscillator signal is only known after this candle closes, so the
    # simulated trade enters at that close and begins exit/SL scanning on the
    # next candle.  This avoids using the signal candle's high/low after-the-fact.
    path_df = df.iloc[oscillator_idx + 1:]
    if path_df.empty:
        return None
    return {
        "direction": source["direction"],
        "entry_price": entry_price,
        "signal_price": signal_price,
        "task_id": source.get("task_id"),
        "entry_time": float(df.iloc[oscillator_idx]["timestamp"]),
        "highs": path_df["high"].to_numpy(dtype=float, copy=False),
        "lows": path_df["low"].to_numpy(dtype=float, copy=False),
        "closes": path_df["close"].to_numpy(dtype=float, copy=False),
        "timestamps": path_df["timestamp"].to_numpy(dtype=float, copy=False),
        "stoch_d_14_1_3": path_df["stoch_d_14_1_3"].to_numpy(dtype=float, copy=False),
        "stoch_d_40_1_4": path_df["stoch_d_40_1_4"].to_numpy(dtype=float, copy=False),
        "stoch_d_60_1_10": path_df["stoch_d_60_1_10"].to_numpy(dtype=float, copy=False),
        "stoch_d_300_1_10": path_df["stoch_d_300_1_10"].to_numpy(dtype=float, copy=False),
        "entry_level_distance_pct": abs(entry_price - signal_price) / entry_price * 100,
        "level_cross_idx": cross_idx,
        "oscillator_idx": oscillator_idx,
        "entry_execution": "signal_candle_close_next_candle_path",
        "toward_direction": source.get("toward_direction"),
        "entry_conditions": format_oscillator_specs(selected_specs),
        "entry_condition_window": int(entry_condition_window or 1),
    }


def bucket_stochastic_exit_return(return_pct):
    """Bucket realized stochastic-close return for diagnostic summary rows."""
    if return_pct is None:
        return None
    value = float(return_pct)
    if value < 0:
        return "Loss <0%"
    if value < 0.5:
        return "Profit 0-0.5%"
    if value < 1:
        return "Profit 0.5-1%"
    if value < 2:
        return "Profit 1-2%"
    if value < 3:
        return "Profit 2-3%"
    if value < 4:
        return "Profit 3-4%"
    return "Profit 4%+"


def build_chart_event_record(path, result, category, label, oscillator_exit_specs=None):
    """Build a chart navigation event for oscillator research result rows."""
    if not path or not result or not path.get("task_id"):
        return None
    exit_idx = result.get("exit_idx")
    exit_price = result.get("exit_price")
    if str(category).startswith("tp_"):
        try:
            tp_level = float(str(category)[3:])
            exit_idx = result.get("tp_hit_indices", {}).get(tp_level, exit_idx)
            if exit_price is None:
                direction = path.get("direction")
                entry_price = float(path.get("entry_price"))
                exit_price = entry_price * (1 + tp_level / 100) if direction == "buy" else entry_price * (1 - tp_level / 100)
        except Exception:
            pass
    timestamps = path.get("timestamps")
    exit_time = None
    if exit_idx is not None and timestamps is not None and 0 <= int(exit_idx) < len(timestamps):
        exit_time = float(timestamps[int(exit_idx)])
    exit_reason = result.get("exit_reason")
    if exit_reason == "oscillator_close":
        exit_conditions = format_oscillator_specs(select_exit_oscillator_specs(path, oscillator_exit_specs))
    elif exit_reason == "stop":
        stop_return = result.get("stop_return_pct")
        try:
            exit_conditions = ("Original stop loss" if result.get("initial_stop_hit")
                               else f"Moved/trailing stop locked at {float(stop_return):+.2f}%")
        except (TypeError, ValueError):
            exit_conditions = "Original or moved stop loss"
    elif exit_reason == "max_adverse_dd":
        exit_conditions = "Maximum adverse drawdown cap reached"
    else:
        exit_conditions = "No completed exit / checkpoint only"
    return {
        "task_id": path.get("task_id"),
        "category": category,
        "label": label,
        "direction": path.get("direction"),
        "entry_time": path.get("entry_time"),
        "entry_price": path.get("entry_price"),
        "exit_time": exit_time,
        "exit_price": exit_price,
        "entry_conditions": path.get("entry_conditions"),
        "entry_condition_window": path.get("entry_condition_window"),
        "entry_execution": path.get("entry_execution"),
        "entry_level_distance_pct": path.get("entry_level_distance_pct"),
        "exit_reason": exit_reason,
        "exit_conditions": exit_conditions,
        "stop_return_pct": result.get("stop_return_pct"),
        "return_pct": result.get("exit_return_pct"),
    }


def chart_event_button(label, category, count):
    """Render summary controls that open a selected event number from a result group."""
    disabled = not bool(count)
    return html.Span([
        html.Span(f"Total: {count}", style={"marginRight": "6px", "fontSize": "11px", "color": "#555"}),
        html.Label("#", style={"fontSize": "11px", "marginRight": "2px"}),
        dcc.Input(
            id={"type": "osc-event-index", "category": category},
            type="number",
            value=1 if count else None,
            min=1,
            max=max(int(count or 0), 1),
            step=1,
            disabled=disabled,
            style={"width": "58px", "fontSize": "11px", "marginRight": "4px"},
        ),
        html.Button(
            f"📈 {label}",
            id={"type": "osc-event-chart", "category": category},
            n_clicks=0,
            disabled=disabled,
            title="Enter an event number, then open that exact chart. Use ‹/› to move through this result group.",
            style={"fontSize": "11px", "padding": "2px 6px", "cursor": "pointer" if not disabled else "not-allowed"},
        ),
    ], style={"display": "inline-flex", "alignItems": "center", "gap": "2px", "flexWrap": "nowrap"})


def build_oscillator_reversal_summary_table(tasks, oscillator_specs, stop_loss_pct, max_dd_pct, tp_levels, stop_rules, sl_grid=None, notional_usd=1000, round_trip_cost_pct=0.0, open_return_pct=0.0, oscillator_exit_specs=None, entry_condition_window=1, oscillator_exit_window=1, return_event_groups=False):
    """Build a read-only diagnostic table for oscillator-confirmed reversal entries."""
    td_style = {"padding": "4px 8px", "border": "1px solid #ddd"}
    notional_usd, round_trip_cost_pct, open_return_pct = normalize_expectancy_inputs(notional_usd, round_trip_cost_pct, open_return_pct)
    total_tasks = len(tasks)
    eligible_tasks = [t for t in tasks if is_task_eligible_for_dynamic_checkup(t)]
    sources = [build_oscillator_reversal_source(t) for t in eligible_tasks]
    sources = [s for s in sources if s]
    level_cross_count = 0
    paths = []
    for source in sources:
        signal_price = float(source["signal_price"])
        df = source["df"]
        if source["level_kind"] == "resistance":
            crossed = bool((df["high"].to_numpy(dtype=float) >= signal_price).any())
        else:
            crossed = bool((df["low"].to_numpy(dtype=float) <= signal_price).any())
        if crossed:
            level_cross_count += 1
        path = build_oscillator_reversal_path_from_source(source, oscillator_specs, entry_condition_window=entry_condition_window)
        if path:
            paths.append(path)
    results = [evaluate_dynamic_checkup_path(p, stop_loss_pct, max_dd_pct, tp_levels, stop_rules, oscillator_exit_specs=oscillator_exit_specs, oscillator_exit_window=oscillator_exit_window) for p in paths]
    valid_results = [r for r in results if r["valid"]]
    valid_total = len(valid_results)
    event_groups = {"original_sl": [], "stochastic_close": []}
    stop_execution_levels = {}
    for level in tp_levels:
        event_groups[f"tp_{level:g}"] = []
    for path, result in zip(paths, results):
        if not result or not result.get("valid"):
            continue
        if result.get("initial_stop_hit"):
            event = build_chart_event_record(path, result, "original_sl", "Original SL exit", oscillator_exit_specs)
            if event:
                event_groups["original_sl"].append(event)
        if result.get("stop_hit") and result.get("stop_return_pct") is not None:
            stop_return_pct = float(result.get("stop_return_pct") or 0.0)
            stop_key_value = f"{stop_return_pct:g}".replace("-", "minus_").replace(".", "p")
            stop_category = f"stop_exec_{stop_key_value}"
            stop_label = ("Original SL" if result.get("initial_stop_hit") else "Moved stop") + f" executed at {stop_return_pct:g}% return"
            stop_execution_levels[stop_category] = stop_return_pct
            event = build_chart_event_record(path, result, stop_category, stop_label, oscillator_exit_specs)
            if event:
                event_groups.setdefault(stop_category, []).append(event)
        if result.get("oscillator_exit_hit"):
            event = build_chart_event_record(path, result, "stochastic_close", "Stochastic close", oscillator_exit_specs)
            if event:
                event_groups["stochastic_close"].append(event)
                bucket = bucket_stochastic_exit_return(result.get("exit_return_pct"))
                if bucket:
                    event_groups.setdefault(f"stoch_bucket_{bucket}", []).append(dict(event, category=f"stoch_bucket_{bucket}", label=bucket))
        for level in tp_levels:
            if level in result.get("tp_hits", set()):
                event = build_chart_event_record(path, result, f"tp_{level:g}", f"TP {fmt_dynamic_level_label(level)} checkpoint", oscillator_exit_specs)
                if event:
                    event_groups[f"tp_{level:g}"].append(event)

    def fmt_stat(count, total):
        return f"{count} / {total} ({count / total * 100:.1f}%)" if total else "0 / 0"

    def scenario_summary(label, scenario_results):
        scenario_total = len(scenario_results)
        original_sl_events = sum(1 for r in scenario_results if r.get("initial_stop_hit"))
        moved_stop_events = sum(1 for r in scenario_results if r.get("moved_stop_hit"))
        max_dd_events = sum(1 for r in scenario_results if r["max_dd_hit"])
        tp05 = sum(1 for r in scenario_results if any(level >= 0.5 for level in r["tp_hits"]))
        tp1 = sum(1 for r in scenario_results if any(level >= 1.0 for level in r["tp_hits"]))
        stop_moved = sum(1 for r in scenario_results if r["stop_moves"])
        oscillator_exits = sum(1 for r in scenario_results if r.get("oscillator_exit_hit"))
        scenario_net = [get_diagnostic_net_return_pct(r, round_trip_cost_pct, open_return_pct) for r in scenario_results]
        scenario_net = [r for r in scenario_net if r is not None]
        avg_net = sum(scenario_net) / scenario_total if scenario_total else 0.0
        total_net_usd = sum(scenario_net) / 100 * notional_usd
        return html.Tr([html.Td(label, style=td_style), html.Td(
            f"entries {fmt_stat(scenario_total, len(eligible_tasks))} | TP0.5 {fmt_stat(tp05, scenario_total)} | TP1 {fmt_stat(tp1, scenario_total)} | "
            f"original SL exit {fmt_stat(original_sl_events, scenario_total)} | moved-stop exit {fmt_stat(moved_stop_events, scenario_total)} | adverse DD cap {fmt_stat(max_dd_events, scenario_total)} | "
            f"stop armed {fmt_stat(stop_moved, scenario_total)} | stochastic close {fmt_stat(oscillator_exits, scenario_total)} | avg net {avg_net:.3f}% | net P/L ${total_net_usd:,.2f}",
            style=td_style)])

    stop_events = sum(1 for r in valid_results if r["stop_hit"])
    original_sl_events = sum(1 for r in valid_results if r.get("initial_stop_hit"))
    moved_stop_events = sum(1 for r in valid_results if r.get("moved_stop_hit"))
    max_dd_events = sum(1 for r in valid_results if r["max_dd_hit"])
    stop_after_tp = sum(1 for r in valid_results if r["stop_after_tp"])
    stop_moved = sum(1 for r in valid_results if r["stop_moves"])
    oscillator_exit_count = sum(1 for r in valid_results if r.get("oscillator_exit_hit"))
    up_sources = [s for s in sources if s.get("toward_direction") == "up"]
    down_sources = [s for s in sources if s.get("toward_direction") == "down"]
    up_paths = [p for p in paths if p.get("toward_direction") == "up"]
    down_paths = [p for p in paths if p.get("toward_direction") == "down"]
    stochastic_exit_bucket_order = ["Loss <0%", "Profit 0-0.5%", "Profit 0.5-1%", "Profit 1-2%", "Profit 2-3%", "Profit 3-4%", "Profit 4%+"]
    stochastic_exit_buckets = {label: 0 for label in stochastic_exit_bucket_order}
    for result in valid_results:
        if result.get("oscillator_exit_hit"):
            bucket = bucket_stochastic_exit_return(result.get("exit_return_pct"))
            if bucket:
                stochastic_exit_buckets[bucket] += 1
    actual_tp_executions = 0
    rows = [
        html.Tr([html.Td("All tasks in snapshot", style=td_style), html.Td(str(total_tasks), style=td_style)]),
        html.Tr([html.Td("Completed tasks considered", style=td_style), html.Td(fmt_stat(len(eligible_tasks), total_tasks), style=td_style)]),
        html.Tr([html.Td("Usable oscillator paths with candle data", style=td_style), html.Td(fmt_stat(len(sources), len(eligible_tasks)), style=td_style)]),
        html.Tr([html.Td("UP-toward sources (resistance → SELL)", style=td_style), html.Td(fmt_stat(len(up_sources), len(sources)), style=td_style)]),
        html.Tr([html.Td("DOWN-toward sources (support → BUY)", style=td_style), html.Td(fmt_stat(len(down_sources), len(sources)), style=td_style)]),
        html.Tr([html.Td("Price crossed signal level", style=td_style), html.Td(fmt_stat(level_cross_count, len(eligible_tasks)), style=td_style)]),
        html.Tr([html.Td("Oscillator reversal entries triggered", style=td_style), html.Td(fmt_stat(valid_total, len(eligible_tasks)), style=td_style)]),
        html.Tr([html.Td("UP-toward oscillator entries", style=td_style), html.Td(fmt_stat(len(up_paths), len(up_sources)), style=td_style)]),
        html.Tr([html.Td("DOWN-toward oscillator entries", style=td_style), html.Td(fmt_stat(len(down_paths), len(down_sources)), style=td_style)]),
        html.Tr([html.Td("Level crossed but oscillator did not trigger", style=td_style), html.Td(fmt_stat(max(level_cross_count - valid_total, 0), len(eligible_tasks)), style=td_style)]),
        html.Tr([html.Td("Active entry oscillator filters", style=td_style), html.Td(format_oscillator_specs(oscillator_specs), style=td_style)]),
        html.Tr([html.Td("Active stochastic close filters", style=td_style), html.Td(format_oscillator_specs(oscillator_exit_specs) if oscillator_exit_specs else "disabled", style=td_style)]),
        html.Tr([html.Td("Condition windows", style=td_style), html.Td(f"entry={int(entry_condition_window or 1)} candle(s), close={int(oscillator_exit_window or 1)} candle(s)", style=td_style)]),
        html.Tr([html.Td(f"Original SL exits (menu SL {float(stop_loss_pct or 0):g}%)", style=td_style), html.Td([fmt_stat(original_sl_events, valid_total), " ", chart_event_button("Chart original SL exits", "original_sl", original_sl_events)], style=td_style)]),
        html.Tr([html.Td("Moved/trailing stop exits", style=td_style), html.Td(fmt_stat(moved_stop_events, valid_total), style=td_style)]),
        html.Tr([html.Td("Any stop exit (original + moved)", style=td_style), html.Td(fmt_stat(stop_events, valid_total), style=td_style)]),
        html.Tr([html.Td("Max adverse DD cap exits", style=td_style), html.Td(fmt_stat(max_dd_events, valid_total), style=td_style)]),
        html.Tr([html.Td("Stop exit after at least one TP checkpoint", style=td_style), html.Td(fmt_stat(stop_after_tp, valid_total), style=td_style)]),
        html.Tr([html.Td("Dynamic stop armed/moved at least once", style=td_style), html.Td(fmt_stat(stop_moved, valid_total), style=td_style)]),
        html.Tr([html.Td("Actual TP orders executed", style=td_style), html.Td(f"{actual_tp_executions} / {valid_total} (TP levels are checkpoints only in this diagnostic)", style=td_style)]),
        html.Tr([html.Td("Actual stochastic close exits", style=td_style), html.Td([fmt_stat(oscillator_exit_count, valid_total), " ", chart_event_button("Chart stochastic exits", "stochastic_close", oscillator_exit_count)], style=td_style)]),
        html.Tr([html.Td("Open/no actual exit fallback", style=td_style), html.Td(fmt_stat(sum(1 for r in valid_results if r.get("exit_return_pct") is None), valid_total), style=td_style)]),
    ]
    if stop_execution_levels:
        rows.append(html.Tr([html.Td("— Actual stop-loss orders executed by stop level —", style=td_style), html.Td("These are real simulated stop exits, grouped by the stop price/return that actually closed the order", style=td_style)]))
        for stop_category, stop_return_pct in sorted(stop_execution_levels.items(), key=lambda item: item[1]):
            count = len(event_groups.get(stop_category, []))
            stop_name = "Original SL" if stop_return_pct < 0 else "Moved/dynamic stop"
            rows.append(html.Tr([
                html.Td(f"{stop_name} executed at {stop_return_pct:g}% return", style=td_style),
                html.Td([fmt_stat(count, valid_total), " ", chart_event_button(f"Chart stop {stop_return_pct:g}%", stop_category, count)], style=td_style),
            ]))
    rows.extend(build_expectancy_summary_rows(valid_results, notional_usd, round_trip_cost_pct, open_return_pct, td_style, label_prefix="Oscillator reversal scenario"))
    if oscillator_exit_specs:
        rows.append(html.Tr([html.Td("— Stochastic close realized-return spread —", style=td_style), html.Td("Only trades actually closed by stochastic conditions", style=td_style)]))
        for bucket_label in stochastic_exit_bucket_order:
            rows.append(html.Tr([html.Td(bucket_label, style=td_style), html.Td([fmt_stat(stochastic_exit_buckets[bucket_label], oscillator_exit_count), " ", chart_event_button("Chart " + bucket_label, "stoch_bucket_" + bucket_label, stochastic_exit_buckets[bucket_label])], style=td_style)]))
    rows.append(html.Tr([html.Td("— TP checkpoint hits (not actual TP orders) —", style=td_style), html.Td("These count favorable price moves reached before the actual exit", style=td_style)]))
    for level in tp_levels:
        label = fmt_dynamic_level_label(level)
        tp_found = sum(1 for r in valid_results if level in r["tp_hits"])
        rows.append(html.Tr([html.Td(f"TP {label} found after oscillator entry", style=td_style), html.Td([fmt_stat(tp_found, valid_total), " ", chart_event_button("Chart TP " + label, f"tp_{level:g}", tp_found)], style=td_style)]))
    for trigger_pct, stop_profit_pct in stop_rules:
        moved = sum(1 for r in valid_results if trigger_pct in r["stop_moves"])
        rows.append(html.Tr([html.Td(f"Dynamic stop armed: after +{fmt_dynamic_level_label(trigger_pct)} move stop to {stop_profit_pct:g}% return", style=td_style), html.Td(fmt_stat(moved, valid_total), style=td_style)]))
    sl_grid = sl_grid or []
    if sl_grid:
        rows.append(html.Tr([html.Td("— Original SL grid scenarios —", style=td_style), html.Td("Each row reruns the same entries/exits with a different original stop-loss distance", style=td_style)]))
        for sl_pct in sl_grid:
            scenario_results = [evaluate_dynamic_checkup_path(p, sl_pct, max_dd_pct, tp_levels, stop_rules, oscillator_exit_specs=oscillator_exit_specs, oscillator_exit_window=oscillator_exit_window) for p in paths]
            rows.append(scenario_summary(f"Original SL set to {fmt_dynamic_level_label(sl_pct)}", scenario_results))
    table = html.Table(rows, style={"borderCollapse": "collapse", "width": "100%", "fontSize": "13px"})
    return (table, event_groups) if return_event_groups else table


def parse_research_stop_rule_presets(text):
    """Parse research stop-rule preset rows separated by |."""
    if text is None or str(text).strip() == "":
        return [parse_dynamic_stop_rules("1:0.35, 1.5:0.75, 2:1, 3:2, 4:3")]
    presets = []
    for raw_preset in str(text).split("|"):
        preset_text = raw_preset.strip()
        if preset_text:
            presets.append(parse_dynamic_stop_rules(preset_text))
    return presets or [[]]


def clone_oscillator_specs_with_level_shift(specs, group_kind, level_shift):
    """Clone specs and relax/stricten thresholds based on high/low group direction."""
    cloned = []
    high_extreme_group = group_kind in ("up", "buy")
    for spec in specs or []:
        new_spec = dict(spec)
        condition = normalize_oscillator_condition(new_spec.get("condition"))
        if condition != "disabled":
            level = float(new_spec.get("level", 0.0))
            # Positive level_shift means stricter. High-extreme groups need higher
            # levels to be stricter; low-extreme groups need lower levels.
            adjusted = level + level_shift if high_extreme_group else level - level_shift
            new_spec["level"] = min(100.0, max(0.0, adjusted))
        cloned.append(new_spec)
    return cloned


def build_oscillator_research_variants(oscillator_specs, oscillator_exit_specs):
    """Build Base/Relaxed/Strict condition variants for research ranking."""
    variant_defs = [
        ("Base levels", 0.0),
        ("Relaxed levels", -5.0),
        ("Strict levels", 3.0),
    ]
    variants = []
    for label, shift in variant_defs:
        entry_variant = None
        if isinstance(oscillator_specs, dict):
            entry_variant = {
                key: clone_oscillator_specs_with_level_shift(value, key, shift)
                for key, value in oscillator_specs.items()
            }
        else:
            entry_variant = clone_oscillator_specs_with_level_shift(oscillator_specs, "up", shift)
        exit_variant = None
        if oscillator_exit_specs:
            exit_variant = {
                key: clone_oscillator_specs_with_level_shift(value, key, shift)
                for key, value in oscillator_exit_specs.items()
            }
        variants.append({"label": label, "entry_specs": entry_variant, "exit_specs": exit_variant})
    return variants


def summarize_research_result(label, entry_window, exit_window, stop_loss_pct, stop_rules, paths, results, eligible_total, notional_usd, round_trip_cost_pct, open_return_pct):
    """Summarize one oscillator research combination into sortable metrics."""
    valid_results = [r for r in results if r and r.get("valid")]
    total = len(valid_results)
    net_returns = [get_diagnostic_net_return_pct(r, round_trip_cost_pct, open_return_pct) for r in valid_results]
    net_returns = [r for r in net_returns if r is not None]
    gross_returns = [float(r.get("exit_return_pct") if r.get("exit_return_pct") is not None else open_return_pct) for r in valid_results]
    avg_net = sum(net_returns) / total if total else -999.0
    total_net_usd = sum(net_returns) / 100 * notional_usd
    gross_profit_pct = sum(r for r in gross_returns if r > 0)
    gross_loss_pct = abs(sum(r for r in gross_returns if r < 0))
    profit_factor = float("inf") if gross_loss_pct == 0 and gross_profit_pct > 0 else (gross_profit_pct / gross_loss_pct if gross_loss_pct else 0.0)
    stochastic_exits = [r for r in valid_results if r.get("oscillator_exit_hit")]
    stop_events = sum(1 for r in valid_results if r.get("stop_hit"))
    original_sl_events = sum(1 for r in valid_results if r.get("initial_stop_hit"))
    moved_stop_events = sum(1 for r in valid_results if r.get("moved_stop_hit"))
    tp1 = sum(1 for r in valid_results if any(level >= 1.0 for level in r.get("tp_hits", set())))
    tp2 = sum(1 for r in valid_results if any(level >= 2.0 for level in r.get("tp_hits", set())))
    winners = sum(1 for r in net_returns if r > 0)
    losers = sum(1 for r in net_returns if r < 0)
    success_rate = winners / total * 100 if total else 0.0
    stochastic_wins = sum(1 for r in stochastic_exits if get_diagnostic_net_return_pct(r, round_trip_cost_pct, open_return_pct) and get_diagnostic_net_return_pct(r, round_trip_cost_pct, open_return_pct) > 0)
    stochastic_success_rate = stochastic_wins / len(stochastic_exits) * 100 if stochastic_exits else 0.0
    original_sl_rate = original_sl_events / total * 100 if total else 0.0
    tp1_rate = tp1 / total * 100 if total else 0.0
    tp2_rate = tp2 / total * 100 if total else 0.0
    bucket_order = ["Loss <0%", "Profit 0-0.5%", "Profit 0.5-1%", "Profit 1-2%", "Profit 2-3%", "Profit 3-4%", "Profit 4%+"]
    buckets = {bucket: 0 for bucket in bucket_order}
    for result in stochastic_exits:
        bucket = bucket_stochastic_exit_return(result.get("exit_return_pct"))
        if bucket:
            buckets[bucket] += 1
    advice = []
    if total < max(30, eligible_total * 0.03):
        advice.append("too few entries")
    if profit_factor < 1:
        advice.append("PF<1 before costs")
    if total and original_sl_events / total > 0.35:
        advice.append("original SL hit rate high")
    if total and len(stochastic_exits) / total < 0.20:
        advice.append("few stochastic exits")
    if total and success_rate < 45:
        advice.append("low win rate")
    if avg_net > 0 and profit_factor >= 1.1 and success_rate >= 45:
        advice.append("candidate for validation")
    return {
        "label": label,
        "entry_window": entry_window,
        "exit_window": exit_window,
        "stop_loss_pct": stop_loss_pct,
        "stop_rules": stop_rules,
        "entries": total,
        "eligible_total": eligible_total,
        "avg_net": avg_net,
        "total_net_usd": total_net_usd,
        "profit_factor": profit_factor,
        "winners": winners,
        "losers": losers,
        "success_rate": success_rate,
        "stochastic_success_rate": stochastic_success_rate,
        "original_sl_rate": original_sl_rate,
        "tp1_rate": tp1_rate,
        "tp2_rate": tp2_rate,
        "stop_events": stop_events,
        "original_sl_events": original_sl_events,
        "moved_stop_events": moved_stop_events,
        "stochastic_exit_count": len(stochastic_exits),
        "tp1": tp1,
        "tp2": tp2,
        "buckets": buckets,
        "advice": "; ".join(advice) if advice else "neutral / compare out-of-sample",
    }


def build_oscillator_research_optimizer_table(tasks, oscillator_specs, oscillator_exit_specs, entry_windows, exit_windows, sl_grid, stop_rule_presets, notional_usd, round_trip_cost_pct, open_return_pct, max_combos=120, top_n=20):
    """Rank oscillator condition/window/SL/stop-rule combinations for research."""
    td_style = {"padding": "4px 8px", "border": "1px solid #ddd", "verticalAlign": "top"}
    notional_usd, round_trip_cost_pct, open_return_pct = normalize_expectancy_inputs(notional_usd, round_trip_cost_pct, open_return_pct)
    eligible_tasks = [t for t in tasks if is_task_eligible_for_dynamic_checkup(t)]
    sources = [build_oscillator_reversal_source(t) for t in eligible_tasks]
    sources = [s for s in sources if s]
    variants = build_oscillator_research_variants(oscillator_specs, oscillator_exit_specs)
    combos = []
    for variant in variants:
        for entry_window in entry_windows:
            for exit_window in exit_windows:
                paths = [build_oscillator_reversal_path_from_source(source, variant["entry_specs"], entry_condition_window=entry_window) for source in sources]
                paths = [p for p in paths if p]
                for stop_loss_pct in sl_grid:
                    for preset_idx, stop_rules in enumerate(stop_rule_presets, start=1):
                        combos.append((variant, entry_window, exit_window, paths, stop_loss_pct, preset_idx, stop_rules))
                        if len(combos) >= int(max_combos or 120):
                            break
                    if len(combos) >= int(max_combos or 120):
                        break
                if len(combos) >= int(max_combos or 120):
                    break
            if len(combos) >= int(max_combos or 120):
                break
        if len(combos) >= int(max_combos or 120):
            break
    summaries = []
    for variant, entry_window, exit_window, paths, stop_loss_pct, preset_idx, stop_rules in combos:
        results = [evaluate_dynamic_checkup_path(p, stop_loss_pct, None, (0.7, 1.0, 2.0, 3.0, 4.0), stop_rules, oscillator_exit_specs=variant["exit_specs"], oscillator_exit_window=exit_window) for p in paths]
        label = f"{variant['label']} | Stop preset {preset_idx}"
        summaries.append(summarize_research_result(label, entry_window, exit_window, stop_loss_pct, stop_rules, paths, results, len(eligible_tasks), notional_usd, round_trip_cost_pct, open_return_pct))
    summaries.sort(key=lambda item: (item["avg_net"], item["profit_factor"], item["entries"]), reverse=True)
    top_n = max(1, int(top_n or 20))
    top = summaries[:top_n]
    header = html.Tr([html.Th(col, style=td_style) for col in ["Rank", "Variant / risk", "Entries", "Win %", "Avg net", "PF", "Stops", "Stoch exits", "TP success", "Stoch exit spread", "Advice"]])
    rows = [header]
    for rank, item in enumerate(top, start=1):
        pf_text = "∞" if item["profit_factor"] == float("inf") else f"{item['profit_factor']:.2f}"
        bucket_text = " | ".join(f"{k}:{v}" for k, v in item["buckets"].items() if v)
        if not bucket_text:
            bucket_text = "none"
        rows.append(html.Tr([
            html.Td(str(rank), style=td_style),
            html.Td(f"{item['label']} | entry win {item['entry_window']} | close win {item['exit_window']} | SL {item['stop_loss_pct']:g}% | rules {format_dynamic_stop_rules_for_display(item['stop_rules'])}", style=td_style),
            html.Td(f"{item['entries']} / {item['eligible_total']} ({item['entries'] / item['eligible_total'] * 100:.1f}%)" if item['eligible_total'] else "0 / 0", style=td_style),
            html.Td(f"{item['success_rate']:.1f}% ({item['winners']}W/{item['losers']}L)", style=td_style),
            html.Td(f"{item['avg_net']:.3f}% | ${item['total_net_usd']:,.0f}", style=td_style),
            html.Td(pf_text, style=td_style),
            html.Td(f"any {item['stop_events']} | original {item['original_sl_events']} ({item['original_sl_rate']:.1f}%) | moved {item['moved_stop_events']}", style=td_style),
            html.Td(f"{item['stochastic_exit_count']} | win {item['stochastic_success_rate']:.1f}%", style=td_style),
            html.Td(f"TP1 {item['tp1']} ({item['tp1_rate']:.1f}%) | TP2 {item['tp2']} ({item['tp2_rate']:.1f}%)", style=td_style),
            html.Td(bucket_text, style=td_style),
            html.Td(item["advice"], style=td_style),
        ]))
    explanation = html.Div([
        html.P(f"Tested {len(summaries)} combinations across {len(sources)} usable sources. Sorted by average net return after costs, then profit factor.", style={"fontWeight": "bold"}),
        html.P("Use this as research only: pick robust candidates with enough entries, PF above 1, positive average net after costs, acceptable original-SL %, strong win %, and then validate on a separate period.", style={"color": "#555"}),
    ])
    return html.Div([explanation, html.Table(rows, style={"borderCollapse": "collapse", "width": "100%", "fontSize": "12px"})])


def format_dynamic_stop_rules_for_display(stop_rules):
    return ", ".join(f"{trigger:g}:{target:g}" for trigger, target in (stop_rules or [])) or "none"

def build_level_reversal_summary_table(tasks, entry_offset_pct, stop_loss_pct, max_dd_pct, tp_levels, stop_rules, sl_grid=None, offset_grid=None, notional_usd=1000, round_trip_cost_pct=0.0, open_return_pct=0.0):
    """Build a read-only diagnostic table for entering reversal at/after level."""
    td_style = {"padding": "4px 8px", "border": "1px solid #ddd"}
    notional_usd, round_trip_cost_pct, open_return_pct = normalize_expectancy_inputs(notional_usd, round_trip_cost_pct, open_return_pct)
    total_tasks = len(tasks)
    eligible_tasks = [t for t in tasks if is_task_eligible_for_dynamic_checkup(t)]
    sources = [build_level_reversal_source(t) for t in eligible_tasks]
    sources = [s for s in sources if s]
    paths = [build_level_reversal_path_from_source(s, entry_offset_pct) for s in sources]
    valid_paths = [p for p in paths if p]
    results = [evaluate_dynamic_checkup_path(p, stop_loss_pct, max_dd_pct, tp_levels, stop_rules) for p in valid_paths]
    valid_results = [r for r in results if r["valid"]]
    valid_total = len(valid_results)
    def fmt_stat(count, total):
        return f"{count} / {total} ({count / total * 100:.1f}%)" if total else "0 / 0"

    def scenario_summary(label, scenario_paths, scenario_results):
        scenario_total = len(scenario_results)
        stop_events = sum(1 for r in scenario_results if r["stop_hit"])
        max_dd_events = sum(1 for r in scenario_results if r["max_dd_hit"])
        tp05 = sum(1 for r in scenario_results if any(level >= 0.5 for level in r["tp_hits"]))
        tp1 = sum(1 for r in scenario_results if any(level >= 1.0 for level in r["tp_hits"]))
        stop_moved = sum(1 for r in scenario_results if r["stop_moves"])
        avg_net = 0.0
        total_net_usd = 0.0
        if scenario_total:
            scenario_net = [get_diagnostic_net_return_pct(r, round_trip_cost_pct, open_return_pct) for r in scenario_results]
            scenario_net = [r for r in scenario_net if r is not None]
            avg_net = sum(scenario_net) / scenario_total
            total_net_usd = sum(scenario_net) / 100 * notional_usd
        return html.Tr([
            html.Td(label, style=td_style),
            html.Td(
                f"entries {fmt_stat(len(scenario_paths), len(eligible_tasks))} | "
                f"TP0.5 {fmt_stat(tp05, scenario_total)} | "
                f"TP1 {fmt_stat(tp1, scenario_total)} | "
                f"SL {fmt_stat(stop_events, scenario_total)} | "
                f"adverse DD cap {fmt_stat(max_dd_events, scenario_total)} | "
                f"stop moved {fmt_stat(stop_moved, scenario_total)} | "
                f"avg net {avg_net:.3f}% | "
                f"net P/L ${total_net_usd:,.2f}",
                style=td_style,
            ),
        ])

    stop_events = sum(1 for r in valid_results if r["stop_hit"])
    max_dd_events = sum(1 for r in valid_results if r["max_dd_hit"])
    stop_after_tp = sum(1 for r in valid_results if r["stop_after_tp"])
    stop_moved = sum(1 for r in valid_results if r["stop_moves"])
    rows = [
        html.Tr([html.Td("All tasks in snapshot", style=td_style), html.Td(str(total_tasks), style=td_style)]),
        html.Tr([html.Td("Completed tasks considered", style=td_style), html.Td(fmt_stat(len(eligible_tasks), total_tasks), style=td_style)]),
        html.Tr([html.Td("Usable level paths with candle data", style=td_style), html.Td(fmt_stat(len(sources), len(eligible_tasks)), style=td_style)]),
        html.Tr([html.Td("Level/offset entries triggered", style=td_style), html.Td(fmt_stat(valid_total, len(eligible_tasks)), style=td_style)]),
        html.Tr([html.Td("Not triggered / did not reach entry", style=td_style), html.Td(fmt_stat(len(eligible_tasks) - valid_total, len(eligible_tasks)), style=td_style)]),
        html.Tr([html.Td("Initial stop events (closed by SL/trailing stop)", style=td_style), html.Td(fmt_stat(stop_events, valid_total), style=td_style)]),
        html.Tr([html.Td("Max adverse DD cap events", style=td_style), html.Td(fmt_stat(max_dd_events, valid_total), style=td_style)]),
        html.Tr([html.Td("Stop after at least one TP", style=td_style), html.Td(fmt_stat(stop_after_tp, valid_total), style=td_style)]),
        html.Tr([html.Td("Dynamic stop moved", style=td_style), html.Td(fmt_stat(stop_moved, valid_total), style=td_style)]),
    ]

    rows.extend(build_expectancy_summary_rows(valid_results, notional_usd, round_trip_cost_pct, open_return_pct, td_style, label_prefix="Level-reversal scenario"))

    for level in tp_levels:
        label = fmt_dynamic_level_label(level)
        tp_found = sum(1 for r in valid_results if level in r["tp_hits"])
        rows.append(html.Tr([html.Td(f"TP {label} found after reversal entry", style=td_style), html.Td(fmt_stat(tp_found, valid_total), style=td_style)]))

    for trigger_pct, stop_profit_pct in stop_rules:
        moved = sum(1 for r in valid_results if trigger_pct in r["stop_moves"])
        rows.append(html.Tr([
            html.Td(f"Stop moved at {fmt_dynamic_level_label(trigger_pct)} to {stop_profit_pct:g}% profit", style=td_style),
            html.Td(fmt_stat(moved, valid_total), style=td_style),
        ]))

    sl_grid = sl_grid or []
    if sl_grid:
        rows.append(html.Tr([html.Td("— SL grid scenarios —", style=td_style), html.Td("Same entry offset, TP levels, max adverse DD, and dynamic stop rules", style=td_style)]))
        for sl_pct in sl_grid:
            scenario_results = [evaluate_dynamic_checkup_path(p, sl_pct, max_dd_pct, tp_levels, stop_rules) for p in valid_paths]
            rows.append(scenario_summary(f"Initial SL {fmt_dynamic_level_label(sl_pct)}", valid_paths, scenario_results))

    offset_grid = offset_grid or []
    if offset_grid:
        rows.append(html.Tr([html.Td("— Entry offset grid —", style=td_style), html.Td("0% means level touch; higher values require overshoot beyond level before reversal entry", style=td_style)]))
        for offset_pct in offset_grid:
            scenario_paths = [build_level_reversal_path_from_source(s, offset_pct) for s in sources]
            scenario_paths = [p for p in scenario_paths if p]
            scenario_results = [evaluate_dynamic_checkup_path(p, stop_loss_pct, max_dd_pct, tp_levels, stop_rules) for p in scenario_paths]
            rows.append(scenario_summary(f"Entry offset {fmt_dynamic_level_label(offset_pct)}", scenario_paths, scenario_results))

    return html.Table(rows, style={"borderCollapse": "collapse", "width": "100%", "fontSize": "13px"})


@app.callback(
    Output("osc-settings-status", "children"),
    Output("osc-settings-open-dropdown", "options"),
    Output("osc-settings-open-dropdown", "value"),
    Input("osc-settings-save-btn", "n_clicks"),
    State("osc-settings-name-input", "value"),
    *[State(component_id, "value") for component_id in OSCILLATOR_SETTINGS_IDS],
    prevent_initial_call=True,
)
def save_oscillator_strategy_settings(n_clicks, settings_name, *values):
    """Persist oscillator/dynamic stochastic strategy menu values as JSON."""
    safe_name = _safe_strategy_settings_name(settings_name)
    if not safe_name:
        return "❌ Enter a settings name before saving.", strategy_setting_options(), no_update
    path = strategy_setting_path(safe_name)
    payload = {
        "schema_version": 1,
        "strategy": "oscillator_level_reversal",
        "saved_at_utc": datetime.now(timezone.utc).isoformat(),
        "parameters": {component_id: value for component_id, value in zip(OSCILLATOR_SETTINGS_IDS, values)},
    }
    os.makedirs(STRATEGY_SETTINGS_DIR, exist_ok=True)
    with open(path, "w", encoding="utf-8") as f:
        json.dump(payload, f, indent=2, sort_keys=True)
    return f"✅ Saved strategy settings: {safe_name}", strategy_setting_options(), safe_name

@app.callback(
    Output("osc-settings-status", "children", allow_duplicate=True),
    Output("osc-settings-open-dropdown", "options", allow_duplicate=True),
    *[Output(component_id, "value") for component_id in OSCILLATOR_SETTINGS_IDS],
    Input("osc-settings-open-btn", "n_clicks"),
    State("osc-settings-open-dropdown", "value"),
    prevent_initial_call=True,
)
def open_oscillator_strategy_settings(n_clicks, settings_name):
    """Load known oscillator/dynamic stochastic strategy fields from a JSON settings file."""
    path = strategy_setting_path(settings_name)
    if not path or not os.path.exists(path):
        return ("❌ Choose an existing settings file to open.", strategy_setting_options(), *[no_update for _ in OSCILLATOR_SETTINGS_IDS])
    try:
        with open(path, "r", encoding="utf-8") as f:
            payload = json.load(f)
        parameters = payload.get("parameters", {}) if isinstance(payload, dict) else {}
        values = [parameters.get(component_id, no_update) for component_id in OSCILLATOR_SETTINGS_IDS]
        loaded_count = sum(1 for value in values if value is not no_update)
        return (f"✅ Opened {settings_name}: loaded {loaded_count} matching parameters.", strategy_setting_options(), *values)
    except Exception as exc:
        return (f"❌ Could not open {settings_name}: {exc}", strategy_setting_options(), *[no_update for _ in OSCILLATOR_SETTINGS_IDS])

@app.callback(
    Output("dynamic-check-status", "children"),
    Output("dynamic-check-results", "children"),
    Input("dynamic-check-run-btn", "n_clicks"),
    State("dynamic-check-sl-input", "value"),
    State("dynamic-check-max-dd-input", "value"),
    State("dynamic-check-tp-levels-input", "value"),
    State("dynamic-check-trail-rules-input", "value"),
    State("dynamic-check-sl-grid-input", "value"),
    State("dynamic-check-be-grid-input", "value"),
    State("dynamic-check-dd-grid-input", "value"),
    State("dynamic-check-notional-input", "value"),
    State("dynamic-check-cost-input", "value"),
    State("dynamic-check-open-return-input", "value"),
    State("golden-store-version", "data"),
    prevent_initial_call=True,
)
def run_dynamic_strategy_checkup(n_clicks, stop_loss_pct, max_dd_pct, tp_text, stop_rules_text, sl_grid_text, be_grid_text, dd_grid_text, notional_usd, round_trip_cost_pct, open_return_pct, _version):
    """On-demand callback for raw-data dynamic strategy diagnostics."""
    if not n_clicks:
        return no_update, no_update
    try:
        tp_levels = parse_dynamic_percent_levels(tp_text)
        stop_rules = parse_dynamic_stop_rules(stop_rules_text)
        sl_grid = parse_dynamic_percent_levels(sl_grid_text, default_levels=())
        be_grid = parse_dynamic_percent_levels(be_grid_text, default_levels=())
        dd_grid = parse_dynamic_percent_levels(dd_grid_text, default_levels=())
        tasks = get_display_tasks_snapshot()
        started = time.time()
        table = build_dynamic_checkup_summary_table(
            tasks,
            stop_loss_pct,
            max_dd_pct,
            tp_levels,
            stop_rules,
            sl_grid=sl_grid,
            be_grid=be_grid,
            dd_grid=dd_grid,
            notional_usd=notional_usd,
            round_trip_cost_pct=round_trip_cost_pct,
            open_return_pct=open_return_pct,
        )
        elapsed = time.time() - started
        status = (
            f"✅ Dynamic checkup run #{n_clicks} complete in {elapsed:.2f}s. "
            f"SL={float(stop_loss_pct or 0):g}%, max adverse DD={'off' if not max_dd_pct else f'{float(max_dd_pct):g}%'}, "
            f"TP={', '.join(fmt_dynamic_level_label(level) for level in tp_levels)}, "
            f"notional=${float(notional_usd or 0):,.0f}, costs={float(round_trip_cost_pct or 0):g}%."
        )
        return status, table
    except Exception as exc:
        return f"❌ Dynamic checkup failed: {exc}", no_update


@app.callback(
    Output("level-reversal-status", "children"),
    Output("level-reversal-results", "children"),
    Input("level-reversal-run-btn", "n_clicks"),
    State("level-reversal-offset-input", "value"),
    State("level-reversal-sl-input", "value"),
    State("level-reversal-max-dd-input", "value"),
    State("level-reversal-tp-levels-input", "value"),
    State("level-reversal-trail-rules-input", "value"),
    State("level-reversal-sl-grid-input", "value"),
    State("level-reversal-offset-grid-input", "value"),
    State("level-reversal-notional-input", "value"),
    State("level-reversal-cost-input", "value"),
    State("level-reversal-open-return-input", "value"),
    State("golden-store-version", "data"),
    prevent_initial_call=True,
)
def run_level_reversal_checkup(n_clicks, entry_offset_pct, stop_loss_pct, max_dd_pct, tp_text, stop_rules_text, sl_grid_text, offset_grid_text, notional_usd, round_trip_cost_pct, open_return_pct, _version):
    """On-demand callback for level-touch/overshoot reversal diagnostics."""
    if not n_clicks:
        return no_update, no_update
    try:
        entry_offset_pct = float(entry_offset_pct or 0.0)
        tp_levels = parse_dynamic_percent_levels(tp_text)
        stop_rules = parse_dynamic_stop_rules(stop_rules_text)
        sl_grid = parse_dynamic_percent_levels(sl_grid_text, default_levels=())
        offset_grid = parse_dynamic_nonnegative_percent_levels(offset_grid_text, default_levels=(0.0,))
        if 0.0 not in offset_grid:
            offset_grid = sorted(set([0.0] + offset_grid))
        tasks = get_display_tasks_snapshot()
        started = time.time()
        table = build_level_reversal_summary_table(
            tasks,
            entry_offset_pct,
            stop_loss_pct,
            max_dd_pct,
            tp_levels,
            stop_rules,
            sl_grid=sl_grid,
            offset_grid=offset_grid,
            notional_usd=notional_usd,
            round_trip_cost_pct=round_trip_cost_pct,
            open_return_pct=open_return_pct,
        )
        elapsed = time.time() - started
        status = (
            f"✅ Level-reversal checkup run #{n_clicks} complete in {elapsed:.2f}s. "
            f"entry offset={entry_offset_pct:g}%, SL={float(stop_loss_pct or 0):g}%, "
            f"max adverse DD={'off' if not max_dd_pct else f'{float(max_dd_pct):g}%'}, "
            f"TP={', '.join(fmt_dynamic_level_label(level) for level in tp_levels)}, "
            f"notional=${float(notional_usd or 0):,.0f}, costs={float(round_trip_cost_pct or 0):g}%."
        )
        return status, table
    except Exception as exc:
        return f"❌ Level-reversal checkup failed: {exc}", no_update


@app.callback(
    Output("osc-reversal-status", "children"),
    Output("osc-reversal-results", "children"),
    Output("osc-event-groups-store", "data"),
    Input("osc-reversal-run-btn", "n_clicks"),
    State("osc-stoch-14-level-input", "value"),
    State("osc-stoch-14-condition-input", "value"),
    State("osc-stoch-40-level-input", "value"),
    State("osc-stoch-40-condition-input", "value"),
    State("osc-stoch-60-level-input", "value"),
    State("osc-stoch-60-condition-input", "value"),
    State("osc-stoch-300-level-input", "value"),
    State("osc-stoch-300-condition-input", "value"),
    State("osc-rsi-level-input", "value"),
    State("osc-rsi-condition-input", "value"),
    State("osc-down-stoch-14-level-input", "value"),
    State("osc-down-stoch-14-condition-input", "value"),
    State("osc-down-stoch-40-level-input", "value"),
    State("osc-down-stoch-40-condition-input", "value"),
    State("osc-down-stoch-60-level-input", "value"),
    State("osc-down-stoch-60-condition-input", "value"),
    State("osc-down-stoch-300-level-input", "value"),
    State("osc-down-stoch-300-condition-input", "value"),
    State("osc-down-rsi-level-input", "value"),
    State("osc-down-rsi-condition-input", "value"),
    State("osc-reversal-sl-input", "value"),
    State("osc-reversal-max-dd-input", "value"),
    State("osc-reversal-tp-levels-input", "value"),
    State("osc-reversal-trail-rules-input", "value"),
    State("osc-reversal-sl-grid-input", "value"),
    State("osc-entry-window-input", "value"),
    State("osc-exit-window-input", "value"),
    State("osc-exit-enabled-input", "value"),
    State("osc-exit-sell-stoch-14-level-input", "value"),
    State("osc-exit-sell-stoch-14-condition-input", "value"),
    State("osc-exit-sell-stoch-40-level-input", "value"),
    State("osc-exit-sell-stoch-40-condition-input", "value"),
    State("osc-exit-sell-stoch-60-level-input", "value"),
    State("osc-exit-sell-stoch-60-condition-input", "value"),
    State("osc-exit-sell-stoch-300-level-input", "value"),
    State("osc-exit-sell-stoch-300-condition-input", "value"),
    State("osc-exit-buy-stoch-14-level-input", "value"),
    State("osc-exit-buy-stoch-14-condition-input", "value"),
    State("osc-exit-buy-stoch-40-level-input", "value"),
    State("osc-exit-buy-stoch-40-condition-input", "value"),
    State("osc-exit-buy-stoch-60-level-input", "value"),
    State("osc-exit-buy-stoch-60-condition-input", "value"),
    State("osc-exit-buy-stoch-300-level-input", "value"),
    State("osc-exit-buy-stoch-300-condition-input", "value"),
    State("osc-reversal-notional-input", "value"),
    State("osc-reversal-cost-input", "value"),
    State("osc-reversal-open-return-input", "value"),
    State("golden-store-version", "data"),
    prevent_initial_call=True,
)
def run_oscillator_reversal_checkup(n_clicks, stoch14_level, stoch14_condition, stoch40_level, stoch40_condition, stoch60_level, stoch60_condition, stoch300_level, stoch300_condition, rsi_level, rsi_condition, down_stoch14_level, down_stoch14_condition, down_stoch40_level, down_stoch40_condition, down_stoch60_level, down_stoch60_condition, down_stoch300_level, down_stoch300_condition, down_rsi_level, down_rsi_condition, stop_loss_pct, max_dd_pct, tp_text, stop_rules_text, sl_grid_text, entry_condition_window, oscillator_exit_window, exit_enabled, exit_sell_stoch14_level, exit_sell_stoch14_condition, exit_sell_stoch40_level, exit_sell_stoch40_condition, exit_sell_stoch60_level, exit_sell_stoch60_condition, exit_sell_stoch300_level, exit_sell_stoch300_condition, exit_buy_stoch14_level, exit_buy_stoch14_condition, exit_buy_stoch40_level, exit_buy_stoch40_condition, exit_buy_stoch60_level, exit_buy_stoch60_condition, exit_buy_stoch300_level, exit_buy_stoch300_condition, notional_usd, round_trip_cost_pct, open_return_pct, _version):
    """On-demand callback for oscillator-confirmed level-reversal diagnostics."""
    if not n_clicks:
        return no_update, no_update, no_update
    try:
        entry_condition_window = max(1, int(entry_condition_window or 1))
        oscillator_exit_window = max(1, int(oscillator_exit_window or 1))
        oscillator_specs = build_oscillator_spec_groups(
            (
                stoch14_level, stoch14_condition,
                stoch40_level, stoch40_condition,
                stoch60_level, stoch60_condition,
                stoch300_level, stoch300_condition,
                rsi_level, rsi_condition,
            ),
            (
                down_stoch14_level, down_stoch14_condition,
                down_stoch40_level, down_stoch40_condition,
                down_stoch60_level, down_stoch60_condition,
                down_stoch300_level, down_stoch300_condition,
                down_rsi_level, down_rsi_condition,
            ),
        )
        oscillator_exit_specs = build_stochastic_exit_spec_groups(
            exit_enabled,
            (
                exit_sell_stoch14_level, exit_sell_stoch14_condition,
                exit_sell_stoch40_level, exit_sell_stoch40_condition,
                exit_sell_stoch60_level, exit_sell_stoch60_condition,
                exit_sell_stoch300_level, exit_sell_stoch300_condition,
            ),
            (
                exit_buy_stoch14_level, exit_buy_stoch14_condition,
                exit_buy_stoch40_level, exit_buy_stoch40_condition,
                exit_buy_stoch60_level, exit_buy_stoch60_condition,
                exit_buy_stoch300_level, exit_buy_stoch300_condition,
            ),
        )
        tp_levels = parse_dynamic_percent_levels(tp_text)
        stop_rules = parse_dynamic_stop_rules(stop_rules_text)
        sl_grid = parse_dynamic_percent_levels(sl_grid_text, default_levels=())
        tasks = get_display_tasks_snapshot()
        started = time.time()
        table, event_groups = build_oscillator_reversal_summary_table(
            tasks,
            oscillator_specs,
            stop_loss_pct,
            max_dd_pct,
            tp_levels,
            stop_rules,
            sl_grid=sl_grid,
            notional_usd=notional_usd,
            round_trip_cost_pct=round_trip_cost_pct,
            open_return_pct=open_return_pct,
            oscillator_exit_specs=oscillator_exit_specs,
            entry_condition_window=entry_condition_window,
            oscillator_exit_window=oscillator_exit_window,
            return_event_groups=True,
        )
        elapsed = time.time() - started
        status = (
            f"✅ Oscillator reversal checkup run #{n_clicks} complete in {elapsed:.2f}s. "
            f"entry filters={format_oscillator_specs(oscillator_specs)}; close filters={format_oscillator_specs(oscillator_exit_specs) if oscillator_exit_specs else 'disabled'}; windows entry={entry_condition_window}, close={oscillator_exit_window}; "
            f"SL={float(stop_loss_pct or 0):g}%, max adverse DD={'off' if not max_dd_pct else f'{float(max_dd_pct):g}%'}, "
            f"TP={', '.join(fmt_dynamic_level_label(level) for level in tp_levels)}, "
            f"notional=${float(notional_usd or 0):,.0f}, costs={float(round_trip_cost_pct or 0):g}%."
        )
        return status, table, event_groups
    except Exception as exc:
        return f"❌ Oscillator reversal checkup failed: {exc}", no_update, no_update



@app.callback(
    Output("osc-research-status", "children"),
    Output("osc-research-results", "children"),
    Input("osc-research-run-btn", "n_clicks"),
    State("osc-stoch-14-level-input", "value"),
    State("osc-stoch-14-condition-input", "value"),
    State("osc-stoch-40-level-input", "value"),
    State("osc-stoch-40-condition-input", "value"),
    State("osc-stoch-60-level-input", "value"),
    State("osc-stoch-60-condition-input", "value"),
    State("osc-stoch-300-level-input", "value"),
    State("osc-stoch-300-condition-input", "value"),
    State("osc-rsi-level-input", "value"),
    State("osc-rsi-condition-input", "value"),
    State("osc-down-stoch-14-level-input", "value"),
    State("osc-down-stoch-14-condition-input", "value"),
    State("osc-down-stoch-40-level-input", "value"),
    State("osc-down-stoch-40-condition-input", "value"),
    State("osc-down-stoch-60-level-input", "value"),
    State("osc-down-stoch-60-condition-input", "value"),
    State("osc-down-stoch-300-level-input", "value"),
    State("osc-down-stoch-300-condition-input", "value"),
    State("osc-down-rsi-level-input", "value"),
    State("osc-down-rsi-condition-input", "value"),
    State("osc-exit-enabled-input", "value"),
    State("osc-exit-sell-stoch-14-level-input", "value"),
    State("osc-exit-sell-stoch-14-condition-input", "value"),
    State("osc-exit-sell-stoch-40-level-input", "value"),
    State("osc-exit-sell-stoch-40-condition-input", "value"),
    State("osc-exit-sell-stoch-60-level-input", "value"),
    State("osc-exit-sell-stoch-60-condition-input", "value"),
    State("osc-exit-sell-stoch-300-level-input", "value"),
    State("osc-exit-sell-stoch-300-condition-input", "value"),
    State("osc-exit-buy-stoch-14-level-input", "value"),
    State("osc-exit-buy-stoch-14-condition-input", "value"),
    State("osc-exit-buy-stoch-40-level-input", "value"),
    State("osc-exit-buy-stoch-40-condition-input", "value"),
    State("osc-exit-buy-stoch-60-level-input", "value"),
    State("osc-exit-buy-stoch-60-condition-input", "value"),
    State("osc-exit-buy-stoch-300-level-input", "value"),
    State("osc-exit-buy-stoch-300-condition-input", "value"),
    State("osc-research-entry-windows-input", "value"),
    State("osc-research-exit-windows-input", "value"),
    State("osc-research-sl-grid-input", "value"),
    State("osc-research-stop-presets-input", "value"),
    State("osc-research-max-combos-input", "value"),
    State("osc-research-top-input", "value"),
    State("osc-reversal-notional-input", "value"),
    State("osc-reversal-cost-input", "value"),
    State("osc-reversal-open-return-input", "value"),
    State("golden-store-version", "data"),
    prevent_initial_call=True,
)
def run_oscillator_research_optimizer(n_clicks, stoch14_level, stoch14_condition, stoch40_level, stoch40_condition, stoch60_level, stoch60_condition, stoch300_level, stoch300_condition, rsi_level, rsi_condition, down_stoch14_level, down_stoch14_condition, down_stoch40_level, down_stoch40_condition, down_stoch60_level, down_stoch60_condition, down_stoch300_level, down_stoch300_condition, down_rsi_level, down_rsi_condition, exit_enabled, exit_sell_stoch14_level, exit_sell_stoch14_condition, exit_sell_stoch40_level, exit_sell_stoch40_condition, exit_sell_stoch60_level, exit_sell_stoch60_condition, exit_sell_stoch300_level, exit_sell_stoch300_condition, exit_buy_stoch14_level, exit_buy_stoch14_condition, exit_buy_stoch40_level, exit_buy_stoch40_condition, exit_buy_stoch60_level, exit_buy_stoch60_condition, exit_buy_stoch300_level, exit_buy_stoch300_condition, entry_windows_text, exit_windows_text, sl_grid_text, stop_presets_text, max_combos, top_n, notional_usd, round_trip_cost_pct, open_return_pct, _version):
    """Research optimizer for oscillator settings, windows, SLs, and stop rules."""
    if not n_clicks:
        return no_update, no_update
    try:
        oscillator_specs = build_oscillator_spec_groups(
            (
                stoch14_level, stoch14_condition,
                stoch40_level, stoch40_condition,
                stoch60_level, stoch60_condition,
                stoch300_level, stoch300_condition,
                rsi_level, rsi_condition,
            ),
            (
                down_stoch14_level, down_stoch14_condition,
                down_stoch40_level, down_stoch40_condition,
                down_stoch60_level, down_stoch60_condition,
                down_stoch300_level, down_stoch300_condition,
                down_rsi_level, down_rsi_condition,
            ),
        )
        oscillator_exit_specs = build_stochastic_exit_spec_groups(
            exit_enabled,
            (
                exit_sell_stoch14_level, exit_sell_stoch14_condition,
                exit_sell_stoch40_level, exit_sell_stoch40_condition,
                exit_sell_stoch60_level, exit_sell_stoch60_condition,
                exit_sell_stoch300_level, exit_sell_stoch300_condition,
            ),
            (
                exit_buy_stoch14_level, exit_buy_stoch14_condition,
                exit_buy_stoch40_level, exit_buy_stoch40_condition,
                exit_buy_stoch60_level, exit_buy_stoch60_condition,
                exit_buy_stoch300_level, exit_buy_stoch300_condition,
            ),
        )
        entry_windows = [int(v) for v in parse_dynamic_percent_levels(entry_windows_text, default_levels=(1, 3, 5))]
        exit_windows = [int(v) for v in parse_dynamic_percent_levels(exit_windows_text, default_levels=(1, 3, 5))]
        sl_grid = parse_dynamic_percent_levels(sl_grid_text, default_levels=(1, 1.5, 2, 2.5, 3))
        stop_presets = parse_research_stop_rule_presets(stop_presets_text)
        tasks = get_display_tasks_snapshot()
        started = time.time()
        table = build_oscillator_research_optimizer_table(
            tasks,
            oscillator_specs,
            oscillator_exit_specs,
            entry_windows,
            exit_windows,
            sl_grid,
            stop_presets,
            notional_usd,
            round_trip_cost_pct,
            open_return_pct,
            max_combos=max_combos,
            top_n=top_n,
        )
        elapsed = time.time() - started
        return f"✅ Research optimizer run #{n_clicks} complete in {elapsed:.2f}s. Tested up to {int(max_combos or 120)} combinations; showing top {int(top_n or 20)}.", table
    except Exception as exc:
        return f"❌ Research optimizer failed: {exc}", no_update

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
        df_limited = read_task_signal_window(fp, task)
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
            df_limited = slice_task_signal_window(
                task, full_df, pre_signal_minutes=SIGNAL_BUFFER_MINUTES
            )
                
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
        df_limited = slice_task_signal_window(
            task, full_df, pre_signal_minutes=SIGNAL_BUFFER_MINUTES
        )
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
        df_limited = read_task_signal_window(
            fp, task, pre_signal_minutes=SIGNAL_BUFFER_MINUTES
        )
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
            df_limited = read_task_signal_window(fp, task)
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

# =============================================================================
# 19. CALLBACKS: ACTIVE DOWNLOAD MONITOR AND DATA MAINTENANCE
# =============================================================================
# Monitor callbacks expose current task progress and control pause/stop actions.
# Maintenance shortcuts queue work but should leave persistence and recalculation
# rules to their dedicated sections below.
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
    # Dynamic tab insertion can initialize these buttons with 0 even though no
    # user action occurred. Never turn component creation into a bulk operation.
    if not any(int(value or 0) > 0 for value in (ev_n, str_n, imp_n)):
        return no_update
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
                    df_limited = read_task_signal_window(fp, t)
                        
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

# =============================================================================
# 20. CALLBACKS: PERSISTENCE, SAVE/LOAD JSON, AND FILE DROPDOWNS
# =============================================================================
# JSON persistence callbacks must preserve the compatibility rules and field
# catalog above. Avoid introducing UI refresh side effects outside Golden Store
# publication helpers.
# =============================================================================

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
    
    filepath = os.path.abspath(os.path.join(LOGS_DIR, filename))
    
    # Get live tasks from RAM (Source of Truth)
    tasks = tm.get_all_tasks()
    protected_sources = {
        os.path.abspath(task._loaded_source_json)
        for task in tasks
        if getattr(task, "_prepared_for_new_json", False)
        and getattr(task, "_loaded_source_json", None)
    }
    if filepath in protected_sources:
        return (
            "❌ Refusing to overwrite the source JSON after changing its period values. "
            "Enter a new filename and save again.",
            filename,
        )
    report_unclassified_task_fields(tasks, reason="save_tasks_to_json")
    
    # Build reconstructed data list
    serializable_data = tasks_to_serializable_snapshot(tasks)

    # 🔧 ATOMIC SAVE with sanitization (removed default=str fallback)
    try:
        write_json_atomic(filepath, serializable_data)
        return f"✅ Saved {len(tasks)} tasks to {filename}", filename
    except Exception as e:
        return f"❌ Save failed: {str(e)}", filename



@app.callback(
    Output("golden-store-version", "data", allow_duplicate=True),
    Input("progress-interval", "n_intervals"),
    State("golden-store-version", "data"),
    prevent_initial_call=True
)
def sync_golden_store_version_from_server(_n_intervals, client_version):
    """Propagate server-side Golden Store publishes into the Dash store.

    Background workers can update the module-level Golden Store, but they cannot
    directly update dcc.Store values in the browser. Polling this lightweight
    version counter lets callbacks that depend on ``golden-store-version``
    refresh after background task creation or other server-side publishes.
    """
    server_version = get_golden_store_version()
    if server_version != client_version:
        return server_version
    return dash.no_update

# 3. Load tasks from selected JSON file (Optimized & Thread-Safe)
def _read_stable_parquet_timestamps(file_path, attempts=3):
    """Read timestamps only after proving the file stayed unchanged during the read.

    A downloader in another thread/process can make a valid Parquet file look
    truncated for a moment. Retry those transient reads, but never classify or
    modify the file here.
    """
    last_error = None
    changed_during_attempt = False
    for attempt in range(max(1, int(attempts))):
        before = None
        try:
            before = os.stat(file_path)
            loaded = pd.read_parquet(file_path, columns=["timestamp"])["timestamp"]
            after = os.stat(file_path)
            before_version = (before.st_mtime_ns, before.st_size)
            after_version = (after.st_mtime_ns, after.st_size)
            if before_version != after_version:
                changed_during_attempt = True
                last_error = RuntimeError("file changed while timestamps were being read")
            else:
                return loaded, None
        except Exception as exc:
            last_error = exc
            try:
                after = os.stat(file_path)
                changed_during_attempt = (
                    before is not None
                    and (before.st_mtime_ns, before.st_size)
                    != (after.st_mtime_ns, after.st_size)
                ) or changed_during_attempt
            except OSError:
                changed_during_attempt = True
        if attempt + 1 < attempts:
            time.sleep(0.2 * (attempt + 1))
    if changed_during_attempt:
        return None, f"file was changing or replaced during verification: {last_error}"
    return None, str(last_error or "unknown Parquet read error")


def check_pre_signal_database_coverage(task_data, minutes, timestamp_cache=None):
    """Verify continuous stored candles before preparing persistent JSON history."""
    try:
        symbols = task_data.get("symbols") or []
        symbol = symbols[0]
        timeframe = str(task_data.get("timeframe"))
        interval_ms = INTERVAL_MS.get(timeframe)
        signal_ms = int(float(task_data.get("signal_time")))
        if not symbol or interval_ms is None:
            return False, "missing symbol or unsupported timeframe"
        requested_start_ms = max(0, signal_ms - int(minutes) * 60_000)
        first_candle = ((requested_start_ms + interval_ms - 1) // interval_ms) * interval_ms
        last_candle = (signal_ms // interval_ms) * interval_ms
        fp = os.path.join(symbol_timeframe_path(symbol, timeframe), "data.parquet")
        if not os.path.exists(fp):
            return False, f"database file not found: {fp}"
        cache = timestamp_cache if timestamp_cache is not None else {}
        if fp not in cache:
            # During one JSON load, read each physical timestamp column once;
            # many tasks often share the same symbol/timeframe file. Cache read
            # failures too: repeatedly decompressing a damaged file wastes an
            # old SSD and cannot make the next task safer.
            loaded, read_error = _read_stable_parquet_timestamps(fp)
            if read_error is None:
                if loaded.dtype.name.startswith("datetime"):
                    loaded = (loaded.astype("int64") // 1_000_000).astype("int64")
                else:
                    loaded = pd.to_numeric(loaded, errors="coerce")
                cache[fp] = (loaded, None)
            else:
                failure_kind = (
                    "busy/changing market-data file"
                    if read_error.startswith("file was changing or replaced")
                    else "unreadable market-data file"
                )
                cache[fp] = (
                    None,
                    f"{failure_kind} for {symbol} {timeframe} "
                    f"(preserved; not modified): {read_error}",
                )
        all_timestamps, cached_error = cache[fp]
        if cached_error:
            return False, cached_error
        timestamps = all_timestamps[
            (all_timestamps >= first_candle) & (all_timestamps <= last_candle)
        ]
        numeric = pd.to_numeric(timestamps, errors="coerce")
        if numeric.isna().any() or numeric.duplicated().any():
            return False, "requested database range has invalid or duplicate timestamps"
        ordered = np.sort(numeric.astype("int64").unique())
        expected = max(0, ((last_candle - first_candle) // interval_ms) + 1)
        if len(ordered) != expected:
            return False, f"needs {expected} candles but found {len(ordered)}"
        if expected and (
            int(ordered[0]) != first_candle or
            int(ordered[-1]) != last_candle or
            (len(ordered) > 1 and not (np.diff(ordered) == interval_ms).all())
        ):
            return False, "requested pre-signal range is not continuous"
        return True, requested_start_ms
    except Exception as exc:
        return False, f"coverage check failed: {exc}"


json_period_update_state = {
    "running": False,
    "progress": 0.0,
    "message": "Idle.",
    "ready_to_save": False,
    "lock": threading.Lock(),
}


def _set_json_period_update_state(message=None, progress=None, running=None, ready_to_save=None):
    with json_period_update_state["lock"]:
        if message is not None:
            json_period_update_state["message"] = message
        if progress is not None:
            json_period_update_state["progress"] = float(progress)
        if running is not None:
            json_period_update_state["running"] = bool(running)
        if ready_to_save is not None:
            json_period_update_state["ready_to_save"] = bool(ready_to_save)


def _task_coverage_dict(task):
    return {
        "task_id": task.task_id,
        "symbols": list(task.symbols),
        "timeframe": task.timeframe,
        "signal_time": task.signal_time,
    }


def _prepare_loaded_tasks_for_new_json(tasks, extra_minutes):
    """Add left history without reclassifying previously saved task results.

    Validation here answers only whether the requested pre-signal candle range is
    safe and complete. A task that cannot be prepared keeps its original period;
    it is not marked invalid and its existing derived results are not modified.
    """
    total = len(tasks)
    prepared = []
    skipped = []
    # Tasks commonly share symbol/timeframe files. Reuse one timestamp column
    # per physical file instead of rereading/decompressing it for every task.
    coverage_cache = {}
    inventory_info = None
    try:
        for index, task in enumerate(tasks, 1):
            label = f"{str(task.task_id)[:8]} {task.symbols[0]} {task.timeframe}"
            task_data = _task_coverage_dict(task)
            original_minutes = max(0, int(getattr(task, "pre_buffer_minutes", 0) or 0))
            target_minutes = original_minutes + extra_minutes
            requested_start = max(0, int(float(task.signal_time)) - target_minutes * 60_000)
            try:
                _set_json_period_update_state(
                    f"[{index}/{total}] Checking {label}...",
                    (index - 1) / total * 90,
                )
                for attempt in range(1, 21):
                    available, detail = check_pre_signal_database_coverage(
                        task_data, target_minutes, coverage_cache
                    )
                    if available:
                        prepared.append((task, target_minutes))
                        break
                    if str(detail).startswith((
                        "unreadable market-data file", "busy/changing market-data file"
                    )):
                        raise RuntimeError(detail)

                    signal_ms = int(float(task.signal_time))
                    interval_ms = INTERVAL_MS.get(str(task.timeframe))
                    if interval_ms is None:
                        raise RuntimeError(f"unsupported timeframe {task.timeframe}")
                    signal_candle_ms = (signal_ms // interval_ms) * interval_ms
                    _set_json_period_update_state(
                        f"[{index}/{total}] Locating stored signal candle for {label}...",
                        (index - 1) / total * 90,
                    )
                    if inventory_info is None:
                        inventory_info = get_database_info(force_refresh=True)
                    containing = next((
                        period for period in inventory_info["details"]
                        if period["symbol"] == task.symbols[0]
                        and str(period["timeframe"]) == str(task.timeframe)
                        and period["start_ms"] <= signal_candle_ms <= period["end_ms"]
                    ), None)
                    if containing is None:
                        raise RuntimeError(
                            "no contiguous stored period contains the aligned signal candle; "
                            "there is no trusted existing period to extend"
                        )

                    missing_minutes = max(
                        1,
                        int(math.ceil((containing["start_ms"] - requested_start) / 60_000)),
                    )
                    fp = os.path.join(
                        symbol_timeframe_path(task.symbols[0], str(task.timeframe)),
                        "data.parquet",
                    )
                    before = (os.path.getsize(fp), os.stat(fp).st_mtime_ns)
                    _set_json_period_update_state(
                        f"[{index}/{total}] Downloading {label}: up to "
                        f"{missing_minutes} missing minutes (attempt {attempt}/20)...",
                        (index - 1) / total * 90,
                    )
                    em.extend_left_safely(
                        task.symbols[0], str(task.timeframe), missing_minutes,
                        progress_base=(index - 1) / total * 90,
                        progress_span=90 / total,
                        period_start=containing["start_ms"],
                    )
                    after = (os.path.getsize(fp), os.stat(fp).st_mtime_ns)
                    clear_parquet_cache()
                    coverage_cache.pop(fp, None)
                    if after != before:
                        inventory_info = None
                    if after == before:
                        available, reason = check_pre_signal_database_coverage(
                            task_data, target_minutes, coverage_cache
                        )
                        if not available:
                            raise RuntimeError(
                                f"Bybit returned no usable earlier candles ({reason})"
                            )
                else:
                    raise RuntimeError("requested range was still incomplete after 20 attempts")
            except Exception as exc:
                skipped.append(f"{label}: {exc}")
            finally:
                _set_json_period_update_state(
                    f"[{index}/{total}] Prepared {len(prepared)}, skipped {len(skipped)}. "
                    f"Last: {label}",
                    index / total * 90,
                )

        # Deeply verify only candidates that obtained complete timestamp coverage.
        verified = []
        coverage_cache = {}
        deep_validation_cache = {}
        for verify_index, (task, target_minutes) in enumerate(prepared, 1):
            label = f"{str(task.task_id)[:8]} {task.symbols[0]} {task.timeframe}"
            _set_json_period_update_state(
                f"Final verification [{verify_index}/{len(prepared)}] {label}...",
                90 + verify_index / max(1, len(prepared)) * 8,
            )
            available, detail = check_pre_signal_database_coverage(
                _task_coverage_dict(task), target_minutes, coverage_cache
            )
            if not available:
                skipped.append(f"{label}: final coverage failed ({detail})")
                continue
            # ``detail`` is the requested pre-signal start returned by the
            # coverage check. Validate only that added/required range through
            # the signal; do not reinterpret the saved task's later results.
            validation_key = (
                task.symbols[0], str(task.timeframe), int(detail), int(float(task.signal_time))
            )
            if validation_key not in deep_validation_cache:
                deep_validation_cache[validation_key] = validate_stored_candle_range(
                    task.symbols[0], str(task.timeframe), detail, task.signal_time
                )
            deep_valid, deep_detail = deep_validation_cache[validation_key]
            if not deep_valid:
                skipped.append(f"{label}: final OHLCV verification failed ({deep_detail})")
                continue
            verified.append((task, target_minutes))

        updated = []
        with tm.lock:
            for task, target_minutes in verified:
                label = f"{str(task.task_id)[:8]} {task.symbols[0]} {task.timeframe}"
                if tm.tasks.get(task.task_id) is not task:
                    skipped.append(f"{label}: task changed while preparation was running")
                    continue
                task.pre_buffer_minutes = target_minutes
                task._prepared_for_new_json = True
                if hasattr(task, "_chart_cache"):
                    task._chart_cache.clear()
                updated.append(task)
            snapshot = list(tm.tasks.values())
        if updated:
            publish_golden_task_snapshot(snapshot, reason="json_period_update")

        skipped_preview = "; ".join(skipped[:8])
        skipped_suffix = f"; and {len(skipped) - 8} more" if len(skipped) > 8 else ""
        if updated:
            message = (
                f"✅ Finished. Added {extra_minutes} left-side minutes to "
                f"{len(updated)}/{total} tasks. Rerun Events, Strategy and Impulse, "
                "then use the now-enabled Save prepared JSON button."
            )
        else:
            message = "⚠️ Finished safely, but no task could be updated."
        if skipped:
            message += (
                f" Not prepared: {len(skipped)} task(s). They were not marked incorrect, and "
                "their original period values/results were kept: "
                f"{skipped_preview}{skipped_suffix}."
            )
        _set_json_period_update_state(message, 100, ready_to_save=bool(updated))
    except Exception as exc:
        _set_json_period_update_state(
            f"❌ Preparation stopped unexpectedly: {exc}. Existing market data and task "
            "period values were preserved.",
            ready_to_save=False,
        )
    finally:
        with em.lock:
            em.running = False
        _set_json_period_update_state(running=False)


@app.callback(
    Output("update-json-pre-signal-status", "children"),
    Input("update-json-pre-signal-btn", "n_clicks"),
    State("update-json-pre-signal-minutes", "value"),
    prevent_initial_call=True,
)
def start_json_period_update(_clicks, minutes_value):
    # The button lives in dynamic tab-content. Dash may invoke the callback when
    # that component is mounted; only a positive click is a user request.
    if not _clicks:
        return no_update
    try:
        extra_minutes = int(minutes_value)
    except (TypeError, ValueError):
        return "❌ Enter a whole number of extra minutes to add."
    if extra_minutes <= 0:
        return "❌ Extra minutes must be greater than zero."
    tasks = [task for task in tm.get_all_tasks() if getattr(task, "_loaded_from_json", False)]
    if not tasks:
        return "⚠️ No JSON-loaded tasks are present. Load a JSON before preparing a new one."
    with json_period_update_state["lock"]:
        if json_period_update_state["running"]:
            return "⚠️ JSON period update is already running."
    with em.lock:
        if em.running:
            return "⚠️ Another safe market-data extension is already running. Please wait."
        em.running = True
        em.progress = 0.0
        em.status = "Starting JSON period update..."
        em.log = []
    _set_json_period_update_state(
        f"▶️ Adding {extra_minutes} left-side minutes to {len(tasks)} loaded tasks...",
        0,
        True,
        False,
    )
    threading.Thread(
        target=_prepare_loaded_tasks_for_new_json,
        args=(list(tasks), extra_minutes),
        daemon=True,
    ).start()
    return (
        f"▶️ Started adding {extra_minutes} minutes for {len(tasks)} tasks. "
        "Unavailable tasks will be skipped and listed."
    )


@app.callback(
    Output("update-json-pre-signal-status", "children", allow_duplicate=True),
    Output("json-period-update-progress", "value"),
    Output("save-prepared-json-btn", "disabled", allow_duplicate=True),
    Input("recalc-status-interval", "n_intervals"),
    prevent_initial_call=True,
)
def poll_json_period_update(_interval):
    with json_period_update_state["lock"]:
        running = json_period_update_state["running"]
        message = json_period_update_state["message"]
        progress = json_period_update_state["progress"]
        ready_to_save = json_period_update_state["ready_to_save"]
        if not running and message == "Idle.":
            return no_update, no_update, True
    if running:
        _em_running, em_progress, em_status, _em_log = em.get_state()
        if em_status and em_status != "Starting JSON period update...":
            message = f"{message} | {em_status}"
        progress = max(progress, em_progress)
    return f"{message} [{progress:.1f}%]", str(progress), not ready_to_save


@app.callback(
    Output("prepared-json-save-status", "children"),
    Output("save-prepared-json-btn", "disabled", allow_duplicate=True),
    Input("save-prepared-json-btn", "n_clicks"),
    State("prepared-json-filename", "value"),
    prevent_initial_call=True,
)
def save_prepared_tasks_to_json(n_clicks, filename):
    """Save a completed period preparation through an explicit guarded action."""
    if not n_clicks:
        return no_update, no_update
    with json_period_update_state["lock"]:
        if json_period_update_state["running"]:
            return "⏳ Preparation is still running; saving remains disabled.", True
        if not json_period_update_state["ready_to_save"]:
            return "⚠️ Nothing newly prepared is ready to save.", True

    message, normalized_filename = save_tasks_to_json(n_clicks, filename)
    if not str(message).startswith("✅"):
        return message, False

    with json_period_update_state["lock"]:
        json_period_update_state["ready_to_save"] = False
    return (
        f"{message}. Prepared task periods were written to {normalized_filename}; "
        "the loaded source JSON was not overwritten.",
        True,
    )


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

    snapshot_audit = audit_task_snapshot_compatibility(data, reason="json_load_raw")

    loaded_ids = []
    skipped = 0
    skipped_missing_id = 0
    skipped_duplicate = 0
    skipped_unloadable = 0
    new_tasks = {}
    seen_ids = set()  # P3 IMPROVEMENT: Track unique task IDs
    
    # 🔧 DATETIME FIELDS that need restoration on load
    datetime_fields = TASK_DATETIME_FIELDS
    
    # 🔧 Use global _parse_timestamp for UTC-aware datetime parsing
    # This ensures all timestamps are converted to UTC-aware datetime objects
    
    for source_item in data:
        try:
            d = dict(source_item)
            # P3 IMPROVEMENT: Check for duplicate task IDs
            task_id_candidate = d.get('task_id')
            if not task_id_candidate:
                print(f"Skipping task without task_id: {d}")
                skipped += 1
                skipped_missing_id += 1
                continue
            if task_id_candidate in seen_ids:
                print(f"Duplicate task_id detected: {task_id_candidate}, skipping")
                skipped += 1
                skipped_duplicate += 1
                continue
            seen_ids.add(task_id_candidate)
            
            # 1. Initialize Task with Core Attributes
            init_kwargs = {k: d.get(k) for k in TASK_INIT_FIELDS}

            # Parse Datetimes for Init
            for k in datetime_fields:
                if k in init_kwargs and isinstance(init_kwargs[k], str):
                    init_kwargs[k] = _parse_timestamp(init_kwargs[k])

            task = DownloadTask(**init_kwargs)
            task._loaded_from_json = True
            task._loaded_source_json = os.path.abspath(filepath)
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
            skipped_unloadable += 1
            
    # 🔧 ATOMIC & THREAD-SAFE MEMORY UPDATE
    # Keep Golden Store in sync with loaded JSON so the paginated table can render
    # page 1 directly from its fast display source instead of falling back to tm.tasks
    # or reusing stale rows from a previous load.
    with tm.lock:
        tm.tasks.clear()
        tm.tasks.update(new_tasks)
        task_snapshot = list(tm.tasks.values())

    # 🔧 CRITICAL: Reset Version to Force Stats & Table Re-render
    # Since we split the callback, increment the version store to trigger both new callbacks.
    published_version = publish_golden_task_snapshot(task_snapshot, reason="json_load")
        
    count = len(loaded_ids)
    msg = f"✅ Loaded {count} tasks from {os.path.basename(filepath)}"
    if skipped > 0:
        skip_parts = []
        if skipped_missing_id:
            skip_parts.append(f"{skipped_missing_id} missing task_id")
        if skipped_duplicate:
            skip_parts.append(f"{skipped_duplicate} duplicate")
        if skipped_unloadable:
            skip_parts.append(f"{skipped_unloadable} unloadable")
        detail = f" ({', '.join(skip_parts)})" if skip_parts else ""
        msg += f" | ⚠️ Skipped {skipped} invalid/duplicate/unloadable record(s){detail}"
    audit_note = format_snapshot_audit_note(snapshot_audit)
    if audit_note:
        msg += f" | {audit_note}"
    # golden-store-version is the table/stat refresh trigger. Avoid also bumping
    # analysis-complete-trigger here because that path performs heavier
    # recalculation-oriented work before the first page can paint on older Macs.
    return msg, loaded_ids, count, 0, dash.no_update, published_version

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
    publish_golden_task_snapshot([], reason="manual_clear", bump_version=False)
    return "🗑️ All tasks cleared.", [], 0, 0

# =============================================================================
# 21. CALLBACKS: BULK ACTIONS, RECALCULATION, AND BACKGROUND WORKERS
# =============================================================================
# Long-running operations coordinate recalc state, task state, and Golden Store
# publication. Keep stop/progress flags explicit and avoid changing calculation
# logic during organization-only refactors.
# =============================================================================

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
    report_unclassified_task_fields(tasks, reason="recalc_table_flags")
    audit_task_snapshot_compatibility(tasks, reason="before_recalc")

    # 🔧 CRITICAL: Serialize tasks to dict format INSIDE the main thread (same logic as save_tasks_to_json)
    # This ensures all attributes are properly captured before passing to background thread
    import copy
    initial_tasks = []
    for t in tasks:
        d = {}
        for k, v in t.__dict__.items():
            # Skip non-serializable objects (locks, events, caches)
            if k in RUNTIME_TASK_FIELDS:
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
    datetime_fields = TASK_DATETIME_FIELDS
    
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
                init_kwargs = {k: t_dict.get(k) for k in TASK_INIT_FIELDS}
                
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
                
                # analyze_signal() owns the synchronization needed by its
                # logging/strategy helpers. Holding the same non-reentrant lock
                # here deadlocks when analyze_signal() calls add_log().
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
    with tm.lock:
        task_snapshot = list(tm.tasks.values())
    publish_golden_task_snapshot(task_snapshot, reason="recalc_complete")

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
        # Keep the permanent cross-tab target visually quiet while no operation
        # is active. The controls themselves already communicate readiness.
        return ""

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

# =============================================================================
# 22. DATABASE CALLBACK REGISTRATION AND APPLICATION ENTRYPOINT
# =============================================================================
# Database-specific UI/callbacks are delegated to database.py. Keep this final so
# the main app is fully constructed before registration.
# =============================================================================

# Register database callbacks
register_database_callbacks(app)

if __name__ == "__main__":
    app.run(debug=DASH_DEBUG_ENABLED, port=8050)
