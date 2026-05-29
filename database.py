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

# =============================================================================
# DATABASE HELPER FUNCTIONS
# =============================================================================

def symbol_timeframe_path(symbol, timeframe):
    """Return the folder path for a given symbol and timeframe."""
    return os.path.join(MARKET_DATA_DIR, symbol.replace("/", "_"), timeframe)


def get_database_info():
    """
    Walk the market_data folder and collect metadata about each Parquet file.
    Safely skips corrupted files and prints their paths for manual cleanup.
    """
    details, total_size, symbols = [], 0, set()
    corrupted_files = []
    for root, _, files in os.walk(MARKET_DATA_DIR):
        for f in files:
            if f == "data.parquet":
                fp = os.path.join(root, f)
                rel = os.path.relpath(root, MARKET_DATA_DIR).split(os.sep)
                if len(rel) == 2:
                    sym, tf = rel
                    symbols.add(sym)
                try:
                    total_size += os.path.getsize(fp)
                    df = pd.read_parquet(fp)
                    if not df.empty:
                        start = df["timestamp"].min()
                        end = df["timestamp"].max()
                        details.append({
                            "symbol": sym,
                            "timeframe": tf,
                            "start": pd.to_datetime(start, unit='ms'),
                            "end": pd.to_datetime(end, unit='ms'),
                            "candles": len(df),
                            "size": os.path.getsize(fp)
                        })
                except Exception as e:
                    corrupted_files.append(fp)
                    print(f"⚠️ Skipping corrupted file: {fp} ({e})")
                    
    if corrupted_files:
        print("\n" + "="*60)
        print("⚠️ CORRUPTED PARQUET FILES DETECTED ⚠️")
        print("These files will cause crashes. Delete them and re-download:")
        for f in corrupted_files:
            folder = os.path.dirname(f)
            print(f"  🗑️ rm -rf '{folder}'")
        print("="*60 + "\n")
        
    return {"size": total_size, "symbols": len(symbols), "details": details}


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
                            interval_ms = INTERVAL_MS.get(timeframe, 60000)
                            if len(df) > 1:
                                diffs = df["timestamp"].diff().iloc[1:].astype('int64')
                                threshold_ns = interval_ms * 1_000_000 * 1.5
                                gaps = diffs[diffs > threshold_ns]
                                if not gaps.empty:
                                    self.add_log(f"  ⚠ Gaps: {len(gaps)} detected")
                                    for i, gap in enumerate(gaps.head(5)):
                                        self.add_log(f"    Gap {i+1}: {gap/1e6:.1f} ms ({gap/60000:.1f} minutes)")
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
                            interval_ms = INTERVAL_MS.get(timeframe, 60000)
                            if len(df) > 1:
                                diffs = df["timestamp"].diff().iloc[1:].astype('int64')
                                threshold_ns = interval_ms * 1_000_000 * 1.5
                                gaps = diffs[diffs > threshold_ns]
                                if not gaps.empty:
                                    self.add_log(f"  ⚠ Gaps: {len(gaps)} detected")
                                    for i, gap in enumerate(gaps.head(5)):
                                        self.add_log(f"    Gap {i+1}: {gap/1e6:.1f} ms ({gap/60000:.1f} minutes)")
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
# DATA ANALYSIS TAB UI
# =============================================================================

def create_data_analysis_tab():
    """Create the Data Analysis tab UI layout."""
    info = get_database_info()
    total_candles = sum(d["candles"] for d in info["details"])
    total_size_mb = info["size"] / 1e6
    total_symbols = info["symbols"]
    
    rows = []
    for d in info["details"]:
        rows.append(html.Tr([
            html.Td(d["symbol"]),
            html.Td(d["timeframe"]),
            html.Td(d["start"].strftime("%Y-%m-%d %H:%M")),
            html.Td(d["end"].strftime("%Y-%m-%d %H:%M")),
            html.Td(f"{d['candles']:,}"),
            html.Td(f"{d['size']/1e6:.2f} MB")
        ]))
    
    table = html.Table([
        html.Thead(html.Tr([html.Th("Symbol"), html.Th("TF"), html.Th("Start"), html.Th("End"), html.Th("Candles"), html.Th("Size")])),
        html.Tbody(rows)
    ], style={"width": "100%", "border": "1px solid black", "borderCollapse": "collapse"})
    
    if info["details"]:
        df = pd.DataFrame(info["details"])
        df_grouped = df.groupby("symbol")["candles"].sum().reset_index()
        fig = px.bar(df_grouped, x="symbol", y="candles", title="Total Candles per Symbol")
    else:
        fig = px.bar(title="No data downloaded yet")
    
    # Build symbol/timeframe dropdown options
    symbol_options = [{"label": s, "value": s} for s in sorted(set(d["symbol"] for d in info["details"]))] if info["details"] else []
    
    return html.Div([
        html.H3("Data Statistics"),
        html.P(f"Total symbols: {total_symbols}"),
        html.P(f"Total candles: {total_candles:,}"),
        html.P(f"Total database size: {total_size_mb:.2f} MB"),
        html.Button("Download Backup", id="download-db-btn"),
        dcc.Download(id="download-db"),
        html.H4("Detailed Table"),
        table,
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