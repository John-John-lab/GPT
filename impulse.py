"""
impulse.py – Self‑contained impulse detection, backtesting, and tuning.
All functions are copied from strategies.py where needed, so this file is independent.
"""

import pandas as pd
import numpy as np
from typing import Dict, List, Tuple, Optional, Any
from itertools import product
from datetime import datetime
import json
import os

# ------------------------------------------------------------
# 1. Core indicators (copied from strategies.py)
# ------------------------------------------------------------
def compute_rsi(series: pd.Series, period: int = 14) -> pd.Series:
    """Calculate RSI for a price series."""
    delta = series.diff()
    gain = delta.clip(lower=0)
    loss = -delta.clip(upper=0)
    avg_gain = gain.rolling(window=period, min_periods=period).mean()
    avg_loss = loss.rolling(window=period, min_periods=period).mean()
    rs = avg_gain / avg_loss
    rsi = 100 - (100 / (1 + rs))
    return rsi

def compute_atr(df: pd.DataFrame, period: int = 14) -> pd.Series:
    """Calculate Average True Range."""
    high_low = df['high'] - df['low']
    high_close = abs(df['high'] - df['close'].shift())
    low_close = abs(df['low'] - df['close'].shift())
    tr = pd.concat([high_low, high_close, low_close], axis=1).max(axis=1)
    atr = tr.rolling(window=period).mean()
    return atr

# ------------------------------------------------------------
# 2. Exit simulation (copied from strategies.py)
# ------------------------------------------------------------
def simulate_trade(df, entry_idx, direction, stop_loss, tp1, tp2, max_bars=30,
                   trail_atr=2.0, atr_series=None, trail_activation_atr=1.0,
                   tp1_size=0.33, tp2_size=0.33, verbose=False):
    """
    Simulate trade forward with scaling out, trailing stop and time stop.
    Returns (exit_price, exit_time_ms, exit_reason)
    """
    if atr_series is None:
        atr_series = df['atr'] if 'atr' in df.columns else pd.Series([0]*len(df))
    entry_price = df.iloc[entry_idx]['close']
    highest = entry_price
    lowest = entry_price
    trailing_active = False
    exit_price = None
    exit_time = None
    exit_reason = None

    try:
        for j in range(entry_idx + 1, min(entry_idx + max_bars + 1, len(df))):
            row = df.iloc[j]
            high, low, close = row['high'], row['low'], row['close']
            current_atr = atr_series.iloc[j] if not pd.isna(atr_series.iloc[j]) else atr_series.mean()

            if direction == 'buy':
                highest = max(highest, high)
                if high >= tp2 and not exit_price:
                    exit_price = tp2
                    exit_time = row['timestamp']
                    exit_reason = 'tp2'
                if high >= tp1 and not exit_price:
                    exit_price = tp1
                    exit_time = row['timestamp']
                    exit_reason = 'tp1'
                if not trailing_active and (highest - entry_price) >= trail_activation_atr * current_atr:
                    trailing_active = True
                if trailing_active and not exit_price:
                    trailing_stop = highest - trail_atr * current_atr
                    effective_stop = max(stop_loss, trailing_stop)
                    if low <= effective_stop:
                        exit_price = effective_stop
                        exit_time = row['timestamp']
                        exit_reason = 'trailing_stop'
                if not trailing_active and not exit_price and low <= stop_loss:
                    exit_price = stop_loss
                    exit_time = row['timestamp']
                    exit_reason = 'initial_stop'
            else:  # sell
                lowest = min(lowest, low)
                if low <= tp2 and not exit_price:
                    exit_price = tp2
                    exit_time = row['timestamp']
                    exit_reason = 'tp2'
                if low <= tp1 and not exit_price:
                    exit_price = tp1
                    exit_time = row['timestamp']
                    exit_reason = 'tp1'
                if not trailing_active and (entry_price - lowest) >= trail_activation_atr * current_atr:
                    trailing_active = True
                if trailing_active and not exit_price:
                    trailing_stop = lowest + trail_atr * current_atr
                    effective_stop = min(stop_loss, trailing_stop)
                    if high >= effective_stop:
                        exit_price = effective_stop
                        exit_time = row['timestamp']
                        exit_reason = 'trailing_stop'
                if not trailing_active and not exit_price and high >= stop_loss:
                    exit_price = stop_loss
                    exit_time = row['timestamp']
                    exit_reason = 'initial_stop'

            if exit_price:
                if verbose:
                    print(f"✅ Exit at j={j}, reason={exit_reason}, price={exit_price:.5f}, time={exit_time}")
                break

        if exit_price is None:
            last_idx = min(entry_idx + max_bars, len(df)-1)
            exit_price = df.iloc[last_idx]['close']
            exit_time = df.iloc[last_idx]['timestamp']
            exit_reason = 'time_stop'
            if verbose:
                print(f"⌛ Time stop at idx={last_idx}, price={exit_price:.5f}")
    except Exception as e:
        print(f"❌ ERROR in simulate_trade: {e}")
        import traceback
        traceback.print_exc()
        # Fallback to entry price (0% P&L)
        exit_price = entry_price
        exit_time = df.iloc[entry_idx]['timestamp']
        exit_reason = f'error_fallback: {str(e)}'
        if verbose:
            print(f"🔄 Fallback: exit_price={exit_price}, exit_time={exit_time}")

    return exit_price, exit_time, exit_reason

# ------------------------------------------------------------
# 3. Impulse detection parameters (tunable)
# ------------------------------------------------------------
DEFAULT_PARAMS = {
    # Price & volume thresholds
    'range_mult': 2.0,          # (high-low) / avg_range minimum
    'vol_mult': 1.5,            # volume / avg_volume minimum
    'body_ratio': 0.6,          # body / total range minimum
    'wick_ratio': 0.5,          # rejection wick / range minimum
    'use_next_candle_confirmation': True,   # require next candle to close opposite
    # RSI filters (optional)
    'rsi_period': 14,
    'rsi_extreme': 80,          # overbought for sell, oversold for buy
    'use_rsi_divergence': True, # enable bearish/bullish divergence detection
    'divergence_lookback': 10,  # candles to check for divergence
    # Advanced filters (optional, can be turned off)
    'use_base_candle': False,   # require a consolidation candle before impulse
    'base_candle_body_ratio_max': 0.4,
    'base_candle_wick_ratio_min': 0.6,
    'use_volume_acceleration': False,   # require volume to increase over last 3 candles
    # Trade management
    'max_bars': 20,             # max bars to hold trade (same as impulse strategy param)
    'stop_loss_atr_mult': 1.2,  # stop loss as multiple of ATR
    'retracement_target': 0.7,  # 70% retracement of impulse move
}

_current_params = DEFAULT_PARAMS.copy()

def set_impulse_params(params: Dict[str, Any]) -> None:
    """Update global impulse parameters."""
    global _current_params
    _current_params.update(params)

def get_impulse_params() -> Dict[str, Any]:
    """Return current impulse parameters."""
    return _current_params.copy()

def reset_impulse_params() -> None:
    """Reset to default parameters."""
    global _current_params
    _current_params = DEFAULT_PARAMS.copy()

# ------------------------------------------------------------
# 4. Helper functions for impulse detection
# ------------------------------------------------------------
def is_base_candle(row: pd.Series, params: Dict) -> bool:
    """Check if candle qualifies as a 'base' (consolidation) before impulse."""
    high, low, open_p, close_p = row['high'], row['low'], row['open'], row['close']
    total_range = high - low
    if total_range == 0:
        return False
    body = abs(close_p - open_p)
    body_ratio = body / total_range
    wick_ratio = (total_range - body) / total_range
    return (body_ratio <= params['base_candle_body_ratio_max'] and
            wick_ratio >= params['base_candle_wick_ratio_min'])

def has_volume_acceleration(df: pd.DataFrame, i: int, lookback: int = 3) -> bool:
    """True if volume has increased for the last `lookback` candles."""
    if i < lookback:
        return False
    vol_series = df['volume'].iloc[i-lookback+1:i+1]
    return all(vol_series.iloc[t] > vol_series.iloc[t-1] for t in range(1, len(vol_series)))

def detect_bearish_divergence(price_series: pd.Series, rsi_series: pd.Series, lookback: int = 10) -> bool:
    """Regular bearish divergence: price higher high, RSI lower high."""
    if len(price_series) < lookback or len(rsi_series) < lookback:
        return False
    price = price_series.iloc[-lookback:]
    rsi = rsi_series.iloc[-lookback:]
    price_high_idx = price.idxmax()
    if price_high_idx != price.index[-1]:
        return False
    rsi_before = rsi.loc[:price_high_idx].iloc[:-1]
    if rsi_before.empty:
        return False
    rsi_high_before = rsi_before.max()
    return rsi.iloc[-1] < rsi_high_before

def detect_bullish_divergence(price_series: pd.Series, rsi_series: pd.Series, lookback: int = 10) -> bool:
    """Regular bullish divergence: price lower low, RSI higher low."""
    if len(price_series) < lookback or len(rsi_series) < lookback:
        return False
    price = price_series.iloc[-lookback:]
    rsi = rsi_series.iloc[-lookback:]
    price_low_idx = price.idxmin()
    if price_low_idx != price.index[-1]:
        return False
    rsi_before = rsi.loc[:price_low_idx].iloc[:-1]
    if rsi_before.empty:
        return False
    rsi_low_before = rsi_before.min()
    return rsi.iloc[-1] > rsi_low_before

# ------------------------------------------------------------
# 5. Core detection function (original)
# ------------------------------------------------------------
def detect_impulse(df: pd.DataFrame, i: int, row: pd.Series,
                   signal_price: float, signal_direction: str,
                   zone: float, vol_spike: bool, verbose: bool = False) -> Optional[Tuple[str, str, int, str]]:
    """
    Analyse candle at index `i` to see if it is a valid impulse setup.
    Returns (entry_type, direction, confidence, extra_info) or None.
    """
    params = _current_params
    low, high, open_p, close_p = row['low'], row['high'], row['open'], row['close']
    vol = row['volume']

    if i < 20:
        return None

    # Use precomputed rolling averages if available (from backtest_impulse), otherwise calculate
    avg_range = df['range_avg'].iloc[i] if 'range_avg' in df.columns else (df['high'].iloc[i-20:i] - df['low'].iloc[i-20:i]).mean()
    avg_volume = df['volume_avg'].iloc[i] if 'volume_avg' in df.columns else df['volume'].iloc[i-20:i].mean()
    range_ratio = (high - low) / avg_range if avg_range > 0 else 1
    vol_ratio = vol / avg_volume if avg_volume > 0 else 1
    body = abs(close_p - open_p)
    body_ratio = body / (high - low) if (high - low) > 0 else 0
    upper_wick = high - max(open_p, close_p)
    lower_wick = min(open_p, close_p) - low
    wick_ratio = max(upper_wick, lower_wick) / (high - low) if (high - low) > 0 else 0

    # Basic impulse conditions (range & volume only)
    if not (range_ratio >= params['range_mult'] and vol_ratio >= params['vol_mult']):
        return None

    impulse_up = (close_p > open_p)
    if impulse_up:
        rejection_wick_ratio = upper_wick / (high - low) if (high - low) > 0 else 0
    else:
        rejection_wick_ratio = lower_wick / (high - low) if (high - low) > 0 else 0

    # FIXED: Use OR for structure filter. Requiring body>=0.6 AND wick>=0.5 is mathematically impossible (sum > 100%)
    structure_ok = (body_ratio >= params['body_ratio']) or (rejection_wick_ratio >= params['wick_ratio'])
    if not structure_ok:
        return None

    # Base candle filter
    if params['use_base_candle'] and i >= 1:
        prev_row = df.iloc[i-1]
        if not is_base_candle(prev_row, params):
            return None

    # Volume acceleration
    if params['use_volume_acceleration'] and not has_volume_acceleration(df, i, 3):
        return None

    # Next candle confirmation
    next_ok = True
    if params['use_next_candle_confirmation'] and i + 1 < len(df):
        next_row = df.iloc[i+1]
        next_close = next_row['close']
        if impulse_up:  # sell setup
            next_ok = (next_close < min(open_p, close_p))
        else:           # buy setup
            next_ok = (next_close > max(open_p, close_p))
    if not next_ok:
        return None

    # RSI divergence and extreme
    rsi_val = None
    if params['use_rsi_divergence'] or params['rsi_extreme']:
        if 'rsi' not in df.columns:
            df['rsi'] = compute_rsi(df['close'], params['rsi_period'])
        rsi_val = df['rsi'].iloc[i]
        rsi_series = df['rsi']

    rsi_ok = True
    divergence_detected = False
    if params['use_rsi_divergence'] and i >= params['divergence_lookback']:
        price_series = df['close'].iloc[i-params['divergence_lookback']:i+1]
        rsi_window = rsi_series.iloc[i-params['divergence_lookback']:i+1]
        if impulse_up:
            if detect_bearish_divergence(price_series, rsi_window, params['divergence_lookback']):
                divergence_detected = True
        else:
            if detect_bullish_divergence(price_series, rsi_window, params['divergence_lookback']):
                divergence_detected = True
        rsi_ok = divergence_detected   # if divergence filter is on, require it

    if params['rsi_extreme'] and rsi_val is not None:
        if impulse_up and rsi_val < params['rsi_extreme']:
            rsi_ok = False
        elif not impulse_up and rsi_val > (100 - params['rsi_extreme']):
            rsi_ok = False
    if not rsi_ok:
        return None

    # All conditions satisfied – build signal
    entry_type = 'impulse'
    confidence = 60 + (20 if vol_spike else 0) + (10 if divergence_detected else 0)
    extra_info_parts = [
        f"range={range_ratio:.1f}x",
        f"vol={vol_ratio:.1f}x",
        f"body={body_ratio:.2f}",
        f"wick={rejection_wick_ratio:.2f}",
        f"next={'✓' if next_ok else '✗'}"
    ]
    if rsi_val is not None:
        extra_info_parts.append(f"RSI={rsi_val:.0f}")
        extra_info_parts.append(f"div={'✓' if divergence_detected else '✗'}")
    extra_info = " ".join(extra_info_parts)

    if signal_direction == 'resistance' and impulse_up and high >= signal_price - zone:
        direction = 'sell'
        if verbose:
            print(f"🔥 IMPULSE (sell) at i={i}: {extra_info}")
        return (entry_type, direction, confidence, extra_info)
    elif signal_direction == 'support' and not impulse_up and low <= signal_price + zone:
        direction = 'buy'
        if verbose:
            print(f"🔥 IMPULSE (buy) at i={i}: {extra_info}")
        return (entry_type, direction, confidence, extra_info)
    return None

# ------------------------------------------------------------
# 6. Backtesting on full DataFrame (original)
# ------------------------------------------------------------
def backtest_impulse(df: pd.DataFrame,
                     signal_price: float,
                     signal_direction: str,
                     signal_time_ms: int,
                     params: Optional[Dict] = None,
                     verbose: bool = False) -> Dict:
    """
    Run impulse detection over the entire DataFrame and simulate trades.
    Returns dictionary with trades list and aggregate metrics.
    """
    if params is not None:
        set_impulse_params(params)

    # Prepare DataFrame & PRECOMPUTE INDICATORS ONCE (Major speedup for grid search)
    df = df.copy()
    df['atr'] = compute_atr(df, period=14)
    df['volume_avg'] = df['volume'].rolling(window=20, min_periods=1).mean()
    df['range_avg'] = (df['high'] - df['low']).rolling(window=20, min_periods=1).mean()
    # Add RSI if needed
    if _current_params['use_rsi_divergence'] or _current_params['rsi_extreme']:
        df['rsi'] = compute_rsi(df['close'], _current_params['rsi_period'])

    buffer_ms = 5 * 60 * 1000
    start_idx = df['timestamp'].searchsorted(signal_time_ms - buffer_ms)
    if start_idx >= len(df):
        return {'trades': [], 'count': 0, 'wins': 0, 'win_rate': 0, 'total_pnl': 0, 'profit_factor': 0, 'avg_pnl': 0}
    df = df.iloc[start_idx:].reset_index(drop=True)

    atr_mean = df['atr'].mean()
    zone = max(atr_mean * 0.3, 1e-8)

    trades = []
    for i in range(1, len(df)):
        row = df.iloc[i]
        low, high, close_p = row['low'], row['high'], row['close']
        vol_spike = row['volume'] > 1.5 * row['volume_avg'] if not pd.isna(row['volume_avg']) else False

        # Touch zone detection
        if signal_direction == 'resistance':
            touch = (high >= signal_price - zone)
        else:
            touch = (low <= signal_price + zone)
        if not touch:
            continue

        # Close confirmation (use default: required for touch to be valid)
        if signal_direction == 'resistance' and close_p >= signal_price:
            continue
        if signal_direction == 'support' and close_p <= signal_price:
            continue

        # Impulse detection
        impulse_res = detect_impulse(df, i, row, signal_price, signal_direction,
                                    zone, vol_spike, verbose)
        if not impulse_res:
            continue
        entry_type, direction, confidence, extra_info = impulse_res
        entry_price = row['close']
        entry_time = row['timestamp']
        atr_val = row['atr'] if not pd.isna(row['atr']) else df['atr'].mean()
        impulse_move = (row['high'] - row['low'])
        retracement_target = _current_params['retracement_target']
        if direction == 'sell':
            stop_loss = entry_price + _current_params['stop_loss_atr_mult'] * atr_val
            tp1 = entry_price - retracement_target * impulse_move
            tp2 = entry_price - 1.0 * impulse_move
        else:  # buy
            stop_loss = entry_price - _current_params['stop_loss_atr_mult'] * atr_val
            tp1 = entry_price + retracement_target * impulse_move
            tp2 = entry_price + 1.0 * impulse_move

        exit_price, exit_time, exit_reason = simulate_trade(
            df, i, direction, stop_loss, tp1, tp2,
            max_bars=_current_params['max_bars'],
            trail_atr=1.5,  # default trail multiplier
            atr_series=df['atr'],
            trail_activation_atr=0.8,
            verbose=verbose
        )
        # Calculate P&L
        if direction == 'buy':
            pnl = (exit_price - entry_price) / entry_price * 100
        else:
            pnl = (entry_price - exit_price) / entry_price * 100
        trades.append({
            'entry_time_ms': entry_time,
            'exit_time_ms': exit_time,
            'entry_price': entry_price,
            'exit_price': exit_price,
            'direction': direction,
            'pnl': pnl,
            'confidence': confidence,
            'extra_info': extra_info,
            'exit_reason': exit_reason
        })
        if verbose:
            print(f"✅ Impulse trade: {direction} at {entry_price:.5f}, P&L={pnl:.2f}%")

    # Compute metrics
    count = len(trades)
    wins = sum(1 for t in trades if t['pnl'] > 0)
    total_pnl = sum(t['pnl'] for t in trades)
    win_rate = (wins / count * 100) if count else 0
    gross_profit = sum(t['pnl'] for t in trades if t['pnl'] > 0)
    gross_loss = abs(sum(t['pnl'] for t in trades if t['pnl'] < 0))
    profit_factor = gross_profit / gross_loss if gross_loss != 0 else float('inf')
    avg_pnl = total_pnl / count if count else 0
    return {
        'trades': trades,
        'count': count,
        'wins': wins,
        'win_rate': win_rate,
        'total_pnl': total_pnl,
        'profit_factor': profit_factor,
        'avg_pnl': avg_pnl,
    }

# ------------------------------------------------------------
# 7. Grid search and walk‑forward (original)
# ------------------------------------------------------------
def grid_search(df: pd.DataFrame,
                signal_price: float,
                signal_direction: str,
                signal_time_ms: int,
                param_grid: Dict[str, List],
                verbose: bool = False) -> pd.DataFrame:
    """
    Exhaustive grid search over parameter combinations.
    param_grid: e.g., {'range_mult': [1.5,2.0], 'vol_mult': [1.2,1.5]}
    Returns DataFrame with each combination and its metrics.
    """
    keys = list(param_grid.keys())
    results = []
    for combo in product(*param_grid.values()):
        params = dict(zip(keys, combo))
        # Skip mathematically impossible structure combinations (body + wick > 95%)
        if params.get('body_ratio', 0) + params.get('wick_ratio', 0) > 0.95:
            continue
        if verbose:
            print(f"Testing {params}")
        res = backtest_impulse(df, signal_price, signal_direction, signal_time_ms,
                               params=params, verbose=False)
        row = params.copy()
        row.update({
            'count': res['count'],
            'wins': res['wins'],
            'win_rate': res['win_rate'],
            'total_pnl': res['total_pnl'],
            'profit_factor': res['profit_factor'],
        })
        results.append(row)
    return pd.DataFrame(results)

def walk_forward(df: pd.DataFrame,
                 signal_price: float,
                 signal_direction: str,
                 signal_time_ms: int,
                 in_sample_pct: float = 0.7,
                 out_sample_pct: float = 0.3,
                 param_grid: Dict[str, List] = None,
                 verbose: bool = False) -> pd.DataFrame:
    """
    Walk‑forward split by time (percentage of total candles).
    in_sample_pct: proportion of data to use for training (e.g., 0.7)
    out_sample_pct: proportion for testing (e.g., 0.3)
    Returns DataFrame with out‑of‑sample results.
    """
    if param_grid is None:
        param_grid = {
            'range_mult': [1.5, 2.0, 2.5],
            'vol_mult': [1.2, 1.5, 1.8],
            'body_ratio': [0.4, 0.5, 0.6],
            'wick_ratio': [0.3, 0.4, 0.5],
            'use_next_candle_confirmation': [True, False],
            'use_rsi_divergence': [True, False],
        }
    df = df.copy()
    df = df.sort_values('timestamp')
    total_candles = len(df)
    in_sample_end = int(total_candles * in_sample_pct)
    if in_sample_end < 10 or total_candles - in_sample_end < 5:
        return pd.DataFrame()  # not enough data

    in_df = df.iloc[:in_sample_end]
    out_df = df.iloc[in_sample_end:]

    # Run grid search on in‑sample
    grid_res = grid_search(in_df, signal_price, signal_direction, signal_time_ms,
                           param_grid, verbose=False)
    if grid_res.empty:
        return pd.DataFrame()
    best_row = grid_res.loc[grid_res['total_pnl'].idxmax()]
    best_params = {k: best_row[k] for k in param_grid.keys()}
    # Test on out‑of‑sample
    out_res = backtest_impulse(out_df, signal_price, signal_direction, signal_time_ms,
                               params=best_params, verbose=False)
    results = pd.DataFrame([{
        'in_start': in_df['timestamp'].min(),
        'in_end': in_df['timestamp'].max(),
        'out_start': out_df['timestamp'].min(),
        'out_end': out_df['timestamp'].max(),
        'best_params': best_params,
        'out_trades': out_res['count'],
        'out_win_rate': out_res['win_rate'],
        'out_total_pnl': out_res['total_pnl'],
    }])
    return results

def walk_forward_candles(df: pd.DataFrame,
                         signal_price: float,
                         signal_direction: str,
                         signal_time_ms: int,
                         in_sample_candles: int,
                         out_sample_candles: int,
                         param_grid: Dict[str, List],
                         verbose: bool = False) -> pd.DataFrame:
    """
    Walk‑forward based on number of candles (not days).
    Splits the data into rolling windows of fixed candle length.
    """
    df = df.copy()
    total_candles = len(df)
    results = []
    current = 0
    while current + in_sample_candles + out_sample_candles <= total_candles:
        in_end = current + in_sample_candles
        out_end = in_end + out_sample_candles
        in_df = df.iloc[current:in_end]
        out_df = df.iloc[in_end:out_end]
        if in_df.empty or out_df.empty:
            break
        grid_res = grid_search(in_df, signal_price, signal_direction, signal_time_ms,
                               param_grid, verbose=False)
        if grid_res.empty:
            current = out_end
            continue
        best_row = grid_res.loc[grid_res['total_pnl'].idxmax()]
        best_params = {k: best_row[k] for k in param_grid.keys()}
        out_res = backtest_impulse(out_df, signal_price, signal_direction, signal_time_ms,
                                   params=best_params, verbose=False)
        results.append({
            'in_start': current,
            'in_end': in_end,
            'out_start': in_end,
            'out_end': out_end,
            'best_params': best_params,
            'out_trades': out_res['count'],
            'out_win_rate': out_res['win_rate'],
            'out_total_pnl': out_res['total_pnl'],
        })
        current = out_end
    return pd.DataFrame(results)

# ------------------------------------------------------------
# 8. Standalone execution (command line) – original
# ------------------------------------------------------------
if __name__ == "__main__":
    import argparse
    parser = argparse.ArgumentParser(description='Impulse detection tuner')
    parser.add_argument('--symbol', type=str, required=True, help='Symbol name')
    parser.add_argument('--timeframe', type=str, default='1', help='Timeframe (e.g., 1)')
    parser.add_argument('--grid', action='store_true', help='Run grid search')
    parser.add_argument('--walkforward', action='store_true', help='Run walk‑forward')
    args = parser.parse_args()

    data_path = f"./market_data/{args.symbol}/{args.timeframe}/data.parquet"
    if not os.path.exists(data_path):
        print(f"Data not found: {data_path}")
        exit(1)
    df = pd.read_parquet(data_path)
    print("Please run this script from the main app’s tuning UI instead.")
    # Optionally you can implement a dummy signal here.

# ============================================================================
# NEW ADDITIONS: Retracement‑based entry (keeps original code intact)
# ============================================================================

def detect_impulse_retracement(df: pd.DataFrame,
                               signal_price: float,
                               signal_direction: str,
                               signal_time_ms: int,
                               pre_buffer_minutes: int = 60,
                               verbose: bool = False) -> List[Dict]:
    """
    Enhanced impulse detection that enters on retracement (50‑70% of impulse move).
    Uses the same global parameters as the original detect_impulse.
    Returns list of trade dicts with entry/exit, pnl, and parameters log.
    """
    params = _current_params
    buffer_ms = pre_buffer_minutes * 60 * 1000
    start_idx = df['timestamp'].searchsorted(signal_time_ms - buffer_ms)
    if start_idx >= len(df):
        return []
    df = df.iloc[start_idx:].reset_index(drop=True)

    # Precompute indicators
    df['atr'] = compute_atr(df, period=14)
    df['volume_avg'] = df['volume'].rolling(20).mean()
    if params['use_rsi_divergence'] or params['rsi_extreme']:
        df['rsi'] = compute_rsi(df['close'], params['rsi_period'])

    atr_mean = df['atr'].mean()
    zone = max(atr_mean * 0.3, 1e-8)

    trades = []
    i = 1
    while i < len(df):
        row = df.iloc[i]
        low, high, open_p, close_p = row['low'], row['high'], row['open'], row['close']

        # Touch the level (within zone) and moving toward it
        if signal_direction == 'resistance':
            touch = (high >= signal_price - zone)
            moving_toward = (close_p > open_p)
        else:
            touch = (low <= signal_price + zone)
            moving_toward = (close_p < open_p)

        if not touch or not moving_toward:
            i += 1
            continue

        # Check basic impulse conditions (same as original detect_impulse)
        if i < 20:
            i += 1
            continue
        recent_ranges = df['high'].iloc[i-20:i] - df['low'].iloc[i-20:i]
        avg_range = recent_ranges.mean()
        avg_volume = df['volume'].iloc[i-20:i].mean()
        range_ratio = (high - low) / avg_range if avg_range > 0 else 1
        vol_ratio = row['volume'] / avg_volume if avg_volume > 0 else 1
        body = abs(close_p - open_p)
        body_ratio = body / (high - low) if (high - low) > 0 else 0
        impulse_up = (close_p > open_p)
        if impulse_up:
            rejection_wick_ratio = (high - max(open_p, close_p)) / (high - low) if (high - low) > 0 else 0
        else:
            rejection_wick_ratio = (min(open_p, close_p) - low) / (high - low) if (high - low) > 0 else 0

        if not (range_ratio >= params['range_mult'] and
                vol_ratio >= params['vol_mult'] and
                body_ratio >= params['body_ratio'] and
                rejection_wick_ratio >= params['wick_ratio']):
            i += 1
            continue

        # Optional strong filters (same as original)
        ok = True
        if params['use_base_candle'] and i >= 1:
            ok = is_base_candle(df.iloc[i-1], params)
        if ok and params['use_volume_acceleration'] and not has_volume_acceleration(df, i, 3):
            ok = False
        if ok and params['use_next_candle_confirmation'] and i+1 < len(df):
            next_row = df.iloc[i+1]
            if impulse_up:
                ok = (next_row['close'] < min(open_p, close_p))
            else:
                ok = (next_row['close'] > max(open_p, close_p))
        if not ok:
            i += 1
            continue

        # RSI filters
        rsi_val = None
        divergence_detected = False
        if params['use_rsi_divergence'] or params['rsi_extreme']:
            rsi_val = df['rsi'].iloc[i]
            if params['use_rsi_divergence'] and i >= params['divergence_lookback']:
                price_series = df['close'].iloc[i-params['divergence_lookback']:i+1]
                rsi_window = df['rsi'].iloc[i-params['divergence_lookback']:i+1]
                if impulse_up:
                    divergence_detected = detect_bearish_divergence(price_series, rsi_window, params['divergence_lookback'])
                else:
                    divergence_detected = detect_bullish_divergence(price_series, rsi_window, params['divergence_lookback'])
                if not divergence_detected:
                    ok = False
            if ok and params['rsi_extreme'] and rsi_val is not None:
                if impulse_up and rsi_val < params['rsi_extreme']:
                    ok = False
                elif not impulse_up and rsi_val > (100 - params['rsi_extreme']):
                    ok = False
        if not ok:
            i += 1
            continue

        # ---- Impulse found. Now wait for retracement entry ----
        impulse_high = high
        impulse_low = low
        impulse_move = impulse_high - impulse_low
        retrace_target = params.get('retracement_target', 0.7)

        entry_idx = None
        for j in range(i+1, len(df)):
            candle = df.iloc[j]
            if signal_direction == 'resistance':  # sell setup
                retrace_price = impulse_high - retrace_target * impulse_move
                if candle['close'] <= retrace_price:
                    entry_idx = j
                    break
            else:  # buy setup
                retrace_price = impulse_low + retrace_target * impulse_move
                if candle['close'] >= retrace_price:
                    entry_idx = j
                    break

        if entry_idx is None:
            i += 1
            continue

        entry_price = df.iloc[entry_idx]['close']
        entry_time = df.iloc[entry_idx]['timestamp']
        atr_val = df.iloc[entry_idx]['atr'] if not pd.isna(df.iloc[entry_idx]['atr']) else atr_mean

        stop_loss_mult = params.get('stop_loss_atr_mult', 1.2)
        if signal_direction == 'resistance':  # sell
            stop_loss = entry_price + stop_loss_mult * atr_val
            tp1 = entry_price - 1.5 * atr_val   # conservative first target
            tp2 = entry_price - 2.5 * atr_val
            direction = 'sell'
        else:
            stop_loss = entry_price - stop_loss_mult * atr_val
            tp1 = entry_price + 1.5 * atr_val
            tp2 = entry_price + 2.5 * atr_val
            direction = 'buy'

        exit_price, exit_time, exit_reason = simulate_trade(
            df, entry_idx, direction, stop_loss, tp1, tp2,
            max_bars=params.get('max_bars', 20),
            trail_atr=1.5,
            atr_series=df['atr'],
            trail_activation_atr=0.8,
            verbose=verbose
        )

        pnl = ((exit_price - entry_price) / entry_price * 100) if direction == 'buy' else ((entry_price - exit_price) / entry_price * 100)

        # Build parameters log (similar to original extra_info but richer)
        param_log = (f"range={range_ratio:.1f}x vol={vol_ratio:.1f}x body={body_ratio:.2f} wick={rejection_wick_ratio:.2f} "
                     f"retrace={retrace_target:.0%} stop={stop_loss_mult:.1f}atr")
        if params['use_next_candle_confirmation']:
            param_log += " next=✓"
        if params['use_base_candle']:
            param_log += " base=✓"
        if params['use_volume_acceleration']:
            param_log += " accel=✓"
        if params['use_rsi_divergence']:
            param_log += f" div={'✓' if divergence_detected else '✗'}"
        if params['rsi_extreme'] and rsi_val is not None:
            param_log += f" RSI={rsi_val:.0f}"

        trades.append({
            'entry_time_ms': entry_time,
            'exit_time_ms': exit_time,
            'entry_price': entry_price,
            'exit_price': exit_price,
            'direction': direction,
            'pnl': pnl,
            'confidence': 60 + (20 if vol_ratio > 1.8 else 0) + (10 if divergence_detected else 0),
            'parameters_log': param_log,
            'exit_reason': exit_reason
        })

        # Skip ahead to avoid overlapping trades
        i = entry_idx + 1

    return trades

def backtest_impulse_retracement(df: pd.DataFrame,
                                 signal_price: float,
                                 signal_direction: str,
                                 signal_time_ms: int,
                                 pre_buffer_minutes: int = 60) -> Dict:
    """
    Backtest wrapper for retracement‑based impulse detection.
    Returns same metrics as backtest_impulse.
    """
    trades = detect_impulse_retracement(df, signal_price, signal_direction, signal_time_ms,
                                        pre_buffer_minutes, verbose=False)
    count = len(trades)
    if count == 0:
        return {'trades': [], 'count': 0, 'wins': 0, 'win_rate': 0, 'total_pnl': 0, 'profit_factor': 0, 'avg_pnl': 0}
    wins = sum(1 for t in trades if t['pnl'] > 0)
    total_pnl = sum(t['pnl'] for t in trades)
    gross_profit = sum(t['pnl'] for t in trades if t['pnl'] > 0)
    gross_loss = abs(sum(t['pnl'] for t in trades if t['pnl'] < 0))
    profit_factor = gross_profit / gross_loss if gross_loss != 0 else float('inf')
    avg_pnl = total_pnl / count if count else 0
    return {
        'trades': trades,
        'count': count,
        'wins': wins,
        'win_rate': wins / count * 100,
        'total_pnl': total_pnl,
        'profit_factor': profit_factor,
        'avg_pnl': avg_pnl,
    }