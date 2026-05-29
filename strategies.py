# strategies.py – Complete professional version with independent exit per signal
import pandas as pd
import numpy as np

# ------------------------------------------------------------
# 1. Core indicators
# ------------------------------------------------------------
def compute_rsi(series, period=14):
    """Calculate RSI for a price series."""
    delta = series.diff()
    gain = delta.clip(lower=0)
    loss = -delta.clip(upper=0)
    avg_gain = gain.rolling(window=period, min_periods=period).mean()
    avg_loss = loss.rolling(window=period, min_periods=period).mean()
    rs = avg_gain / avg_loss
    rsi = 100 - (100 / (1 + rs))
    return rsi

def compute_atr(df, period=14):
    """Calculate Average True Range."""
    high_low = df['high'] - df['low']
    high_close = abs(df['high'] - df['close'].shift())
    low_close = abs(df['low'] - df['close'].shift())
    tr = pd.concat([high_low, high_close, low_close], axis=1).max(axis=1)
    atr = tr.rolling(window=period).mean()
    return atr

def compute_obv(df):
    """On‑Balance Volume."""
    obv = (np.sign(df['close'].diff()) * df['volume']).fillna(0).cumsum()
    return obv

def compute_force_index(df, period=13):
    """Elder's Force Index = volume * (close - previous close)"""
    fi = df['volume'] * (df['close'] - df['close'].shift(1))
    return fi.rolling(window=period).mean()

def bollinger_bands(df, period=20, std_dev=2):
    """Calculate Bollinger Bands (middle, upper, lower)"""
    middle = df['close'].rolling(window=period).mean()
    std = df['close'].rolling(window=period).std()
    upper = middle + (std * std_dev)
    lower = middle - (std * std_dev)
    return upper, lower

# ------------------------------------------------------------
# 2. Divergence detection
# ------------------------------------------------------------
def detect_divergence(price_series, rsi_series, lookback=10):
    """Regular and hidden divergence detection."""
    if len(price_series) < lookback or len(rsi_series) < lookback:
        return None
    price = price_series.iloc[-lookback:]
    rsi = rsi_series.iloc[-lookback:]
    # Regular bullish
    if price.idxmin() == price.index[-1] and rsi.idxmin() != rsi.index[-1]:
        if price.min() < price.iloc[:-1].min() and rsi.min() > rsi.iloc[:-1].min():
            return 'regular_bullish'
    # Regular bearish
    if price.idxmax() == price.index[-1] and rsi.idxmax() != rsi.index[-1]:
        if price.max() > price.iloc[:-1].max() and rsi.max() < rsi.iloc[:-1].max():
            return 'regular_bearish'
    # Hidden bullish
    if price.idxmin() != price.index[-1] and rsi.idxmin() == rsi.index[-1]:
        if price.min() > price.iloc[:-1].min() and rsi.min() < rsi.iloc[:-1].min():
            return 'hidden_bullish'
    # Hidden bearish
    if price.idxmax() != price.index[-1] and rsi.idxmax() == rsi.index[-1]:
        if price.max() < price.iloc[:-1].max() and rsi.max() > rsi.iloc[:-1].max():
            return 'hidden_bearish'
    return None

def obv_divergence(price_series, obv_series, lookback=10):
    """Return 'bullish' or 'bearish' divergence between price and OBV."""
    if len(price_series) < lookback or len(obv_series) < lookback:
        return None
    price = price_series.iloc[-lookback:]
    obv = obv_series.iloc[-lookback:]
    # Bullish: price lower low, OBV higher low
    if price.idxmin() == price.index[-1] and obv.idxmin() != obv.index[-1]:
        if price.min() < price.iloc[:-1].min() and obv.min() > obv.iloc[:-1].min():
            return 'bullish'
    # Bearish: price higher high, OBV lower high
    if price.idxmax() == price.index[-1] and obv.idxmax() != obv.index[-1]:
        if price.max() > price.iloc[:-1].max() and obv.max() < obv.iloc[:-1].max():
            return 'bearish'
    return None

# ------------------------------------------------------------
# 3. Candlestick patterns
# ------------------------------------------------------------
def is_engulfing(prev_row, row):
    prev_bearish = prev_row['close'] < prev_row['open']
    curr_bullish = row['close'] > row['open']
    if prev_bearish and curr_bullish:
        if row['close'] > prev_row['open'] and row['open'] < prev_row['close']:
            return 'bullish_engulfing'
    prev_bullish = prev_row['close'] > prev_row['open']
    curr_bearish = row['close'] < row['open']
    if prev_bullish and curr_bearish:
        if row['open'] > prev_row['close'] and row['close'] < prev_row['open']:
            return 'bearish_engulfing'
    return None

def is_pin_bar(row):
    body = abs(row['close'] - row['open'])
    high, low, open_p, close_p = row['high'], row['low'], row['open'], row['close']
    upper_wick = high - max(open_p, close_p)
    lower_wick = min(open_p, close_p) - low
    total_range = high - low
    if total_range == 0:
        return False, False
    body_ratio = body / total_range
    is_upper_pin = (upper_wick > 2 * body) and (upper_wick > 2 * lower_wick) and (body_ratio < 0.3)
    is_lower_pin = (lower_wick > 2 * body) and (lower_wick > 2 * upper_wick) and (body_ratio < 0.3)
    return is_upper_pin, is_lower_pin

def is_shooting_star(row):
    body = abs(row['close'] - row['open'])
    upper_wick = row['high'] - max(row['open'], row['close'])
    lower_wick = min(row['open'], row['close']) - row['low']
    total_range = row['high'] - row['low']
    if total_range == 0:
        return False
    return (body / total_range < 0.3) and (upper_wick > 2 * body) and (lower_wick < 0.3 * body)

def is_hammer(row):
    body = abs(row['close'] - row['open'])
    upper_wick = row['high'] - max(row['open'], row['close'])
    lower_wick = min(row['open'], row['close']) - row['low']
    total_range = row['high'] - row['low']
    if total_range == 0:
        return False
    return (body / total_range < 0.3) and (lower_wick > 2 * body) and (upper_wick < 0.3 * body)

def is_doji(row, tolerance=0.001):
    return abs(row['close'] - row['open']) <= tolerance * row['close']

def is_inside_bar(row, prev_row):
    return row['high'] <= prev_row['high'] and row['low'] >= prev_row['low']

# ------------------------------------------------------------
# 4. Volume enhancements (optional)
# ------------------------------------------------------------
def compute_volume_profile(df, lookback=200):
    """Compute High Volume Nodes (HVN) and Low Volume Nodes (LVN)."""
    if len(df) < lookback:
        lookback = len(df)
    nbins = max(50, int(lookback / 4))
    bins = np.linspace(df['low'].min(), df['high'].max(), nbins)
    volume_profile = np.zeros(nbins-1)
    for i in range(len(df) - lookback, len(df)):
        price = df['close'].iloc[i]
        vol = df['volume'].iloc[i]
        idx = np.digitize(price, bins) - 1
        if 0 <= idx < len(volume_profile):
            volume_profile[idx] += vol
    mean_vol = np.mean(volume_profile)
    hvns = [bins[i] for i, v in enumerate(volume_profile) if v > mean_vol * 1.5]
    lvns = [bins[i] for i, v in enumerate(volume_profile) if v < mean_vol * 0.5 and v > 0]
    return hvns, lvns

def compute_volume_delta(df):
    """Calculate Volume Delta (buying volume - selling volume per candle)."""
    delta = (df['volume'] * (df['close'] > df['open']).astype(int) -
             df['volume'] * (df['close'] < df['open']).astype(int))
    return delta

def detect_absorption(df, level, idx, direction):
    """Detect absorption: heavy volume with little price movement."""
    vol_spike = df['volume'].iloc[idx] > 1.5 * df['volume_avg'].iloc[idx]
    if not vol_spike:
        return False
    delta = compute_volume_delta(df)
    # For support (buy) absorption: price rises but delta falls (selling pressure absorbed)
    if direction == 'buy':
        price_rose = df['close'].iloc[idx] > df['close'].iloc[idx-2]
        delta_fell = delta.iloc[idx] < delta.iloc[idx-2]
        return price_rose and delta_fell
    else:  # sell
        price_fell = df['close'].iloc[idx] < df['close'].iloc[idx-2]
        delta_rose = delta.iloc[idx] > delta.iloc[idx-2]
        return price_fell and delta_rose

def compute_klinger_oscillator(df, short=34, long=55, signal=13):
    """Calculate Klinger Volume Oscillator and its signal line."""
    high, low, close, volume = df['high'], df['low'], df['close'], df['volume']
    trend = (close - close.shift(1)).apply(lambda x: 1 if x > 0 else (-1 if x < 0 else 0))
    range_r = high - low
    force = volume * abs(close.diff()) / (range_r + 1e-8)
    kvo = force.ewm(span=short, adjust=False).mean() - force.ewm(span=long, adjust=False).mean()
    signal_line = kvo.ewm(span=signal, adjust=False).mean()
    return kvo, signal_line

# ------------------------------------------------------------
# 5. Strategy parameters per type (tunable)
# ------------------------------------------------------------
STRATEGY_PARAMS = {
    'bounce': {
        'stop_loss_mult': 1.5,
        'tp1_mult': 1.5,
        'tp2_mult': 2.5,
        'trail_mult': 1.5,
        'max_bars': 15,
        'trail_activation_mult': 0.75,
        'min_confidence': 30,
    },
    'retest': {
        'stop_loss_mult': 2.0,
        'tp1_mult': 2.0,
        'tp2_mult': 3.5,
        'trail_mult': 2.0,
        'max_bars': 20,
        'trail_activation_mult': 1.0,
        'min_confidence': 30,
    },
    'momentum': {
        'stop_loss_mult': 1.0,
        'tp1_mult': 4.0,
        'tp2_mult': 4.0,
        'trail_mult': 2.5,
        'max_bars': 25,
        'trail_activation_mult': 1.0,
        'min_confidence': 40,
    },
    'impulse': {
        'stop_loss_mult': 1.2,
        'tp1_mult': 2.0,
        'tp2_mult': 3.0,
        'trail_mult': 1.5,
        'max_bars': 20,
        'trail_activation_mult': 0.8,
        'min_confidence': 40,
    }
}

# Impulse detection constants (research‑based) – kept for reference but new tunable parameters inside detect_strategies override them
IMPULSE_RANGE_MULT = 3.0      # (unused – see tunable params inside detect_strategies)
IMPULSE_VOL_MULT = 1.5
IMPULSE_BODY_RATIO = 0.7
EXHAUSTION_WICK_RATIO = 0.67
RETRACEMENT_TARGET = 0.7

# ------------------------------------------------------------
# 6. Professional exit simulation with partial take profits and trailing stop
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
                    ts_str = pd.to_datetime(exit_time, unit='ms', utc=True).strftime('%Y-%m-%d %H:%M:%S UTC')
                    print(f"✅ Exit at j={j}, reason={exit_reason}, price={exit_price:.5f}, time={ts_str}")
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
            ts_str = pd.to_datetime(exit_time, unit='ms', utc=True).strftime('%Y-%m-%d %H:%M:%S UTC')
            print(f"🔄 Fallback: exit_price={exit_price}, exit_time={ts_str}")

    return exit_price, exit_time, exit_reason

# ------------------------------------------------------------
# 7. Main detection function (all improvements integrated)
# ------------------------------------------------------------
def detect_strategies(df, signal_price, signal_direction, signal_time_ms,
                      use_close_confirmation=True,
                      use_second_touch=False,
                      use_obv_divergence=False,
                      use_force_index=False,
                      use_rsi_extreme=False,
                      use_ma_slope=False,
                      use_bollinger_bands=False,
                      use_hvn_lvn=False,
                      use_absorption=False,
                      use_cvd=False,
                      use_klinger=False,
                      zone_atr_mult=0.3,
                      verbose=False):
    """
    Enhanced signal detection with fixed retest direction, waiting period, rejection confirmation,
    momentum filters, optional volume enhancements, AND a remaining bars check to ensure each
    signal has enough data after entry for a meaningful exit.
    Returns list of signal dicts.
    """
    if df.empty:
        return []
    df = df.copy()
    df['rsi'] = compute_rsi(df['close'])
    df['atr'] = compute_atr(df, period=14)
    df['volume_avg'] = df['volume'].rolling(window=20).mean()

    # Optional indicators
    if use_obv_divergence:
        df['obv'] = compute_obv(df)
    if use_force_index:
        df['force_index'] = compute_force_index(df)
    if use_bollinger_bands:
        upper_bb, lower_bb = bollinger_bands(df)
        df['bb_upper'] = upper_bb
        df['bb_lower'] = lower_bb
    if use_ma_slope:
        df['ema20'] = df['close'].ewm(span=20, adjust=False).mean()
    if use_hvn_lvn:
        hvns, lvns = compute_volume_profile(df)
    else:
        hvns, lvns = [], []
    if use_cvd or use_absorption:
        df['delta'] = compute_volume_delta(df)
    if use_klinger:
        df['kvo'], df['kvo_signal'] = compute_klinger_oscillator(df)

    atr_mean = df['atr'].mean()
    zone = max(atr_mean * zone_atr_mult, 1e-8)

    # ---------- Impulse tunable parameters (adjust here) ----------
    impulse_range_mult = 2.0      # Candle range ≥ this × average range (lower = more sensitive)
    impulse_vol_mult = 1.2        # Volume ≥ this × average volume
    impulse_body_ratio = 0.5      # Body ≥ this fraction of total range (0.5 = 50%)
    exhaustion_wick_ratio = 0.5   # Wick ≥ this fraction of total range (for rejection)
    use_next_candle_confirmation = False   # True = stricter, False = more signals
    # -------------------------------------------------------------

    buffer_ms = 5 * 60 * 1000
    start_idx = df['timestamp'].searchsorted(signal_time_ms - buffer_ms)
    if start_idx >= len(df):
        return []
    df = df.iloc[start_idx:].reset_index(drop=True)

    last_touch_info = None
    breakout_idx = None          # index of first breakout candle (close beyond level)
    signals = []

    for i in range(1, len(df)):
        row = df.iloc[i]
        low, high, open_p, close_p = row['low'], row['high'], row['open'], row['close']

        # Touch detection with zone
        if signal_direction == 'resistance':
            touch = (high >= signal_price - zone)
        else:
            touch = (low <= signal_price + zone)
        if not touch:
            continue

        if verbose:
            ts_str = pd.to_datetime(row['timestamp'], unit='ms', utc=True).strftime('%Y-%m-%d %H:%M:%S UTC')
            print(f"🔔 TOUCH at i={i}, time={ts_str}, close={close_p:.4f}, high={high:.4f}, low={low:.4f}")

        # Close confirmation (optional)
        if use_close_confirmation:
            if signal_direction == 'resistance' and close_p >= signal_price:
                continue
            if signal_direction == 'support' and close_p <= signal_price:
                continue

        # Candlestick patterns
        pattern = None
        engulf = is_engulfing(df.iloc[i-1], row)
        if engulf:
            pattern = engulf
        else:
            is_upin, is_lpin = is_pin_bar(row)
            if is_upin or is_lpin:
                pattern = 'upper_pin' if is_upin else 'lower_pin'
            elif is_shooting_star(row):
                pattern = 'shooting_star'
            elif is_hammer(row):
                pattern = 'hammer'
            elif is_doji(row):
                pattern = 'doji'
            elif is_inside_bar(row, df.iloc[i-1]):
                pattern = 'inside_bar'

        vol_spike = row['volume'] > 1.5 * row['volume_avg'] if not pd.isna(row['volume_avg']) else False
        if verbose:
            print(f"   pattern={pattern}, vol_spike={vol_spike}")

        # RSI divergence
        rsi_div = None
        if i >= 10:
            price_series = df['close'].iloc[i-10:i+1]
            rsi_series = df['rsi'].iloc[i-10:i+1]
            rsi_div = detect_divergence(price_series, rsi_series)

        # OBV divergence (optional)
        obv_div = None
        if use_obv_divergence and i >= 10:
            price_series = df['close'].iloc[i-10:i+1]
            obv_series = df['obv'].iloc[i-10:i+1]
            obv_div = obv_divergence(price_series, obv_series)

        # Force Index (optional)
        force_ok = False
        if use_force_index and i >= 13:
            fi_val = df['force_index'].iloc[i]
            fi_std = df['force_index'].std()
            if signal_direction == 'resistance' and fi_val < 0 and abs(fi_val) > 2 * fi_std:
                force_ok = True
            elif signal_direction == 'support' and fi_val > 0 and fi_val > 2 * fi_std:
                force_ok = True

        # RSI extreme filter (optional)
        rsi_extreme_ok = True
        if use_rsi_extreme:
            if signal_direction == 'resistance' and df['rsi'].iloc[i] < 60:
                rsi_extreme_ok = False
            if signal_direction == 'support' and df['rsi'].iloc[i] > 40:
                rsi_extreme_ok = False

        # Moving average slope (optional)
        ma_slope_ok = True
        if use_ma_slope and i >= 20:
            ema_slope = df['ema20'].iloc[i] - df['ema20'].iloc[i-5]
            if signal_direction == 'resistance' and ema_slope > 0:
                ma_slope_ok = False
            if signal_direction == 'support' and ema_slope < 0:
                ma_slope_ok = False

        # Bollinger Band touch (optional)
        bb_ok = True
        if use_bollinger_bands and 'bb_upper' in df.columns:
            if signal_direction == 'resistance':
                bb_ok = (row['high'] >= df['bb_upper'].iloc[i])
            else:
                bb_ok = (row['low'] <= df['bb_lower'].iloc[i])

        # Breakout detection (first candle closing beyond the level)
        if breakout_idx is None:
            if signal_direction == 'resistance' and close_p > signal_price:
                breakout_idx = i
            elif signal_direction == 'support' and close_p < signal_price:
                breakout_idx = i

        breakout_before = (breakout_idx is not None and breakout_idx < i)

        # Second touch qualification (optional)
        second_touch_qualified = False
        if use_second_touch and last_touch_info is not None:
            if signal_direction == 'resistance':
                moved_away = (last_touch_info['price'] - df.iloc[last_touch_info['idx']]['low']) >= 0.5 * atr_mean
            else:
                moved_away = (df.iloc[last_touch_info['idx']]['high'] - last_touch_info['price']) >= 0.5 * atr_mean
            if moved_away:
                second_touch_qualified = True
        if use_second_touch and not second_touch_qualified:
            last_touch_info = {'idx': i, 'price': row['close']}
            continue

        # ------------------------------
        # 1. Bounce detection (no prior breakout)
        # ------------------------------
        entry_type = None
        direction = None
        confidence = 0

        if not breakout_before:
            if signal_direction == 'resistance':
                if pattern in ['bearish_engulfing', 'shooting_star', 'upper_pin']:
                    entry_type = 'bounce'
                    direction = 'sell'
                    confidence += 40
            else:
                if pattern in ['bullish_engulfing', 'hammer', 'lower_pin']:
                    entry_type = 'bounce'
                    direction = 'buy'
                    confidence += 40
            if vol_spike:
                confidence += 20
            if rsi_div in ['regular_bearish', 'regular_bullish']:
                confidence += 30
            if obv_div == ('bearish' if signal_direction == 'resistance' else 'bullish'):
                confidence += 20
            if force_ok:
                confidence += 15
            if not rsi_extreme_ok or not ma_slope_ok or not bb_ok:
                confidence = 0
            if verbose and entry_type:
                print(f"   🔥 BOUNCE candidate: {entry_type} {direction}, confidence={confidence}")

        # ------------------------------
        # 2. Retest detection (after breakout, waiting period, rejection confirmation)
        # ------------------------------
        if not entry_type and breakout_before and breakout_idx is not None:
            wait_bars = i - breakout_idx
            if wait_bars >= 2:
                retest_confirmed = False
                if signal_direction == 'resistance':
                    if low <= signal_price <= high and close_p > signal_price:
                        retest_confirmed = True
                    if not retest_confirmed and pattern in ['bullish_engulfing', 'hammer', 'lower_pin']:
                        retest_confirmed = True
                else:
                    if low <= signal_price <= high and close_p < signal_price:
                        retest_confirmed = True
                    if not retest_confirmed and pattern in ['bearish_engulfing', 'shooting_star', 'upper_pin']:
                        retest_confirmed = True

                if retest_confirmed:
                    entry_type = 'retest'
                    direction = 'buy' if signal_direction == 'resistance' else 'sell'
                    confidence = 40
                    if vol_spike:
                        confidence += 20
                    if rsi_div in ['hidden_bearish', 'hidden_bullish']:
                        confidence += 20
                    if obv_div == ('bearish' if signal_direction == 'resistance' else 'bullish'):
                        confidence += 20
                    if not ma_slope_ok:
                        confidence = 0
                    if use_hvn_lvn:
                        if signal_direction == 'resistance' and any(abs(signal_price - h) < zone for h in hvns):
                            confidence += 15
                        elif signal_direction == 'support' and any(abs(signal_price - l) < zone for l in lvns):
                            confidence += 15
                    if use_absorption and detect_absorption(df, signal_price, i, direction):
                        confidence += 20
                    if verbose and entry_type:
                        print(f"   🔥 RETEST candidate: {entry_type} {direction}, confidence={confidence}")

        # ------------------------------
        # 3. Momentum detection (breakout with volume and filters)
        # ------------------------------
        if not entry_type:
            is_breakout = False
            if signal_direction == 'resistance' and close_p > signal_price:
                is_breakout = True
            elif signal_direction == 'support' and close_p < signal_price:
                is_breakout = True

            if is_breakout and vol_spike:
                momentum_ok = True
                atr_val = row['atr'] if not pd.isna(row['atr']) else df['atr'].mean()
                if signal_direction == 'resistance' and close_p < signal_price + 0.3 * atr_val:
                    momentum_ok = False
                elif signal_direction == 'support' and close_p > signal_price - 0.3 * atr_val:
                    momentum_ok = False

                if momentum_ok and use_rsi_extreme:
                    if signal_direction == 'resistance' and row['rsi'] < 50:
                        momentum_ok = False
                    if signal_direction == 'support' and row['rsi'] > 50:
                        momentum_ok = False

                if momentum_ok and use_ma_slope and i >= 20:
                    ema_slope = df['ema20'].iloc[i] - df['ema20'].iloc[i-5]
                    if signal_direction == 'resistance' and ema_slope < 0:
                        momentum_ok = False
                    if signal_direction == 'support' and ema_slope > 0:
                        momentum_ok = False

                if momentum_ok and use_bollinger_bands and 'bb_upper' in df.columns:
                    if signal_direction == 'resistance' and close_p < df['bb_upper'].iloc[i] * 0.98:
                        momentum_ok = False
                    if signal_direction == 'support' and close_p > df['bb_lower'].iloc[i] * 1.02:
                        momentum_ok = False

                if momentum_ok and use_cvd and i >= 10:
                    cvd_slope = df['delta'].iloc[i] - df['delta'].iloc[i-5]
                    if (signal_direction == 'resistance' and cvd_slope < 0) or (signal_direction == 'support' and cvd_slope > 0):
                        momentum_ok = False
                    else:
                        confidence += 15

                if momentum_ok and use_klinger and i >= 13:
                    if (signal_direction == 'resistance' and df['kvo'].iloc[i] > df['kvo_signal'].iloc[i]) or \
                       (signal_direction == 'support' and df['kvo'].iloc[i] < df['kvo_signal'].iloc[i]):
                        momentum_ok = False
                    else:
                        confidence += 20

                if momentum_ok:
                    entry_type = 'momentum'
                    direction = 'buy' if signal_direction == 'resistance' else 'sell'
                    confidence = 50 + (20 if vol_spike else 0) + (20 if rsi_div and 'regular' in rsi_div else 0)
                    if i > 1:
                        if signal_direction == 'resistance' and df.iloc[i-1]['close'] > signal_price:
                            confidence += 15
                        elif signal_direction == 'support' and df.iloc[i-1]['close'] < signal_price:
                            confidence += 15
                    if verbose and entry_type:
                        print(f"   🔥 MOMENTUM candidate: {entry_type} {direction}, confidence={confidence}")

        # ------------------------------
        # 3.5 Impulse detection (improved with tunable parameters and detailed logging)
        # ------------------------------
        if not entry_type and i >= 20:
            # Compute rolling averages for impulse detection
            recent_ranges = df['high'].iloc[i-20:i] - df['low'].iloc[i-20:i]
            avg_range = recent_ranges.mean()
            avg_volume = df['volume'].iloc[i-20:i].mean()
            range_ratio = (high - low) / avg_range if avg_range > 0 else 1
            vol_ratio = row['volume'] / avg_volume if avg_volume > 0 else 1
            body = abs(close_p - open_p)
            body_ratio = body / (high - low) if (high - low) > 0 else 0
            upper_wick = high - max(open_p, close_p)
            lower_wick = min(open_p, close_p) - low
            wick_ratio = max(upper_wick, lower_wick) / (high - low) if (high - low) > 0 else 0

            # Individual condition checks (using tunable parameters)
            range_ok = range_ratio >= impulse_range_mult
            vol_ok = vol_ratio >= impulse_vol_mult
            body_ok = body_ratio >= impulse_body_ratio
            wick_ok = wick_ratio >= exhaustion_wick_ratio
            is_impulse = range_ok and vol_ok and body_ok

            if verbose:
                print(f"   🔍 IMPULSE CHECK: range={range_ratio:.2f} (need {impulse_range_mult}) {range_ok}, "
                      f"vol={vol_ratio:.2f} (need {impulse_vol_mult}) {vol_ok}, "
                      f"body={body_ratio:.2f} (need {impulse_body_ratio}) {body_ok}, "
                      f"wick={wick_ratio:.2f} (need {exhaustion_wick_ratio}) {wick_ok}")

            if is_impulse:
                # Determine impulse direction
                impulse_up = (close_p > open_p)

                # For resistance (sell reversal)
                if signal_direction == 'resistance' and impulse_up and high >= signal_price - zone:
                    if wick_ok:
                        next_ok = True
                        if use_next_candle_confirmation and i + 1 < len(df):
                            next_row = df.iloc[i+1]
                            next_close = next_row['close']
                            next_ok = (next_close < min(open_p, close_p))
                            if verbose:
                                print(f"      Next candle close={next_close:.5f}, need < {min(open_p, close_p):.5f} -> {next_ok}")
                        if next_ok:
                            entry_type = 'impulse'
                            direction = 'sell'
                            confidence = 60 + (20 if vol_spike else 0)
                            extra_info = (f"Impulse sell: range={range_ratio:.1f}x vol={vol_ratio:.1f}x "
                                          f"body={body_ratio:.2f} wick={wick_ratio:.2f}")
                            if verbose:
                                print(f"🔥 IMPULSE (sell) at i={i}: {extra_info}")

                # For support (buy reversal)
                elif signal_direction == 'support' and not impulse_up and low <= signal_price + zone:
                    if wick_ok:
                        next_ok = True
                        if use_next_candle_confirmation and i + 1 < len(df):
                            next_row = df.iloc[i+1]
                            next_close = next_row['close']
                            next_ok = (next_close > max(open_p, close_p))
                            if verbose:
                                print(f"      Next candle close={next_close:.5f}, need > {max(open_p, close_p):.5f} -> {next_ok}")
                        if next_ok:
                            entry_type = 'impulse'
                            direction = 'buy'
                            confidence = 60 + (20 if vol_spike else 0)
                            extra_info = (f"Impulse buy: range={range_ratio:.1f}x vol={vol_ratio:.1f}x "
                                          f"body={body_ratio:.2f} wick={wick_ratio:.2f}")
                            if verbose:
                                print(f"🔥 IMPULSE (buy) at i={i}: {extra_info}")

        # ------------------------------
        # 4. Signal generation and exit simulation
        # ------------------------------
        if entry_type and confidence >= STRATEGY_PARAMS[entry_type]['min_confidence']:
            remaining_bars = len(df) - i - 1
            min_needed = max(5, STRATEGY_PARAMS[entry_type]['max_bars'] // 2)
            if remaining_bars < min_needed:
                if verbose:
                    print(f"   ❌ REJECTED {entry_type}: only {remaining_bars} bars left after entry, need {min_needed}")
                continue

            entry_price = row['close']
            entry_time = row['timestamp']
            atr_val = row['atr'] if not pd.isna(row['atr']) else df['atr'].mean()
            params = STRATEGY_PARAMS[entry_type].copy()
            params['atr_val'] = atr_val

            # For impulse, compute TP/SL based on 70% retracement of the impulse move
            if entry_type == 'impulse':
                impulse_move = (high - low)
                if direction == 'sell':
                    stop_loss = entry_price + params['stop_loss_mult'] * atr_val
                    tp1 = entry_price - RETRACEMENT_TARGET * impulse_move
                    tp2 = entry_price - 1.0 * impulse_move
                else:  # buy
                    stop_loss = entry_price - params['stop_loss_mult'] * atr_val
                    tp1 = entry_price + RETRACEMENT_TARGET * impulse_move
                    tp2 = entry_price + 1.0 * impulse_move
            else:
                # Standard TP/SL calculation for other strategies
                if direction == 'buy':
                    stop_loss = entry_price - params['stop_loss_mult'] * atr_val
                    if entry_type == 'momentum':
                        tp1 = 1e12
                        tp2 = 1e12
                    else:
                        tp1 = entry_price + params['tp1_mult'] * atr_val
                        tp2 = entry_price + params['tp2_mult'] * atr_val
                else:
                    stop_loss = entry_price + params['stop_loss_mult'] * atr_val
                    if entry_type == 'momentum':
                        tp1 = -1e12
                        tp2 = -1e12
                    else:
                        tp1 = entry_price - params['tp1_mult'] * atr_val
                        tp2 = entry_price - params['tp2_mult'] * atr_val

            # Simulate exit
            exit_price, exit_time, exit_reason = simulate_trade(
                df, i, direction, stop_loss, tp1, tp2,
                max_bars=params['max_bars'],
                trail_atr=params['trail_mult'],
                atr_series=df['atr'],
                trail_activation_atr=params['trail_activation_mult'],
                verbose=verbose
            )

            if verbose:
                ts_str = pd.to_datetime(entry_time, unit='ms', utc=True).strftime('%Y-%m-%d %H:%M:%S UTC')
                print(f"✅ Adding {entry_type} {direction} at {ts_str} price={entry_price:.4f}, conf={confidence}, exit_reason={exit_reason}")

            signal_dict = {
                'type': entry_type,
                'direction': direction,
                'entry_price': entry_price,
                'entry_time_ms': entry_time,
                'exit_price': exit_price,
                'exit_time_ms': exit_time,
                'exit_reason': exit_reason,
                'confidence': min(confidence, 100),
                'pattern': pattern,
                'divergence': rsi_div,
                'obv_divergence': obv_div,
                'volume_spike': vol_spike,
                'params': params
            }
            # Add extra_info if impulse (for logging)
            if entry_type == 'impulse' and 'extra_info' in locals():
                signal_dict['extra_info'] = extra_info
            signals.append(signal_dict)

        else:
            if verbose and entry_type:
                min_conf = STRATEGY_PARAMS[entry_type]['min_confidence']
                print(f"   ❌ REJECTED {entry_type}: confidence={confidence} < {min_conf}")

        # Update last touch info for second touch detection
        if touch:
            last_touch_info = {'idx': i, 'price': row['close']}

    return signals