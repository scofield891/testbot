import os
import sys
import time
import json
import re
import math
import random
import signal
import asyncio
import threading
import logging
import hashlib
from dataclasses import dataclass, field
from typing import Optional, Dict, Tuple, List
from datetime import datetime, timedelta
from zoneinfo import ZoneInfo

import numpy as np
import pandas as pd
import ccxt

import telegram
from telegram.request import HTTPXRequest
from telegram.error import RetryAfter, TimedOut

from logging.handlers import RotatingFileHandler
from collections import Counter

# ================== ENV ==================
BOT_TOKEN = os.getenv("BOT_TOKEN")         # Telegram bot token
CHAT_ID   = os.getenv("CHAT_ID")           # Telegram chat id (channel id ok)

# ================== Genel Ayarlar ==================
TEST_MODE = False
STARTUP_MSG_ENABLED = True
VERBOSE_LOG = True

# Zaman dilimi (TCE gate için)
DEFAULT_TZ = os.getenv("BOT_TZ", "Europe/Istanbul")

# ================== Mimari / Performans ==================
MAX_CONCURRENT_FETCHES = int(os.getenv("MAX_CONCURRENT_FETCHES", "4"))
RATE_LIMIT_MS          = int(os.getenv("RATE_LIMIT_MS", "200"))
N_SHARDS               = int(os.getenv("N_SHARDS", "5"))
BATCH_SIZE             = int(os.getenv("BATCH_SIZE", "10"))
INTER_BATCH_SLEEP      = float(os.getenv("INTER_BATCH_SLEEP", "5.0"))
SCAN_PAUSE_SEC         = float(os.getenv("SCAN_PAUSE_SEC", "60.0"))

LINEAR_ONLY            = os.getenv("LINEAR_ONLY", "1") == "1"
QUOTE_WHITELIST        = tuple([x.strip() for x in os.getenv("QUOTE_WHITELIST", "USDT").split(",") if x.strip()])

# ================== OHLCV / İndikatör ==================
MIN_BARS   = int(os.getenv("MIN_BARS", "120"))     # TCE için yeterli bar
VOL_WIN    = int(os.getenv("VOL_WIN", "60"))
VOL_Q      = float(os.getenv("VOL_Q", "0.60"))

# Basit volume filtresi (mimari kalsın diye duruyor; istersen kapat)
USE_VOLUME_FILTER      = os.getenv("USE_VOLUME_FILTER", "0") == "1"
VOL_MA_RATIO_MIN       = float(os.getenv("VOL_MA_RATIO_MIN", "1.10"))
VOL_Z_MIN              = float(os.getenv("VOL_Z_MIN", "1.2"))

# Cooldown
COOLDOWN_MINUTES = int(os.getenv("COOLDOWN_MINUTES", "60"))
APPLY_COOLDOWN_BOTH_DIRECTIONS = os.getenv("APPLY_COOLDOWN_BOTH_DIRECTIONS", "1") == "1"


# ================== TP/SL (R-tabanlı plan) ==================
TP_SL_ENABLED = os.getenv("TP_SL_ENABLED", "1") == "1"
USE_TP_SL_GUARD = os.getenv("USE_TP_SL_GUARD", "0") == "1"

# ATR / SL (classic ATR-based stop)
TP_ATR_LEN = int(os.getenv("TP_ATR_LEN", "18"))
SL_MULTIPLIER = float(os.getenv("SL_MULTIPLIER", "1.4"))
SL_BUFFER = float(os.getenv("SL_BUFFER", "0.15"))

# Rejim (ADX) — TP planı için
ADX_TREND_ON = float(os.getenv("ADX_TREND_ON", "23"))

def regime_mode_from_adx(adx_last: float) -> str:
    return "trend" if (np.isfinite(adx_last) and adx_last >= ADX_TREND_ON) else "range"

def r_tp_plan(mode: str, is_ob: bool, R: float) -> dict:
    """R-tabanlı TP planı.
    - Trend modu (ADX ≥ ADX_TREND_ON): TP1=1.0R (%30), TP2=2.0R (%30), kalan %40
    - Range modu (ADX < ADX_TREND_ON): TP1=0.8R (%40), TP2=1.2R (%30), kalan %30
    - OB standalone (bu botta kullanılmıyor): TP1=1.0R (%40), TP2=1.5R (%30), kalan %30
    """
    if is_ob:
        return dict(tp1_mult=1.0, tp2_mult=1.5, tp1_pct=0.40, tp2_pct=0.30, rest_pct=0.30, desc="ob")
    if mode == "trend":
        return dict(tp1_mult=1.0, tp2_mult=2.0, tp1_pct=0.30, tp2_pct=0.30, rest_pct=0.40, desc="trend")
    return dict(tp1_mult=0.8, tp2_mult=1.2, tp1_pct=0.40, tp2_pct=0.30, rest_pct=0.30, desc="range")

def r_plan_guards_ok(mode: str, R: float, atr: float, entry: float, tp1_price: float, *, is_ob: bool = False) -> (bool, str):
    """RR guard: R/ATR eşiği.
    - Trend: R/ATR >= 1.00
    - Range: R/ATR >= 0.90
    - OB: R/ATR >= 0.80
    """
    if not all(map(np.isfinite, [R, atr, entry, tp1_price])) or atr <= 0 or R <= 0:
        return False, "nan"
    r_over_atr = R / atr
    if is_ob:
        r_min = 0.80
    else:
        r_min = 1.00 if mode == "trend" else 0.90
    if r_over_atr < r_min:
        return False, f"R/ATR<{r_min:.2f} (got {r_over_atr:.2f})"
    return True, "ok"

def _classic_sl_only(side: str, entry: float, atr: float) -> float:
    sl_abs = (SL_MULTIPLIER + SL_BUFFER) * atr
    if side == "LONG":
        return entry - sl_abs
    return entry + sl_abs

def compute_tp_sl_plan(df: pd.DataFrame, side: str) -> dict:
    """Sinyal barı (-2) için TP/SL planı üretir."""
    bar = df.iloc[-2]
    entry = safe_float(bar["close"], np.nan)
    if not np.isfinite(entry):
        return {}

    high = df["high"].to_numpy(dtype=np.float64)
    low = df["low"].to_numpy(dtype=np.float64)
    close = df["close"].to_numpy(dtype=np.float64)

    atr_arr = atr_np(high, low, close, TP_ATR_LEN)
    atr = float(atr_arr[-2]) if len(atr_arr) >= 2 else float("nan")

    adx_last = safe_float(bar.get("tce_adx", np.nan), np.nan)

    if not np.isfinite(atr) or atr <= 0:
        return {}

    sl = _classic_sl_only(side, entry, atr)
    R = abs(entry - sl)
    mode = regime_mode_from_adx(adx_last)

    plan = r_tp_plan(mode, is_ob=False, R=R)
    tp1 = entry + plan["tp1_mult"] * R if side == "LONG" else entry - plan["tp1_mult"] * R
    tp2 = entry + plan["tp2_mult"] * R if side == "LONG" else entry - plan["tp2_mult"] * R

    guard_ok, guard_reason = r_plan_guards_ok(mode, R, atr, entry, tp1, is_ob=False)

    out = dict(entry=entry, sl=sl, tp1=tp1, tp2=tp2, atr=atr, R=R, guard_ok=guard_ok, guard_reason=guard_reason)
    out.update(plan)
    return out

# ================== TCE Parametreleri ==================
# Pine: Trend Consensus Engine [TCE] (v6) — defaults
# Not: Bu bot "Kripto" profilinde tarama yapar. BIST presetleri yine de durur.

TCE_PROFILE = os.getenv("TCE_PROFILE", "Kripto")  # Otomatik / Kripto / BIST (burada default Kripto)

# --- ADX Filter 🛡️ (Pine defaults)
TCE_ADX_MODE   = os.getenv("TCE_ADX_MODE", "Soft")  # Off / Soft / Hard
TCE_ADX_LEN    = int(os.getenv("TCE_ADX_LEN", "14"))
TCE_ADX_EARLY  = os.getenv("TCE_ADX_EARLY", "1") == "1"  # Early pass

# --- Squeeze (LazyBear) 🧨 (Pine defaults)
TCE_SQZ_MODE         = os.getenv("TCE_SQZ_MODE", "Soft")  # Soft / Hard / Off
TCE_SQZ_LEN          = int(os.getenv("TCE_SQZ_LEN", "20"))
TCE_SQZ_BB_MULT      = float(os.getenv("TCE_SQZ_BB_MULT", "2.0"))
TCE_SQZ_KC_MULT      = float(os.getenv("TCE_SQZ_KC_MULT", "1.5"))
TCE_SQZ_PENALTY_PT   = int(os.getenv("TCE_SQZ_PENALTY_PT", "18"))
TCE_SQZ_POW_REF_ATR  = float(os.getenv("TCE_SQZ_POW_REF_ATR", "1.20"))

# --- Pinbar Veto 🧷 (Pine defaults)
TCE_USE_PINBAR_VETO = os.getenv("TCE_USE_PINBAR_VETO", "1") == "1"
TCE_PIN_WICK_MIN    = float(os.getenv("TCE_PIN_WICK_MIN", "0.55"))
TCE_PIN_BODY_MAX    = float(os.getenv("TCE_PIN_BODY_MAX", "0.30"))
TCE_PIN_CLOSE_MAX   = float(os.getenv("TCE_PIN_CLOSE_MAX", "0.35"))

# --- Score 🧮 (Pine defaults)
TCE_SCORE_THRESHOLD = float(os.getenv("TCE_SCORE_THRESHOLD", "70"))
TCE_ATR_LEN_NORM    = int(os.getenv("TCE_ATR_LEN_NORM", "14"))
TCE_SLOPE_BARS      = int(os.getenv("TCE_SLOPE_BARS", "5"))

TCE_AT_POS_REF      = float(os.getenv("TCE_AT_POS_REF", "0.55"))
TCE_R_POS_REF       = float(os.getenv("TCE_R_POS_REF", "0.30"))

TCE_USE_NEG_PENALTY = os.getenv("TCE_USE_NEG_PENALTY", "1") == "1"
TCE_AT_NEG_MAX      = int(os.getenv("TCE_AT_NEG_MAX", "14"))
TCE_R_NEG_MAX       = int(os.getenv("TCE_R_NEG_MAX", "10"))
TCE_AT_NEG_DEAD     = float(os.getenv("TCE_AT_NEG_DEAD", "0.05"))
TCE_R_NEG_DEAD      = float(os.getenv("TCE_R_NEG_DEAD", "0.04"))
TCE_AT_NEG_REF      = float(os.getenv("TCE_AT_NEG_REF", "0.35"))
TCE_R_NEG_REF       = float(os.getenv("TCE_R_NEG_REF", "0.25"))

# --- Ramp (Pine: Kripto=3, BIST=1)
TCE_RAMP_BARS_CRYPTO = int(os.getenv("TCE_RAMP_BARS_CRYPTO", "3"))
TCE_RAMP_BARS_BIST   = int(os.getenv("TCE_RAMP_BARS_BIST", "1"))

# --- Mod seçimi (Otomatik / Flow / Vegas / Guppy)
TCE_SCORE_MODE   = os.getenv("TCE_SCORE_MODE", "Otomatik")  # Otomatik / Flow / Vegas / Guppy
TCE_SHOW_GUPPY   = os.getenv("TCE_SHOW_GUPPY", "1") == "1"
TCE_SHOW_FLOW    = os.getenv("TCE_SHOW_FLOW", "0") == "1"
TCE_SHOW_VEGAS   = os.getenv("TCE_SHOW_VEGAS", "0") == "1"

# ✅ ZORUNLU: Mod her zaman Guppy (env ile uğraştırma)
FORCE_GUPPY_MODE = True
if FORCE_GUPPY_MODE:
    TCE_SCORE_MODE = "Guppy"
    TCE_SHOW_GUPPY = True
    TCE_SHOW_FLOW  = False
    TCE_SHOW_VEGAS = False

# --- AlphaTrend inputları (Pine defaults)
TCE_AT_AP      = int(os.getenv("TCE_AT_AP", "14"))
TCE_AT_COEFF   = float(os.getenv("TCE_AT_COEFF", "1.0"))
TCE_AT_SRC     = os.getenv("TCE_AT_SRC", "close")  # close / hlc3 (şimdilik close)
TCE_AT_NO_VOL  = os.getenv("TCE_AT_NO_VOL", "0") == "1"  # novolumedata

# --- MA Resistance (Donchian mid + SMA) (Pine defaults)
TCE_R_N1   = int(os.getenv("TCE_R_N1", "21"))
TCE_R_ACT  = int(os.getenv("TCE_R_ACT", "21"))

# --- Flow/Vegas lengths (Pine defaults)
TCE_FLOW_LEN = int(os.getenv("TCE_FLOW_LEN", "34"))
TCE_VEGAS_1  = int(os.getenv("TCE_VEGAS_1", "144"))
TCE_VEGAS_2  = int(os.getenv("TCE_VEGAS_2", "169"))

# ================== Messaging prefs ==================

SEND_REJECT_MSG = False
MESSAGE_THROTTLE_SECS = float(os.getenv("MESSAGE_THROTTLE_SECS", "20.0"))

# ================== Logging ==================
logger = logging.getLogger()
if not logger.handlers:
    logger.setLevel(logging.INFO)
    fmt = logging.Formatter('%(asctime)s - %(levelname)s - %(message)s')

    ch = logging.StreamHandler(sys.stdout); ch.setFormatter(fmt); logger.addHandler(ch)
    fh = RotatingFileHandler('bot.log', maxBytes=5_000_000, backupCount=3); fh.setFormatter(fmt); logger.addHandler(fh)

class MinimalInfoFilter(logging.Filter):
    def filter(self, record: logging.LogRecord) -> bool:
        if record.levelno != logging.INFO:
            return True
        msg = str(record.getMessage())
        return (
            msg.startswith("Shard ") or
            msg.startswith(" (veri yok)") or
            msg.startswith(" - ")
        )
for h in logger.handlers:
    h.addFilter(MinimalInfoFilter())

logging.getLogger('telegram').setLevel(logging.ERROR)
logging.getLogger('httpx').setLevel(logging.ERROR)

# ================== Borsa ==================
exchange = ccxt.bybit({
    "enableRateLimit": True,
    "options": {"defaultType": "swap"},
    "timeout": 90000,
})

MARKETS: Dict = {}
_fetch_sem = asyncio.Semaphore(MAX_CONCURRENT_FETCHES)
_rate_lock = asyncio.Lock()
_last_call_ts = 0.0
_rate_penalty_ms = 0.0

# ================== Telegram ==================
telegram_bot = None
if BOT_TOKEN and not TEST_MODE:
    try:
        telegram_bot = telegram.Bot(token=BOT_TOKEN, request=HTTPXRequest(connection_pool_size=8))
    except Exception as e:
        logger.error(f"Telegram init error: {e.__class__.__name__}: {e}")
        telegram_bot = None

message_queue: asyncio.Queue = asyncio.Queue(maxsize=200)
_last_message_hashes: Dict[str, float] = {}

# ================== State ==================
STATE_FILE = os.getenv("STATE_FILE", "state.json")

@dataclass
class PosState:
    last_signal_ts: float = 0.0
    last_side: str = ""              # "LONG"/"SHORT"
    last_bar_ts: int = 0
    cooldown_until: float = 0.0

_state_lock = threading.Lock()
state_map: Dict[str, PosState] = {}


# ----------------- Utils -----------------
def clamp(x: float, lo: float, hi: float) -> float:
    return float(min(hi, max(lo, x)))

def norm_by_atr(x: float, atr: float) -> float:
    return float(x / atr) if atr and atr > 0 else 0.0

def safe_float(x, default=0.0) -> float:
    try:
        v = float(x)
        return v if math.isfinite(v) else default
    except Exception:
        return default

# ----------------- State IO -----------------
def load_state() -> None:
    global state_map
    if not os.path.exists(STATE_FILE):
        return
    try:
        with open(STATE_FILE, "r", encoding="utf-8") as f:
            raw = json.load(f)
        mp = {}
        for k, v in raw.items():
            mp[k] = PosState(**v)
        state_map = mp
    except Exception as e:
        logger.warning(f"State load failed: {e.__class__.__name__}: {e}")

def save_state() -> None:
    try:
        with _state_lock:
            raw = {k: vars(v) for k, v in state_map.items()}
        with open(STATE_FILE, "w", encoding="utf-8") as f:
            json.dump(raw, f, ensure_ascii=False, indent=2)
    except Exception as e:
        logger.warning(f"State save failed: {e.__class__.__name__}: {e}")

# ----------------- Telegram Queue -----------------
async def enqueue_message(text: str, is_retry: bool = False):
    if not BOT_TOKEN or not CHAT_ID or TEST_MODE:
        logger.debug(f"Mesaj atlandı (Telegram kapalı veya TEST_MODE): {text[:50]}")
        return

    msg_hash = hashlib.md5(text.encode()).hexdigest()
    now = time.time()
    if not is_retry:
        last = _last_message_hashes.get(msg_hash, 0.0)
        if now - last < MESSAGE_THROTTLE_SECS:
            return

    try:
        message_queue.put_nowait(text)
        _last_message_hashes[msg_hash] = now
        # cleanup
        for h in list(_last_message_hashes.keys()):
            if now - _last_message_hashes[h] > 60.0:
                del _last_message_hashes[h]
    except asyncio.QueueFull:
        logger.warning("Mesaj kuyruğu dolu, mesaj düşürüldü.")

async def message_sender():
    while True:
        message = await message_queue.get()
        try:
            if telegram_bot:
                await telegram_bot.send_message(chat_id=CHAT_ID, text=message)
                await asyncio.sleep(1)
        except (RetryAfter, TimedOut) as e:
            wait_time = getattr(e, "retry_after", 5) + 2
            logger.warning(f"Telegram: RetryAfter, {wait_time-2}s bekle")
            await asyncio.sleep(wait_time)
            await enqueue_message(message, is_retry=True)
        except Exception as e:
            logger.error(f"Telegram mesaj hatası: {e.__class__.__name__}: {str(e)}")
        message_queue.task_done()

# ----------------- Markets / Symbols -----------------
async def load_markets():
    global MARKETS
    if MARKETS:
        return MARKETS
    MARKETS = await asyncio.to_thread(exchange.load_markets)
    return MARKETS

async def discover_bybit_symbols(linear_only: bool = True, quote_whitelist: Tuple[str, ...] = ("USDT",)) -> List[str]:
    markets = MARKETS or await load_markets()
    syms: List[str] = []
    for s, m in markets.items():
        if not m.get("active", True):
            continue
        if not m.get("swap", False):
            continue
        if linear_only and not m.get("linear", False):
            continue
        if m.get("quote") not in quote_whitelist:
            continue
        syms.append(s)
    return sorted(set(syms))

# ----------------- Rate-limit Dostu OHLCV -----------------
async def fetch_ohlcv_async(symbol: str, timeframe: str, limit: int):
    """Semaphor'u asla yeniden yaratma; sadece beklemeyi adaptif arttır."""
    global _last_call_ts, _rate_penalty_ms
    max_attempts = 5
    base_ms = RATE_LIMIT_MS

    for attempt in range(1, max_attempts + 1):
        try:
            async with _fetch_sem:
                async with _rate_lock:
                    now = asyncio.get_event_loop().time()
                    wait = max(0.0, (_last_call_ts + (base_ms + _rate_penalty_ms) / 1000.0) - now)
                    if wait > 0:
                        await asyncio.sleep(wait)
                    _last_call_ts = asyncio.get_event_loop().time()

                data = await asyncio.to_thread(exchange.fetch_ohlcv, symbol, timeframe, None, limit)

            if _rate_penalty_ms > 0:
                _rate_penalty_ms = max(0.0, _rate_penalty_ms * 0.6)
            return data

        except (ccxt.RateLimitExceeded, ccxt.DDoSProtection):
            _rate_penalty_ms = min(4000.0, (_rate_penalty_ms * 1.5) + 150.0)
            backoff = 0.8 * attempt + random.random() * 0.6
            await asyncio.sleep(backoff)

        except (ccxt.RequestTimeout, ccxt.NetworkError):
            backoff = 0.6 * attempt + random.random() * 0.6
            await asyncio.sleep(backoff)

    raise ccxt.NetworkError(f"fetch_ohlcv failed after retries: {symbol} {timeframe}")

# ================== Basic TA ==================
def ema_np(closes: np.ndarray, span: int) -> np.ndarray:
    k = 2 / (span + 1)
    out = np.zeros_like(closes, dtype=np.float64)
    out[0] = closes[0]
    for i in range(1, len(closes)):
        out[i] = closes[i] * k + out[i - 1] * (1 - k)
    return out

def rma_np(arr: np.ndarray, length: int) -> np.ndarray:
    # Wilder RMA
    out = np.full_like(arr, np.nan, dtype=np.float64)
    if length <= 0 or len(arr) == 0:
        return out
    alpha = 1.0 / length
    out[0] = arr[0]
    for i in range(1, len(arr)):
        out[i] = alpha * arr[i] + (1 - alpha) * out[i - 1]
    return out

def atr_np(high: np.ndarray, low: np.ndarray, close: np.ndarray, length: int = 14) -> np.ndarray:
    prev_close = np.roll(close, 1)
    prev_close[0] = close[0]
    tr = np.maximum(high - low, np.maximum(np.abs(high - prev_close), np.abs(low - prev_close)))
    return rma_np(tr, length)

def dmi_adx(df: pd.DataFrame, length: int = 14) -> Tuple[np.ndarray, np.ndarray, np.ndarray]:
    high = df["high"].to_numpy(dtype=np.float64)
    low = df["low"].to_numpy(dtype=np.float64)
    close = df["close"].to_numpy(dtype=np.float64)

    up = np.diff(high, prepend=high[0])
    dn = -np.diff(low, prepend=low[0])

    plus_dm = np.where((up > dn) & (up > 0), up, 0.0)
    minus_dm = np.where((dn > up) & (dn > 0), dn, 0.0)

    atr = atr_np(high, low, close, length)
    plus_di = 100 * rma_np(plus_dm, length) / np.where(atr == 0, np.nan, atr)
    minus_di = 100 * rma_np(minus_dm, length) / np.where(atr == 0, np.nan, atr)

    dx = 100 * np.abs(plus_di - minus_di) / np.where((plus_di + minus_di) == 0, np.nan, (plus_di + minus_di))
    adx = rma_np(np.nan_to_num(dx, nan=0.0), length)

    return plus_di, minus_di, adx

# ================== Volume stats ==================
def add_volume_columns(df: pd.DataFrame) -> pd.DataFrame:
    v = df["volume"].astype(float)
    df["vol_ma"] = v.rolling(VOL_WIN).mean()
    # z-score
    mu = v.rolling(VOL_WIN).mean()
    sd = v.rolling(VOL_WIN).std(ddof=0)
    df["vol_z"] = (v - mu) / sd.replace(0, np.nan)
    # dvol quantile
    dvol = (df["close"].astype(float) * v).astype(float)
    df["dvol_q"] = dvol.rolling(VOL_WIN).quantile(VOL_Q)
    return df

def simple_volume_ok(df: pd.DataFrame) -> Tuple[bool, str]:
    last = df.iloc[-2]
    vol = safe_float(last.get("volume", np.nan), np.nan)
    vol_ma = safe_float(last.get("vol_ma", np.nan), np.nan)
    if not (np.isfinite(vol) and np.isfinite(vol_ma) and vol_ma > 0):
        return False, "vol_nan"
    ratio = vol / vol_ma
    vz = safe_float(df["vol_z"].iloc[-2], 0.0) if "vol_z" in df.columns else 0.0
    d = safe_float((df["close"] * df["volume"]).iloc[-2], 0.0)
    d_q = safe_float(df["dvol_q"].iloc[-2], 0.0) if "dvol_q" in df.columns else 0.0

    ratio_ok = ratio >= VOL_MA_RATIO_MIN
    vz_ok = vz >= VOL_Z_MIN
    d_ok = (d >= d_q) if np.isfinite(d_q) and d_q > 0 else True
    ok = bool(ratio_ok and vz_ok and d_ok)
    reason = f"ratio={ratio:.2f}{'✓' if ratio_ok else '✗'}, vz={vz:.2f}{'✓' if vz_ok else '✗'}, dvol>q={d_ok}"
    return ok, reason

# ================== TCE (Core) ==================
def _tce_adx_pass(df: pd.DataFrame) -> pd.Series:
    """Pine: ta.dmi(adxLen, adxLen) + threshold/early + adxMult"""
    di_p, di_m, adx = dmi_adx(df, TCE_ADX_LEN)
    df["tce_di_plus"] = di_p
    df["tce_di_minus"] = di_m
    df["tce_adx"] = adx

    prof = (TCE_PROFILE or "Kripto").strip()
    prof_eff = "Kripto" if prof.lower() in ("otomatik", "kripto") else "BIST"

    adx_thresh   = 18.0 if prof_eff == "BIST" else 20.0
    adx_earlybuf = 6.0  if prof_eff == "BIST" else 3.0
    adx_mult_min = 0.85 if prof_eff == "BIST" else 0.80
    adx_mult_max = 1.00
    adx_range    = 20.0 if prof_eff == "BIST" else 15.0

    adx_strong = df["tce_adx"] >= adx_thresh
    adx_early = (
        bool(TCE_ADX_EARLY)
        and (df["tce_adx"] >= (adx_thresh - adx_earlybuf))
        and (df["tce_adx"] > df["tce_adx"].shift(1))
    )

    mode = (TCE_ADX_MODE or "Soft").strip().lower()
    if mode == "off":
        adx_pass = pd.Series(True, index=df.index)
    else:
        adx_pass = (adx_strong | adx_early)

    # Pine: adxNorm + adxMult
    adx_norm = np.clip((df["tce_adx"] - (adx_thresh - adx_earlybuf)) / adx_range, 0.0, 1.0)
    adx_mult = np.clip(adx_mult_min + (adx_mult_max - adx_mult_min) * adx_norm, 0.0, 2.0)

    df["tce_adx_mult"] = adx_mult.astype(float)
    df["tce_adx_pass"] = adx_pass.astype(bool)

    # Pine: BIST'te Hard seçilse bile Soft çalışır
    if prof_eff == "BIST":
        df["tce_adx_mode_eff"] = "Off" if mode == "off" else "Soft"
    else:
        df["tce_adx_mode_eff"] = "Off" if mode == "off" else ("Hard" if mode == "hard" else "Soft")

    return df["tce_adx_pass"]


def _tce_squeeze_momentum(df: pd.DataFrame) -> pd.Series:
    """Pine: Squeeze Momentum (LazyBear) — mom=linreg(close-m2, len, 0)"""
    close = df["close"].astype(float)
    high = df["high"].astype(float)
    low = df["low"].astype(float)

    L = int(TCE_SQZ_LEN)
    bbMult = float(TCE_SQZ_BB_MULT)
    kcMult = float(TCE_SQZ_KC_MULT)

    # BB
    basisBB = close.rolling(L).mean()
    devBB = bbMult * close.rolling(L).std(ddof=0)
    upperBB = basisBB + devBB
    lowerBB = basisBB - devBB

    # KC
    tr = pd.concat([
        (high - low),
        (high - close.shift(1)).abs(),
        (low - close.shift(1)).abs()
    ], axis=1).max(axis=1)
    maKC = close.rolling(L).mean()
    rangeKC = tr.rolling(L).mean()
    upperKC = maKC + kcMult * rangeKC
    lowerKC = maKC - kcMult * rangeKC

    squeeze_on = (lowerBB > lowerKC) & (upperBB < upperKC)
    squeeze_off = (lowerBB < lowerKC) & (upperBB > upperKC)

    # LazyBear momentum
    m1 = (high.rolling(L).max() + low.rolling(L).min()) / 2.0
    m2 = (m1 + close.rolling(L).mean()) / 2.0
    val = close - m2

    # ta.linreg(val, L, 0) => end-point of rolling regression
    idx = np.arange(L, dtype=np.float64)
    sum_x = float(np.sum(idx))
    sum_x2 = float(np.sum(idx ** 2))
    denom = (L * sum_x2 - (sum_x ** 2))

    arr = val.to_numpy(dtype=np.float64)
    mom = np.full(arr.shape[0], np.nan, dtype=np.float64)
    if denom != 0 and len(arr) >= L:
        for i in range(L - 1, len(arr)):
            y = arr[i - L + 1: i + 1]
            if not np.all(np.isfinite(y)):
                continue
            sum_y = float(np.sum(y))
            sum_xy = float(np.sum(idx * y))
            b = (L * sum_xy - sum_x * sum_y) / denom
            a = (sum_y - b * sum_x) / L
            mom[i] = a + b * (L - 1)

    df["tce_sqz_on"] = squeeze_on.astype(bool)
    df["tce_sqz_off"] = squeeze_off.astype(bool)
    df["tce_sqz_mom"] = mom
    return df["tce_sqz_mom"]


def _tce_alpha_trend(df: pd.DataFrame) -> pd.Series:
    """Pine AlphaTrend: ATR=SMA(TR), cond = (MFI>=50) or (RSI>=50 if novolume)."""
    high = df["high"].astype(float)
    low = df["low"].astype(float)
    close = df["close"].astype(float)
    open_ = df["open"].astype(float)

    AP = int(TCE_AT_AP)
    coeff = float(TCE_AT_COEFF)

    # TR + ATR(SMA)
    prev_close = close.shift(1)
    tr = pd.concat([
        (high - low),
        (high - prev_close).abs(),
        (low - prev_close).abs()
    ], axis=1).max(axis=1)
    atr_sma = tr.rolling(AP).mean()

    upT = low - atr_sma * coeff
    downT = high + atr_sma * coeff

    # RSI (Wilder)
    diff = close.diff()
    gain = diff.clip(lower=0).to_numpy(dtype=np.float64)
    loss = (-diff.clip(upper=0)).to_numpy(dtype=np.float64)
    avg_gain = rma_np(gain, AP)
    avg_loss = rma_np(loss, AP)
    rs = avg_gain / np.where(avg_loss == 0, np.nan, avg_loss)
    rsi = 100.0 - (100.0 / (1.0 + rs))
    rsi_s = pd.Series(rsi, index=df.index)

    # MFI
    vol = df.get("volume")
    if vol is not None:
        vol = vol.astype(float)
        tp = (high + low + close) / 3.0
        rmf = tp * vol
        tp_diff = tp.diff()
        pos_mf = rmf.where(tp_diff > 0, 0.0)
        neg_mf = rmf.where(tp_diff < 0, 0.0).abs()
        pos_sum = pos_mf.rolling(AP).sum()
        neg_sum = neg_mf.rolling(AP).sum()
        mr = pos_sum / neg_sum.replace(0, np.nan)
        mfi = 100.0 - (100.0 / (1.0 + mr))
    else:
        mfi = pd.Series(np.nan, index=df.index)

    novol = bool(TCE_AT_NO_VOL) or (vol is None) or mfi.isna().all()
    cond = (rsi_s >= 50.0) if novol else (mfi >= 50.0)

    # recursive AlphaTrend
    out = np.full(len(df), np.nan, dtype=np.float64)
    up_arr = upT.to_numpy(dtype=np.float64)
    dn_arr = downT.to_numpy(dtype=np.float64)
    cond_arr = cond.to_numpy(dtype=bool)

    if len(df) > 0:
        out[0] = up_arr[0] if np.isfinite(up_arr[0]) else np.nan
    for i in range(1, len(df)):
        prev = out[i - 1]
        if not np.isfinite(prev):
            prev = up_arr[i - 1] if np.isfinite(up_arr[i - 1]) else dn_arr[i - 1]
        if cond_arr[i]:
            v = up_arr[i]
            out[i] = prev if (np.isfinite(v) and v < prev) else v
        else:
            v = dn_arr[i]
            out[i] = prev if (np.isfinite(v) and v > prev) else v

    df["tce_at"] = out
    df["tce_at2"] = pd.Series(out, index=df.index).shift(2)
    df["tce_at_up"] = (df["tce_at"] > df["tce_at2"]).fillna(False)
    return df["tce_at"]


def _tce_r_line(df: pd.DataFrame) -> pd.Series:
    """Pine: Donchian mid (n1) + SMA(ACT)."""
    n1 = int(TCE_R_N1)
    act = int(TCE_R_ACT)

    a = df["high"].astype(float).rolling(n1).max()
    b = df["low"].astype(float).rolling(n1).min()
    c = (a + b) / 2.0
    r = c.rolling(act).mean()

    df["tce_r"] = r
    return df["tce_r"]


def _tce_guppy_vegas_flow(df: pd.DataFrame) -> None:
    close = df["close"].astype(float).to_numpy(dtype=np.float64)
    high = df["high"].astype(float).to_numpy(dtype=np.float64)
    low = df["low"].astype(float).to_numpy(dtype=np.float64)

    # Guppy (Pine: 3/15 vs 30/60)
    df["tce_g_short_fast"] = ema_np(close, 3)
    df["tce_g_short_slow"] = ema_np(close, 15)
    df["tce_g_long_fast"]  = ema_np(close, 30)
    df["tce_g_long_slow"]  = ema_np(close, 60)

    # Vegas
    df["tce_vegas_144"] = ema_np(close, int(TCE_VEGAS_1))
    df["tce_vegas_169"] = ema_np(close, int(TCE_VEGAS_2))

    # Flow band (EMA high/low channel)
    L = int(TCE_FLOW_LEN)
    df["tce_flow_high"] = ema_np(high, L)
    df["tce_flow_low"]  = ema_np(low,  L)


def _tce_scores(df: pd.DataFrame) -> None:
    """Pine skor motoru (Long birebir). Short: simetrik ayna."""

    def clamp(x, lo, hi):
        return np.minimum(hi, np.maximum(lo, x))

    def norm_by_atr(x, atr):
        return np.where(atr > 0, x / atr, 0.0)

    prof = (TCE_PROFILE or "Kripto").strip()
    prof_eff = "Kripto" if prof.lower() in ("otomatik", "kripto") else "BIST"

    slopeBars = int(TCE_SLOPE_BARS)
    slopeBarsEff = max(2, slopeBars - 2) if prof_eff == "BIST" else slopeBars

    rampBarsEff = int(TCE_RAMP_BARS_BIST) if prof_eff == "BIST" else int(TCE_RAMP_BARS_CRYPTO)

    # ATR normalize (Wilder)
    high = df["high"].to_numpy(dtype=np.float64)
    low = df["low"].to_numpy(dtype=np.float64)
    close = df["close"].to_numpy(dtype=np.float64)
    atrN = atr_np(high, low, close, int(TCE_ATR_LEN_NORM))
    df["tce_atrN"] = atrN

    # --- SQZ pass (lime) + power
    mom = df["tce_sqz_mom"].to_numpy(dtype=np.float64)
    mom_prev = np.roll(mom, 1); mom_prev[0] = np.nan
    sqzLime_long = (mom > 0) & (mom > mom_prev)
    sqzLime_short = (mom < 0) & (mom < mom_prev)

    sqzMode = (TCE_SQZ_MODE or "Soft").strip()
    sqzUsed = sqzMode.lower() != "off"
    sqzPassL = (~sqzUsed) | sqzLime_long
    sqzPassS = (~sqzUsed) | sqzLime_short

    # --- Pinbar veto (bear for long, bull for short)
    rng = (df["high"] - df["low"]).to_numpy(dtype=np.float64)
    body = np.abs((df["close"] - df["open"]).to_numpy(dtype=np.float64))
    uw = (df["high"] - np.maximum(df["open"], df["close"])).to_numpy(dtype=np.float64)
    lw = (np.minimum(df["open"], df["close"]) - df["low"]).to_numpy(dtype=np.float64)
    closeLoc = np.where(rng > 0, (df["close"] - df["low"]).to_numpy(dtype=np.float64) / rng, 0.5)

    wickMin = float(TCE_PIN_WICK_MIN)
    bodyMax = float(TCE_PIN_BODY_MAX)
    closeMax = float(TCE_PIN_CLOSE_MAX)

    # BIST tolerans
    if prof_eff == "BIST":
        wickMin = float(clamp(wickMin - 0.05, 0.10, 0.90))
        bodyMax = float(clamp(bodyMax + 0.05, 0.05, 0.90))
        closeMax = float(clamp(closeMax + 0.05, 0.05, 0.95))

    usePB = bool(TCE_USE_PINBAR_VETO)
    bearPinbar = usePB & (rng > 0) & ((uw / np.where(rng == 0, np.nan, rng)) >= wickMin) & ((body / np.where(rng == 0, np.nan, rng)) <= bodyMax) & (closeLoc <= closeMax)
    bullPinbar = usePB & (rng > 0) & ((lw / np.where(rng == 0, np.nan, rng)) >= wickMin) & ((body / np.where(rng == 0, np.nan, rng)) <= bodyMax) & (closeLoc >= (1.0 - closeMax))

    df["tce_pin_bear"] = bearPinbar.astype(bool)
    df["tce_pin_bull"] = bullPinbar.astype(bool)

    # --- AT (0..40)
    at = df["tce_at"].to_numpy(dtype=np.float64)
    at2 = np.roll(at, 2); at2[:2] = np.nan
    atUp = at > at2
    atDn = at < at2
    priceAboveAT = close > at
    priceBelowAT = close < at

    atSlopeS = norm_by_atr(at - np.roll(at, slopeBarsEff), atrN)
    atSlopeS[:slopeBarsEff] = 0.0

    # Long slopes
    atSlopeP_L = np.maximum(atSlopeS, 0.0)
    atSlopeN_L = np.maximum(-atSlopeS, 0.0)
    atSlopePts_L = 15.0 * clamp(atSlopeP_L / float(TCE_AT_POS_REF), 0, 1)
    atNegEff_L = np.maximum(atSlopeN_L - float(TCE_AT_NEG_DEAD), 0.0)
    atPenalty_L = (int(TCE_AT_NEG_MAX) * clamp(atNegEff_L / float(TCE_AT_NEG_REF), 0, 1)) if bool(TCE_USE_NEG_PENALTY) else 0.0

    # Short slopes (ayna)
    atSlopeP_S = np.maximum(-atSlopeS, 0.0)
    atSlopeN_S = np.maximum(atSlopeS, 0.0)
    atSlopePts_S = 15.0 * clamp(atSlopeP_S / float(TCE_AT_POS_REF), 0, 1)
    atNegEff_S = np.maximum(atSlopeN_S - float(TCE_AT_NEG_DEAD), 0.0)
    atPenalty_S = (int(TCE_AT_NEG_MAX) * clamp(atNegEff_S / float(TCE_AT_NEG_REF), 0, 1)) if bool(TCE_USE_NEG_PENALTY) else 0.0

    # ramp
    atStateL = atUp & priceAboveAT
    atStateS = atDn & priceBelowAT

    def ramp_factor(state: np.ndarray, bars_needed: int) -> np.ndarray:
        out = np.zeros_like(state, dtype=np.float64)
        cnt = 0
        for i, s in enumerate(state):
            if s:
                cnt += 1
            else:
                cnt = 0
            out[i] = min(cnt / max(bars_needed, 1), 1.0) if s else 0.0
        return out

    atRampL = ramp_factor(atStateL, rampBarsEff)
    atRampS = ramp_factor(atStateS, rampBarsEff)

    atPosL = (atUp.astype(float) * 15.0) + (priceAboveAT.astype(float) * 10.0) + atSlopePts_L
    atScoreL = clamp(atPosL * atRampL - atPenalty_L, 0, 40)

    atPosS = (atDn.astype(float) * 15.0) + (priceBelowAT.astype(float) * 10.0) + atSlopePts_S
    atScoreS = clamp(atPosS * atRampS - atPenalty_S, 0, 40)

    df["tce_atScore_long"] = atScoreL
    df["tce_atScore_short"] = atScoreS

    # --- R (0..30)
    R = df["tce_r"].to_numpy(dtype=np.float64)
    priceAboveR = close > R
    priceBelowR = close < R

    rSlopeS = norm_by_atr(R - np.roll(R, slopeBarsEff), atrN)
    rSlopeS[:slopeBarsEff] = 0.0

    # Long
    rSlopeP_L = np.maximum(rSlopeS, 0.0)
    rSlopeN_L = np.maximum(-rSlopeS, 0.0)
    rSlopePts_L = 12.0 * clamp(rSlopeP_L / float(TCE_R_POS_REF), 0, 1)
    rNegEff_L = np.maximum(rSlopeN_L - float(TCE_R_NEG_DEAD), 0.0)
    rPenalty_L = (int(TCE_R_NEG_MAX) * clamp(rNegEff_L / float(TCE_R_NEG_REF), 0, 1)) if bool(TCE_USE_NEG_PENALTY) else 0.0
    rDistN_L = norm_by_atr(close - R, atrN)

    rStateL = priceAboveR & (rSlopeS >= 0)
    rRampL = ramp_factor(rStateL, rampBarsEff)

    rPosL = (priceAboveR.astype(float) * 12.0) + rSlopePts_L + clamp(6.0 * rDistN_L, 0, 6)
    rScoreL = clamp(rPosL * rRampL - rPenalty_L, 0, 30)

    # Short (ayna)
    rSlopeP_S = np.maximum(-rSlopeS, 0.0)
    rSlopeN_S = np.maximum(rSlopeS, 0.0)
    rSlopePts_S = 12.0 * clamp(rSlopeP_S / float(TCE_R_POS_REF), 0, 1)
    rNegEff_S = np.maximum(rSlopeN_S - float(TCE_R_NEG_DEAD), 0.0)
    rPenalty_S = (int(TCE_R_NEG_MAX) * clamp(rNegEff_S / float(TCE_R_NEG_REF), 0, 1)) if bool(TCE_USE_NEG_PENALTY) else 0.0
    rDistN_S = norm_by_atr(R - close, atrN)

    rStateS = priceBelowR & (rSlopeS <= 0)
    rRampS = ramp_factor(rStateS, rampBarsEff)

    rPosS = (priceBelowR.astype(float) * 12.0) + rSlopePts_S + clamp(6.0 * rDistN_S, 0, 6)
    rScoreS = clamp(rPosS * rRampS - rPenalty_S, 0, 30)

    df["tce_rScore_long"] = rScoreL
    df["tce_rScore_short"] = rScoreS

    # --- Mod (0..30)
    # ✅ Zorunlu Guppy modu
    if globals().get("FORCE_GUPPY_MODE", False):
        active = "Guppy"
    else:
        autoPick = "Guppy" if TCE_SHOW_GUPPY else ("Flow" if TCE_SHOW_FLOW else ("Vegas" if TCE_SHOW_VEGAS else "None"))
        active = autoPick if (TCE_SCORE_MODE or "Otomatik").lower() == "otomatik" else TCE_SCORE_MODE

    modL = np.zeros_like(close, dtype=np.float64)
    modS = np.zeros_like(close, dtype=np.float64)

    if active == "Flow":
        fh = df["tce_flow_high"].to_numpy(dtype=np.float64)
        fl = df["tce_flow_low"].to_numpy(dtype=np.float64)
        bandW = fh - fl
        posL = np.where(bandW > 0, (close - fl) / bandW, 0.0)
        posL = clamp(posL, 0, 1)
        modL = clamp((posL * 20.0) + (close > fh).astype(float) * 10.0, 0, 30)

        posS = np.where(bandW > 0, (fh - close) / bandW, 0.0)
        posS = clamp(posS, 0, 1)
        modS = clamp((posS * 20.0) + (close < fl).astype(float) * 10.0, 0, 30)

    elif active == "Vegas":
        e1 = df["tce_vegas_144"].to_numpy(dtype=np.float64)
        e2 = df["tce_vegas_169"].to_numpy(dtype=np.float64)
        vBull = e1 > e2
        vBear = e1 < e2
        spreadL = norm_by_atr(e1 - e2, atrN)
        spreadS = norm_by_atr(e2 - e1, atrN)

        modL = clamp((vBull.astype(float) * 15.0) + ((close > e1) & (close > e2)).astype(float) * 10.0 + clamp(5.0 * spreadL, 0, 5), 0, 30)
        modS = clamp((vBear.astype(float) * 15.0) + ((close < e1) & (close < e2)).astype(float) * 10.0 + clamp(5.0 * spreadS, 0, 5), 0, 30)

    else:  # Guppy
        sslow = df["tce_g_short_slow"].to_numpy(dtype=np.float64)
        lfast = df["tce_g_long_fast"].to_numpy(dtype=np.float64)
        gBull = sslow > lfast
        gBear = sslow < lfast
        sslow_prev = np.roll(sslow, 1); sslow_prev[0] = np.nan
        lfast_prev = np.roll(lfast, 1); lfast_prev[0] = np.nan
        gCrossUp = (sslow > lfast) & (sslow_prev <= lfast_prev)
        gCrossDn = (sslow < lfast) & (sslow_prev >= lfast_prev)
        spreadL = norm_by_atr(sslow - lfast, atrN)
        spreadS = norm_by_atr(lfast - sslow, atrN)

        modL = clamp((gBull.astype(float) * 15.0) + (gCrossUp.astype(float) * 10.0) + clamp(5.0 * spreadL, 0, 5), 0, 30)
        modS = clamp((gBear.astype(float) * 15.0) + (gCrossDn.astype(float) * 10.0) + clamp(5.0 * spreadS, 0, 5), 0, 30)

    df["tce_modScore_long"] = modL
    df["tce_modScore_short"] = modS

    # --- SQZ POWER (0..20)
    sqzPow01_L = np.zeros_like(close, dtype=np.float64)
    sqzPow01_S = np.zeros_like(close, dtype=np.float64)

    if sqzUsed:
        ref = atrN * float(TCE_SQZ_POW_REF_ATR)
        sqzPow01_L = np.where(sqzPassL, clamp(mom / np.where(ref == 0, np.nan, ref), 0, 1), 0.0)
        sqzPow01_S = np.where(sqzPassS, clamp((-mom) / np.where(ref == 0, np.nan, ref), 0, 1), 0.0)

    sqzPowPt_L = sqzPow01_L * 20.0 if sqzUsed else 0.0
    sqzPowPt_S = sqzPow01_S * 20.0 if sqzUsed else 0.0

    # --- RAW -> 0..100
    rawSumL = atScoreL + rScoreL + modL + (sqzPowPt_L if sqzUsed else 0.0)
    rawSumS = atScoreS + rScoreS + modS + (sqzPowPt_S if sqzUsed else 0.0)

    maxSum = 100.0 + (20.0 if sqzUsed else 0.0)
    score100_raw_L = clamp((rawSumL / maxSum) * 100.0, 0, 100)
    score100_raw_S = clamp((rawSumS / maxSum) * 100.0, 0, 100)

    sqzPenaltyEff = int(max(int(TCE_SQZ_PENALTY_PT) - (4 if prof_eff == "BIST" else 0), 0))
    penalty100 = clamp((sqzPenaltyEff / maxSum) * 100.0, 0, 100)

    def apply_sqz(total_raw, sqz_pass):
        if sqzMode.lower() == "hard":
            return np.where(sqz_pass, total_raw, 0.0)
        if sqzMode.lower() == "soft":
            return clamp(total_raw - np.where(sqz_pass, 0.0, penalty100), 0, 100)
        return total_raw

    totalL = apply_sqz(score100_raw_L, sqzPassL)
    totalS = apply_sqz(score100_raw_S, sqzPassS)

    # --- ADX uygulanır
    adx_mode_eff = df["tce_adx_mode_eff"].iloc[-1] if "tce_adx_mode_eff" in df.columns else ("Hard" if (TCE_ADX_MODE or "Soft").lower() == "hard" else ("Soft" if (TCE_ADX_MODE or "Soft").lower() == "soft" else "Off"))
    adx_pass = df["tce_adx_pass"].to_numpy(dtype=bool) if "tce_adx_pass" in df.columns else np.ones_like(close, dtype=bool)
    adx_mult = df["tce_adx_mult"].to_numpy(dtype=np.float64) if "tce_adx_mult" in df.columns else np.ones_like(close, dtype=np.float64)

    if adx_mode_eff == "Hard":
        totalL = np.where(adx_pass, totalL, 0.0)
        totalS = np.where(adx_pass, totalS, 0.0)
    elif adx_mode_eff == "Soft":
        totalL = clamp(totalL * adx_mult, 0, 100)
        totalS = clamp(totalS * adx_mult, 0, 100)

    # --- blocked + decisionOk
    sqzBlocksL = (sqzMode.lower() != "off") & (~sqzPassL)
    sqzBlocksS = (sqzMode.lower() != "off") & (~sqzPassS)

    pinBlocksL = bearPinbar
    pinBlocksS = bullPinbar

    # Crypto: ADX bloklayabilir; BIST: bloklamasın
    # element-wise ADX block (sadece Kripto)
    if (prof_eff != "BIST") and (adx_mode_eff != "Off"):
        adxBlocks = (~adx_pass)
    else:
        adxBlocks = np.zeros_like(close, dtype=bool)

    blockedL = sqzBlocksL | pinBlocksL | adxBlocks
    blockedS = sqzBlocksS | pinBlocksS | adxBlocks

    df["tce_blocked_long"] = blockedL.astype(bool)
    df["tce_blocked_short"] = blockedS.astype(bool)
    df["tce_sqz_pass_long"] = sqzPassL.astype(bool)
    df["tce_sqz_pass_short"] = sqzPassS.astype(bool)

    df["tce_total_long"] = totalL
    df["tce_total_short"] = totalS

    thr = float(TCE_SCORE_THRESHOLD)
    df["tce_decision_ok_long"] = (totalL >= thr) & (~blockedL)
    df["tce_decision_ok_short"] = (totalS >= thr) & (~blockedS)

    # cross events (bar close)
    df["tce_score_cross_up"] = df["tce_decision_ok_long"] & (df["tce_total_long"].shift(1) < thr)
    df["tce_score_cross_dn"] = df["tce_decision_ok_short"] & (df["tce_total_short"].shift(1) < thr)


def add_tce_columns(df: pd.DataFrame) -> pd.DataFrame:
    _tce_adx_pass(df)
    _tce_squeeze_momentum(df)
    _tce_alpha_trend(df)
    _tce_r_line(df)
    _tce_guppy_vegas_flow(df)
    _tce_scores(df)
    return df


# ================== Sinyal üretimi ==================
def _fmt_price(x: float) -> str:
    if not np.isfinite(x):
        return "-"
    ax = abs(x)
    if ax >= 1000:
        return f"{x:.2f}".rstrip("0").rstrip(".")
    if ax >= 1:
        return f"{x:.4f}".rstrip("0").rstrip(".")
    if ax >= 0.01:
        return f"{x:.5f}".rstrip("0").rstrip(".")
    if ax >= 0.001:
        return f"{x:.6f}".rstrip("0").rstrip(".")
    return f"{x:.8f}".rstrip("0").rstrip(".")

def format_signal(symbol: str, timeframe: str, side: str, df: pd.DataFrame, plan: Optional[dict] = None) -> str:
    """Telegram formatı: kullanıcı şablonu (BUY/SELL + Entry/SL/TP1/TP2 + Tarih)."""
    last = df.iloc[-2]

    # Tarih (Istanbul)
    ts_ms = int(last.get("timestamp", 0))
    dt = datetime.fromtimestamp(ts_ms / 1000, tz=ZoneInfo("UTC")).astimezone(ZoneInfo(DEFAULT_TZ))
    date_str = dt.strftime("%d.%m.%Y")

    if side == "LONG":
        head = f"{symbol} {timeframe}: BUY (LONG) 📈"
    else:
        head = f"{symbol} {timeframe}: SELL (SHORT) 📉"

    price = safe_float(last.get("close", np.nan), np.nan)
    if plan:
        entry = safe_float(plan.get("entry", price), price)
        sl = safe_float(plan.get("sl", np.nan), np.nan)
        tp1 = safe_float(plan.get("tp1", np.nan), np.nan)
        tp2 = safe_float(plan.get("tp2", np.nan), np.nan)
    else:
        entry, sl, tp1, tp2 = price, float("nan"), float("nan"), float("nan")

    lines = [
        head,
        "",
        f"Entry: {_fmt_price(entry)}",
        f"SL: {_fmt_price(sl)}",
        f"TP1: {_fmt_price(tp1)}",
        f"TP2: {_fmt_price(tp2)}",
        f"Tarih: {date_str}",
    ]
    return "\n".join
# =====================
# LTF CONFIRM (4H -> 2H SQZ COLOR CONFIRM)
# =====================
LTF_CONFIRM_ENABLED = True
LTF_CONFIRM_TIMEFRAME = "2h"   # hard-coded: no .env
LTF_CONFIRM_OFFSET_TF = "2h"   # 4h kapanışı teyidi için 2 saat önce başlayan 2H mum

def _tf_to_ms(tf: str) -> int:
    """Convert timeframe like '2h','4h','30m' to milliseconds."""
    tf = (tf or "").strip().lower()
    m = re.fullmatch(r"(\d+)([mhd])", tf)
    if not m:
        raise ValueError(f"Unsupported timeframe: {tf}")
    n = int(m.group(1))
    unit = m.group(2)
    if unit == "m":
        return n * 60 * 1000
    if unit == "h":
        return n * 60 * 60 * 1000
    if unit == "d":
        return n * 24 * 60 * 60 * 1000
    raise ValueError(f"Unsupported timeframe unit: {unit}")

async def ltf_sqz_confirm(symbol: str, bar_open_ts_4h: int, side: str) -> bool:
    """4H sinyal mumunun kapanışına denk gelen 2H teyidi.
    - LONG için: 2H SQZ 'açık yeşil' (mom>0 ve artıyor) olmalı
    - SHORT için: 2H SQZ 'açık kırmızı' (mom<0 ve daha negatif) olmalı
    Teyit mumu: bar_open_ts_4h + 2H (yani 4H mumunun ortasındaki 2H mum; close anında kapanır).
    """
    if not LTF_CONFIRM_ENABLED:
        return True

    try:
        tf_ms_2h = _tf_to_ms(LTF_CONFIRM_OFFSET_TF)
        target_open_ts_2h = int(bar_open_ts_4h) + tf_ms_2h
    except Exception:
        return True  # timeframe parse fail -> block etme

    try:
        data2 = await fetch_ohlcv_async(symbol, LTF_CONFIRM_TIMEFRAME, max(MIN_BARS, 250))
        df2 = ohlcv_to_df(data2)
        if df2 is None or len(df2) < max(60, TCE_SQZ_LEN + 5):
            return False

        # SQZ mom hesapla (LazyBear)
        _tce_squeeze_momentum(df2)
        mom = df2["tce_sqz_mom"].to_numpy(dtype=np.float64)
        mom_prev = np.roll(mom, 1)
        mom_prev[0] = np.nan

        sqz_open_green = (mom > 0) & (mom > mom_prev)   # lime
        sqz_open_red = (mom < 0) & (mom < mom_prev)     # red (daha negatif)

        ts_arr = df2["timestamp"].to_numpy(dtype=np.int64)

        # target timestamp'i bul (tam eşleşme), yoksa en yakını al
        idxs = np.where(ts_arr == target_open_ts_2h)[0]
        if len(idxs) == 0:
            # en yakın mumu seç
            diffs = np.abs(ts_arr - target_open_ts_2h)
            j = int(np.argmin(diffs))
            # 2H mum genişliğinin yarısından büyükse güvenme
            if diffs[j] > int(tf_ms_2h * 0.51):
                return False
            i = j
        else:
            i = int(idxs[-1])

        if side == "LONG":
            return bool(sqz_open_green[i])
        else:
            return bool(sqz_open_red[i])

    except Exception as e:
        logger.debug(f"[LTF_CONFIRM_ERR] {symbol}: {e.__class__.__name__}")
        return False


(lines)


async def check_signals(symbol: str, timeframe: str = '4h'):
    key = f"{symbol}|{timeframe}"
    st = state_map.get(key, PosState())

    # cooldown (Fetch'i boşuna yapmamak için: sadece "iki yön" modunda en başta kes)
    now_ts = time.time()
    if APPLY_COOLDOWN_BOTH_DIRECTIONS and now_ts < st.cooldown_until:
        return

    # fetch
    try:
        data = await fetch_ohlcv_async(symbol, timeframe, max(MIN_BARS, 250))
    except Exception as e:
        logger.debug(f" (veri yok) {symbol} {timeframe}: {e.__class__.__name__}")
        return

    if not data or len(data) < MIN_BARS:
        return

    df = pd.DataFrame(data, columns=["timestamp","open","high","low","close","volume"])
    df["timestamp"] = df["timestamp"].astype(int)
    df[["open","high","low","close","volume"]] = df[["open","high","low","close","volume"]].astype(float)

    # indicators: TCE (volume kolonları sadece filtre açıksa)
    if USE_VOLUME_FILTER:
        df = add_volume_columns(df)
    df = add_tce_columns(df)

    # Bar timestamp (confirmed bar = -2)
    bar_ts = int(df["timestamp"].iloc[-2])

    # Aynı kapanmış mumu tekrar işleme (restart / tekrar tarama spam'ini keser)
    if st.last_bar_ts == bar_ts:
        return

    # Volume filter (opsiyonel)
    if USE_VOLUME_FILTER:
        ok, reason = simple_volume_ok(df)
        if not ok:
            if VERBOSE_LOG:
                logger.debug(f"[VOL_REJECT] {symbol} {timeframe} | {reason}")
            st.last_bar_ts = bar_ts
            state_map[key] = st
            return

    # cross
    cross_long = bool(df["tce_score_cross_up"].iloc[-2]) if "tce_score_cross_up" in df.columns else False
    cross_short = bool(df["tce_score_cross_dn"].iloc[-2]) if "tce_score_cross_dn" in df.columns else False

    # Aynı mumda hem LONG hem SHORT => pas geç
    if cross_long and cross_short:
        st.last_bar_ts = bar_ts
        state_map[key] = st
        return

    if not (cross_long or cross_short):
        # sadece bar işaretle
        st.last_bar_ts = bar_ts
        state_map[key] = st
        return

    side = "LONG" if cross_long else "SHORT"

    # cooldown (yön bazlı)
    if (not APPLY_COOLDOWN_BOTH_DIRECTIONS) and (st.last_side == side) and (now_ts < st.cooldown_until):
        return


    # --- LTF teyit (4H sinyali için 2H SQZ rengi) ---
    if not await ltf_sqz_confirm(symbol, bar_ts, side):
        if VERBOSE_LOG:
            logger.debug(f"[LTF_CONFIRM_REJECT] {symbol} {timeframe} | side={side}")
        st.last_bar_ts = bar_ts
        state_map[key] = st
        return

    # --- TP/SL planı ---
    plan = None
    if TP_SL_ENABLED:
        try:
            plan = compute_tp_sl_plan(df, side)
            if USE_TP_SL_GUARD and plan is not None and not plan.get("guard_ok", True):
                if VERBOSE_LOG:
                    logger.debug(f"[TP_SL_GUARD_REJECT] {symbol} {timeframe} | {plan.get('guard_reason','')}")
                st.last_bar_ts = bar_ts
                state_map[key] = st
                return
        except Exception as e:
            logger.debug(f"[TP_SL_ERR] {symbol} {timeframe}: {e.__class__.__name__}")
            plan = None

    # mesaj
    msg = format_signal(symbol, timeframe, side, df, plan=plan)
    await enqueue_message(msg)

    # state update
    st.last_signal_ts = now_ts
    st.last_side = side
    st.last_bar_ts = bar_ts
    st.cooldown_until = now_ts + COOLDOWN_MINUTES * 60
    state_map[key] = st

# ================== Ana Döngü ==================
_stop = asyncio.Event()

def _handle_stop():
    _stop.set()

async def main():
    load_state()

    loop = asyncio.get_event_loop()
    try:
        for s in (signal.SIGINT, signal.SIGTERM):
            loop.add_signal_handler(s, _handle_stop)
    except NotImplementedError:
        pass

    sender_task = asyncio.create_task(message_sender())

    if STARTUP_MSG_ENABLED and telegram_bot and CHAT_ID and not TEST_MODE:
        await enqueue_message("🤖 Kripto Sinyal Bot başladı (Sinyal motoru: SADECE TCE)")

    await load_markets()

    while not _stop.is_set():
        try:
            symbols = await discover_bybit_symbols(LINEAR_ONLY, QUOTE_WHITELIST)
            if not symbols:
                logger.error("Sembol listesi boş. Bybit markets yüklenemedi olabilir.")
                await asyncio.sleep(SCAN_PAUSE_SEC)
                continue

            random.shuffle(symbols)
            shards = [symbols[i::N_SHARDS] for i in range(N_SHARDS)]

            for i, shard in enumerate(shards, start=1):
                logger.info(f"Shard {i}/{len(shards)} -> {len(shard)} sembol taranacak")
                # shard'ı batch batch tara (RAM/CPU daha stabil)
                for j in range(0, len(shard), max(1, BATCH_SIZE)):
                    batch = shard[j:j + max(1, BATCH_SIZE)]
                    tasks = [check_signals(symbol, timeframe='4h') for symbol in batch]
                    await asyncio.gather(*tasks, return_exceptions=True)
                    await asyncio.sleep(INTER_BATCH_SLEEP)

            save_state()
            await asyncio.sleep(SCAN_PAUSE_SEC)

        except asyncio.CancelledError:
            break
        except Exception as e:
            logger.exception(f"Tur genel hatası: {e}")
            await asyncio.sleep(SCAN_PAUSE_SEC)

    # kapanış
    try:
        await message_queue.join()
    except Exception:
        pass

    sender_task.cancel()
    try:
        if getattr(exchange, "session", None):
            exchange.session.close()
    except Exception:
        pass
    if telegram_bot:
        try:
            await telegram_bot.close()
        except Exception:
            pass

    save_state()
    logger.info("Cleanup tamamlandı, bot kapatıldı.")

if __name__ == "__main__":
    asyncio.run(main())
