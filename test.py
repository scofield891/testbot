import ccxt
import numpy as np
import pandas as pd
import telegram
from telegram.request import HTTPXRequest
from telegram.error import RetryAfter, TimedOut
import logging
import asyncio
import threading
from datetime import datetime, timedelta
import time
import pytz
import sys
import os
import random
import requests
from requests.adapters import HTTPAdapter
from urllib3.util.retry import Retry
from logging.handlers import RotatingFileHandler
import json
from collections import Counter
import hashlib
import uuid
import signal
from dataclasses import dataclass, field
from typing import Optional

# ================== Sabitler ==================
BOT_TOKEN = os.getenv("BOT_TOKEN")
CHAT_ID = os.getenv("CHAT_ID")
TEST_MODE = False
VERBOSE_LOG = True
STARTUP_MSG_ENABLED = True

# ==== LBG (Local Breakout) AYARLARI ====
LBG_BACK_BARS    = 8   # Cross mumu DAHİL geriye bakılacak tepe/dip bar sayısı
LBG_FORWARD_WIN  = 12  # Kesişimden sonra kırılım için beklenecek max bar sayısı

LOOKBACK_ATR = 18
SL_MULTIPLIER = 1.4
TP_MULTIPLIER1 = None
TP_MULTIPLIER2 = None

# Güvenli defaults
TP_MULTIPLIER1 = 1.0 if 'TP_MULTIPLIER1' not in globals() or TP_MULTIPLIER1 is None else TP_MULTIPLIER1
TP_MULTIPLIER2 = 2.0 if 'TP_MULTIPLIER2' not in globals() or TP_MULTIPLIER2 is None else TP_MULTIPLIER2

SL_BUFFER = 0.15
COOLDOWN_MINUTES = 60
INSTANT_SL_BUFFER = 0.04
ADX_PERIOD = 14
APPLY_COOLDOWN_BOTH_DIRECTIONS = True
USE_FROTH_GUARD = False
FROTH_GUARD_K_ATR = 1.2
MAX_CONCURRENT_FETCHES = 4
RATE_LIMIT_MS = 200
N_SHARDS = 5
BATCH_SIZE = 10
INTER_BATCH_SLEEP = 5.0
LINEAR_ONLY = True
QUOTE_WHITELIST = ("USDT",)
VOL_WIN = 60
VOL_Q = 0.60
OBV_SLOPE_WIN = 4
NTX_PERIOD = 14
NTX_K_EFF = 10
NTX_VOL_WIN = 60
NTX_THR_LO, NTX_THR_HI = 44.0, 54.0
NTX_ATRZ_LO, NTX_ATRZ_HI = -1.0, 1.5
NTX_MIN_FOR_HYBRID = 44.0
NTX_RISE_K_STRICT = 5
NTX_RISE_MIN_NET = 1.0
NTX_RISE_POS_RATIO = 0.6
NTX_RISE_EPS = 0.05
NTX_RISE_K_HYBRID = 3
NTX_FROTH_K = 1.0

# EMA Ayarları (Sadece 13 ve 34 kaldı)
EMA_FAST = 13
EMA_MID = 34
ADX_SOFT = 21
MIN_BARS = 80
NEW_SYMBOL_COOLDOWN_MIN = 180
ADX_RISE_K = 5
ADX_RISE_MIN_NET = 1.0
ADX_RISE_POS_RATIO = 0.6
ADX_RISE_EPS = 0.0
ADX_RISE_USE_HYBRID = True

RECENCY_K = 6
RECENCY_OPP_K = 2

USE_GATE_V3 = True
G3_MIN_ADX = 22
G3_MIN_ADX_BEAR = 24
G3_NTX_BONUS_BEAR = 6.0
G3_NTX_SLOPE_WIN = 5
G3_USE_RETEST = False
G3_BOS_LOOKBACK = 12
G3_BOS_CONFIRM_BARS = 2
G3_BOS_MIN_BREAK_ATR = 0.20
G3_SWING_WIN = 7
G3_ENTRY_DIST_EMA13_ATR = 0.90
G3_FF_MIN_SCORE = 3
G3_FF_MIN_SCORE_BEAR = 4
USE_ROBUST_SLOPE = True
SCAN_PAUSE_SEC = 120
BEAR_ADX_ON = 23 # trend ON/OFF eşiği
BEAR_ADX_OFF = 20 # trend ON/OFF eşiği
CLASSIC_MIN_RR = 1.0

# ==== SQZ Breakout Ayarları ====
SQZ_OFF_LOOKBACK = 6 
SQZ_MOM_SLOPE_WIN = 2 
SQZ_RANGE_REQUIRE_RETEST = True 
SQZ_RETEST_MAX_BARS = 3 

# ====== ORDER BLOCK (OB) Ayarları ======
ONLY_OB_MODE = False 
USE_OB_STANDALONE = True
OB_MIN_RR = 1.0
OB_REQUIRE_SMI = True 
OB_REQUIRE_G3_GATE = True 
OB_TREND_FILTER = False # 89 kalktığı için False yapıldı
OB_LOOKBACK = 30
OB_DISPLACEMENT_ATR = 1.50 
OB_BODY_RATIO_MIN = 0.60
OB_FIRST_TOUCH_ONLY = True
OB_RETEST_REQUIRED = True
OB_RETEST_MAX_BARS = 3
OB_STOP_ATR_BUFFER = 0.10
OB_CONS_ATR_THR = 0.50
OB_CONS_VOL_THR = 1.80
OB_MIN_R_OVER_ATR = 0.80

# ---- SAFE DEFAULTS ----
ONLY_OB_MODE = bool(globals().get("ONLY_OB_MODE", False))
SEND_REJECT_MSG = bool(globals().get("SEND_REJECT_MSG", False))
OB_HYBRID = bool(globals().get("OB_HYBRID", False))
OB_REQUIRE_SMI = bool(globals().get("OB_REQUIRE_SMI", False))
OB_REQUIRE_G3_GATE = bool(globals().get("OB_REQUIRE_G3_GATE", False))

# ==== Dynamic mode & profil ====
DYNAMIC_MODE = True
FF_ACTIVE_PROFILE = os.getenv("FF_PROFILE", "garantici")

if FF_ACTIVE_PROFILE == "agresif":
    NTX_LOCAL_WIN = 240
    VOL_MA_RATIO_MIN = 1.02
    VOL_Z_MIN = 0.8
    FF_BODY_MIN = 0.40
    FF_UPWICK_MAX = 0.40
    FF_DNWICK_MAX = 0.40
    FF_BB_MIN = 0.20
    G3_BOS_CONFIRM_BARS = max(1, G3_BOS_CONFIRM_BARS - 1)
else:
    NTX_LOCAL_WIN = 300
    VOL_MA_RATIO_MIN = 1.05
    VOL_Z_MIN = 1.0
    FF_BODY_MIN = 0.45
    FF_UPWICK_MAX = 0.35
    FF_DNWICK_MAX = 0.35
    FF_BB_MIN = 0.22

NTX_LOCAL_Q = 0.60
NTX_Z_EWMA_ALPHA = 0.02
ADX_TREND_ON = 23
R_MAX_ATR_MULT_RANGE = 1.6
R_MAX_ATR_MULT_TREND = 2.2
TP1_MIN_ATR_GAP_RANGE = 0.8
TP1_MIN_ATR_GAP_TREND = 1.0

# ==== Dip-Tepe Parametreleri ====
DIPTEPE_ATR_LEN = 14
DIPTEPE_K_ATR = 1.25
DIPTEPE_BRK_LEN = 4
DIPTEPE_BRK_BUF_ATR = 0.12
DIPTEPE_SEQ_WIN = 3
DIPTEPE_MIN_SEP = 8
DIPTEPE_BODY_MIN = 0.30
DIPTEPE_A_LOOKBACK = 50
STRONG_TREND_ADX = 28 

DEFAULT_TZ = os.getenv("BOT_TZ", "Europe/Istanbul")
SEND_REJECT_MSG = False 

# Telegram throttle
MESSAGE_THROTTLE_SECS = 20.0
STATE_SAVE_DEBOUNCE_SECS = 2.0
_state_lock = threading.Lock()
_stats_lock = asyncio.Lock()
_last_state_save = 0.0
_last_message_hashes = {} 
scan_status = {} 
crit_total_counts = Counter() 
crit_false_counts = Counter() 
new_symbol_until = {} 
_ntx_cache_lock = threading.Lock()
ntx_local_cache = {} 

async def mark_status(symbol: str, code: str, detail: Optional[str] = None):
    async with _stats_lock:
        scan_status[symbol] = {"code": code, "detail": detail}

async def record_crit_batch(criteria):
    for name, ok in criteria:
        crit_total_counts[name] += 1
        if not ok:
            crit_false_counts[name] += 1

# ================== Logging ==================
logger = logging.getLogger()
if not logger.handlers:
    logger.setLevel(logging.INFO)
    formatter = logging.Formatter('%(asctime)s - %(levelname)s - %(message)s')
    console_handler = logging.StreamHandler(sys.stdout)
    console_handler.setFormatter(formatter)
    logger.addHandler(console_handler)
    file_handler = RotatingFileHandler('bot_test.log', maxBytes=5_000_000, backupCount=3)
    file_handler.setFormatter(formatter)
    logger.addHandler(file_handler)

class MinimalInfoFilter(logging.Filter):
    def filter(self, record: logging.LogRecord) -> bool:
        if record.levelno != logging.INFO:
            return True
        msg = str(record.getMessage())
        return (
            msg.startswith("Shard ") or
            msg.startswith("Kriter FALSE dökümü") or
            msg.startswith(" (veri yok)") or
            msg.startswith(" - ")
        )

for h in logger.handlers:
    h.addFilter(MinimalInfoFilter())
logging.getLogger('telegram').setLevel(logging.ERROR)
logging.getLogger('httpx').setLevel(logging.ERROR)

logger.info(f"TP_MULTIPLIER1={TP_MULTIPLIER1}, TP_MULTIPLIER2={TP_MULTIPLIER2}")

# ================== Borsa & Bot ==================
exchange = ccxt.bybit({
    'enableRateLimit': True,
    'options': {'defaultType': 'swap'},
    'timeout': 90000
})
MARKETS = {}
_fetch_sem = asyncio.Semaphore(MAX_CONCURRENT_FETCHES)
_rate_lock = asyncio.Lock()
_last_call_ts = 0.0
_rate_penalty_ms = 0.0

async def load_markets():
    global MARKETS
    if not MARKETS:
        MARKETS = await asyncio.to_thread(exchange.load_markets)
    return MARKETS

def configure_exchange_session(exchange, pool=50):
    s = requests.Session()
    adapter = HTTPAdapter(
        pool_connections=pool,
        pool_maxsize=pool,
        max_retries=Retry(total=3, backoff_factor=0.3, status_forcelist=[429, 500, 502, 503, 504])
    )
    s.mount('https://', adapter)
    s.mount('http://', adapter)
    exchange.session = s

configure_exchange_session(exchange, pool=50)

telegram_bot = telegram.Bot(
    token=BOT_TOKEN,
    request=HTTPXRequest(connection_pool_size=20, pool_timeout=30.0)
) if BOT_TOKEN else None

# ================== Global State ==================
signal_cache = {}
message_queue = asyncio.Queue(maxsize=2000)
STATE_FILE = 'positions_test.json'
DT_KEYS = {"last_signal_time", "entry_time", "last_bar_time", "last_regime_bar"}

@dataclass
class PosState:
    signal: Optional[str] = None
    entry_price: Optional[float] = None
    sl_price: Optional[float] = None
    tp1_price: Optional[float] = None
    tp2_price: Optional[float] = None
    highest_price: Optional[float] = None
    lowest_price: Optional[float] = None
    avg_atr_ratio: Optional[float] = None
    remaining_ratio: float = 1.0
    last_signal_time: Optional[datetime] = None
    last_signal_type: Optional[str] = None
    entry_time: Optional[datetime] = None
    tp1_hit: bool = False
    tp2_hit: bool = False
    last_bar_time: Optional[datetime] = None
    regime_dir: Optional[str] = None
    last_regime_bar: Optional[datetime] = None
    trend_on_prev: bool = False
    used_ob_ids: set = field(default_factory=set)
    tp1_pct: float = 0.0
    tp2_pct: float = 0.0
    rest_pct: float = 1.0
    plan_desc: str = ""

def _default_pos_state():
    return PosState().__dict__.copy()

def _json_default(o):
    if isinstance(o, datetime):
        return o.isoformat()
    return str(o)

def _parse_dt(val):
    if isinstance(val, str):
        try:
            return datetime.fromisoformat(val)
        except Exception:
            return val
    return val

def load_state():
    if os.path.exists(STATE_FILE):
        try:
            with open(STATE_FILE, 'r') as f:
                data = json.load(f)
            for k, v in data.items():
                if isinstance(v, dict):
                    for dk in DT_KEYS:
                         if dk in v:
                            v[dk] = _parse_dt(v[dk])
                    if 'used_ob_ids' in v and isinstance(v['used_ob_ids'], list):
                        v['used_ob_ids'] = set(v['used_ob_ids'])
            return data
        except Exception as e:
            logger.warning(f"State yüklenemedi: {e}")
            return {}
    return {}

def save_state():
    global _last_state_save
    now = time.time()
    if now - _last_state_save < STATE_SAVE_DEBOUNCE_SECS:
        return
    try:
        with _state_lock:
            payload = dict(signal_cache)
            for k, v in payload.items():
                if isinstance(v, dict) and isinstance(v.get('used_ob_ids'), set):
                    v['used_ob_ids'] = list(v['used_ob_ids'])
            with open(STATE_FILE, 'w') as f:
                json.dump(payload, f, default=_json_default)
            _last_state_save = now
    except Exception as e:
        logger.warning(f"State kaydedilemedi: {e}")

signal_cache = load_state()

# ================== Util ==================
def _safe_tz():
    try:
        return pytz.timezone(DEFAULT_TZ)
    except Exception:
        return pytz.UTC

def clamp(x, lo, hi):
    return max(lo, min(hi, x))

def ema_smooth(new, old, alpha=0.3):
    if old is None: return new
    return old * (1 - alpha) + new * alpha

def rolling_z(series: pd.Series, win: int) -> float:
    s = series.tail(win).astype(float)
    if s.size < 5 or s.std(ddof=0) == 0 or not np.isfinite(s.iloc[-1]):
        return 0.0
    return float((s.iloc[-1] - s.mean()) / (s.std(ddof=0) + 1e-12))

def fmt_sym(symbol, x):
    try:
        return exchange.price_to_precision(symbol, float(x))
    except Exception:
        return f"{float(x):.6f}"

def bars_since(mask: pd.Series, idx: int = -2) -> int:
    s = mask.iloc[: idx + 1]
    rev = s.values[::-1]
    return int(np.argmax(rev)) if rev.any() else len(rev)

def format_signal_msg(symbol: str, timeframe: str, side: str,
                     entry: float, sl: float, tp1: float, tp2: float | None,
                     reason_line: str = "EMA Cross veya BOS veya Order Block",
                     tz_name: str = DEFAULT_TZ) -> str:
    tz = _safe_tz()
    date_str = datetime.now(tz).strftime("%d.%m.%Y")
    title = "LBG BOT: BUY (LONG) 🚀" if side == "buy" else "LBG BOT: SELL (SHORT) 📉"
    lines = [
        f"{symbol} {timeframe}: {title}",
        f"Sebep: {reason_line}",
        f"Entry: {fmt_sym(symbol, entry)}",
        f"SL: {fmt_sym(symbol, sl)}",
        f"TP1: {fmt_sym(symbol, tp1)}",
    ]
    if tp2 is not None and abs(tp2 - tp1) > 1e-12:
        lines.append(f"TP2: {fmt_sym(symbol, tp2)}")
    lines.append(f"Tarih: {date_str}")
    return "\n".join(lines)

def rising_ema(series: pd.Series, win: int = 5, eps: float = 0.0, pos_ratio_thr: float = 0.55, **kwargs):
    if 'pos_ratio_th' in kwargs: pos_ratio_thr = kwargs.pop('pos_ratio_th')
    s = pd.to_numeric(series, errors='coerce').dropna()
    if len(s) < win + 2: return False, 0.0, 0.0
    ema = s.ewm(span=win, adjust=False).mean()
    slope = float(ema.iloc[-1] - ema.iloc[-2])
    diffs = np.diff(ema.iloc[-(win+1):].values)
    pos_ratio = float((diffs > eps).mean()) if diffs.size else 0.0
    ok = (slope > eps) and (pos_ratio >= pos_ratio_thr)
    return ok, slope, pos_ratio

def robust_up(series: pd.Series, win: int = 5, eps: float = 0.0, pos_ratio_thr: float = 0.55, **kwargs):
    if 'pos_ratio_th' in kwargs: pos_ratio_thr = kwargs.pop('pos_ratio_th')
    s = pd.to_numeric(series, errors='coerce').dropna()
    if len(s) < win + 2: return False, 0.0, 0.0
    window_vals = s.iloc[-(win+1):].values
    med_d = float(np.median(np.diff(window_vals)))
    pos_ratio = float((np.diff(window_vals) > eps).mean())
    ok = (med_d > eps) and (pos_ratio >= pos_ratio_thr)
    return ok, med_d, pos_ratio

def _last_true_index(s: pd.Series, upto_idx: int) -> int:
    vals = s.iloc[:upto_idx+1]
    vals = vals.fillna(False).astype(bool).values
    for i in range(len(vals)-1, -1, -1):
        if vals[i]: return i
    return -1

def regime_mode_from_adx(adx_last: float) -> str:
    return "trend" if (np.isfinite(adx_last) and adx_last >= ADX_TREND_ON) else "range"

def r_tp_plan(mode: str, is_ob: bool, R: float) -> dict:
    if is_ob:
        return dict(tp1_mult=1.0, tp2_mult=1.5, tp1_pct=0.40, tp2_pct=0.30, rest_pct=0.30, desc="ob")
    if mode == "trend":
        return dict(tp1_mult=1.0, tp2_mult=2.0, tp1_pct=0.30, tp2_pct=0.30, rest_pct=0.40, desc="trend")
    return dict(tp1_mult=0.8, tp2_mult=1.2, tp1_pct=0.40, tp2_pct=0.30, rest_pct=0.30, desc="range")

def r_plan_guards_ok(mode: str, R: float, atr: float, entry: float, tp1_price: float, *, is_ob: bool = False) -> (bool, str):
    if not all(map(np.isfinite, [R, atr, entry, tp1_price])) or atr <= 0 or R <= 0:
        return False, "nan"
    r_over_atr = R / atr
    if is_ob: r_min = 0.80
    else:
        if mode == "trend": r_min = 1.00
        else: r_min = 0.90
    if r_over_atr < r_min:
        return False, f"R/ATR<{r_min:.2f} (got {r_over_atr:.2f})"
    return True, "ok"

def apply_split_to_state(state: dict, plan: dict):
    state['tp1_pct'] = plan['tp1_pct']
    state['tp2_pct'] = plan.get('tp2_pct', 0.0) or 0.0
    state['rest_pct'] = plan['rest_pct']
    state['plan_desc'] = plan['desc']

def build_reason_text(side: str, cross_up_1334: bool, cross_dn_1334: bool, lbg_long: bool, lbg_short: bool, structL: bool, structS: bool, obL_ok: bool, obS_ok: bool, dip_recent: bool, top_recent: bool) -> str:
    tags = []
    if side == "buy":
        if cross_up_1334: tags.append("EMA 13/34 Cross (Up)")
        if lbg_long: tags.append("LBG Breakout")
        if structL: tags.append("BOS Long")
        if obL_ok: tags.append("Order Block Long")
        if dip_recent: tags.append("Dip onaylı")
    else:
        if cross_dn_1334: tags.append("EMA 13/34 Cross (Down)")
        if lbg_short: tags.append("LBG Breakout")
        if structS: tags.append("BOS Short")
        if obS_ok: tags.append("Order Block Short")
        if top_recent: tags.append("Tepe onaylı")
    return " + ".join(tags) if tags else "N/A"

def get_regime_bucket(adx_last: float) -> str:
    if np.isfinite(adx_last):
        if adx_last >= 28: return "strong"
        elif adx_last >= 20: return "neutral"
    return "range"

def _is_local_low(df: pd.DataFrame, i: int, win: int = DIPTEPE_SEQ_WIN) -> bool:
    if i - win < 0 or i + win >= len(df): return False
    lows = df['low'].values
    return lows[i] == np.min(lows[i-win:i+win+1])

def _is_local_high(df: pd.DataFrame, i: int, win: int = DIPTEPE_SEQ_WIN) -> bool:
    if i - win < 0 or i + win >= len(df): return False
    highs = df['high'].values
    return highs[i] == np.max(highs[i-win:i+win+1])

def _bar_body_ratio(row) -> float:
    o, h, l, c = float(row['open']), float(row['high']), float(row['low']), float(row['close'])
    rng = max(h - l, 1e-12)
    return abs(c - o) / rng

def diptepe_signal(df: pd.DataFrame) -> tuple[bool, bool, str]:
    if len(df) < max(DIPTEPE_A_LOOKBACK, DIPTEPE_BRK_LEN + 3) or 'atr' not in df.columns:
        return False, False, "dt_data_short"
    idx_last = len(df) - 2
    atr = float(df['atr'].iloc[idx_last])
    if not np.isfinite(atr) or atr <= 0: return False, False, "dt_nan_atr"
    start = max(5, idx_last - DIPTEPE_A_LOOKBACK)
    dip_i = top_i = None
    for i in range(idx_last - DIPTEPE_MIN_SEP, start, -1):
        if dip_i is None and _is_local_low(df, i, DIPTEPE_SEQ_WIN): dip_i = i
        if top_i is None and _is_local_high(df, i, DIPTEPE_SEQ_WIN): top_i = i
        if dip_i is not None and top_i is not None: break
    dip_ok = top_ok = False
    note = []
    if dip_i is not None:
        ref_level = float(df['high'].iloc[dip_i])
        seq = df.iloc[idx_last - DIPTEPE_BRK_LEN + 1: idx_last + 1]
        if not seq.empty:
            crossed = (seq['close'] > (ref_level + DIPTEPE_BRK_BUF_ATR * atr)).any()
            body_ok = (_bar_body_ratio(df.iloc[idx_last]) >= DIPTEPE_BODY_MIN)
            dip_ok = bool(crossed and body_ok)
            if dip_ok: note.append("DIP")
    if top_i is not None:
        ref_level = float(df['low'].iloc[top_i])
        seq = df.iloc[idx_last - DIPTEPE_BRK_LEN + 1: idx_last + 1]
        if not seq.empty:
            crossed = (seq['close'] < (ref_level - DIPTEPE_BRK_BUF_ATR * atr)).any()
            body_ok = (_bar_body_ratio(df.iloc[idx_last]) >= DIPTEPE_BODY_MIN)
            top_ok = bool(crossed and body_ok)
            if top_ok: note.append("TEPE")
    return dip_ok, top_ok, "+".join(note) if note else "none"

async def enqueue_message(text: str, is_retry: bool = False):
    if not BOT_TOKEN or not CHAT_ID or TEST_MODE:
        if TEST_MODE and VERBOSE_LOG:
             logger.debug(f"[TEST_MODE] Mock Mesaj: {text[:50]}...")
        if not BOT_TOKEN:
            return
    msg_hash = hashlib.md5(text.encode()).hexdigest()
    now = time.time()
    if not is_retry:
        last_sent = _last_message_hashes.get(msg_hash, 0)
        if now - last_sent < MESSAGE_THROTTLE_SECS: return
    try:
        message_queue.put_nowait(text)
        _last_message_hashes[msg_hash] = now
        for h in list(_last_message_hashes.keys()):
            if now - _last_message_hashes[h] > 60.0: del _last_message_hashes[h]
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
            wait_time = getattr(e, 'retry_after', 5) + 2
            await asyncio.sleep(wait_time)
            await enqueue_message(message, is_retry=True)
        except Exception as e:
            logger.error(f"Telegram mesaj hatası: {e}")
        message_queue.task_done()

async def fetch_ohlcv_async(symbol, timeframe, limit):
    global _last_call_ts, _rate_penalty_ms
    max_attempts = 5
    base_ms = RATE_LIMIT_MS
    for attempt in range(1, max_attempts + 1):
        try:
            async with _fetch_sem:
                async with _rate_lock:
                    now = asyncio.get_event_loop().time()
                    wait = max(0.0, (_last_call_ts + (base_ms + _rate_penalty_ms)/1000.0) - now)
                    if wait > 0: await asyncio.sleep(wait)
                    _last_call_ts = asyncio.get_event_loop().time()
                data = await asyncio.to_thread(exchange.fetch_ohlcv, symbol, timeframe, None, limit)
            if _rate_penalty_ms > 0: _rate_penalty_ms = max(0.0, _rate_penalty_ms * 0.6)
            return data
        except (ccxt.RateLimitExceeded, ccxt.DDoSProtection):
            _rate_penalty_ms = min(4000.0, (_rate_penalty_ms * 1.5) + 150.0)
            backoff = 0.8 * attempt + random.random() * 0.6
            await asyncio.sleep(backoff)
        except (ccxt.RequestTimeout, ccxt.NetworkError):
            backoff = 0.6 * attempt + random.random() * 0.6
            await asyncio.sleep(backoff)
    raise ccxt.NetworkError(f"fetch_ohlcv failed after retries: {symbol} {timeframe}")

async def discover_bybit_symbols(linear_only=True, quote_whitelist=("USDT",)):
    global MARKETS
    markets = MARKETS or await load_markets()
    syms = []
    for s, m in markets.items():
        if not m.get('active', True): continue
        if not m.get('swap', False): continue
        if linear_only and not m.get('linear', False): continue
        if m.get('quote') not in quote_whitelist: continue
        syms.append(s)
    return sorted(set(syms))

def simple_volume_ok(df: pd.DataFrame, side: str) -> (bool, str):
    last = df.iloc[-2]
    vol = float(last['volume'])
    vol_ma = float(last['vol_ma']) if pd.notna(last['vol_ma']) else np.nan
    if not (np.isfinite(vol) and np.isfinite(vol_ma) and vol_ma > 0): return False, "vol_nan"
    ratio = vol / vol_ma
    vz = float(df['vol_z'].iloc[-2]) if 'vol_z' in df.columns and pd.notna(df['vol_z'].iloc[-2]) else 0.0
    d = float((df['close'] * df['volume']).iloc[-2])
    d_q = float(df['dvol_q'].iloc[-2]) if 'dvol_q' in df.columns and pd.notna(df['dvol_q'].iloc[-2]) else 0.0
    ratio_ok = (ratio >= VOL_MA_RATIO_MIN)
    vz_ok = (vz >= VOL_Z_MIN)
    d_ok = (d >= d_q) if np.isfinite(d_q) and d_q > 0 else True
    ok = bool(ratio_ok and vz_ok and d_ok)
    return ok, f"ratio={ratio:.2f}{'✓' if ratio_ok else '✗'}, vz={vz:.2f}{'✓' if vz_ok else '✗'}"

def calculate_ema(closes, span):
    return pd.Series(closes).ewm(span=span, adjust=False).mean().values

def calculate_adx(df, symbol, period=ADX_PERIOD):
    df['high_diff'] = df['high'] - df['high'].shift(1)
    df['low_diff'] = df['low'].shift(1) - df['low']
    df['+DM'] = np.where((df['high_diff'] > df['low_diff']) & (df['high_diff'] > 0), df['high_diff'], 0)
    df['-DM'] = np.where((df['low_diff'] > df['high_diff']) & (df['low_diff'] > 0), df['low_diff'], 0)
    high_low = df['high'] - df['low']
    high_close = np.abs(df['high'] - df['close'].shift(1))
    low_close = np.abs(df['low'] - df['close'].shift(1))
    df['TR'] = np.maximum(high_low, np.maximum(high_close, low_close))
    alpha = 1.0 / period
    tr_ema = df['TR'].ewm(alpha=alpha, adjust=False).mean().fillna(0)
    df['di_plus'] = 100 * (df['+DM'].ewm(alpha=alpha, adjust=False).mean() / tr_ema.replace(0, np.nan)).fillna(0)
    df['di_minus'] = 100 * (df['-DM'].ewm(alpha=alpha, adjust=False).mean() / tr_ema.replace(0, np.nan)).fillna(0)
    denom = (df['di_plus'] + df['di_minus']).clip(lower=1e-9)
    df['DX'] = (100 * (df['di_plus'] - df['di_minus']).abs() / denom).replace([np.inf, -np.inf], np.nan)
    df['adx'] = df['DX'].ewm(alpha=alpha, adjust=False).mean()
    return df

def calculate_bb(df, period=20, mult=2.0):
    mid = df['close'].rolling(period).mean()
    std = df['close'].rolling(period).std(ddof=0)
    df['bb_mid'] = mid
    df['bb_std'] = std
    df['bb_upper'] = mid + mult * std
    df['bb_lower'] = mid - mult * std
    return df

def calc_sqzmom_lb(df: pd.DataFrame, length=20, mult_bb=2.0, lengthKC=20, multKC=1.5, use_true_range=True):
    src = df['close'].astype(float)
    basis = src.rolling(length).mean()
    dev = src.rolling(length).std(ddof=0) * mult_bb
    upperBB = basis + dev
    lowerBB = basis - dev
    ma = src.rolling(lengthKC).mean()
    if use_true_range:
        tr1 = (df['high'] - df['low']).astype(float)
        tr2 = (df['high'] - df['close'].shift()).abs().astype(float)
        tr3 = (df['low'] - df['close'].shift()).abs().astype(float)
        tr = pd.concat([tr1, tr2, tr3], axis=1).max(axis=1)
    else:
        tr = (df['high'] - df['low']).astype(float)
    rangema = tr.rolling(lengthKC).mean()
    upperKC = ma + rangema * multKC
    lowerKC = ma - rangema * multKC
    sqz_on = (lowerBB > lowerKC) & (upperBB < upperKC)
    sqz_off = (lowerBB < lowerKC) & (upperBB > upperKC)
    no_sqz = (~sqz_on) & (~sqz_off)
    highest = df['high'].rolling(lengthKC).max()
    lowest = df['low'].rolling(lengthKC).min()
    mid1 = (highest + lowest) / 2.0
    mid2 = src.rolling(lengthKC).mean()
    center = (mid1 + mid2) / 2.0
    series = (src - center)
    val = pd.Series(index=df.index, dtype='float64')
    for i in range(lengthKC-1, len(series)):
        y = series.iloc[i-lengthKC+1:i+1].values
        x = np.arange(lengthKC, dtype=float)
        if np.isfinite(y).sum() >= 2:
            m, b = np.polyfit(x, y, 1)
            val.iloc[i] = m*(lengthKC-1) + b
        else:
            val.iloc[i] = np.nan
    df['lb_sqz_val'] = val
    df['lb_sqz_on'] = sqz_on
    df['lb_sqz_off'] = sqz_off
    df['lb_sqz_no'] = no_sqz
    return df

def ensure_atr(df, period=14):
    if 'atr' in df.columns: return df
    tr1 = (df['high'] - df['low']).abs()
    tr2 = (df['high'] - df['close'].shift()).abs()
    tr3 = (df['low'] - df['close'].shift()).abs()
    tr = pd.concat([tr1, tr2, tr3], axis=1).max(axis=1)
    df['atr'] = tr.ewm(alpha=1/period, adjust=False).mean()
    return df

def calculate_obv_and_volma(df, vol_ma_window=20, spike_window=60):
    close = df['close'].values
    vol = df['volume'].values
    obv = np.zeros_like(close, dtype=float)
    for i in range(1, len(close)):
        if close[i] > close[i-1]: obv[i] = obv[i-1] + vol[i]
        elif close[i] < close[i-1]: obv[i] = obv[i-1] - vol[i]
        else: obv[i] = obv[i-1]
    df['obv'] = obv
    df['vol_ma'] = pd.Series(vol, index=df.index).rolling(vol_ma_window).mean()
    vol_s = pd.Series(vol, index=df.index)
    df['vol_med'] = vol_s.rolling(spike_window).median()
    df['vol_mad'] = vol_s.rolling(spike_window).apply(lambda x: np.median(np.abs(x - np.median(x))), raw=True)
    denom = (1.4826 * df['vol_mad']).replace(0, np.nan)
    df['vol_z'] = (vol_s - df['vol_med']) / denom
    dvol = (df['close'] * df['volume']).astype(float)
    df['dvol_q'] = dvol.rolling(VOL_WIN).quantile(VOL_Q)
    return df

def get_atr_values(df, lookback_atr=LOOKBACK_ATR):
    df = ensure_atr(df, period=14)
    if len(df) < lookback_atr + 2: return np.nan, np.nan
    atr_series = df['atr'].iloc[-(lookback_atr+1):-1].dropna()
    close_last = float(df['close'].iloc[-2]) if pd.notna(df['close'].iloc[-2]) else np.nan
    if atr_series.empty or not np.isfinite(close_last) or close_last == 0: return np.nan, np.nan
    atr_value = float(df['atr'].iloc[-2])
    avg_atr_ratio = float(atr_series.mean() / close_last)
    return atr_value, avg_atr_ratio

def _compute_ntx_z(ntx: pd.Series, win_ema: int = 21, win_q: int = 120) -> pd.Series:
    s = pd.to_numeric(ntx, errors='coerce')
    ema = s.ewm(span=win_ema, adjust=False).mean()
    q50 = s.rolling(win_q, min_periods=max(10, win_q//4)).quantile(0.5)
    q84 = s.rolling(win_q, min_periods=max(10, win_q//4)).quantile(0.84)
    denom = (q84 - q50).replace(0, np.nan)
    z = (ema - q50) / (denom + 1e-12)
    return z.fillna(0.0)

def calculate_indicators(df: pd.DataFrame, symbol: str, timeframe: str) -> pd.DataFrame | None:
    if len(df) < MIN_BARS: return None
    df['timestamp'] = pd.to_datetime(df['timestamp'], unit='ms', utc=True)
    df.set_index('timestamp', inplace=True)
    df.index = df.index.tz_convert(_safe_tz())
    closes = df['close'].values.astype(np.float64)
    df['ema13'] = calculate_ema(closes, EMA_FAST)
    df['ema34'] = calculate_ema(closes, EMA_MID)
    # EMA 89 KALDIRILDI
    df = calculate_bb(df)
    df = calc_sqzmom_lb(df)
    df = calculate_adx(df, symbol)
    df = ensure_atr(df, period=14)
    df = calculate_obv_and_volma(df)
    df = calc_ntx(df)
    if 'ntx' in df.columns:
        df['ntx_z'] = _compute_ntx_z(df['ntx'])
    return df

def calc_ntx(df: pd.DataFrame, period: int = NTX_PERIOD, k_eff: int = NTX_K_EFF) -> pd.DataFrame:
    close = df['close'].astype(float)
    atr = df['atr'].astype(float).replace(0, np.nan)
    ema13 = df['ema13'].astype(float)
    num = (close - close.shift(k_eff)).abs()
    den = close.diff().abs().rolling(k_eff).sum()
    er = (num / (den + 1e-12)).clip(0, 1).fillna(0)
    slope_norm = (ema13 - ema13.shift(k_eff)) / ((atr * k_eff) + 1e-12)
    slope_mag = slope_norm.abs().clip(0, 3) / 3.0
    slope_mag = slope_mag.fillna(0)
    dif = close.diff()
    sign_price = np.sign(dif)
    sign_slope = np.sign(slope_norm.shift(1)).replace(0, np.nan)
    same_dir = (sign_price == sign_slope).astype(float)
    pos_ratio = same_dir.rolling(k_eff).mean().fillna(0)
    vol_ratio = (df['volume'] / df['vol_ma'].replace(0, np.nan)).clip(lower=0).fillna(0)
    vol_sig = np.tanh(np.maximum(0.0, vol_ratio - 1.0)).fillna(0)
    base = (0.35 * er + 0.35 * slope_mag + 0.15 * pos_ratio + 0.15 * vol_sig).clip(0, 1)
    df['ntx_raw'] = base
    df['ntx'] = df['ntx_raw'].ewm(alpha=1.0/period, adjust=False).mean() * 100.0
    return df

def ntx_threshold(atr_z: float) -> float:
    a = clamp((atr_z - NTX_ATRZ_LO) / (NTX_ATRZ_HI - NTX_ATRZ_LO + 1e-12), 0.0, 1.0)
    return NTX_THR_LO + a * (NTX_THR_HI - NTX_THR_LO)

def ntx_vote(df: pd.DataFrame, ntx_thr: float) -> bool:
    if 'ntx' not in df.columns: return False
    ntx_last = float(df['ntx'].iloc[-2]) if pd.notna(df['ntx'].iloc[-2]) else np.nan
    return bool(np.isfinite(ntx_last) and ntx_last >= ntx_thr)

def compute_dynamic_band_k(df: pd.DataFrame, adx_last: float) -> float:
    return 0.25 # Basitleştirildi, EMA 89 olmadığı için çok kritik değil ama SQZ için dursun

def compute_ntx_local_thr(df: pd.DataFrame, base_thr: float, symbol: str = None) -> (float, float):
    q_val = None
    tail = df['ntx'].iloc[-(NTX_LOCAL_WIN+2):-2].dropna()
    min_bars = 40 if FF_ACTIVE_PROFILE == "agresif" else 60
    if len(tail) >= min_bars:
        q_val = float(tail.quantile(NTX_LOCAL_Q))
        if symbol is not None:
            with _ntx_cache_lock:
                ntx_local_cache[symbol] = ema_smooth(q_val, ntx_local_cache.get(symbol, q_val))
                q_val = ntx_local_cache[symbol]
    if q_val is None or not np.isfinite(q_val): return base_thr, float('nan')
    return max(base_thr, q_val), q_val

def candle_body_wicks(row):
    o, h, l, c = float(row['open']), float(row['high']), float(row['low']), float(row['close'])
    rng = max(h - l, 1e-12)
    body = abs(c - o)
    upper_wick = h - max(o, c)
    lower_wick = min(o, c) - l
    return body / rng, upper_wick / rng, lower_wick / rng

def fake_filter_v2(df: pd.DataFrame, side: str, bear_mode: bool) -> (bool, str):
    if len(df) < max(VOL_WIN + 2, OBV_SLOPE_WIN + 2): return False, "data_short"
    last = df.iloc[-2]
    vol_ok, vol_reason = simple_volume_ok(df, side)
    body, up, low = candle_body_wicks(last)
    bb_prox = _bb_prox(last, side=side)
    obv_slope = _obv_slope_recent(df, win=OBV_SLOPE_WIN)
    body_ok = body >= FF_BODY_MIN
    wick_ok = (up <= FF_UPWICK_MAX) if side == "long" else (low <= FF_DNWICK_MAX)
    bb_ok = bb_prox >= FF_BB_MIN
    obv_ok = (obv_slope > 0) if side == "long" else (obv_slope < 0)
    score = int(vol_ok) + int(body_ok) + int(wick_ok) + int(bb_ok) + int(obv_ok)
    ff_min_score = G3_FF_MIN_SCORE_BEAR if bear_mode else G3_FF_MIN_SCORE
    return (score >= ff_min_score), f"score={score}/{ff_min_score} vol={vol_ok}"

def _bb_prox(last, side="long"):
    if side == "long":
        num = float(last['close'] - last['bb_mid']); den = float(last['bb_upper'] - last['bb_mid'])
    else:
        num = float(last['bb_mid'] - last['close']); den = float(last['bb_mid'] - last['bb_lower'])
    if not (np.isfinite(num) and np.isfinite(den)) or den <= 0: return 0.0
    return clamp(num/den, 0.0, 1.0)

def _obv_slope_recent(df: pd.DataFrame, win=OBV_SLOPE_WIN) -> float:
    s = df['obv'].iloc[-(win+1):-1].astype(float) if 'obv' in df.columns else pd.Series(dtype=float)
    if s.size < 3 or s.isna().any(): return 0.0
    if USE_ROBUST_SLOPE:
        ok1, slope1, _ = rising_ema(s, win=win, eps=0.0, pos_ratio_thr=0.55)
        ok2, slope2, _ = robust_up(s, win=win, eps=0.0, pos_ratio_thr=0.55)
        if ok1 or ok2: return float(slope1 if ok1 else slope2)
        return float(np.median(np.diff(s.values)))
    x = np.arange(len(s))
    m, _ = np.polyfit(x, s.values, 1)
    return float(m)

def _recent_sqz_off(df: pd.DataFrame, lookback=SQZ_OFF_LOOKBACK) -> bool:
    if 'lb_sqz_off' not in df.columns or len(df) < lookback + 2: return False
    return bool(df['lb_sqz_off'].iloc[-(lookback+1):-1].any())

def _lb_val_momentum(df: pd.DataFrame, side: str, win=SQZ_MOM_SLOPE_WIN) -> bool:
    if 'lb_sqz_val' not in df.columns or len(df) < win + 3: return False
    v_now = float(df['lb_sqz_val'].iloc[-2])
    v_prev = float(df['lb_sqz_val'].iloc[-3])
    if not (np.isfinite(v_now) and np.isfinite(v_prev)): return False
    if side == "long": return (v_now > 0) and (v_now > v_prev)
    else: return (v_now < 0) and (v_now < v_prev)

def _range_retest_ok(df: pd.DataFrame, side: str, max_bars=SQZ_RETEST_MAX_BARS) -> bool:
    if not SQZ_RANGE_REQUIRE_RETEST: return True
    if 'bb_mid' not in df.columns: return False
    rng = df.iloc[-(max_bars+1):-1]
    if rng.empty: return False
    for i in range(len(rng)):
        row = rng.iloc[i]
        mid = float(row['bb_mid']); c = float(row['close'])
        if not (np.isfinite(mid) and np.isfinite(c)): continue
        prox = abs(c - mid) / max(abs(mid), 1e-12)
        if prox <= 0.005:
            next_row = df.iloc[-2]
            if side == "long": return float(next_row['close']) > float(next_row['open'])
            else: return float(next_row['close']) < float(next_row['open'])
    return False

def _classic_rr_ok(df, side: str, atrv: float, entry: float,
                   tp1_mult: float | None = None,
                   tp2_mult: float | None = None):
    if not (np.isfinite(entry) and np.isfinite(atrv) and atrv > 0):
        return False, None, None, None, None
    TP1_DEF, TP2_DEF = 1.0, 2.0
    if tp1_mult is None: tp1_mult = (TP_MULTIPLIER1 if isinstance(TP_MULTIPLIER1, (int, float)) else TP1_DEF)
    if tp2_mult is None: tp2_mult = (TP_MULTIPLIER2 if isinstance(TP_MULTIPLIER2, (int, float)) else TP2_DEF)
    sl_abs = (SL_MULTIPLIER + SL_BUFFER) * atrv
    if side == "buy":
        sl = entry - sl_abs
        tp1 = entry + (tp1_mult * atrv)
        tp2 = entry + (tp2_mult * atrv) if tp2_mult is not None else None
    else:
        sl = entry + sl_abs
        tp1 = entry - (tp1_mult * atrv)
        tp2 = entry - (tp2_mult * atrv) if tp2_mult is not None else None
    risk = abs(entry - sl)
    reward = abs(tp1 - entry)
    rr = (reward / (risk + 1e-12)) if risk > 0 else 0.0
    return rr >= CLASSIC_MIN_RR, sl, tp1, tp2, rr

def is_sqz_breakout(df: pd.DataFrame, side: str, regime: str, adx_last: float, bear_mode: bool) -> (bool, str):
    if len(df) < 60 or 'lb_sqz_off' not in df.columns or 'lb_sqz_val' not in df.columns:
        return False, "sqz_data_short"
    off_ok = _recent_sqz_off(df, lookback=SQZ_OFF_LOOKBACK)
    if not off_ok: return False, "sqz_not_off"
    mom_ok = _lb_val_momentum(df, side=side, win=SQZ_MOM_SLOPE_WIN)
    if not mom_ok: return False, "lb_val_mom_fail"
    # Trend filtresi (EMA 89) kaldırıldı
    fk_ok, fk_dbg = fake_filter_v2(df, side=side, bear_mode=bear_mode)
    if not fk_ok: return False, f"ff_fail({fk_dbg})"
    if regime == "range":
         if not _range_retest_ok(df, side=side, max_bars=SQZ_RETEST_MAX_BARS):
            return False, "retest_fail"
    entry = float(df['close'].iloc[-2])
    atrv = float(df['atr'].iloc[-2]) if 'atr' in df.columns else np.nan
    ok_rr, _, _, _, rr = _classic_rr_ok(df, "buy" if side=="long" else "sell", atrv, entry)
    if not ok_rr: return False, f"rr<{CLASSIC_MIN_RR} (rr={rr:.2f})"
    return True, "ok"

def _is_swing_high(df, i, win=G3_SWING_WIN):
    if i - win < 0 or i + win >= len(df): return False
    h = df['high'].values
    return h[i] == max(h[i-win:i+win+1])

def _is_swing_low(df, i, win=G3_SWING_WIN):
    if i - win < 0 or i + win >= len(df): return False
    l = df['low'].values
    return l[i] == min(l[i-win:i+win+1])

def _last_swing_levels(df, win=G3_SWING_WIN):
    idx_last = len(df) - 2
    sh = None; sl = None
    for i in range(idx_last-1, max(idx_last-60, 0), -1):
        if sh is None and _is_swing_high(df, i, win=win): sh = float(df['high'].iloc[i])
        if sl is None and _is_swing_low(df, i, win=win): sl = float(df['low'].iloc[i])
        if sh is not None and sl is not None: break
    return sh, sl

# EMA 89 OLMADIĞI İÇİN TREND OK SİLİNDİ

def _ob_trend_filter(df: pd.DataFrame, side: str) -> bool:
    # 89 kalktığı için bu her zaman True döner (devre dışı)
    return True

def _momentum_ok(df, side, adx_last, vote_ntx, ntx_thr, bear_mode, regime: str = None):
    adx_min = 0 if bear_mode else G3_MIN_ADX
    adx_gate = np.isfinite(adx_last) and (adx_last >= adx_min)
    ntx_gate = vote_ntx
    s = df['ntx'] if 'ntx' in df.columns else None
    if s is None: ntx_trend_ok = False
    else:
        ok1, _, _ = rising_ema(s, win=G3_NTX_SLOPE_WIN, eps=0.0, pos_ratio_thr=0.55)
        ok2, _, _ = robust_up(s, win=G3_NTX_SLOPE_WIN, eps=0.0, pos_ratio_thr=0.55)
        ntx_trend_ok = ok1 or ok2
    if regime == "range": mom_ok_base = bool(ntx_gate and ntx_trend_ok)
    else:
        score = int(adx_gate) + int(ntx_gate) + int(ntx_trend_ok)
        mom_ok_base = (score >= 2)
    if DYNAMIC_MODE:
        adx_trend_ok = rising_ema(df['adx'], win=6, pos_ratio_thr=0.6)[0] or robust_up(df['adx'], win=6, pos_ratio_thr=0.6)[0]
        ntx_trend2_ok = rising_ema(df['ntx'], win=5, pos_ratio_thr=0.6)[0] or robust_up(df['ntx'], win=5, pos_ratio_thr=0.6)[0]
        mom_ok = bool(mom_ok_base or (adx_trend_ok and (ntx_gate or ntx_trend2_ok)) or (ntx_trend2_ok and adx_gate))
    else: mom_ok = mom_ok_base
    return mom_ok, ""

def _quality_ok(df, side, bear_mode):
    fk_ok, fk_dbg = fake_filter_v2(df, side=side, bear_mode=bear_mode)
    last = df.iloc[-2]
    ema13 = float(last['ema13']); close = float(last['close']); atrv = float(last['atr'])
    ema13_ok = np.isfinite(atrv) and (abs(close - ema13) <= G3_ENTRY_DIST_EMA13_ATR * atrv)
    return (fk_ok and ema13_ok), f"ff={fk_ok}"

def _classic_sl_only(df, side: str, atrv: float, entry: float):
    sl_abs = (SL_MULTIPLIER + SL_BUFFER) * atrv
    sl = entry - sl_abs if side == "buy" else entry + sl_abs
    return sl

def _tr_series(df):
    high_low = (df['high'] - df['low']).astype(float)
    high_close = (df['high'] - df['close'].shift()).abs().astype(float)
    low_close = (df['low'] - df['close'].shift()).abs().astype(float)
    return pd.concat([high_low, high_close, low_close], axis=1).max(axis=1)

def _ensure_prev_close(df: pd.DataFrame) -> pd.DataFrame:
    if 'close_prev' not in df.columns: df['close_prev'] = df['close'].shift(1)
    return df

def _displacement_candle_ok(df: pd.DataFrame, i: int, side: str) -> bool:
    row = df.iloc[i]
    if not np.isfinite(row.get('atr', np.nan)): return False
    rng = float(row['high'] - row['low'])
    if rng <= 0: return False
    body = abs(float(row['close'] - row['open']))
    if not (_true_range(row) >= OB_DISPLACEMENT_ATR * float(row['atr']) and (body/rng) >= OB_BODY_RATIO_MIN): return False
    if side == 'long' and not (row['close'] > row['open']): return False
    if side == 'short' and not (row['close'] < row['open']): return False
    return _swept_prev_liquidity(df, i, side)

def _true_range(row):
    return max(float(row['high']-row['low']), float(abs(row['high']-row['close_prev'])), float(abs(row['low']-row['close_prev'])))

def _swept_prev_liquidity(df: pd.DataFrame, i: int, side: str) -> bool:
    if i-1 < 0: return False
    prev_h = float(df['high'].iloc[i-1]); prev_l = float(df['low'].iloc[i-1])
    this_h = float(df['high'].iloc[i]); this_l = float(df['low'].iloc[i])
    if side == 'long': return np.isfinite(this_l) and np.isfinite(prev_l) and (this_l < prev_l)
    else: return np.isfinite(this_h) and np.isfinite(prev_h) and (this_h > prev_h)

def _bos_after_displacement(df, side, disp_idx, min_break_atr=G3_BOS_MIN_BREAK_ATR, confirm_bars=G3_BOS_CONFIRM_BARS):
    sh, sl = _last_swing_levels(df)
    if sh is None and sl is None: return False
    rng = df.iloc[disp_idx+1 : disp_idx+1+max(1, confirm_bars)]
    if rng.empty: return False
    atr_ref = float(df['atr'].iloc[disp_idx])
    if side == 'long' and sh is not None: return bool((rng['close'] > sh + min_break_atr * atr_ref).any())
    if side == 'short' and sl is not None: return bool((rng['close'] < sl - min_break_atr * atr_ref).any())
    return False

def _has_fvg_after(df: pd.DataFrame, k: int, side: str) -> bool:
    if k-1 < 0 or k+1 >= len(df): return False
    h_prev = float(df['high'].iloc[k-1]); l_prev = float(df['low'].iloc[k-1])
    h_next = float(df['high'].iloc[k+1]); l_next = float(df['low'].iloc[k+1])
    if side == 'long': return np.isfinite(l_next) and np.isfinite(h_prev) and (l_next > h_prev)
    else: return np.isfinite(h_next) and np.isfinite(l_prev) and (h_next < l_prev)

def _last_opposite_body_zone(df: pd.DataFrame, disp_idx: int, side: str):
    if disp_idx <= 0: return None, None, None
    for i in range(disp_idx-1, max(disp_idx-OB_LOOKBACK, -1), -1):
        r = df.iloc[i]
        if side == 'long':
            if float(r['close']) < float(r['open']): return float(max(r['open'], r['close'])), float(min(r['open'], r['close'])), i
        else:
            if float(r['close']) > float(r['open']): return float(max(r['open'], r['close'])), float(min(r['open'], r['close'])), i
    return None, None, None

def _ob_first_touch_reject(df: pd.DataFrame, idx_last: int, side: str, z_high: float, z_low: float) -> bool:
    bar = df.iloc[idx_last]
    o, h, l, c = map(float, (bar['open'], bar['high'], bar['low'], bar['close']))
    touched = (l <= z_high and h >= z_low) if side=='long' else (h >= z_low and l <= z_high)
    if not touched: return False
    if side == 'long': return (c > o) and (c > z_high)
    else: return (c < o) and (c < z_low)

def _find_displacement_ob(df: pd.DataFrame, side: str):
    if len(df) < max(OB_LOOKBACK+5, 60) or 'atr' not in df.columns: return False, "ob_data_short", None, None, None
    df = _ensure_prev_close(df)
    idx_last = len(df) - 2
    atr_series = df['atr']
    for k in range(idx_last-2, max(idx_last-OB_LOOKBACK, 2), -1):
        if not _displacement_candle_ok(df, k, side): continue
        if not _has_fvg_after(df, k, side): continue
        if not _bos_after_displacement(df, side, k): continue
        z_high, z_low, opp_idx = _last_opposite_body_zone(df, k, side)
        if z_high is None: continue
        atrv_k = float(atr_series.iloc[k])
        if abs(z_high - z_low) > 0.60 * atrv_k: continue
        if not _ob_first_touch_reject(df, idx_last, side, z_high, z_low): continue
        if OB_FIRST_TOUCH_ONLY:
            post = df.iloc[k+1:idx_last]
            if side == 'long' and ((post['low'] <= z_high) & (post['high'] >= z_low)).any(): continue
            if side == 'short' and ((post['high'] >= z_low) & (post['low'] <= z_high)).any(): continue
        ob_id = f"{int(df.index[k].value)}_{side}_{round(z_high,6)}_{round(z_low,6)}"
        return True, "strict_ob_ok", z_high, z_low, ob_id
    return False, "no_ob", None, None, None

def _ob_rr_ok(df: pd.DataFrame, side: str, z_high: float | None, z_low: float | None):
    if z_high is None or z_low is None or 'atr' not in df.columns or len(df) < 3: return False, None, None
    entry = float(df['close'].iloc[-2]); atrv = float(df['atr'].iloc[-2])
    buf = OB_STOP_ATR_BUFFER * atrv
    sl_price = float(z_low) - buf if side == "long" else float(z_high) + buf
    R = abs(entry - sl_price)
    if R/atrv < OB_MIN_R_OVER_ATR: return False, None, None
    return True, (sl_price, None, None), (entry, 1.0)

def _order_block_cons_fallback(df: pd.DataFrame, side: str, lookback=10) -> (bool, str):
    if not OB_HYBRID: return False, "hybrid_off"
    idx_last = len(df) - 2
    win = df.iloc[idx_last - lookback:idx_last]
    if (win['atr'] <= OB_CONS_ATR_THR * win['atr'].mean()).mean() < 0.7: return False, "cons_fail"
    c_last = float(df['close'].iloc[idx_last])
    brk = c_last > float(win['high'].max()) if side == 'long' else c_last < float(win['low'].min())
    return bool(brk), "cons_break"

def _tighten_fake_filter_range(df: pd.DataFrame, side: str, fk_ok: bool) -> (bool, str):
    if not fk_ok: return False, "ff_base_fail"
    last = df.iloc[-2]
    body, up, low = candle_body_wicks(last)
    body_min = max(FF_BODY_MIN, 0.50)
    up_max = min(FF_UPWICK_MAX, 0.30)
    dn_max = min(FF_DNWICK_MAX, 0.30)
    bb_prox = _bb_prox(last, side)
    body_ok = (body >= body_min)
    wick_ok = (up <= up_max) if side == "long" else (low <= dn_max)
    bb_ok = (bb_prox >= max(FF_BB_MIN, 0.30))
    return bool(body_ok and wick_ok and bb_ok), "tight_ok"

def _score_side(side, ok_gate, struct_ok, adx_last, ntx_last, ff_ok):
    score = 0
    score += 2 if ok_gate else 0
    score += 2 if struct_ok else 0
    score += 1 if ((adx_last or 0) >= 23) else 0
    score += 1 if ((ntx_last or 0) >= 50) else 0
    score += 1 if ff_ok else 0
    return score

def _summarize_coverage(all_symbols):
    codes = {s: scan_status.get(s, {}).get('code') for s in all_symbols}
    return {
        "total": len(all_symbols),
        "ok": sum(1 for c in codes.values() if c == 'completed'),
        "error": sum(1 for c in codes.values() if c == 'error'),
        "skip": sum(1 for c in codes.values() if c == 'skip')
    }

def _log_false_breakdown():
    logger.info("Kriter FALSE dökümü (yüksekten düşüğe):")
    if not crit_total_counts:
        logger.info(" (veri yok)")
        return
    items = sorted(crit_total_counts.items(), key=lambda kv: crit_false_counts[kv[0]], reverse=True)
    for name, total in items:
        f = crit_false_counts[name]
        logger.info(f" - {name}: {f}/{total} ({(f/total*100):.1f}%)")

async def entry_gate_v3(df, side, adx_last, vote_ntx, ntx_thr, bear_mode, symbol=None, regime: str = None):
    # Trend filtresi (EMA 89) kaldırıldı, sadece momentum ve kalite bakıyoruz
    ntx_q = float('nan')
    if DYNAMIC_MODE:
        ntx_thr, ntx_q = compute_ntx_local_thr(df, base_thr=ntx_thr, symbol=symbol)
    mom_ok_base, m_dbg = _momentum_ok(df, side, adx_last, vote_ntx, ntx_thr, bear_mode, regime=regime)
    quality_ok, q_dbg = _quality_ok(df, side, bear_mode)
    return (mom_ok_base and quality_ok), f"mom={mom_ok_base}, qual={quality_ok}"

async def check_signals(symbol: str, timeframe: str = '4h') -> None:
    tz = _safe_tz()
    try:
        await mark_status(symbol, "started")
        now = datetime.now(tz)
        until = new_symbol_until.get(symbol)
        if until and now < until:
            await mark_status(symbol, "cooldown", "new_symbol_cooldown")
            return

        limit_need = max(150, LOOKBACK_ATR + 80, ADX_PERIOD + 40)
        ohlcv = await fetch_ohlcv_async(symbol, timeframe, limit=limit_need)
        df = pd.DataFrame(ohlcv, columns=['timestamp', 'open', 'high', 'low', 'close', 'volume'])
        if df is None or df.empty or len(df) < MIN_BARS:
            new_symbol_until[symbol] = now + timedelta(minutes=NEW_SYMBOL_COOLDOWN_MIN)
            await mark_status(symbol, "min_bars", f"bars={len(df) if df is not None else 0}")
            return

        calc = calculate_indicators(df, symbol, timeframe)
        if calc is None:
            await mark_status(symbol, "skip", "indicators_failed")
            return
        df = calc

        atr_value, avg_atr_ratio = get_atr_values(df, LOOKBACK_ATR)
        if not np.isfinite(atr_value):
            await mark_status(symbol, "skip", "invalid_atr")
            return

        adx_last = float(df['adx'].iloc[-2]) if pd.notna(df['adx'].iloc[-2]) else np.nan
        regime = get_regime_bucket(adx_last)
        atr_z = rolling_z(df['atr'], LOOKBACK_ATR) if 'atr' in df else 0.0

        async with _stats_lock:
            trend_prev = signal_cache.get(f"{symbol}_{timeframe}", _default_pos_state()).get('trend_on_prev', False)
        trend_on = (np.isfinite(adx_last) and ((adx_last >= BEAR_ADX_ON) or (trend_prev and adx_last > BEAR_ADX_OFF)))
        bull_mode = bool(trend_on)
        bear_mode = not bull_mode
        cur_key = f"{symbol}_{timeframe}"

        async with _stats_lock:
            st = signal_cache.setdefault(cur_key, _default_pos_state())
            st['used_ob_ids'] = set(st.get('used_ob_ids', []))
            used_set = set(st['used_ob_ids'])
            st['trend_on_prev'] = bull_mode
            signal_cache[cur_key] = st

        ntx_thr = ntx_threshold(atr_z)
        vote_ntx = ntx_vote(df, ntx_thr)
        dip_ok, top_ok, dt_tag = diptepe_signal(df)
        fk_ok_L, fk_dbg_L = fake_filter_v2(df, side="long", bear_mode=bear_mode)
        fk_ok_S, fk_dbg_S = fake_filter_v2(df, side="short", bear_mode=bear_mode)
        if regime == "range":
            fk_ok_L, _ = _tighten_fake_filter_range(df, side="long", fk_ok=fk_ok_L)
            fk_ok_S, _ = _tighten_fake_filter_range(df, side="short", fk_ok=fk_ok_S)

        smi_val_now = float(df['lb_sqz_val'].iloc[-2])
        smi_open_green = (smi_val_now > 0) and (smi_val_now > float(df['lb_sqz_val'].iloc[-3]))
        smi_open_red = (smi_val_now < 0) and (smi_val_now < float(df['lb_sqz_val'].iloc[-3]))
        is_green = (df['close'].iloc[-2] > df['open'].iloc[-2])
        is_red = (df['close'].iloc[-2] < df['open'].iloc[-2])

        okL, _ = await entry_gate_v3(df, "long", adx_last, vote_ntx, ntx_thr, bear_mode, symbol, regime)
        okS, _ = await entry_gate_v3(df, "short", adx_last, vote_ntx, ntx_thr, bear_mode, symbol, regime)

        # OB Logic (89 Filtresi Çıkarıldı)
        obL_ok, _, obL_high, obL_low, obL_id = _find_displacement_ob(df, side="long")
        obS_ok, _, obS_high, obS_low, obS_id = _find_displacement_ob(df, side="short")
        if OB_HYBRID and not obL_ok:
            if _order_block_cons_fallback(df, "long")[0]: obL_ok = True
        if OB_HYBRID and not obS_ok:
            if _order_block_cons_fallback(df, "short")[0]: obS_ok = True

        obL_rr_ok, obL_prices, _ = _ob_rr_ok(df, "long", obL_high, obL_low)
        obS_rr_ok, obS_prices, _ = _ob_rr_ok(df, "short", obS_high, obS_low)
        # EMA 89 filtresi OB için de kapalı
        obL_trend_ok = True 
        obS_trend_ok = True
        
        ob_req_smi = bool(OB_REQUIRE_SMI)
        ob_req_gate = bool(OB_REQUIRE_G3_GATE)
        obL_smi_ok = (not ob_req_smi) or (smi_open_green and is_green)
        obS_smi_ok = (not ob_req_smi) or (smi_open_red and is_red)
        obL_gate_ok = (not ob_req_gate) or okL
        obS_gate_ok = (not ob_req_gate) or okS
        obL_touch_ok = (not OB_FIRST_TOUCH_ONLY) or (obL_id and (obL_id not in used_set))
        obS_touch_ok = (not OB_FIRST_TOUCH_ONLY) or (obS_id and (obS_id not in used_set))

        ob_buy_standalone = USE_OB_STANDALONE and obL_ok and obL_rr_ok and obL_smi_ok and obL_gate_ok and obL_touch_ok
        ob_sell_standalone = USE_OB_STANDALONE and obS_ok and obS_rr_ok and obS_smi_ok and obS_gate_ok and obS_touch_ok

        # SQZ Logic (EMA 89 yok)
        sqzL_ok, _ = is_sqz_breakout(df, "long", regime, adx_last, bear_mode)
        sqzS_ok, _ = is_sqz_breakout(df, "short", regime, adx_last, bear_mode)

        # === EMA 13/34 Cross ===
        e13 = df['ema13']; e34 = df['ema34']
        e13_prev, e34_prev = e13.iloc[-3], e34.iloc[-3]
        e13_last, e34_last = e13.iloc[-2], e34.iloc[-2]
        
        cross_up_1334 = (pd.notna(e13_prev) and pd.notna(e34_prev) and pd.notna(e13_last) and pd.notna(e34_last)
                         and (e13_prev <= e34_prev) and (e13_last > e34_last))
        cross_dn_1334 = (pd.notna(e13_prev) and pd.notna(e34_prev) and pd.notna(e13_last) and pd.notna(e34_last)
                         and (e13_prev >= e34_prev) and (e13_last < e34_last))
        
        cross_up_series = (e13.shift(1) <= e34.shift(1)) & (e13 > e34)
        cross_dn_series = (e13.shift(1) >= e34.shift(1)) & (e13 < e34)
        idx_lastbar = len(df) - 2
        idx_up = _last_true_index(cross_up_series, idx_lastbar)
        idx_dn = _last_true_index(cross_dn_series, idx_lastbar)

        # === LBG (Local Breakout) SİSTEMİ ===
        # Burada EMA 89'dan bağımsız, sadece 13/34 kesişimi sonrası lokal kırılım aranıyor.
        lbg_long = False
        if idx_up >= 0:
            bars_since = idx_lastbar - idx_up
            if 0 < bars_since <= LBG_FORWARD_WIN:
                lookback_idx = max(0, idx_up - (LBG_BACK_BARS - 1))
                ref_high = df['high'].iloc[lookback_idx : idx_up + 1].max()
                check_range = df.iloc[idx_up + 1 : idx_lastbar + 1]
                if not check_range.empty and (check_range['close'] > ref_high).any():
                    lbg_long = True
                    if VERBOSE_LOG: logger.debug(f"{symbol} {timeframe}: LBG LONG! Cross@{idx_up}, Ref={ref_high:.4f}")

        lbg_short = False
        if idx_dn >= 0:
            bars_since = idx_lastbar - idx_dn
            if 0 < bars_since <= LBG_FORWARD_WIN:
                lookback_idx = max(0, idx_dn - (LBG_BACK_BARS - 1))
                ref_low = df['low'].iloc[lookback_idx : idx_dn + 1].min()
                check_range = df.iloc[idx_dn + 1 : idx_lastbar + 1]
                if not check_range.empty and (check_range['close'] < ref_low).any():
                    lbg_short = True
                    if VERBOSE_LOG: logger.debug(f"{symbol} {timeframe}: LBG SHORT! Cross@{idx_dn}, Ref={ref_low:.4f}")
        
        structL, structS = False, False

        # === ENTRY LOGIC (EMA 89 YOK, SADECE LBG + MOM + FILTER) ===
        buy_classic = (lbg_long and smi_open_green and is_green and okL and fk_ok_L)
        sell_classic = (lbg_short and smi_open_red and is_red and okS and fk_ok_S)

        buy_ob = ob_buy_standalone
        sell_ob = ob_sell_standalone
        buy_sqz = (not buy_ob) and sqzL_ok
        sell_sqz = (not sell_ob) and sqzS_ok
        buy_ema = (not buy_ob) and (not buy_sqz) and buy_classic
        sell_ema = (not sell_ob) and (not sell_sqz) and sell_classic

        if ONLY_OB_MODE:
            buy_condition = ob_buy_standalone
            sell_condition = ob_sell_standalone
            reason = "Order Block"
        else:
            buy_condition = bool(buy_ob or buy_sqz or buy_ema)
            sell_condition = bool(sell_ob or sell_sqz or sell_ema)
            if buy_condition:
                if buy_ob: reason = "Order Block"
                elif buy_sqz: reason = "SQZ Breakout"
                else: reason = "LBG Breakout (13/34)"
            elif sell_condition:
                if sell_ob: reason = "Order Block"
                elif sell_sqz: reason = "SQZ Breakout"
                else: reason = "LBG Breakout (13/34)"
            else: reason = "N/A"

        criteria = [
            ("cross_up_1334", cross_up_1334),
            ("cross_dn_1334", cross_dn_1334),
            ("lbg_long", lbg_long),
            ("lbg_short", lbg_short),
            ("smi_open_green", smi_open_green),
            ("smi_open_red", smi_open_red),
            ("fk_long", fk_ok_L),
            ("fk_short", fk_ok_S),
            ("is_green", is_green),
            ("is_red", is_red),
            ("order_block_long", obL_ok),
            ("order_block_short", obS_ok),
            ("sqz_long", sqzL_ok),
            ("sqz_short", sqzS_ok),
        ]
        await record_crit_batch(criteria)

        if buy_condition and sell_condition:
            new_symbol_until[symbol] = now + timedelta(minutes=NEW_SYMBOL_COOLDOWN_MIN)
            await mark_status(symbol, "skip", "conflict")
            return

        # Position Management & Signaling
        bar_time = df.index[-2]
        if not isinstance(bar_time, (pd.Timestamp, datetime)): bar_time = pd.to_datetime(bar_time, errors="ignore")
        
        async with _stats_lock:
            current_pos = signal_cache.setdefault(cur_key, _default_pos_state())
            # Ensure used_ob_ids is set
            if not isinstance(current_pos.get('used_ob_ids'), set):
                 current_pos['used_ob_ids'] = set(current_pos.get('used_ob_ids', []))

        same_bar = (pd.Timestamp(current_pos.get('last_bar_time')).value == pd.Timestamp(bar_time).value) if current_pos.get('last_bar_time') else False
        exit_cross_long = (e13.shift(1) >= e34.shift(1)) & (e13 < e34)
        exit_cross_short = (e13.shift(1) <= e34.shift(1)) & (e13 > e34)
        exit_long = exit_cross_long.iloc[-2]
        exit_short = exit_cross_short.iloc[-2]

        if (buy_condition or sell_condition) and (current_pos['signal'] is not None):
            new_signal = 'buy' if buy_condition else 'sell'
            if current_pos['signal'] != new_signal:
                current_price = float(df['close'].iloc[-1])
                await enqueue_message(f"{symbol} {timeframe}: REVERSAL CLOSE 🔁")
                async with _stats_lock:
                    signal_cache[cur_key] = _default_pos_state()
                    signal_cache[cur_key]['trend_on_prev'] = bull_mode
                save_state()
                async with _stats_lock: current_pos = signal_cache[cur_key]

        if buy_condition and current_pos['signal'] != 'buy':
            if not same_bar:
                entry_price = float(df['close'].iloc[-2])
                if ob_buy_standalone and obL_prices:
                    sl_price, _, _ = obL_prices
                else:
                    sl_price = _classic_sl_only(df, "buy", atr_value, entry_price)
                R = abs(entry_price - sl_price)
                mode = regime_mode_from_adx(adx_last)
                plan = r_tp_plan(mode, ob_buy_standalone, R)
                tp1_price = entry_price + plan['tp1_mult'] * R
                tp2_price = (entry_price + plan['tp2_mult'] * R) if plan['tp2_mult'] else None
                
                ok_guard, why_guard = r_plan_guards_ok(mode, R, atr_value, entry_price, tp1_price, is_ob=ob_buy_standalone)
                if ok_guard:
                    async with _stats_lock:
                        current_pos.update({
                            'signal': 'buy', 'entry_price': entry_price, 'sl_price': sl_price,
                            'tp1_price': tp1_price, 'tp2_price': tp2_price,
                            'last_signal_time': now, 'last_signal_type': 'buy',
                            'last_bar_time': bar_time, 'trend_on_prev': bull_mode
                        })
                        apply_split_to_state(current_pos, plan)
                        if ob_buy_standalone and obL_id: used_set.add(obL_id)
                        st = signal_cache[cur_key]
                        st.update(current_pos)
                        st['used_ob_ids'] = set(used_set)
                        signal_cache[cur_key] = st
                    
                    await enqueue_message(format_signal_msg(symbol, timeframe, "buy", entry_price, sl_price, tp1_price, tp2_price, reason))
                    save_state()

        elif sell_condition and current_pos['signal'] != 'sell':
             if not same_bar:
                entry_price = float(df['close'].iloc[-2])
                if ob_sell_standalone and obS_prices:
                    sl_price, _, _ = obS_prices
                else:
                    sl_price = _classic_sl_only(df, "sell", atr_value, entry_price)
                R = abs(entry_price - sl_price)
                mode = regime_mode_from_adx(adx_last)
                plan = r_tp_plan(mode, ob_sell_standalone, R)
                tp1_price = entry_price - plan['tp1_mult'] * R
                tp2_price = (entry_price - plan['tp2_mult'] * R) if plan['tp2_mult'] else None
                
                ok_guard, why_guard = r_plan_guards_ok(mode, R, atr_value, entry_price, tp1_price, is_ob=ob_sell_standalone)
                if ok_guard:
                    async with _stats_lock:
                        current_pos.update({
                            'signal': 'sell', 'entry_price': entry_price, 'sl_price': sl_price,
                            'tp1_price': tp1_price, 'tp2_price': tp2_price,
                            'last_signal_time': now, 'last_signal_type': 'sell',
                            'last_bar_time': bar_time, 'trend_on_prev': bull_mode
                        })
                        apply_split_to_state(current_pos, plan)
                        if ob_sell_standalone and obS_id: used_set.add(obS_id)
                        st = signal_cache[cur_key]
                        st.update(current_pos)
                        st['used_ob_ids'] = set(used_set)
                        signal_cache[cur_key] = st

                    await enqueue_message(format_signal_msg(symbol, timeframe, "sell", entry_price, sl_price, tp1_price, tp2_price, reason))
                    save_state()

        # Exit/TP logic
        if current_pos['signal'] == 'buy':
            current_price = float(df['close'].iloc[-1])
            if exit_long:
                 async with _stats_lock:
                    signal_cache[cur_key] = _default_pos_state()
                 await enqueue_message(f"{symbol} {timeframe}: EMA EXIT (LONG) 🔁")
                 save_state()
        elif current_pos['signal'] == 'sell':
            current_price = float(df['close'].iloc[-1])
            if exit_short:
                 async with _stats_lock:
                     signal_cache[cur_key] = _default_pos_state()
                 await enqueue_message(f"{symbol} {timeframe}: EMA EXIT (SHORT) 🔁")
                 save_state()

        await mark_status(symbol, "completed")

    except Exception as e:
        logger.exception(f"{symbol} {timeframe}: Hata")
        await mark_status(symbol, "error", str(e))

_stop = asyncio.Event()
def _handle_stop(): _stop.set()

async def main():
    loop = asyncio.get_event_loop()
    try:
        for s in (signal.SIGINT, signal.SIGTERM): loop.add_signal_handler(s, _handle_stop)
    except NotImplementedError: pass
    asyncio.create_task(message_sender())
    if STARTUP_MSG_ENABLED: await enqueue_message("TEST BOT BAŞLATILDI! (SADE LBG + NO 89) 🚀")
    await load_markets()
    while not _stop.is_set():
        try:
            async with _stats_lock: scan_status.clear()
            crit_false_counts.clear(); crit_total_counts.clear()
            symbols = await discover_bybit_symbols(linear_only=LINEAR_ONLY, quote_whitelist=QUOTE_WHITELIST)
            random.shuffle(symbols)
            shards = [symbols[i::N_SHARDS] for i in range(N_SHARDS)]
            for i, shard in enumerate(shards, start=1):
                logger.info(f"Shard {i}/{len(shards)} -> {len(shard)} sembol taranacak")
                tasks = [check_signals(symbol, timeframe='4h') for symbol in shard]
                await asyncio.gather(*tasks, return_exceptions=True)
                await asyncio.sleep(INTER_BATCH_SLEEP)
            _log_false_breakdown()
            await asyncio.sleep(SCAN_PAUSE_SEC)
        except Exception as e:
            logger.exception(f"Tur hatası: {e}")
            await asyncio.sleep(SCAN_PAUSE_SEC)

if __name__ == "__main__":
    asyncio.run(main())
