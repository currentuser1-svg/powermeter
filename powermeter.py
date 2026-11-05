#!/usr/bin/env python3
"""
powermeter — сколько электроэнергии съели CPU и GPU: кВт·ч по дням и месяцам.

Ватты берутся из LibreHardwareMonitor через его веб-сервер (data.json):
«CPU Package» процессора и «GPU Package» видеокарты. Раз в POLL_SECONDS
значения снимаются, мощность интегрируется по времени, Вт·ч копятся по часам
в SQLite рядом со скриптом. Только стандартная библиотека Python 3.8+.

В LHM включить: Options → Remote Web Server → Run (порт по умолчанию 8085).

  python powermeter.py sensors          проверить связь с LHM и какие сенсоры взяты
  python powermeter.py run              логгер + страничка http://127.0.0.1:8087
  python powermeter.py report [ГГГГ-ММ] отчёт в консоль: по дням и по месяцам
"""
from __future__ import annotations

import argparse
import base64
import calendar
import html
import http.client
import json
import logging
import logging.handlers
import math
import os
import re
import signal
import sqlite3
import sys
import threading
import time
import urllib.error
import urllib.parse
import urllib.request
from datetime import date, datetime
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path

# ═══════════════════════════════ настройки ═══════════════════════════════

LHM_URL = "http://127.0.0.1:8085/data.json"
LHM_USER = ""           # если в LHM включено Remote Web Server → Authentication
LHM_PASSWORD = ""

# Канал → какие сенсоры в него суммировать.
# None — автопоиск: CPU = «CPU Package», GPU = «GPU Package» дискретной карты
# (встройку не берём, она и так сидит внутри CPU Package).
# Можно явно списком SensorId — их показывает `python powermeter.py sensors`:
#   "GPU": ["/gpu-nvidia/0/power/0"],
CHANNELS = {
    "CPU": None,
    "GPU": None,
}

POLL_SECONDS = 2        # как часто спрашивать LHM (сам LHM обновляется раз в 1 с)
FLUSH_SECONDS = 30      # как часто сбрасывать накопленное в базу
MAX_GAP_SECONDS = 30    # дыру длиннее (сон, LHM закрыт) не интерполируем — она не считается
MAX_WATTS = 1500        # больше — глюк датчика, такое значение пропускаем

WEB_HOST = "127.0.0.1"  # "0.0.0.0" — открыть страничку в локалку
WEB_PORT = 8087         # 0 — без странички

# «≈ от розетки» — оценка. Датчики видят только CPU и GPU, а ещё есть плата,
# память, диски, вентиляторы, USB и потери в блоке питания. Монитор не входит.
# Есть ваттметр или умная розетка — подгони эти два числа по ней.
OTHER_WATTS = 30        # Вт на всё остальное, пока комп работает
PSU_EFFICIENCY = 0.85   # КПД блока питания на такой нагрузке
TARIFF = 4.32           # цена за кВт·ч
CURRENCY = "грн"

BASE_DIR = Path(__file__).resolve().parent
DB_PATH = BASE_DIR / "powermeter.db"
LOG_PATH = BASE_DIR / "powermeter.log"

# ══════════════════════════════════════════════════════════════════════════

log = logging.getLogger("powermeter")

MONTHS = ("Январь", "Февраль", "Март", "Апрель", "Май", "Июнь",
          "Июль", "Август", "Сентябрь", "Октябрь", "Ноябрь", "Декабрь")
MONTHS_GEN = ("января", "февраля", "марта", "апреля", "мая", "июня",
              "июля", "августа", "сентября", "октября", "ноября", "декабря")
WEEKDAYS = ("пн", "вт", "ср", "чт", "пт", "сб", "вс")


def num(x: float, nd: int = 2, group: str = " ") -> str:
    """1234.5 → '1 234,50': запятая и пробел между тысячами."""
    return f"{x:,.{nd}f}".replace(",", "\0").replace(".", ",").replace("\0", group)


def month_title(y: int, m: int) -> str:
    return f"{MONTHS[m - 1]} {y}"


def next_month(y: int, m: int) -> tuple:
    return (y + 1, 1) if m == 12 else (y, m + 1)


def prev_month(y: int, m: int) -> tuple:
    return (y - 1, 12) if m == 1 else (y, m - 1)


def parse_month(s: str):
    """'2026-11' → (2026, 11); пусто → текущий месяц; мусор → None."""
    s = (s or "").strip()
    if not s:
        t = date.today()
        return t.year, t.month
    mt = re.fullmatch(r"(\d{4})-(\d{1,2})", s)
    if mt and 1 <= int(mt.group(2)) <= 12:
        return int(mt.group(1)), int(mt.group(2))
    return None


def avg_w(wh: float, secs: float) -> float:
    return wh / (secs / 3600) if secs > 0 else 0.0


def wall_kwh(wh: float, secs: float) -> float:
    """Оценка «от розетки»: (CPU+GPU + прочее) / КПД блока питания."""
    eff = PSU_EFFICIENCY if PSU_EFFICIENCY > 0 else 1.0
    return (wh + OTHER_WATTS * secs / 3600) / eff / 1000


# ═══════════════════════════ LibreHardwareMonitor ═══════════════════════════

class LHMError(Exception):
    pass


_OPENER = urllib.request.build_opener(urllib.request.ProxyHandler({}))  # мимо системного прокси
_NUM = re.compile(r"-?\d+(?:[.,]\d+)?")

# канал: (какие SensorId вообще подходят, «родной» индекс сенсора, имена сенсора)
# По индексу — на случай, если сенсор переименован в LHM.
_AUTO = {
    "CPU": (re.compile(r"^/(?:intelcpu|amdcpu)/\d+/power/\d+$"),
            re.compile(r"^/(?:intelcpu|amdcpu)/\d+/power/0$"),
            ("CPU Package", "Package")),
    "GPU": (re.compile(r"^/gpu-(?:nvidia|amd)/\d+/power/\d+$"),
            re.compile(r"^/gpu-nvidia/\d+/power/0$|^/gpu-amd/\d+/power/3$"),
            ("GPU Package",)),
}


def fetch_lhm(url: str, timeout: float = 3.0) -> dict:
    req = urllib.request.Request(url, headers={"Accept": "application/json"})
    if LHM_USER:
        token = base64.b64encode(f"{LHM_USER}:{LHM_PASSWORD}".encode()).decode()
        req.add_header("Authorization", "Basic " + token)
    try:
        with _OPENER.open(req, timeout=timeout) as resp:
            return json.loads(resp.read().decode("utf-8-sig"))
    except urllib.error.HTTPError as e:
        if e.code == 401:
            raise LHMError("LHM просит логин/пароль — заполни LHM_USER и LHM_PASSWORD") from None
        raise LHMError(f"LHM ответил HTTP {e.code}") from None
    except (urllib.error.URLError, http.client.HTTPException, OSError) as e:
        raise LHMError(f"нет связи с {url} ({getattr(e, 'reason', e)})") from None
    except ValueError as e:
        raise LHMError(f"LHM прислал не JSON ({e})") from None


def iter_sensors(node: dict, path: tuple = ()):
    """Обход дерева data.json: (узел сенсора, название железа)."""
    if "SensorId" in node:
        yield node, (path[-2] if len(path) >= 2 else "")
        return
    for child in node.get("Children") or ():
        yield from iter_sensors(child, path + (str(node.get("Text", "")),))


def sensor_value(s: dict):
    raw = s.get("RawValue")  # есть в свежих LHM; в старых только строка вида "86,4 W"
    if isinstance(raw, (int, float)) and not isinstance(raw, bool):
        v = float(raw)
    else:
        m = _NUM.search(str(s.get("Value", "")))
        if not m:
            return None
        v = float(m.group().replace(",", "."))
    return v if math.isfinite(v) else None


def pick_sensors(tree: dict) -> dict:
    """{канал: [(SensorId, имя сенсора, железо, ватты|None), ...]} по CHANNELS."""
    out = {ch: [] for ch in CHANNELS}
    for s, hw in iter_sensors(tree):
        sid, text = str(s.get("SensorId", "")), str(s.get("Text", ""))
        for ch, ids in CHANNELS.items():
            if ids is None:
                rule = _AUTO.get(ch)
                hit = (rule is not None and s.get("Type") == "Power"
                       and rule[0].match(sid) is not None
                       and (text in rule[2] or rule[1].match(sid) is not None))
            else:
                hit = sid in ids
            if hit:
                out[ch].append((sid, text, hw, sensor_value(s)))
    return out


def channel_watts(picked: dict) -> dict:
    """{канал: сумма ватт или None, если данных нет}"""
    res = {}
    for ch, items in picked.items():
        vals = [w for *_, w in items if w is not None and 0 <= w <= MAX_WATTS]
        res[ch] = sum(vals) if vals else None
    return res


# ══════════════════════════════ счёт и база ══════════════════════════════

SCHEMA = """
CREATE TABLE IF NOT EXISTS energy (
    hour    INTEGER NOT NULL,   -- начало часа, unix time
    channel TEXT    NOT NULL,
    wh      REAL    NOT NULL,   -- Вт·ч за этот час
    secs    REAL    NOT NULL,   -- сколько секунд этого часа были с данными
    PRIMARY KEY (hour, channel)
)"""

UPSERT = ("INSERT INTO energy (hour, channel, wh, secs) VALUES (?, ?, ?, ?) "
          "ON CONFLICT(hour, channel) DO UPDATE SET "
          "wh = wh + excluded.wh, secs = secs + excluded.secs")


def open_db(path) -> sqlite3.Connection:
    db = sqlite3.connect(str(path), timeout=15)
    db.execute("PRAGMA journal_mode=WAL")  # чтобы отчёт читал, пока логгер пишет
    db.execute(SCHEMA)
    db.commit()
    return db


def flush(db: sqlite3.Connection, acc: dict) -> bool:
    if not acc:
        return True
    try:
        with db:
            db.executemany(UPSERT, [(h, ch, v[0], v[1]) for (h, ch), v in acc.items()])
    except sqlite3.Error as e:
        log.warning("не смог записать в базу (%s), попробую позже", e)
        return False
    acc.clear()
    return True


class Meter:
    """Интегрирует мощность по времени (трапеции) в Вт·ч по часам."""

    def __init__(self):
        self.acc = {}    # (час, канал) → [Вт·ч, секунд]
        self.last = {}   # канал → (wall, monotonic, ватты)
        self.live = {"ts": None, "watts": {}, "sensors": {}, "error": "ещё не опрашивал LHM"}

    def sample(self, watts: dict, t_wall: float, t_mono: float) -> None:
        for ch, w in watts.items():
            if w is None:
                continue  # нет значения — дыра; если короткая, перекроется следующим замером
            prev = self.last.get(ch)
            if prev is not None:
                d_mono, d_wall = t_mono - prev[1], t_wall - prev[0]
                # длинная дыра (сон, LHM лежал) или прыжок часов — этот отрезок не считаем
                if 0 < d_mono <= MAX_GAP_SECONDS and abs(d_wall - d_mono) <= 5:
                    hour = int(t_wall // 3600) * 3600
                    a = self.acc.setdefault((hour, ch), [0.0, 0.0])
                    a[0] += (prev[2] + w) / 2 * d_mono / 3600
                    a[1] += d_mono
            self.last[ch] = (t_wall, t_mono, w)


def load_rows(db, t_from=None, t_to=None) -> list:
    sql, args = "SELECT hour, channel, wh, secs FROM energy", ()
    if t_from is not None:
        sql, args = sql + " WHERE hour >= ? AND hour < ?", (int(t_from), int(t_to))
    return db.execute(sql + " ORDER BY hour", args).fetchall()


def channel_order(rows) -> list:
    seen = {r[1] for r in rows}
    return [c for c in CHANNELS if c in seen or not seen] + sorted(seen - set(CHANNELS))


def group(rows, key) -> dict:
    """Часовые строки → {ключ: {"wh": {канал: Вт·ч}, "secs": секунд с данными}}."""
    hours = {}
    for hour, ch, wh, secs in rows:
        h = hours.setdefault(hour, [{}, 0.0])
        h[0][ch] = h[0].get(ch, 0.0) + wh
        h[1] = max(h[1], min(secs, 3600.0))  # час «с данными», если был хоть один канал
    out = {}
    for hour in sorted(hours):
        whs, secs = hours[hour]
        g = out.setdefault(key(hour), {"wh": {}, "secs": 0.0})
        for ch, wh in whs.items():
            g["wh"][ch] = g["wh"].get(ch, 0.0) + wh
        g["secs"] += secs
    return out


def month_report(db, y: int, m: int, now: float = None) -> dict:
    now = time.time() if now is None else now
    t0 = datetime(y, m, 1).timestamp()
    t1 = datetime(*next_month(y, m), 1).timestamp()
    rows = load_rows(db, t0, t1)
    chans = channel_order(rows)
    by_day = group(rows, lambda h: datetime.fromtimestamp(h).day)
    today = date.today()
    days = []
    for d in range(1, calendar.monthrange(y, m)[1] + 1):
        g, dd = by_day.get(d), date(y, m, d)
        days.append({
            "day": d, "date": dd, "has": g is not None,
            "wh": [g["wh"].get(c, 0.0) if g else 0.0 for c in chans],
            "secs": g["secs"] if g else 0.0,
            "today": dd == today, "future": dd > today,
        })
    wh = [sum(d["wh"][i] for d in days) for i in range(len(chans))]
    total, secs = sum(wh), sum(d["secs"] for d in days)
    rep = {"y": y, "m": m, "channels": chans, "days": days, "wh": wh, "total_wh": total,
           "secs": secs, "wall_kwh": wall_kwh(total, secs), "projection": None}
    # прогноз на весь месяц: темп с момента начала записи в этом месяце
    if rows and t0 <= now < t1:
        h0 = rows[0][0]
        s0 = max(min(r[3], 3600.0) for r in rows if r[0] == h0)
        start = max(t0, min(h0 + 3600 - s0, now - s0))
        elapsed = now - start
        if elapsed >= 6 * 3600:
            k = (t1 - t0) / elapsed
            rep["projection"] = {"total_kwh": total / 1000 * k, "wall_kwh": rep["wall_kwh"] * k}
    return rep


def months_report(db) -> tuple:
    rows = load_rows(db)
    chans = channel_order(rows)
    by_month = group(rows, lambda h: datetime.fromtimestamp(h).strftime("%Y-%m"))
    out = []
    for ym in sorted(by_month, reverse=True):
        g = by_month[ym]
        wh = [g["wh"].get(c, 0.0) for c in chans]
        out.append({"ym": ym, "wh": wh, "total_wh": sum(wh), "secs": g["secs"],
                    "wall_kwh": wall_kwh(sum(wh), g["secs"])})
    return chans, out


# ══════════════════════════════ логгер (run) ══════════════════════════════

def setup_logging(to_file: bool) -> None:
    log.setLevel(logging.INFO)
    fmt = logging.Formatter("%(asctime)s %(levelname)s %(message)s", "%Y-%m-%d %H:%M:%S")
    if sys.stderr is not None:          # у pythonw.exe консоли нет
        h = logging.StreamHandler()
        h.setFormatter(fmt)
        log.addHandler(h)
    if to_file:
        fh = logging.handlers.RotatingFileHandler(LOG_PATH, maxBytes=1_000_000,
                                                  backupCount=2, encoding="utf-8")
        fh.setFormatter(fmt)
        log.addHandler(fh)


def acquire_lock(path: Path):
    """Второй логгер на ту же базу посчитал бы всё дважды — не пускаем."""
    f = open(path, "a+")
    try:
        if os.name == "nt":
            import msvcrt
            f.seek(0)
            msvcrt.locking(f.fileno(), msvcrt.LK_NBLCK, 1)
        else:
            import fcntl
            fcntl.flock(f.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
    except OSError:
        log.error("логгер уже запущен (занят %s)", path)
        sys.exit(1)
    return f


def _raise_interrupt(*_):
    raise KeyboardInterrupt


def cmd_run(args) -> int:
    setup_logging(to_file=True)
    for name in ("SIGTERM", "SIGBREAK"):
        if hasattr(signal, name):
            signal.signal(getattr(signal, name), _raise_interrupt)
    db_path = Path(args.db)
    lock = acquire_lock(db_path.with_suffix(".lock"))  # держим открытым до выхода
    db = open_db(db_path)
    poll = args.poll or POLL_SECONDS
    meter = Meter()
    if args.port:
        start_web(meter, db_path, args.url, args.host, args.port)
    log.info("старт: LHM %s, опрос раз в %s с, база %s", args.url, poll, db_path)

    next_flush = time.monotonic() + FLUSH_SECONDS
    last_err, last_err_log, last_ids = None, 0.0, None
    try:
        while True:
            t_mono, t_wall = time.monotonic(), time.time()
            try:
                picked = pick_sensors(fetch_lhm(args.url))
                watts, err = channel_watts(picked), None
            except LHMError as e:
                picked, watts, err = {}, {}, str(e)
            meter.sample(watts, t_wall, t_mono)
            meter.live = {
                "ts": t_wall, "watts": watts, "error": err,
                "sensors": {ch: [[sid, name, hw] for sid, name, hw, _ in items]
                            for ch, items in picked.items()},
            }
            # в журнал — только перемены, чтобы не пухнул
            if err:
                if err != last_err or t_mono - last_err_log > 600:
                    log.warning("%s", err)
                    last_err_log = t_mono
            elif last_err:
                log.info("LHM снова отвечает")
            last_err = err
            if not err:
                ids = {ch: tuple(i[0] for i in items) for ch, items in picked.items()}
                if ids != last_ids:
                    for ch, items in picked.items():
                        if items:
                            log.info("%s ← %s", ch, "; ".join(
                                f"{sid} «{name}» ({hw})" for sid, name, hw, _ in items))
                        else:
                            log.warning("%s: сенсор не найден — см. `powermeter.py sensors` "
                                        "и CHANNELS в начале скрипта", ch)
                    last_ids = ids
            if t_mono >= next_flush:
                flush(db, meter.acc)
                next_flush = t_mono + FLUSH_SECONDS
            time.sleep(max(0.05, poll - (time.monotonic() - t_mono)))
    except KeyboardInterrupt:
        log.info("остановка")
    finally:
        flush(db, meter.acc)
        db.close()
        lock.close()
    return 0


# ═══════════════════════════════ страничка ═══════════════════════════════

_LIGHT = ("#2a78d6", "#eb6834", "#1baf7a", "#eda100", "#e87ba4", "#008300", "#6250d6", "#e34948")
_DARK = ("#3987e5", "#d95926", "#199e70", "#c98500", "#d55181", "#008300", "#9085e9", "#e66767")


def _vars(dark: bool) -> str:
    base = ("color-scheme:dark;--page:#0d0d0d;--surface:#1a1a19;--ink:#f0efec;--ink2:#c3c2b7;"
            "--muted:#898781;--grid:#2c2c2a;--axis:#383835;--border:rgba(255,255,255,.10);"
            if dark else
            "color-scheme:light;--page:#f9f9f7;--surface:#fcfcfb;--ink:#0b0b0b;--ink2:#52514e;"
            "--muted:#898781;--grid:#e1e0d9;--axis:#c3c2b7;--border:rgba(11,11,11,.10);")
    return base + "".join(f"--s{i}:{c};" for i, c in enumerate(_DARK if dark else _LIGHT))


PAGE_CSS = (
    ".viz-root{" + _vars(False) + "}"
    "@media (prefers-color-scheme:dark){:root:where(:not([data-theme=\"light\"])) .viz-root{"
    + _vars(True) + "}}"
    ":root[data-theme=\"dark\"] .viz-root{" + _vars(True) + "}"
    + """
*{box-sizing:border-box}
body{margin:0;background:var(--page);color:var(--ink);font:14px/1.45 system-ui,-apple-system,"Segoe UI",sans-serif}
.wrap{max-width:1000px;margin:0 auto;padding:20px 20px 32px}
.bar{display:flex;align-items:center;gap:12px;flex-wrap:wrap;margin-bottom:16px}
.bar h1{font-size:20px;font-weight:600;margin:0;min-width:150px;text-align:center}
.nav{color:var(--ink2);text-decoration:none;padding:4px 10px;border:1px solid var(--border);border-radius:8px;background:var(--surface)}
.nav:hover{color:var(--ink)}
.nav.off{visibility:hidden}
.live{margin-left:auto;color:var(--ink2);font-variant-numeric:tabular-nums}
.card,.tile{background:var(--surface);border:1px solid var(--border);border-radius:12px}
.card{padding:16px 18px;margin-bottom:14px}
.label{color:var(--ink2);font-size:13px}
.hero .value{font-size:52px;font-weight:600;line-height:1.15;margin:2px 0}
.unit,.u{font-weight:500;color:var(--ink2)}
.hero .unit{font-size:20px}
.tile .u{font-size:14px}
.sub,.note{color:var(--muted);font-size:12.5px}
.tiles{display:grid;grid-template-columns:repeat(auto-fit,minmax(170px,1fr));gap:12px;margin-bottom:14px}
.tile{padding:12px 14px}
.tile .value{font-size:22px;font-weight:600;margin:2px 0}
.sw{display:inline-block;width:10px;height:10px;border-radius:2px;margin-right:6px}
.card-head{display:flex;justify-content:space-between;align-items:baseline;gap:12px;flex-wrap:wrap;margin-bottom:6px}
h2{font-size:15px;font-weight:600;margin:0 0 8px}
.card-head h2{margin:0}
.legend{display:flex;gap:4px 16px;flex-wrap:wrap;font-size:13px}
.legend .hw{color:var(--muted)}
#chart{width:100%;height:260px}
#chart svg{display:block}
#chart text{font:11px system-ui,-apple-system,"Segoe UI",sans-serif;font-variant-numeric:tabular-nums}
.grid{stroke:var(--grid)}
.axis{stroke:var(--axis)}
.tick{fill:var(--muted)}
.tick.today{fill:var(--ink);font-weight:600}
.dlabel,.slabel{fill:var(--ink2)}
.hit{fill:transparent;pointer-events:all}
.col{outline:none}
.col.partial .seg{opacity:.55}
.col:hover .seg,.col:focus .seg{filter:brightness(1.12)}
.col:focus-visible .hit{stroke:var(--axis)}
.scroll{overflow-x:auto}
table{border-collapse:collapse;width:100%;font-variant-numeric:tabular-nums;font-size:13px}
th,td{padding:5px 8px;text-align:right;border-bottom:1px solid var(--grid);white-space:nowrap}
th{color:var(--ink2);font-weight:500}
th:first-child,td:first-child{text-align:left}
tr.tot td{font-weight:600;border-bottom:0}
tr.cur td{background:var(--grid)}
details{margin-top:10px}
summary{cursor:pointer;color:var(--ink2);margin-bottom:6px}
a{color:inherit}
.empty{color:var(--ink2);text-align:center;padding:60px 0}
.tip{position:fixed;z-index:9;pointer-events:none;background:var(--surface);border:1px solid var(--border);border-radius:8px;padding:8px 10px;box-shadow:0 6px 20px rgba(0,0,0,.14);font-size:12.5px;min-width:160px}
.tip-head{color:var(--ink2);margin-bottom:4px}
.tip-row{display:flex;align-items:center;gap:8px;line-height:1.6}
.tip-row .lbl{color:var(--ink2)}
.key{width:12px;flex:none;border-top:2px solid transparent}
.tip-foot{color:var(--muted);margin-top:4px}
footer{color:var(--muted);font-size:12px;line-height:1.6}
"""
    + "".join(f".s{i}{{fill:var(--s{i})}}.c{i}{{background:var(--s{i})}}"
              f".key.k{i}{{border-top-color:var(--s{i})}}" for i in range(8)))

PAGE_JS = r"""
(function () {
  var D = JSON.parse(document.getElementById('month-data').textContent);
  var box = document.getElementById('chart'), tip = document.getElementById('tip');
  var NS = 'http://www.w3.org/2000/svg';
  function fmt(x, nd) { return x.toLocaleString('ru-RU', {minimumFractionDigits: nd, maximumFractionDigits: nd}); }
  function el(name, attrs, parent) {
    var e = document.createElementNS(NS, name);
    for (var k in attrs) e.setAttribute(k, attrs[k]);
    if (parent) parent.appendChild(e);
    return e;
  }
  function nice(max) {
    if (!(max > 0)) return {top: 1, step: 0.25};
    var raw = max / 4, p = Math.pow(10, Math.floor(Math.log10(raw))), f = raw / p;
    var step = (f <= 1 ? 1 : f <= 2 ? 2 : f <= 2.5 ? 2.5 : f <= 5 ? 5 : 10) * p;
    return {top: Math.ceil(max / step - 1e-9) * step, step: step};
  }
  function decimals(step) {
    for (var nd = 0; nd < 4; nd++) { var s = step * Math.pow(10, nd); if (Math.abs(s - Math.round(s)) < 1e-6) return nd; }
    return 3;
  }
  function colPath(x, y, w, h, r) {  // скруглённый верх, квадратное основание
    r = Math.min(r, w / 2, h);
    return 'M' + x + ',' + (y + h) + 'V' + (y + r) + 'a' + r + ',' + r + ' 0 0 1 ' + r + ',' + (-r) +
      'H' + (x + w - r) + 'a' + r + ',' + r + ' 0 0 1 ' + r + ',' + r + 'V' + (y + h) + 'Z';
  }
  function row(val, label, k) {
    var r = document.createElement('div'); r.className = 'tip-row';
    var key = document.createElement('span'); key.className = 'key' + (k === null ? '' : ' k' + k); r.appendChild(key);
    var b = document.createElement('strong'); b.textContent = val; r.appendChild(b);
    var s = document.createElement('span'); s.className = 'lbl'; s.textContent = label; r.appendChild(s);
    return r;
  }
  function hide() { tip.hidden = true; }
  function show(i, px, py) {
    var d = D.days[i];
    if (!(d.total > 0)) { hide(); return; }
    tip.textContent = '';
    var h = document.createElement('div'); h.className = 'tip-head'; h.textContent = d.date; tip.appendChild(h);
    tip.appendChild(row(d.total_s + ' ' + D.unit, 'всего', null));
    for (var k = d.vals.length - 1; k >= 0; k--) tip.appendChild(row(d.vals_s[k], D.channels[k], k));
    var f = document.createElement('div'); f.className = 'tip-foot'; f.textContent = d.foot; tip.appendChild(f);
    tip.hidden = false;
    var pad = 14, tw = tip.offsetWidth, th = tip.offsetHeight, left = px + pad, top = py + pad;
    if (left + tw > window.innerWidth - 8) left = px - pad - tw;
    if (top + th > window.innerHeight - 8) top = py - pad - th;
    tip.style.left = Math.max(8, left) + 'px'; tip.style.top = Math.max(8, top) + 'px';
  }
  function draw() {
    box.textContent = '';
    var W = Math.max(320, box.clientWidth), H = 260, m = {t: 24, r: 44, b: 28, l: 48};
    var pw = W - m.l - m.r, ph = H - m.t - m.b, n = D.days.length;
    var totals = D.days.map(function (d) { return d.total; });
    var maxT = Math.max.apply(null, totals), sc = nice(maxT), top = sc.top, nd = decimals(sc.step);
    function y(v) { return m.t + ph - v / top * ph; }
    var svg = el('svg', {width: W, height: H, viewBox: '0 0 ' + W + ' ' + H, role: 'img', 'aria-label': D.aria}, box);
    for (var v = 0; v <= top + 1e-9; v += sc.step) {
      var yy = Math.round(y(v)) + 0.5;
      el('line', {x1: m.l, x2: W - m.r, y1: yy, y2: yy, 'class': v === 0 ? 'axis' : 'grid'}, svg);
      el('text', {x: m.l - 8, y: yy + 4, 'class': 'tick', 'text-anchor': 'end'}, svg).textContent = fmt(v, nd);
    }
    var band = pw / n, bw = Math.max(3, Math.min(24, band * 0.62));
    var maxI = maxT > 0 ? totals.indexOf(maxT) : -1, lastI = -1;
    D.days.forEach(function (d, i) { if (d.total > 0) lastI = i; });
    D.days.forEach(function (d, i) {
      var cx = m.l + band * i + band / 2, x = cx - bw / 2;
      var g = el('g', {'class': 'col' + (d.today ? ' partial' : '')}, svg);
      if (d.total > 0) { g.setAttribute('tabindex', '0'); g.setAttribute('aria-label', d.aria); }
      el('rect', {x: m.l + band * i, y: m.t, width: band, height: ph, 'class': 'hit'}, g);
      var segs = [], base = 0;
      d.vals.forEach(function (val, k) { if (val > 0) segs.push([val, k]); });
      segs.forEach(function (s, j) {
        var y0 = y(base), y1 = y(base + s[0]);
        base += s[0];
        var h = y0 - y1 - (j > 0 ? 2 : 0);  // 2px просвет между сегментами
        if (h < 1) return;
        if (j === segs.length - 1) el('path', {d: colPath(x, y1, bw, h, 4), 'class': 'seg s' + s[1]}, g);
        else el('rect', {x: x, y: y1, width: bw, height: h, 'class': 'seg s' + s[1]}, g);
        if (i === lastI && h >= 13) {
          el('text', {x: x + bw + 6, y: y1 + h / 2 + 4, 'class': 'slabel'}, svg).textContent = D.channels[s[1]];
        }
      });
      if (i === maxI) {
        el('text', {x: cx, y: y(d.total) - 7, 'class': 'dlabel', 'text-anchor': 'middle'}, svg).textContent = d.total_s;
      }
      if (band >= 16 || i % 2 === 0 || d.today) {
        el('text', {x: cx, y: H - m.b + 17, 'class': 'tick' + (d.today ? ' today' : ''), 'text-anchor': 'middle'}, svg).textContent = d.label;
      }
      g.addEventListener('pointermove', function (e) { show(i, e.clientX, e.clientY); });
      g.addEventListener('pointerleave', hide);
      g.addEventListener('focus', function () { var r = g.getBoundingClientRect(); show(i, r.left + r.width / 2, r.top + 30); });
      g.addEventListener('blur', hide);
    });
  }
  if (box) {
    draw();
    var rt;
    window.addEventListener('resize', function () { clearTimeout(rt); rt = setTimeout(draw, 120); });
  }
  var liveEl = document.getElementById('live');
  setInterval(function () {
    fetch('/api/live', {cache: 'no-store'})
      .then(function (r) { return r.json(); })
      .then(function (j) { liveEl.textContent = j.text; })
      .catch(function () { liveEl.textContent = 'логгер не отвечает'; });
  }, 5000);
})();
"""


def live_text(live: dict) -> str:
    if live.get("error"):
        return "LHM: " + live["error"]
    w = {c: v for c, v in (live.get("watts") or {}).items() if v is not None}
    if not w:
        return "нет данных с датчиков"
    total = sum(w.values())
    eff = PSU_EFFICIENCY if PSU_EFFICIENCY > 0 else 1.0
    return ("Сейчас: " + " · ".join(f"{c} {num(v, 0)} Вт" for c, v in w.items())
            + f" · ≈{num((total + OTHER_WATTS) / eff, 0)} Вт от розетки")


def live_json(live: dict) -> dict:
    return dict(live, text=live_text(live))


def month_json(rep: dict) -> dict:
    ch = rep["channels"]
    return {
        "month": f"{rep['y']}-{rep['m']:02d}", "channels": ch,
        "kwh": {c: rep["wh"][i] / 1000 for i, c in enumerate(ch)},
        "total_kwh": rep["total_wh"] / 1000, "hours": rep["secs"] / 3600,
        "wall_kwh_estimate": rep["wall_kwh"], "cost_estimate": rep["wall_kwh"] * TARIFF,
        "projection": rep["projection"],
        "days": [{"date": d["date"].isoformat(), "hours": d["secs"] / 3600,
                  "kwh": {c: d["wh"][i] / 1000 for i, c in enumerate(ch)}}
                 for d in rep["days"] if d["has"]],
    }


def render_page(db, y: int, m: int, live: dict, url: str) -> str:
    e = html.escape
    rep = month_report(db, y, m)
    mchans, months = months_report(db)
    chans = rep["channels"]
    title = month_title(y, m)
    (py_, pm_), (ny_, nm_) = prev_month(y, m), next_month(y, m)
    eff_pct = round(PSU_EFFICIENCY * 100)

    # — данные для графика —
    days_js = []
    for d in rep["days"]:
        tot, dd = sum(d["wh"]), d["date"]
        date_s = f"{dd.day} {MONTHS_GEN[dd.month - 1]}, {WEEKDAYS[dd.weekday()]}"
        vals_s = [num(w / 1000, 2) for w in d["wh"]]
        foot = f"ср. {num(avg_w(tot, d['secs']), 0)} Вт · {num(d['secs'] / 3600, 1)} ч с данными"
        if d["today"]:
            foot += " · день ещё идёт"
        days_js.append({
            "label": str(dd.day), "date": date_s, "today": d["today"],
            "vals": [round(w / 1000, 4) for w in d["wh"]], "vals_s": vals_s,
            "total": round(tot / 1000, 4), "total_s": num(tot / 1000, 2), "foot": foot,
            "aria": f"{date_s}: всего {num(tot / 1000, 2)} кВт·ч, "
                    + ", ".join(f"{c} {v}" for c, v in zip(chans, vals_s)),
        })
    data = {"unit": "кВт·ч", "channels": chans, "aria": f"Потребление по дням, {title}, кВт·ч",
            "days": days_js}
    data_json = json.dumps(data, ensure_ascii=False).replace("</", "<\\/")

    # — плитки —
    def tile(label, value, note, sw=None):
        swh = f'<span class="sw c{sw}"></span>' if sw is not None else ""
        return (f'<div class="tile"><div class="label">{swh}{e(label)}</div>'
                f'<div class="value">{value}</div><div class="note">{note}</div></div>')

    tiles = [tile(c, f'{num(rep["wh"][i] / 1000, 2)}<span class="u"> кВт·ч</span>',
                  f'ср. {num(avg_w(rep["wh"][i], rep["secs"]), 0)} Вт', sw=i)
             for i, c in enumerate(chans)]
    tiles.append(tile("≈ от розетки", f'{num(rep["wall_kwh"], 1)}<span class="u"> кВт·ч</span>',
                      f"+{OTHER_WATTS} Вт на остальное, КПД БП {eff_pct} %"))
    tiles.append(tile("≈ стоимость", f'{num(rep["wall_kwh"] * TARIFF, 0)}<span class="u"> {e(CURRENCY)}</span>',
                      f"{num(TARIFF, 2)} {e(CURRENCY)} за кВт·ч, от розетки"))
    if rep["projection"]:
        p = rep["projection"]
        tiles.append(tile("Прогноз на месяц", f'≈ {num(p["total_kwh"], 0)}<span class="u"> кВт·ч</span>',
                          f'≈ {num(p["wall_kwh"] * TARIFF, 0)} {e(CURRENCY)} от розетки, если дальше так же'))

    # — легенда —
    sens = live.get("sensors") or {}
    legend = ""
    for i, c in enumerate(chans):
        hw = ", ".join(sorted({x[2] for x in sens.get(c, []) if x[2]}))
        legend += (f'<span><span class="sw c{i}"></span>{e(c)}'
                   + (f' <span class="hw">{e(hw)}</span>' if hw else "") + "</span>")

    # — таблица по дням —
    head = "".join(f"<th>{e(c)}</th>" for c in chans)
    trs = []
    for d in rep["days"]:
        if d["future"]:
            continue
        dd = d["date"]
        lab = f"{dd.day:02d}.{dd.month:02d} {WEEKDAYS[dd.weekday()]}"
        if not d["has"]:
            trs.append(f"<tr><td>{lab}</td>" + "<td>—</td>" * (len(chans) + 3) + "</tr>")
            continue
        tot = sum(d["wh"])
        trs.append(f"<tr><td>{lab}</td>" + "".join(f"<td>{num(w / 1000, 3)}</td>" for w in d["wh"])
                   + f"<td>{num(tot / 1000, 3)}</td><td>{num(avg_w(tot, d['secs']), 0)}</td>"
                   f"<td>{num(d['secs'] / 3600, 1)}</td></tr>")
    trs.append('<tr class="tot"><td>Итого</td>' + "".join(f"<td>{num(w / 1000, 2)}</td>" for w in rep["wh"])
               + f"<td>{num(rep['total_wh'] / 1000, 2)}</td><td>{num(avg_w(rep['total_wh'], rep['secs']), 0)}</td>"
               f"<td>{num(rep['secs'] / 3600, 0)}</td></tr>")
    day_table = (f'<div class="scroll"><table><thead><tr><th>День</th>{head}<th>Всего, кВт·ч</th>'
                 f'<th>Ср. Вт</th><th>Часов с данными</th></tr></thead><tbody>{"".join(trs)}</tbody></table></div>')

    # — таблица по месяцам —
    mhead = "".join(f"<th>{e(c)}</th>" for c in mchans)
    mtrs = []
    for mo in months:
        yy, mm = map(int, mo["ym"].split("-"))
        cls = ' class="cur"' if (yy, mm) == (y, m) else ""
        mtrs.append(f'<tr{cls}><td><a href="/?month={mo["ym"]}">{month_title(yy, mm)}</a></td>'
                    + "".join(f"<td>{num(w / 1000, 2)}</td>" for w in mo["wh"])
                    + f"<td>{num(mo['total_wh'] / 1000, 2)}</td><td>{num(mo['wall_kwh'], 1)}</td>"
                    f"<td>{num(mo['wall_kwh'] * TARIFF, 0)}</td><td>{num(mo['secs'] / 3600, 0)}</td></tr>")
    months_table = (f'<div class="scroll"><table><thead><tr><th>Месяц</th>{mhead}<th>Всего, кВт·ч</th>'
                    f'<th>≈ от розетки, кВт·ч</th><th>≈ {e(CURRENCY)}</th><th>Часов с данными</th></tr></thead>'
                    f'<tbody>{"".join(mtrs)}</tbody></table></div>'
                    if mtrs else '<div class="empty">Пока пусто</div>')

    # — подвал —
    src = []
    for c in CHANNELS:
        items = sens.get(c, [])
        src.append(f"{e(c)}: " + (", ".join(f"{e(s)} «{e(n)}»" for s, n, _ in items) if items else "не найден"))
    footer = (f"Источник: {e(url)} · {' · '.join(src)}<br>"
              f"«≈ от розетки» = (CPU+GPU + {OTHER_WATTS} Вт) / {num(PSU_EFFICIENCY, 2)} — оценка, без монитора. "
              f"Дыры в данных длиннее {MAX_GAP_SECONDS} с не считаются.")

    nav_prev = f'<a class="nav" href="/?month={py_}-{pm_:02d}">‹ {MONTHS[pm_ - 1]}</a>'
    nav_next = (f'<a class="nav" href="/?month={ny_}-{nm_:02d}">{MONTHS[nm_ - 1]} ›</a>'
                if datetime(ny_, nm_, 1) <= datetime.now() else '<span class="nav off">—</span>')
    chart = ('<div id="chart"></div>' if rep["secs"] > 0
             else '<div class="empty">Нет данных за этот месяц</div>')
    return (
        '<!doctype html><html lang="ru"><head><meta charset="utf-8">'
        '<meta name="viewport" content="width=device-width,initial-scale=1">'
        '<meta name="color-scheme" content="light dark">'
        f'<title>{e(title)} · CPU+GPU, кВт·ч</title><style>{PAGE_CSS}</style></head>'
        '<body class="viz-root"><div class="wrap">'
        f'<div class="bar">{nav_prev}<h1>{e(title)}</h1>{nav_next}'
        f'<span class="live" id="live">{e(live_text(live))}</span></div>'
        '<section class="card hero"><div class="label">CPU + GPU за месяц</div>'
        f'<div class="value">{num(rep["total_wh"] / 1000, 2 if rep["total_wh"] < 10000 else 1)}'
        '<span class="unit"> кВт·ч</span></div>'
        f'<div class="sub">по датчикам LHM · {num(rep["secs"] / 3600, 0)} ч с данными</div></section>'
        f'<section class="tiles">{"".join(tiles)}</section>'
        f'<section class="card"><div class="card-head"><h2>По дням, кВт·ч</h2>'
        f'<div class="legend">{legend}</div></div>{chart}'
        f'<details><summary>Таблица по дням</summary>{day_table}</details></section>'
        f'<section class="card"><h2>По месяцам</h2>{months_table}</section>'
        f'<footer>{footer}</footer></div>'
        '<div id="tip" class="tip" hidden></div>'
        f'<script id="month-data" type="application/json">{data_json}</script>'
        f'<script>{PAGE_JS}</script></body></html>'
    )


class _Server(ThreadingHTTPServer):
    daemon_threads = True
    allow_reuse_address = os.name != "nt"  # на Windows SO_REUSEADDR пускает второй процесс на тот же порт


def start_web(meter: Meter, db_path: Path, url: str, host: str, port: int):
    class Handler(BaseHTTPRequestHandler):
        server_version = "powermeter"

        def log_message(self, *_):
            pass

        def _send(self, code, body, ctype):
            data = body.encode("utf-8")
            self.send_response(code)
            self.send_header("Content-Type", ctype + "; charset=utf-8")
            self.send_header("Content-Length", str(len(data)))
            self.send_header("Cache-Control", "no-store")
            self.end_headers()
            self.wfile.write(data)

        def do_GET(self):
            u = urllib.parse.urlsplit(self.path)
            q = urllib.parse.parse_qs(u.query)
            try:
                if u.path == "/api/live":
                    self._send(200, json.dumps(live_json(meter.live), ensure_ascii=False), "application/json")
                elif u.path in ("/", "/api/month"):
                    y, m = parse_month(q.get("month", [""])[0]) or parse_month("")
                    db = sqlite3.connect(str(db_path), timeout=15)
                    try:
                        if u.path == "/":
                            self._send(200, render_page(db, y, m, meter.live, url), "text/html")
                        else:
                            body = json.dumps(month_json(month_report(db, y, m)), ensure_ascii=False)
                            self._send(200, body, "application/json")
                    finally:
                        db.close()
                else:
                    self._send(404, "not found", "text/plain")
            except Exception as ex:  # страничка не должна ронять логгер
                log.exception("ошибка странички")
                self._send(500, f"ошибка: {ex}", "text/plain")

    try:
        srv = _Server((host, port), Handler)
    except OSError as ex:
        log.warning("страничка не запустилась на %s:%s (%s) — логгер работает без неё", host, port, ex)
        return None
    threading.Thread(target=srv.serve_forever, name="web", daemon=True).start()
    shown = "127.0.0.1" if host in ("", "0.0.0.0") else host
    log.info("страничка: http://%s:%s/", shown, port)
    return srv


# ══════════════════════════════ sensors / report ══════════════════════════════

def cmd_sensors(args) -> int:
    try:
        tree = fetch_lhm(args.url)
    except LHMError as ex:
        print(f"✗ {ex}")
        if str(ex).startswith("нет связи"):
            print("  В LHM: Options → Remote Web Server → Run. Порт — там же, Interface / Port.")
        return 1
    print(f"✓ LHM отвечает: {args.url}\n")
    picked = pick_sensors(tree)
    chosen = {it[0]: ch for ch, items in picked.items() for it in items}
    rows = [(str(s.get("SensorId", "")), hw, str(s.get("Text", "")), sensor_value(s))
            for s, hw in iter_sensors(tree) if s.get("Type") == "Power"]
    if not rows:
        print("Power-сенсоров нет совсем. Проверь, что LHM запущен от админа и стоит PawnIO.")
    else:
        w = [max(len(r[i]) for r in rows) for i in range(3)]
        print(f"  {'SensorId':<{w[0]}}  {'Железо':<{w[1]}}  {'Сенсор':<{w[2]}}  {'Сейчас':>10}")
        for sid, hw, name, v in rows:
            val = "—" if v is None else f"{num(v, 1)} Вт"
            mark = f"   ← {chosen[sid]}" if sid in chosen else ""
            print(f"  {sid:<{w[0]}}  {hw:<{w[1]}}  {name:<{w[2]}}  {val:>10}{mark}")
    print()
    watts = channel_watts(picked)
    for ch, items in picked.items():
        if items:
            print(f"  {ch} = {'—' if watts[ch] is None else num(watts[ch], 1) + ' Вт'}")
        else:
            print(f"  ⚠ {ch}: подходящий сенсор не найден — впиши SensorId в CHANNELS в начале скрипта")
    return 0


def text_bar(frac: float, width: int) -> str:
    parts = " ▏▎▍▌▋▊▉"
    n = max(0.0, min(1.0, frac)) * width
    full, rest = int(n), int((n - int(n)) * 8)
    return "█" * full + (parts[rest] if rest and full < width else "")


def cmd_report(args) -> int:
    ym = parse_month(args.month)
    if ym is None:
        print("Месяц пишется как ГГГГ-ММ, например 2026-11")
        return 2
    y, m = ym
    db = open_db(args.db)
    rep = month_report(db, y, m)
    chans = rep["channels"]
    print(f"\n  {month_title(y, m)}: кВт·ч по датчикам LHM\n")
    if rep["secs"] <= 0:
        print("  Нет данных за этот месяц.\n")
    else:
        print(f"  {'День':<6}" + "".join(f"{c:>9}" for c in chans)
              + f"{'Всего':>9}{'Ср. Вт':>8}{'Часов':>7}")
        top = max(sum(d["wh"]) for d in rep["days"]) or 1.0
        for d in rep["days"]:
            if d["future"]:
                continue
            lab = f"{d['day']:02d} {WEEKDAYS[d['date'].weekday()]}"
            if not d["has"]:
                print(f"  {lab:<6}" + f"{'—':>9}" * (len(chans) + 1))
                continue
            tot = sum(d["wh"])
            print(f"  {lab:<6}" + "".join(f"{num(w / 1000, 3):>9}" for w in d["wh"])
                  + f"{num(tot / 1000, 3):>9}{num(avg_w(tot, d['secs']), 0):>8}"
                  f"{num(d['secs'] / 3600, 1):>7}  {text_bar(tot / top, 20)}")
        tot = rep["total_wh"]
        print(f"  {'Итого':<6}" + "".join(f"{num(w / 1000, 2):>9}" for w in rep["wh"])
              + f"{num(tot / 1000, 2):>9}{num(avg_w(tot, rep['secs']), 0):>8}{num(rep['secs'] / 3600, 0):>7}\n")
        print(f"  ≈ от розетки: {num(rep['wall_kwh'], 1)} кВт·ч ≈ {num(rep['wall_kwh'] * TARIFF, 0)} {CURRENCY}"
              f"   (+{OTHER_WATTS} Вт на остальное, КПД БП {round(PSU_EFFICIENCY * 100)} %, "
              f"{num(TARIFF, 2)} {CURRENCY}/кВт·ч)")
        p = rep["projection"]
        if p:
            print(f"  Прогноз на весь месяц: ≈ {num(p['total_kwh'], 1)} кВт·ч по датчикам, "
                  f"≈ {num(p['wall_kwh'], 1)} кВт·ч ≈ {num(p['wall_kwh'] * TARIFF, 0)} {CURRENCY} от розетки")
        print()
    mchans, months = months_report(db)
    if months:
        print(f"  {'Месяц':<15}" + "".join(f"{c:>9}" for c in mchans)
              + f"{'Всего':>9}{'≈ розетка':>11}{'≈ ' + CURRENCY:>9}{'Часов':>7}")
        for mo in months[:24]:
            yy, mm = map(int, mo["ym"].split("-"))
            print(f"  {month_title(yy, mm):<15}" + "".join(f"{num(w / 1000, 2):>9}" for w in mo["wh"])
                  + f"{num(mo['total_wh'] / 1000, 2):>9}{num(mo['wall_kwh'], 1):>11}"
                  f"{num(mo['wall_kwh'] * TARIFF, 0):>9}{num(mo['secs'] / 3600, 0):>7}")
        print()
    db.close()
    return 0


def main(argv=None) -> int:
    for stream in (sys.stdout, sys.stderr):  # кириллица и значки не должны ронять вывод
        if stream is not None and hasattr(stream, "reconfigure"):
            try:
                stream.reconfigure(errors="replace")
            except (OSError, ValueError):
                pass
    common = argparse.ArgumentParser(add_help=False)
    common.add_argument("--url", default=LHM_URL, help=f"data.json LHM (по умолчанию {LHM_URL})")
    common.add_argument("--db", default=str(DB_PATH), help="файл базы SQLite")
    p = argparse.ArgumentParser(prog="powermeter", description=__doc__,
                                formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = p.add_subparsers(dest="cmd", metavar="команда")
    sub.add_parser("sensors", parents=[common], help="проверить связь с LHM, показать power-сенсоры")
    r = sub.add_parser("run", parents=[common], help="логгер + страничка")
    r.add_argument("--host", default=WEB_HOST, help="адрес странички")
    r.add_argument("--port", type=int, default=WEB_PORT, help="порт странички, 0 — без неё")
    r.add_argument("--poll", type=float, default=None, help="интервал опроса LHM, с")
    rp = sub.add_parser("report", parents=[common], help="отчёт в консоль")
    rp.add_argument("month", nargs="?", default="", help="ГГГГ-ММ, по умолчанию текущий")
    args = p.parse_args(argv)
    if args.cmd == "run":
        return cmd_run(args)
    if args.cmd == "sensors":
        return cmd_sensors(args)
    if args.cmd == "report":
        return cmd_report(args)
    p.print_help()
    return 0


if __name__ == "__main__":
    sys.exit(main())
