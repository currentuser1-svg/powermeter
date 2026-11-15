#!/usr/bin/env python3
"""
powermeter — сколько электроэнергии съели CPU и GPU на твоих компах: кВт·ч по дням и месяцам.

Ватты берутся из LibreHardwareMonitor каждого хоста через его веб-сервер (data.json).
Каждый хост опрашивается в своём потоке раз в POLL_SECONDS, мощность интегрируется
по времени, Вт·ч копятся по часам в SQLite рядом со скриптом.
Только стандартная библиотека Python 3.8+.

На каждом хосте в LHM: Options → Remote Web Server → Run (порт по умолчанию 8085),
для удалённых хостов — Interface = адрес в локалке и разрешённый порт в брандмауэре.
Хосты добавляются и правятся на страничке: http://127.0.0.1:8087/hosts

  python powermeter.py sensors          проверить связь со всеми хостами и какие сенсоры взяты
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
import subprocess
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

# Хосты для первого запуска. Дальше список живёт в базе (таблица hosts)
# и правится на страничке /hosts — эту константу менять уже не нужно.
# cpu / gpu: "auto" — автопоиск, "off" — канала нет (считается как 0),
#            или SensorId через пробел (их показывает `python powermeter.py sensors`).
# other_watts — Вт на остальное железо этого компа (плата, память, диски, вентиляторы);
# psu_eff — КПД его блока питания. Оба нужны только для оценки «≈ от розетки».
DEFAULT_HOSTS = [
    {"name": "local",   "label": "Мой комп",    "url": "http://127.0.0.1:8085/data.json",
     "cpu": "auto", "gpu": "auto", "other_watts": 20, "psu_eff": 0.85},
    {"name": "remote",  "label": "Удалённый",   "url": "http://192.168.1.20:8085/data.json",
     "cpu": "auto", "gpu": "auto", "other_watts": 20, "psu_eff": 0.85},
    # виртуалка с пробросом видеокарты: процессорных ватт в VM нет, их не считаем;
    # «прочее» = 0, потому что железо под ней — это другой комп
    {"name": "vm-gpu",   "label": "VM-GPU", "url": "http://192.168.1.21:8085/data.json",
     "cpu": "off",  "gpu": "auto", "other_watts": 0,  "psu_eff": 0.85},
    {"name": "server-2", "label": "Сервер-2",     "url": "http://192.168.1.22:8085/data.json",
     "cpu": "auto", "gpu": "auto", "other_watts": 20, "psu_eff": 0.85},
]

KINDS = ("CPU", "GPU")

LHM_PORT = 8085             # порт LHM по умолчанию, подставляется, если в адресе его нет
POLL_SECONDS = 2            # как часто спрашивать LHM (сам LHM обновляется раз в 1 с)
OFFLINE_RETRY_SECONDS = 10  # если хост не отвечает — стучимся реже
FETCH_TIMEOUT = 3.0         # сколько ждать ответа LHM
FLUSH_SECONDS = 30          # как часто сбрасывать накопленное в базу
MAX_GAP_SECONDS = 30        # дыру длиннее (сон, LHM закрыт) не интерполируем — она не считается
MAX_WATTS = 1500            # больше — глюк датчика, такое значение пропускаем

WEB_HOST = "127.0.0.1"      # "0.0.0.0" — открыть страничку в локалку (на ней можно править хосты!)
WEB_PORT = 8087             # 0 — без странички

# Значения по умолчанию для новых хостов в форме на /hosts
OTHER_WATTS = 20
PSU_EFFICIENCY = 0.85

TARIFF = 4.32               # цена за кВт·ч
CURRENCY = "грн"

BASE_DIR = Path(__file__).resolve().parent
DB_PATH = BASE_DIR / "powermeter.db"

# ══════════════════════════════════════════════════════════════════════════

log = logging.getLogger("powermeter")

MONTHS = ("Январь", "Февраль", "Март", "Апрель", "Май", "Июнь",
          "Июль", "Август", "Сентябрь", "Октябрь", "Ноябрь", "Декабрь")
MONTHS_GEN = ("января", "февраля", "марта", "апреля", "мая", "июня",
              "июля", "августа", "сентября", "октября", "ноября", "декабря")
WEEKDAYS = ("пн", "вт", "ср", "чт", "пт", "сб", "вс")
N_COLORS = 8


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


def host_of(ch: str) -> str:
    """'server-2-GPU' → 'server-2'."""
    return ch.rsplit("-", 1)[0] if "-" in ch else "local"


def kind_of(ch: str) -> str:
    return ch.rsplit("-", 1)[1] if "-" in ch else ch


# ═══════════════════════════ LibreHardwareMonitor ═══════════════════════════

class LHMError(Exception):
    pass


_OPENER = urllib.request.build_opener(urllib.request.ProxyHandler({}))  # мимо системного прокси
_NUM = re.compile(r"-?\d+(?:[.,]\d+)?")

# канал: (какие SensorId вообще подходят, «родной» индекс сенсора, имена сенсора)
# По индексу — на случай, если сенсор переименован в LHM.
# Встройку (gpu-intel-integrated) не берём: она и так сидит внутри CPU Package.
_AUTO = {
    "CPU": (re.compile(r"^/(?:intelcpu|amdcpu)/\d+/power/\d+$"),
            re.compile(r"^/(?:intelcpu|amdcpu)/\d+/power/0$"),
            ("CPU Package", "Package")),
    "GPU": (re.compile(r"^/gpu-(?:nvidia|amd)/\d+/power/\d+$"),
            re.compile(r"^/gpu-nvidia/\d+/power/0$|^/gpu-amd/\d+/power/3$"),
            ("GPU Package",)),
}


def fetch_lhm(url: str, user: str = "", password: str = "", timeout: float = FETCH_TIMEOUT) -> dict:
    req = urllib.request.Request(url, headers={"Accept": "application/json"})
    if user:
        token = base64.b64encode(f"{user}:{password}".encode()).decode()
        req.add_header("Authorization", "Basic " + token)
    try:
        with _OPENER.open(req, timeout=timeout) as resp:
            return json.loads(resp.read().decode("utf-8-sig"))
    except urllib.error.HTTPError as e:
        if e.code == 401:
            raise LHMError("LHM просит логин/пароль (или они неверные)") from None
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
        m = _NUM.search(str(raw if raw is not None else s.get("Value", "")))
        if not m:
            return None
        v = float(m.group().replace(",", "."))
    return v if math.isfinite(v) else None


def sensor_mode(v):
    """'auto' | 'off' | кортеж SensorId."""
    v = (v or "").strip()
    if v.lower() in ("", "auto"):
        return "auto"
    if v.lower() == "off":
        return "off"
    return tuple(x for x in re.split(r"[\s,;]+", v) if x)


def auto_kind(s: dict):
    """Какой канал автопоиск взял бы из этого сенсора (или None)."""
    if s.get("Type") != "Power":
        return None
    sid, text = str(s.get("SensorId", "")), str(s.get("Text", ""))
    for kind, (any_id, own_id, names) in _AUTO.items():
        if any_id.match(sid) and (text in names or own_id.match(sid)):
            return kind
    return None


def pick_sensors(tree: dict, modes: dict) -> dict:
    """{канал: [(SensorId, имя, железо, Вт)]} — только для включённых каналов."""
    out = {k: [] for k, m in modes.items() if m != "off"}
    for s, hw in iter_sensors(tree):
        sid = str(s.get("SensorId", ""))
        ak = None
        for kind in out:
            m = modes[kind]
            if m == "auto":
                if ak is None:
                    ak = auto_kind(s) or ""
                hit = ak == kind
            else:
                hit = sid in m
            if hit:
                out[kind].append((sid, str(s.get("Text", "")), hw, sensor_value(s)))
    return out


def power_sensors(tree: dict) -> list:
    """Все Power-сенсоры хоста — для проверки на /hosts и `sensors`."""
    return [{"id": str(s.get("SensorId", "")), "text": str(s.get("Text", "")), "hw": hw,
             "value": sensor_value(s), "auto": auto_kind(s)}
            for s, hw in iter_sensors(tree) if s.get("Type") == "Power"]


def channel_watts(picked: dict) -> dict:
    res = {}
    for ch, items in picked.items():
        vals = [w for *_, w in items if w is not None and 0 <= w <= MAX_WATTS]
        res[ch] = sum(vals) if vals else None
    return res


# ═══════════════════════════════ база ═══════════════════════════════

SCHEMA = """
CREATE TABLE IF NOT EXISTS energy (
    hour    INTEGER NOT NULL,
    channel TEXT    NOT NULL,
    wh      REAL    NOT NULL,
    secs    REAL    NOT NULL,
    PRIMARY KEY (hour, channel)
);
CREATE TABLE IF NOT EXISTS hosts (
    name        TEXT    PRIMARY KEY,
    label       TEXT    NOT NULL,
    url         TEXT    NOT NULL,
    username    TEXT    NOT NULL DEFAULT '',
    password    TEXT    NOT NULL DEFAULT '',
    cpu         TEXT    NOT NULL DEFAULT 'auto',
    gpu         TEXT    NOT NULL DEFAULT 'auto',
    other_watts REAL    NOT NULL DEFAULT 20,
    psu_eff     REAL    NOT NULL DEFAULT 0.85,
    enabled     INTEGER NOT NULL DEFAULT 1,
    pos         INTEGER NOT NULL DEFAULT 0
);
"""

UPSERT = ("INSERT INTO energy (hour, channel, wh, secs) VALUES (?, ?, ?, ?) "
          "ON CONFLICT(hour, channel) DO UPDATE SET "
          "wh = wh + excluded.wh, secs = secs + excluded.secs")

HOST_FIELDS = ("name", "label", "url", "username", "password", "cpu", "gpu",
               "other_watts", "psu_eff", "enabled", "pos")


def open_db(path) -> sqlite3.Connection:
    db = sqlite3.connect(str(path), timeout=15)
    db.execute("PRAGMA journal_mode=WAL")
    db.executescript(SCHEMA)
    with db:
        # самая первая версия писала каналы без имени хоста: "CPU" → "local-CPU"
        if db.execute("SELECT 1 FROM energy WHERE channel IN ('CPU','GPU') LIMIT 1").fetchone():
            db.execute("INSERT INTO energy (hour, channel, wh, secs) "
                       "SELECT hour, 'local-' || channel, wh, secs FROM energy "
                       "WHERE channel IN ('CPU','GPU') "
                       "ON CONFLICT(hour, channel) DO UPDATE SET "
                       "wh = wh + excluded.wh, secs = MAX(secs, excluded.secs)")
            db.execute("DELETE FROM energy WHERE channel IN ('CPU','GPU')")
        if not db.execute("SELECT 1 FROM hosts LIMIT 1").fetchone():
            for i, h in enumerate(DEFAULT_HOSTS):
                db.execute("INSERT INTO hosts (name, label, url, cpu, gpu, other_watts, psu_eff, pos) "
                           "VALUES (?, ?, ?, ?, ?, ?, ?, ?)",
                           (h["name"], h["label"], h["url"], h["cpu"], h["gpu"],
                            h["other_watts"], h["psu_eff"], i + 1))
    return db


def load_hosts(db, only_enabled: bool = False) -> list:
    sql = "SELECT " + ", ".join(HOST_FIELDS) + " FROM hosts"
    if only_enabled:
        sql += " WHERE enabled = 1"
    return [dict(zip(HOST_FIELDS, r)) for r in db.execute(sql + " ORDER BY pos, name")]


def get_host(db, name: str):
    r = db.execute("SELECT " + ", ".join(HOST_FIELDS) + " FROM hosts WHERE name = ?", (name,)).fetchone()
    return dict(zip(HOST_FIELDS, r)) if r else None


def save_host(db, h: dict, new: bool) -> None:
    cols = ("label", "url", "username", "password", "cpu", "gpu", "other_watts", "psu_eff")
    with db:
        if new:
            pos = db.execute("SELECT COALESCE(MAX(pos), 0) + 1 FROM hosts").fetchone()[0]
            db.execute(f"INSERT INTO hosts (name, {', '.join(cols)}, enabled, pos) "
                       f"VALUES (?, {', '.join('?' * len(cols))}, 1, ?)",
                       (h["name"], *(h[c] for c in cols), pos))
        else:
            db.execute(f"UPDATE hosts SET {', '.join(c + ' = ?' for c in cols)} WHERE name = ?",
                       (*(h[c] for c in cols), h["name"]))


_TR = dict(zip("абвгдеёжзийклмнопрстуфхцчшщъыьэюяі",
               "a b v g d e e zh z i y k l m n o p r s t u f h ts ch sh sch _ y _ e yu ya i".split()))


def make_name(db, label: str) -> str:
    """Короткий латинский id хоста из названия: «Сервер-2» → server-2. Он же префикс каналов в базе."""
    s = "".join(_TR.get(c, c) for c in label.lower())
    s = re.sub(r"[^a-z0-9]+", "", s.replace("_", ""))[:16] or "host"
    taken = {r[0] for r in db.execute("SELECT name FROM hosts")}
    name, i = s, 2
    while name in taken:
        name, i = f"{s}{i}", i + 1
    return name


# ═══════════════════════════════ счёт ═══════════════════════════════

class Meter:
    """Копит Вт·ч по (час, канал). Пишут потоки-опросчики, читают страничка и flush."""

    def __init__(self):
        self.lock = threading.Lock()
        self.acc = {}
        self.last = {}
        self.live = {}   # хост → последнее, что от него пришло
        self.cfg = []    # включённые хосты, в порядке показа

    def sample(self, watts: dict, t_wall: float, t_mono: float) -> None:
        """Трапеция между прошлым и текущим замером. Вызывать под self.lock."""
        for ch, w in watts.items():
            if w is None:
                continue
            prev = self.last.get(ch)
            if prev is not None:
                d_mono, d_wall = t_mono - prev[1], t_wall - prev[0]
                if 0 < d_mono <= MAX_GAP_SECONDS and abs(d_wall - d_mono) <= 5:
                    hour = int(t_wall // 3600) * 3600
                    a = self.acc.setdefault((hour, ch), [0.0, 0.0])
                    a[0] += (prev[2] + w) / 2 * d_mono / 3600
                    a[1] += d_mono
            self.last[ch] = (t_wall, t_mono, w)

    def update(self, host: dict, picked: dict, watts: dict, err, t_wall: float, t_mono: float) -> None:
        name = host["name"]
        with self.lock:
            if err is None:
                self.sample({f"{name}-{k}": w for k, w in watts.items()}, t_wall, t_mono)
            self.live[name] = {"ts": t_wall, "error": err, "watts": dict(watts),
                               "sensors": {k: [list(i[:3]) for i in v] for k, v in picked.items()}}

    def forget(self, name: str) -> None:
        with self.lock:
            self.live.pop(name, None)

    def snapshot(self) -> dict:
        now = time.time()
        stale = 3 * max(POLL_SECONDS, OFFLINE_RETRY_SECONDS) + FETCH_TIMEOUT
        with self.lock:
            cfg, live = list(self.cfg), dict(self.live)
        hosts, wall, online = [], 0.0, 0
        for h in cfg:
            e = live.get(h["name"])
            off = [k for k in KINDS if sensor_mode(h[k.lower()]) == "off"]
            watts, sensors = {}, {}
            if e is None:
                state, note = "wait", "ещё не опрашивал"
            elif e["error"]:
                state, note = "bad", e["error"]
            elif now - e["ts"] > stale:
                state, note = "bad", "давно нет данных"
            else:
                state, watts, sensors = "ok", e["watts"], e["sensors"]
                hw = sorted({s[2] for v in sensors.values() for s in v if s[2]})
                miss = [k for k in KINDS if k not in off and watts.get(k) is None]
                note = ", ".join(hw) + ("; не найден сенсор: " + ", ".join(miss) if miss else "")
            s = sum(w for w in watts.values() if w is not None)
            if state == "ok":
                online += 1
                wall += (s + h["other_watts"]) / (h["psu_eff"] if h["psu_eff"] > 0 else 1.0)
            hosts.append({"name": h["name"], "label": h["label"], "state": state, "note": note,
                          "watts": {k: watts.get(k) for k in KINDS}, "off": off, "sum": s,
                          "sensors": sensors})
        if not cfg:
            text = "хостов нет — добавь на странице «Хосты»"
        else:
            text = f"Сейчас ≈ {num(wall, 0)} Вт от розетки · на связи {online} из {len(cfg)}"
        return {"ts": now, "kinds": list(KINDS), "hosts": hosts, "wall_w": wall,
                "online": online, "text": text}


def flush(db: sqlite3.Connection, meter: Meter) -> bool:
    with meter.lock:
        items, meter.acc = meter.acc, {}
    if not items:
        return True
    try:
        with db:
            db.executemany(UPSERT, [(h, ch, v[0], v[1]) for (h, ch), v in items.items()])
    except sqlite3.Error as e:
        log.warning("не смог записать в базу (%s), попробую позже", e)
        with meter.lock:  # вернуть несохранённое
            for k, v in items.items():
                a = meter.acc.setdefault(k, [0.0, 0.0])
                a[0] += v[0]
                a[1] += v[1]
        return False
    return True


# ═══════════════════════════════ отчёты ═══════════════════════════════

def load_rows(db, t_from=None, t_to=None) -> list:
    sql, args = "SELECT hour, channel, wh, secs FROM energy", ()
    if t_from is not None:
        sql, args = sql + " WHERE hour >= ? AND hour < ?", (int(t_from), int(t_to))
    return db.execute(sql + " ORDER BY hour", args).fetchall()


def aggregate(rows, key) -> dict:
    """Группы по key(hour): Вт·ч по каналам, секунды с данными по хостам и в целом."""
    hours = {}
    for hour, ch, wh, secs in rows:
        h = hours.setdefault(hour, ({}, {}))
        h[0][ch] = h[0].get(ch, 0.0) + wh
        hn = host_of(ch)
        h[1][hn] = max(h[1].get(hn, 0.0), min(secs, 3600.0))
    out = {}
    for hour in sorted(hours):
        whs, hs = hours[hour]
        g = out.setdefault(key(hour), {"wh": {}, "hs": {}, "secs": 0.0})
        for ch, wh in whs.items():
            g["wh"][ch] = g["wh"].get(ch, 0.0) + wh
        for hn, s in hs.items():
            g["hs"][hn] = g["hs"].get(hn, 0.0) + s
        g["secs"] += max(hs.values())
    return out


EMPTY = {"wh": {}, "hs": {}, "secs": 0.0}


def series_list(db, seen: set) -> list:
    """Серии графика = хосты: настроенные (в их порядке) + удалённые, но с данными."""
    meta = {h["name"]: h for h in load_hosts(db)}
    if seen:
        names = [n for n in meta if n in seen] + sorted(seen - set(meta))
    else:
        names = [n for n, h in meta.items() if h["enabled"]]
    return [{"name": n, "label": meta[n]["label"] if n in meta else n,
             "ow": meta[n]["other_watts"] if n in meta else OTHER_WATTS,
             "eff": meta[n]["psu_eff"] if n in meta else PSU_EFFICIENCY} for n in names]


def series_wh(g: dict, series: list) -> list:
    return [sum(v for ch, v in g["wh"].items() if host_of(ch) == s["name"]) for s in series]


def wall_kwh(g: dict, series: list) -> float:
    """Оценка «от розетки»: по каждому хосту (CPU+GPU + прочее) / КПД его блока питания."""
    smap = {s["name"]: s for s in series}
    tot = 0.0
    for hn, secs in g["hs"].items():
        s = smap.get(hn, {"ow": OTHER_WATTS, "eff": PSU_EFFICIENCY})
        wh = sum(v for ch, v in g["wh"].items() if host_of(ch) == hn)
        tot += (wh + s["ow"] * secs / 3600) / (s["eff"] if s["eff"] > 0 else 1.0) / 1000
    return tot


def month_report(db, y: int, m: int, now: float = None) -> dict:
    now = time.time() if now is None else now
    t0 = datetime(y, m, 1).timestamp()
    t1 = datetime(*next_month(y, m), 1).timestamp()
    rows = load_rows(db, t0, t1)
    series = series_list(db, {host_of(r[1]) for r in rows})
    by_day = aggregate(rows, lambda h: datetime.fromtimestamp(h).day)
    mg = aggregate(rows, lambda h: 0).get(0, EMPTY)
    today = date.today()
    days = []
    for d in range(1, calendar.monthrange(y, m)[1] + 1):
        g, dd = by_day.get(d), date(y, m, d)
        days.append({
            "day": d, "date": dd, "has": g is not None,
            "wh": series_wh(g or EMPTY, series), "secs": g["secs"] if g else 0.0,
            "today": dd == today, "future": dd > today,
        })
    wh = series_wh(mg, series)
    rep = {"y": y, "m": m, "series": series, "labels": [s["label"] for s in series],
           "days": days, "wh": wh, "total_wh": sum(wh), "secs": mg["secs"],
           "hsecs": [mg["hs"].get(s["name"], 0.0) for s in series],
           "kind_wh": [{kind_of(ch): v for ch, v in mg["wh"].items() if host_of(ch) == s["name"]}
                       for s in series],
           "wall_kwh": wall_kwh(mg, series), "projection": None}
    if rows and t0 <= now < t1:
        h0 = rows[0][0]
        s0 = max(min(r[3], 3600.0) for r in rows if r[0] == h0)
        start = max(t0, min(h0 + 3600 - s0, now - s0))
        elapsed = now - start
        if elapsed >= 6 * 3600:
            k = (t1 - t0) / elapsed
            rep["projection"] = {"total_kwh": rep["total_wh"] / 1000 * k, "wall_kwh": rep["wall_kwh"] * k}
    return rep


def months_report(db) -> tuple:
    rows = load_rows(db)
    series = series_list(db, {host_of(r[1]) for r in rows})
    by_month = aggregate(rows, lambda h: datetime.fromtimestamp(h).strftime("%Y-%m"))
    out = []
    for ym in sorted(by_month, reverse=True):
        g = by_month[ym]
        wh = series_wh(g, series)
        out.append({"ym": ym, "wh": wh, "total_wh": sum(wh), "secs": g["secs"],
                    "wall_kwh": wall_kwh(g, series)})
    return series, out


# ══════════════════════════════ логгер (run) ══════════════════════════════

def setup_logging(log_path) -> None:
    log.setLevel(logging.INFO)
    fmt = logging.Formatter("%(asctime)s %(levelname)s %(message)s", "%Y-%m-%d %H:%M:%S")
    if sys.stderr is not None:
        h = logging.StreamHandler()
        h.setFormatter(fmt)
        log.addHandler(h)
    if log_path:
        fh = logging.handlers.RotatingFileHandler(log_path, maxBytes=1_000_000,
                                                  backupCount=2, encoding="utf-8")
        fh.setFormatter(fmt)
        log.addHandler(fh)


def acquire_lock(path: Path, wait: float = 0.0):
    f = open(path, "a+")
    deadline = time.monotonic() + wait
    while True:
        try:
            if os.name == "nt":
                import msvcrt
                f.seek(0)
                msvcrt.locking(f.fileno(), msvcrt.LK_NBLCK, 1)
            else:
                import fcntl
                fcntl.flock(f.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
            return f
        except OSError:
            if time.monotonic() >= deadline:
                log.error("логгер уже запущен (занят %s)", path)
                sys.exit(1)
            time.sleep(0.5)


def supervised() -> bool:
    """Запущен ли логгер под присмотром (служба NSSM, systemd, Docker), который сам поднимет его после выхода."""
    if os.environ.get("POWERMETER_SUPERVISED"):
        return os.environ["POWERMETER_SUPERVISED"] not in ("0", "no", "false")
    if os.path.exists("/.dockerenv"):
        return True
    if os.name == "nt":
        try:
            out = subprocess.run(["tasklist", "/FI", f"PID eq {os.getppid()}", "/FO", "CSV", "/NH"],
                                 capture_output=True, timeout=5).stdout
            return b"nssm" in out.lower()
        except (OSError, subprocess.SubprocessError):
            return False
    return os.getppid() == 1  # systemd


RESTART_EXIT_CODE = 3  # ненулевой — чтобы и Restart=on-failure / restart: on-failure подняли заново


def respawn() -> None:
    """Запустить свою копию с теми же параметрами; она подождёт, пока этот процесс отпустит базу."""
    cmd = [sys.executable, os.path.abspath(sys.argv[0])] + sys.argv[1:]
    kw = {}
    if os.name == "nt":
        kw["creationflags"] = subprocess.DETACHED_PROCESS | subprocess.CREATE_NEW_PROCESS_GROUP
    else:
        kw["start_new_session"] = True
    subprocess.Popen(cmd, env=dict(os.environ, POWERMETER_WAIT_LOCK="1"), cwd=os.getcwd(),
                     stdin=subprocess.DEVNULL, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
                     close_fds=True, **kw)


def _raise_interrupt(*_):
    raise KeyboardInterrupt


class Poller(threading.Thread):
    """Опрашивает один хост в своём потоке: зависший хост не тормозит остальные."""

    def __init__(self, host: dict, meter: Meter, poll: float):
        super().__init__(name="poll-" + host["name"], daemon=True)
        self.host, self.meter, self.poll = host, meter, poll
        self.modes = {k: sensor_mode(host[k.lower()]) for k in KINDS}
        self.stop_ev = threading.Event()

    def run(self) -> None:
        h, tag = self.host, f"[{self.host['label']}]"
        last_err, last_err_log, last_ids = None, -1e9, None
        while not self.stop_ev.is_set():
            t_mono, t_wall = time.monotonic(), time.time()
            try:
                tree = fetch_lhm(h["url"], h["username"], h["password"])
                picked = pick_sensors(tree, self.modes)
                watts, err = channel_watts(picked), None
            except LHMError as e:
                picked, watts, err = {}, {}, str(e)
            except Exception as e:  # кривой JSON и прочее — поток не должен умирать
                picked, watts, err = {}, {}, f"ошибка разбора ответа LHM ({e!r})"
            if self.stop_ev.is_set():
                break
            self.meter.update(h, picked, watts, err, t_wall, t_mono)
            if err:
                if err != last_err or t_mono - last_err_log > 3600:
                    log.warning("%s %s", tag, err)
                    last_err_log = t_mono
            elif last_err:
                log.info("%s снова отвечает", tag)
            last_err = err
            if not err:
                ids = {k: tuple(i[0] for i in v) for k, v in picked.items()}
                if ids != last_ids:
                    for k, items in picked.items():
                        if items:
                            log.info("%s %s ← %s", tag, k, "; ".join(
                                f"{sid} «{name}» ({hw})" for sid, name, hw, _ in items))
                        else:
                            log.warning("%s %s: сенсор не найден — выбери вручную на /hosts", tag, k)
                    last_ids = ids
            delay = self.poll if not err else max(self.poll, OFFLINE_RETRY_SECONDS)
            self.stop_ev.wait(max(0.05, delay - (time.monotonic() - t_mono)))


class App:
    def __init__(self, db_path: Path, poll: float):
        self.db_path, self.poll = db_path, poll
        self.meter = Meter()
        self.changed = threading.Event()  # страничка поменяла список хостов
        self.restart = threading.Event()  # страничка попросила перезапуск
        self.started = time.time()
        self.supervised = supervised()
        self.srv = None

    def connect(self) -> sqlite3.Connection:
        return sqlite3.connect(str(self.db_path), timeout=15)


def cmd_run(args) -> int:
    db_path = Path(args.db)
    setup_logging(db_path.with_suffix(".log"))  # по умолчанию это powermeter.log рядом со скриптом
    for name in ("SIGTERM", "SIGBREAK"):
        if hasattr(signal, name):
            signal.signal(getattr(signal, name), _raise_interrupt)
    lock = acquire_lock(db_path.with_suffix(".lock"),
                        wait=20.0 if os.environ.pop("POWERMETER_WAIT_LOCK", "") else 0.0)
    db = open_db(db_path)
    app = App(db_path, args.poll or POLL_SECONDS)
    pollers = {}  # имя → (конфиг, поток)

    def sync() -> None:
        hosts = load_hosts(db, only_enabled=True)
        want = {h["name"]: h for h in hosts}
        for name in list(pollers):
            cfg, p = pollers[name]
            if want.get(name) != cfg:
                p.stop_ev.set()
                del pollers[name]
                app.meter.forget(name)
        for name, h in want.items():
            if name not in pollers:
                p = Poller(h, app.meter, app.poll)
                p.start()
                pollers[name] = (h, p)
        with app.meter.lock:
            app.meter.cfg = hosts
        return hosts

    sync()
    if args.port:
        app.srv = start_web(app, args.host, args.port)
    log.info("старт: опрос раз в %s с, база %s, хосты: %s%s", app.poll, db_path,
             ", ".join(f"{cfg['label']} ({cfg['url']})" for cfg, _ in pollers.values()) or "нет",
             " (под службой)" if app.supervised else "")

    next_flush = time.monotonic() + FLUSH_SECONDS
    try:
        while not app.restart.is_set():
            if app.changed.wait(1.0):
                app.changed.clear()
                if app.restart.is_set():
                    break
                log.info("список хостов обновлён: %s", ", ".join(h["label"] for h in sync()) or "пусто")
            if time.monotonic() >= next_flush:
                flush(db, app.meter)
                next_flush = time.monotonic() + FLUSH_SECONDS
    except KeyboardInterrupt:
        log.info("остановка")
    finally:
        for _, p in pollers.values():
            p.stop_ev.set()
        flush(db, app.meter)
        db.close()
        if app.srv:
            app.srv.shutdown()
            app.srv.server_close()
        lock.close()
    if app.restart.is_set():
        if app.supervised:
            log.info("перезапуск: выхожу, служба запустит заново")
            return RESTART_EXIT_CODE
        log.info("перезапуск: запускаю новую копию")
        respawn()
    return 0


# ═══════════════════════════════ страничка ═══════════════════════════════

_LIGHT = ("#2a78d6", "#eb6834", "#1baf7a", "#eda100", "#e87ba4", "#008300", "#6250d6", "#e34948")
_DARK = ("#3987e5", "#d95926", "#199e70", "#c98500", "#d55181", "#008300", "#9085e9", "#e66767")


def _vars(dark: bool) -> str:
    base = ("color-scheme:dark;--page:#0d0d0d;--surface:#1a1a19;--ink:#f0efec;--ink2:#c3c2b7;"
            "--muted:#898781;--grid:#2c2c2a;--axis:#383835;--border:rgba(255,255,255,.10);"
            "--good:#199e70;--bad:#e66767;"
            if dark else
            "color-scheme:light;--page:#f9f9f7;--surface:#fcfcfb;--ink:#0b0b0b;--ink2:#52514e;"
            "--muted:#898781;--grid:#e1e0d9;--axis:#c3c2b7;--border:rgba(11,11,11,.10);"
            "--good:#1baf7a;--bad:#e34948;")
    return base + "".join(f"--s{i}:{c};" for i, c in enumerate(_DARK if dark else _LIGHT))


PAGE_CSS = (
    ".viz-root{" + _vars(False) + "}"
    "@media (prefers-color-scheme:dark){:root:where(:not([data-theme=\"light\"])) .viz-root{"
    + _vars(True) + "}}"
    ":root[data-theme=\"dark\"] .viz-root{" + _vars(True) + "}"
    + """
*{box-sizing:border-box}
body{margin:0;background:var(--page);color:var(--ink);font:14px/1.45 system-ui,-apple-system,"Segoe UI",sans-serif}
.wrap{max-width:1000px;margin:0 auto;padding:20px 16px 32px}
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
td.l,th.l{text-align:left;white-space:normal}
tr.tot td{font-weight:600;border-bottom:0}
tr.cur td{background:var(--grid)}
tr.dim td{color:var(--muted)}
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
.dot{display:inline-block;width:8px;height:8px;border-radius:50%;margin-right:7px;background:var(--muted);vertical-align:middle}
.dot.ok{background:var(--good)}
.dot.bad{background:var(--bad)}
.good{color:var(--good)}
.bad{color:var(--bad)}
.alert{border:1px solid var(--bad);color:var(--bad);border-radius:10px;padding:10px 12px;margin-bottom:14px;background:var(--surface)}
.notice{border:1px solid var(--good);border-radius:10px;padding:10px 12px;margin-bottom:14px;background:var(--surface)}
button,.btn{font:inherit;font-size:13px;color:var(--ink);background:var(--surface);border:1px solid var(--border);border-radius:8px;padding:4px 10px;cursor:pointer;text-decoration:none;display:inline-block}
button:hover,.btn:hover{border-color:var(--axis)}
button.primary{background:var(--s0);border-color:var(--s0);color:#fff}
button.danger{color:var(--bad)}
form.inl{display:inline}
.acts{display:flex;gap:6px;justify-content:flex-end;flex-wrap:wrap}
.fgrid{display:grid;grid-template-columns:repeat(auto-fit,minmax(210px,1fr));gap:12px 16px}
.fgrid label{display:flex;flex-direction:column;gap:4px;color:var(--ink2);font-size:13px}
.fgrid .hint{color:var(--muted);font-size:12px}
input,select{font:inherit;color:var(--ink);background:var(--page);border:1px solid var(--border);border-radius:8px;padding:6px 8px;width:100%}
input[type=checkbox]{width:auto}
.mode{display:flex;gap:6px}
.mode select{width:auto;flex:none}
.actions{display:flex;gap:8px;margin-top:14px;flex-wrap:wrap;align-items:center}
#probe-out{margin-top:12px}
code{font-size:12px;word-break:break-all}
"""
    + "".join(f".s{i}{{fill:var(--s{i})}}.c{i}{{background:var(--s{i})}}"
              f".key.k{i}{{border-top-color:var(--s{i})}}" for i in range(N_COLORS)))

PAGE_JS = r"""
(function () {
  var NC = 8;
  var dataEl = document.getElementById('month-data');
  var D = dataEl ? JSON.parse(dataEl.textContent) : null;
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
  function colPath(x, y, w, h, r) {
    r = Math.min(r, w / 2, h);
    return 'M' + x + ',' + (y + h) + 'V' + (y + r) + 'a' + r + ',' + r + ' 0 0 1 ' + r + ',' + (-r) +
      'H' + (x + w - r) + 'a' + r + ',' + r + ' 0 0 1 ' + r + ',' + r + 'V' + (y + h) + 'Z';
  }
  function row(val, label, k) {
    var r = document.createElement('div'); r.className = 'tip-row';
    var key = document.createElement('span'); key.className = 'key' + (k === null ? '' : ' k' + (k % NC)); r.appendChild(key);
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
    for (var k = d.vals.length - 1; k >= 0; k--) if (d.vals[k] > 0) tip.appendChild(row(d.vals_s[k], D.channels[k], k));
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
        var h = y0 - y1 - (j > 0 ? 2 : 0);
        if (h < 1) return;
        var cls = 'seg s' + (s[1] % NC);
        if (j === segs.length - 1) el('path', {d: colPath(x, y1, bw, h, 4), 'class': cls}, g);
        else el('rect', {x: x, y: y1, width: bw, height: h, 'class': cls}, g);
        if (i === lastI && h >= 13 && n - i <= 2) {
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
  if (box && D) {
    draw();
    var rt;
    window.addEventListener('resize', function () { clearTimeout(rt); rt = setTimeout(draw, 120); });
  }

  // ── «сейчас»: строка в шапке и таблица хостов
  var liveEl = document.getElementById('live'), rowsEl = document.getElementById('live-rows');
  function wfmt(w) { return w == null ? '—' : Math.round(w) + ' Вт'; }
  function cell(tr, text, cls) {
    var td = document.createElement('td'); if (cls) td.className = cls; td.textContent = text; tr.appendChild(td); return td;
  }
  function renderLive(j) {
    if (liveEl) liveEl.textContent = j.text;
    if (!rowsEl) return;
    rowsEl.textContent = '';
    j.hosts.forEach(function (h) {
      var tr = document.createElement('tr');
      var td = cell(tr, '', 'l');
      var dot = document.createElement('span'); dot.className = 'dot ' + h.state; td.appendChild(dot);
      td.appendChild(document.createTextNode(h.label));
      j.kinds.forEach(function (k) {
        cell(tr, h.off.indexOf(k) >= 0 ? 'нет (0)' : h.state !== 'ok' ? '—' : h.watts[k] == null ? 'нет сенсора' : wfmt(h.watts[k]));
      });
      cell(tr, h.state === 'ok' ? wfmt(h.sum) : '—');
      cell(tr, h.note, 'l note');
      rowsEl.appendChild(tr);
    });
  }
  var liveData = document.getElementById('live-data');
  if (liveData) renderLive(JSON.parse(liveData.textContent));
  if (liveEl) setInterval(function () {
    fetch('/api/live', {cache: 'no-store'})
      .then(function (r) { return r.json(); })
      .then(renderLive)
      .catch(function () { liveEl.textContent = 'логгер не отвечает'; });
  }, 3000);
})();
"""

HOSTS_JS = r"""
(function () {
  var f = document.getElementById('hostform');
  if (!f) return;
  var kinds = ['cpu', 'gpu'];
  function sync(k) { f.elements[k + '_ids'].hidden = f.elements[k + '_mode'].value !== 'manual'; }
  kinds.forEach(function (k) { f.elements[k + '_mode'].addEventListener('change', function () { sync(k); }); sync(k); });
  function ids(k) { return f.elements[k + '_ids'].value.split(/[\s,;]+/).filter(Boolean); }
  var out = document.getElementById('probe-out'), btn = document.getElementById('probe');
  function el(tag, text, cls) { var e = document.createElement(tag); if (text != null) e.textContent = text; if (cls) e.className = cls; return e; }
  btn.addEventListener('click', function () {
    out.textContent = 'Опрашиваю…';
    btn.disabled = true;
    fetch('/api/probe', {method: 'POST', body: new URLSearchParams(new FormData(f))})
      .then(function (r) { return r.json(); })
      .then(render)
      .catch(function (e) { out.textContent = 'Ошибка: ' + e; })
      .then(function () { btn.disabled = false; });
  });
  function render(j) {
    out.textContent = '';
    if (!j.ok) { out.appendChild(el('p', '✗ ' + j.error, 'bad')); return; }
    var p = el('p', '✓ ' + j.url + ' отвечает. ', 'good');
    p.appendChild(el('span', j.summary, 'note'));
    out.appendChild(p);
    if (!j.sensors.length) { out.appendChild(el('p', 'Power-сенсоров у этого LHM нет совсем.', 'bad')); return; }
    out.appendChild(el('p', 'Галочками можно выбрать сенсоры вручную (режим станет «вручную»). ' +
                              'Встройку Intel не отмечай — она уже внутри CPU Package.', 'note'));
    var wrap = el('div', null, 'scroll'), t = el('table'), head = el('tr');
    ['Сенсор', 'Железо', 'Сейчас', 'CPU', 'GPU'].forEach(function (s, i) { head.appendChild(el('th', s, i < 2 ? 'l' : '')); });
    var thead = el('thead'); thead.appendChild(head); t.appendChild(thead);
    var tb = el('tbody');
    j.sensors.forEach(function (s) {
      var tr = el('tr');
      var td = el('td', s.text + ' ', 'l'); td.appendChild(el('code', s.id, 'note')); tr.appendChild(td);
      tr.appendChild(el('td', s.hw, 'l'));
      tr.appendChild(el('td', s.value == null ? '—' : s.value.toFixed(1) + ' Вт'));
      kinds.forEach(function (k) {
        var K = k.toUpperCase(), mode = f.elements[k + '_mode'].value;
        var cb = el('input'); cb.type = 'checkbox'; cb.dataset.kind = k; cb.value = s.id;
        cb.checked = mode === 'manual' ? ids(k).indexOf(s.id) >= 0 : mode === 'auto' && s.auto === K;
        cb.addEventListener('change', function () {
          f.elements[k + '_mode'].value = 'manual'; sync(k);
          var sel = [];
          tb.querySelectorAll('input[data-kind="' + k + '"]').forEach(function (c) { if (c.checked) sel.push(c.value); });
          f.elements[k + '_ids'].value = sel.join(' ');
        });
        var c = el('td'); c.appendChild(cb);
        if (s.auto === K) c.appendChild(el('span', ' авто', 'note'));
        tr.appendChild(c);
      });
      tb.appendChild(tr);
    });
    t.appendChild(tb); wrap.appendChild(t); out.appendChild(wrap);
  }
  document.querySelectorAll('form[data-confirm]').forEach(function (fm) {
    fm.addEventListener('submit', function (ev) { if (!confirm(fm.dataset.confirm)) ev.preventDefault(); });
  });
})();
"""


def page(title: str, body: str, script: str = "") -> str:
    return ('<!doctype html><html lang="ru"><head><meta charset="utf-8">'
            '<meta name="viewport" content="width=device-width,initial-scale=1">'
            '<meta name="color-scheme" content="light dark">'
            f'<title>{html.escape(title)}</title><style>{PAGE_CSS}</style></head>'
            f'<body class="viz-root"><div class="wrap">{body}</div>'
            + (f"<script>{script}</script>" if script else "") + "</body></html>")


def json_script(id_: str, data) -> str:
    return (f'<script id="{id_}" type="application/json">'
            + json.dumps(data, ensure_ascii=False).replace("</", "<\\/") + "</script>")


def month_json(rep: dict) -> dict:
    hosts = []
    for i, s in enumerate(rep["series"]):
        hosts.append({"name": s["name"], "label": s["label"], "kwh": rep["wh"][i] / 1000,
                      "by_kind_kwh": {k: v / 1000 for k, v in rep["kind_wh"][i].items()},
                      "hours": rep["hsecs"][i] / 3600})
    return {
        "month": f"{rep['y']}-{rep['m']:02d}", "hosts": hosts,
        "total_kwh": rep["total_wh"] / 1000, "hours": rep["secs"] / 3600,
        "wall_kwh_estimate": rep["wall_kwh"], "cost_estimate": rep["wall_kwh"] * TARIFF,
        "projection": rep["projection"],
        "days": [{"date": d["date"].isoformat(), "hours": d["secs"] / 3600,
                  "kwh": {s["name"]: d["wh"][i] / 1000 for i, s in enumerate(rep["series"])}}
                 for d in rep["days"] if d["has"]],
    }


def render_month(db, y: int, m: int, live: dict) -> str:
    e = html.escape
    rep = month_report(db, y, m)
    mseries, months = months_report(db)
    labels = rep["labels"]
    title = month_title(y, m)
    (py_, pm_), (ny_, nm_) = prev_month(y, m), next_month(y, m)

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
                    + ", ".join(f"{c} {v}" for c, v in zip(labels, vals_s)),
        })
    data = {"unit": "кВт·ч", "channels": labels, "aria": f"Потребление по дням, {title}, кВт·ч",
            "days": days_js}

    def tile(label, value, note, sw=None):
        swh = f'<span class="sw c{sw % N_COLORS}"></span>' if sw is not None else ""
        return (f'<div class="tile"><div class="label">{swh}{e(label)}</div>'
                f'<div class="value">{value}</div><div class="note">{note}</div></div>')

    tiles = []
    for i, s in enumerate(rep["series"]):
        kinds = " · ".join(f"{k} {num(v / 1000, 2)}" for k, v in sorted(rep["kind_wh"][i].items()))
        note = (kinds + " · " if kinds else "") + f"ср. {num(avg_w(rep['wh'][i], rep['hsecs'][i]), 0)} Вт"
        tiles.append(tile(s["label"], f'{num(rep["wh"][i] / 1000, 2)}<span class="u"> кВт·ч</span>', note, sw=i))
    tiles.append(tile("≈ от розетки", f'{num(rep["wall_kwh"], 1)}<span class="u"> кВт·ч</span>',
                      "+ прочее железо и КПД БП каждого хоста"))
    tiles.append(tile("≈ стоимость", f'{num(rep["wall_kwh"] * TARIFF, 0)}<span class="u"> {e(CURRENCY)}</span>',
                      f"{num(TARIFF, 2)} {e(CURRENCY)} за кВт·ч, от розетки"))
    if rep["projection"]:
        p = rep["projection"]
        tiles.append(tile("Прогноз на месяц", f'≈ {num(p["total_kwh"], 0)}<span class="u"> кВт·ч</span>',
                          f'≈ {num(p["wall_kwh"] * TARIFF, 0)} {e(CURRENCY)} от розетки, если дальше так же'))

    legend = "".join(f'<span><span class="sw c{i % N_COLORS}"></span>{e(c)}</span>' for i, c in enumerate(labels))

    head = "".join(f"<th>{e(c)}</th>" for c in labels)
    trs = []
    for d in rep["days"]:
        if d["future"]:
            continue
        dd = d["date"]
        lab = f"{dd.day:02d}.{dd.month:02d} {WEEKDAYS[dd.weekday()]}"
        if not d["has"]:
            trs.append(f"<tr><td>{lab}</td>" + "<td>—</td>" * (len(labels) + 3) + "</tr>")
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

    mhead = "".join(f"<th>{e(s['label'])}</th>" for s in mseries)
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

    live_card = ('<section class="card"><div class="card-head"><h2>Сейчас</h2>'
                 '<a class="note" href="/hosts">настроить хосты</a></div><div class="scroll"><table>'
                 '<thead><tr><th>Хост</th>' + "".join(f"<th>{k}</th>" for k in KINDS)
                 + '<th>Сумма</th><th class="l">Железо / статус</th></tr></thead>'
                 '<tbody id="live-rows"></tbody></table></div></section>')

    footer = ("«≈ от розетки» = по каждому хосту (CPU + GPU + прочее железо) / КПД блока питания — "
              "оценка, без монитора; «прочее» и КПД задаются на странице хостов. "
              f"Дыры в данных длиннее {MAX_GAP_SECONDS} с не считаются.")

    nav_prev = f'<a class="nav" href="/?month={py_}-{pm_:02d}">‹ {MONTHS[pm_ - 1]}</a>'
    nav_next = (f'<a class="nav" href="/?month={ny_}-{nm_:02d}">{MONTHS[nm_ - 1]} ›</a>'
                if datetime(ny_, nm_, 1) <= datetime.now() else '<span class="nav off">—</span>')
    chart = ('<div id="chart"></div>' if rep["secs"] > 0
             else '<div class="empty">Нет данных за этот месяц</div>')
    body = (
        f'<div class="bar">{nav_prev}<h1>{e(title)}</h1>{nav_next}'
        f'<span class="live" id="live">{e(live["text"])}</span>'
        '<a class="nav" href="/hosts">Хосты</a></div>'
        '<section class="card hero"><div class="label">CPU + GPU за месяц, все хосты</div>'
        f'<div class="value">{num(rep["total_wh"] / 1000, 2 if rep["total_wh"] < 10000 else 1)}'
        '<span class="unit"> кВт·ч</span></div>'
        f'<div class="sub">по датчикам LHM · {num(rep["secs"] / 3600, 0)} ч с данными</div></section>'
        f'<section class="tiles">{"".join(tiles)}</section>'
        f'{live_card}'
        f'<section class="card"><div class="card-head"><h2>По дням, кВт·ч</h2>'
        f'<div class="legend">{legend}</div></div>{chart}'
        f'<details><summary>Таблица по дням</summary>{day_table}</details></section>'
        f'<section class="card"><h2>По месяцам</h2>{months_table}</section>'
        f'<footer>{footer}</footer>'
        '<div id="tip" class="tip" hidden></div>'
        + json_script("month-data", data) + json_script("live-data", live)
    )
    return page(f"{title} · CPU+GPU, кВт·ч", body, PAGE_JS)


# ─────────────────────────────── хосты ───────────────────────────────

class FormError(Exception):
    pass


def build_url(address: str, port: int) -> str:
    """'192.168.1.22' + 8085 → http://192.168.1.22:8085/data.json; полный URL оставляем как есть."""
    a = (address or "").strip()
    if not a:
        raise FormError("Нужен адрес: IP или имя компа")
    if "://" in a or "/" in a:
        try:
            u = urllib.parse.urlsplit(a if "://" in a else "http://" + a)
            explicit_port = u.port
        except ValueError:
            raise FormError("Не понял адрес") from None
        if u.scheme not in ("http", "https") or not u.hostname or "@" in u.netloc:
            raise FormError("Адрес должен быть вида 192.168.1.10 или http://192.168.1.10:8085")
        netloc = u.netloc if explicit_port else f"{u.netloc}:{port}"
        path = u.path if u.path not in ("", "/") else "/data.json"
        return urllib.parse.urlunsplit((u.scheme, netloc, path, u.query, ""))
    if not re.fullmatch(r"[A-Za-z0-9._-]+(:\d{1,5})?", a):
        raise FormError("Адрес должен быть вида 192.168.1.10 или имя компа")
    return f"http://{a}/data.json" if ":" in a else f"http://{a}:{port}/data.json"


def split_url(url: str) -> tuple:
    mt = re.fullmatch(r"http://([^/:@]+):(\d+)/data\.json", url)
    return (mt.group(1), mt.group(2)) if mt else (url, str(LHM_PORT))


def _field(form: dict, k: str) -> str:
    return (form.get(k) or [""])[0].strip()


def conn_from_form(form: dict, existing) -> dict:
    """Адрес и логин из формы: всё, что нужно, чтобы достучаться до LHM."""
    try:
        port = int(_field(form, "port") or LHM_PORT)
        if not 1 <= port <= 65535:
            raise ValueError
    except ValueError:
        raise FormError("Порт — число от 1 до 65535") from None
    h = {"url": build_url(_field(form, "address"), port), "username": _field(form, "username")}
    pw = (form.get("password") or [""])[0]
    if not h["username"]:
        pw = ""
    elif not pw and existing:
        pw = existing["password"]  # пустое поле при правке = не менять
    h["password"] = pw
    return h


def host_from_form(form: dict, existing) -> dict:
    def g(k):
        return _field(form, k)

    label = g("label")[:40]
    if not label:
        raise FormError("Нужно название хоста")
    h = dict(conn_from_form(form, existing), label=label)
    for k in ("cpu", "gpu"):
        mode = g(k + "_mode") or "auto"
        if mode == "manual":
            ids = " ".join(x for x in re.split(r"[\s,;]+", g(k + "_ids")) if x)
            if not ids:
                raise FormError(f"{k.upper()}: выбран режим «вручную», но не указан ни один SensorId "
                                "(нажми «Проверить связь» и отметь сенсоры галочками)")
            h[k] = ids
        elif mode in ("auto", "off"):
            h[k] = mode
        else:
            raise FormError(f"{k.upper()}: непонятный режим")
    if h["cpu"] == "off" and h["gpu"] == "off":
        raise FormError("И CPU, и GPU выключены — с этого хоста нечего считать")
    try:
        h["other_watts"] = float((g("other_watts") or "0").replace(",", "."))
        eff = float((g("psu_eff") or "100").replace(",", "."))
    except ValueError:
        raise FormError("«Прочее» и КПД — числа") from None
    if not 0 <= h["other_watts"] <= 5000:
        raise FormError("«Прочее» — от 0 до 5000 Вт")
    if not 30 <= eff <= 100:
        raise FormError("КПД блока питания — от 30 до 100 %")
    h["psu_eff"] = eff / 100
    return h


def mode_text(v: str) -> str:
    m = sensor_mode(v)
    if m == "auto":
        return "авто"
    if m == "off":
        return "нет (0)"
    return f"вручную ({len(m)})"


def render_hosts(db, live: dict, edit=None, vals=None, error=None, notice=None, app=None) -> str:
    e = html.escape
    hosts = load_hosts(db)
    status = {h["name"]: h for h in live["hosts"]}
    rows = []
    for h in hosts:
        st = status.get(h["name"])
        if not h["enabled"]:
            dot, stxt = "", "выключен"
        elif st is None:
            dot, stxt = "", "ещё не опрашивал"
        elif st["state"] == "ok":
            dot, stxt = "ok", f"{num(st['sum'], 0)} Вт"
        else:
            dot, stxt = st["state"], st["note"]
        addr = urllib.parse.urlsplit(h["url"]).netloc or h["url"]
        n = e(h["name"])
        rows.append(
            f'<tr{"" if h["enabled"] else " class=dim"}><td class="l"><span class="dot {dot}"></span>{e(h["label"])}'
            f'<div class="note">id: {n}{" · логин " + e(h["username"]) if h["username"] else ""}</div></td>'
            f'<td class="l">{e(addr)}</td><td>{mode_text(h["cpu"])}</td><td>{mode_text(h["gpu"])}</td>'
            f'<td>{num(h["other_watts"], 0)} Вт / {num(h["psu_eff"] * 100, 0)} %</td>'
            f'<td class="l">{e(stxt)}</td><td><div class="acts">'
            f'<a class="btn" href="/hosts?edit={urllib.parse.quote(h["name"])}">Изменить</a>'
            f'<form class="inl" method="post" action="/hosts/toggle"><input type="hidden" name="name" value="{n}">'
            f'<button>{"Выключить" if h["enabled"] else "Включить"}</button></form>'
            f'<form class="inl" method="post" action="/hosts/delete" data-confirm="Удалить «{e(h["label"])}» из опроса? '
            f'Накопленные кВт·ч останутся в отчётах."><input type="hidden" name="name" value="{n}">'
            f'<button class="danger">Удалить</button></form></div></td></tr>')
    table = ('<div class="scroll"><table><thead><tr><th>Хост</th><th class="l">Адрес</th><th>CPU</th><th>GPU</th>'
             '<th>Прочее / КПД</th><th class="l">Сейчас</th><th></th></tr></thead><tbody>'
             + "".join(rows) + "</tbody></table></div>") if rows else '<div class="empty">Хостов пока нет</div>'

    if vals is None:
        if edit:
            a, p = split_url(edit["url"])
            vals = {"label": edit["label"], "address": a, "port": p, "username": edit["username"],
                    "other_watts": f"{edit['other_watts']:g}", "psu_eff": f"{edit['psu_eff'] * 100:g}"}
            for k in ("cpu", "gpu"):
                m = sensor_mode(edit[k])
                vals[k + "_mode"] = m if isinstance(m, str) else "manual"
                vals[k + "_ids"] = "" if isinstance(m, str) else " ".join(m)
        else:
            vals = {"port": str(LHM_PORT), "cpu_mode": "auto", "gpu_mode": "auto",
                    "other_watts": f"{OTHER_WATTS:g}", "psu_eff": f"{PSU_EFFICIENCY * 100:g}"}

    def v(k):
        return e(vals.get(k, ""))

    def mode_field(k):
        opts = "".join(f'<option value="{o}"{" selected" if vals.get(k + "_mode") == o else ""}>{t}</option>'
                       for o, t in (("auto", "авто"), ("off", "нет — считать 0"), ("manual", "вручную")))
        return (f'<label>{k.upper()}<span class="mode"><select name="{k}_mode">{opts}</select>'
                f'<input name="{k}_ids" value="{v(k + "_ids")}" placeholder="SensorId через пробел"></span></label>')

    form = (
        f'<section class="card" id="form"><h2>{"Изменить «" + e(edit["label"]) + "»" if edit else "Добавить хост"}</h2>'
        '<p class="note">Данные — как в LibreHardwareMonitor на том компе: Options → Remote Web Server '
        '(адрес, порт, а если включена Authentication — логин и пароль). В Interface там должен быть адрес '
        'в локалке, а не 127.0.0.1, и порт открыт в брандмауэре.</p>'
        '<form method="post" action="/hosts/save" id="hostform" autocomplete="off">'
        + (f'<input type="hidden" name="name" value="{e(edit["name"])}">' if edit else "")
        + '<div class="fgrid">'
        f'<label>Название<input name="label" value="{v("label")}" required maxlength="40" placeholder="Сервер-2"></label>'
        f'<label>Адрес (IP или имя компа)<input name="address" value="{v("address")}" required placeholder="192.168.1.22"></label>'
        f'<label>Порт<input name="port" value="{v("port")}" inputmode="numeric"></label>'
        f'<label>Логин<input name="username" value="{v("username")}" autocomplete="off"></label>'
        '<label>Пароль<input name="password" type="password" autocomplete="new-password"'
        + (' placeholder="пусто — не менять"' if edit and edit["password"] else "") + '></label>'
        + mode_field("cpu") + mode_field("gpu")
        + f'<label>Прочее железо, Вт<input name="other_watts" value="{v("other_watts")}" inputmode="decimal">'
        '<span class="hint">плата, память, диски, вентиляторы; для VM — 0</span></label>'
        f'<label>КПД блока питания, %<input name="psu_eff" value="{v("psu_eff")}" inputmode="decimal"></label>'
        '</div><div class="actions">'
        '<button type="button" id="probe">Проверить связь</button>'
        f'<button type="submit" class="primary">{"Сохранить" if edit else "Добавить"}</button>'
        + ('<a class="btn" href="/hosts">Отмена</a>' if edit else "")
        + '</div></form><div id="probe-out"></div></section>')

    body = ('<div class="bar"><a class="nav" href="/">‹ К отчёту</a><h1>Хосты</h1>'
            f'<span class="live">{e(live["text"])}</span></div>'
            + (f'<div class="alert">{e(error)}</div>' if error else "")
            + (f'<div class="notice">{e(notice)}</div>' if notice else "")
            + f'<section class="card"><h2>Опрашиваются</h2>{table}'
            '<p class="note">id хоста — префикс его каналов в базе. Удалённый хост пропадает из опроса, '
            'но его кВт·ч остаются в отчётах.</p></section>'
            + form + (restart_card(app) if app else ""))
    return page("Хосты · powermeter", body, HOSTS_JS)


def restart_card(app) -> str:
    up = int(time.time() - app.started)
    up_s = (f"{up // 86400} д " if up >= 86400 else "") + f"{up % 86400 // 3600} ч {up % 3600 // 60} мин"
    how = ("служба запустит его заново" if app.supervised
           else "он сам запустит свою новую копию")
    return ('<section class="card"><h2>Логгер</h2>'
            f'<p class="note">Работает {up_s}, с {datetime.fromtimestamp(app.started):%d.%m.%Y %H:%M}. '
            'Хосты подхватываются на лету, перезапуск нужен только после обновления powermeter.py. '
            f'Накопленное сохранится в базу, логгер выйдет, и {how}; пропадёт пара секунд замеров.</p>'
            '<form method="post" action="/restart" data-confirm="Перезапустить логгер?">'
            '<button>Перезапустить логгер</button></form></section>')


RESTART_PAGE = ('<div class="bar"><h1>Перезапускаюсь…</h1></div>'
                '<p class="note" id="st">Жду, пока логгер поднимется.</p>'
                '<script>(function(){var n=0;function t(){fetch("/api/live",{cache:"no-store"})'
                '.then(function(r){if(r.ok)location.href="/hosts";else throw 0;})'
                '.catch(function(){if(++n>40)document.getElementById("st").textContent='
                '"Логгер так и не поднялся — загляни в powermeter.log.";else setTimeout(t,1000);});}'
                'setTimeout(t,2500);})();</script>')


def probe(db, form: dict) -> dict:
    name = _field(form, "name")
    try:
        h = conn_from_form(form, get_host(db, name) if name else None)
    except FormError as ex:
        return {"ok": False, "error": str(ex)}
    try:
        tree = fetch_lhm(h["url"], h["username"], h["password"])
    except LHMError as ex:
        return {"ok": False, "error": str(ex), "url": h["url"]}
    sens = power_sensors(tree)
    auto = {}
    for s in sens:
        if s["auto"] and s["value"] is not None:
            auto[s["auto"]] = auto.get(s["auto"], 0.0) + s["value"]
    summary = ("Автопоиск нашёл: " + ", ".join(f"{k} ≈ {num(w, 0)} Вт" for k, w in sorted(auto.items()))
               if auto else "Автопоиск ничего не нашёл — выбери сенсоры вручную.")
    missing = [k for k in KINDS if k not in auto]
    if auto and missing:
        summary += f" Нет: {', '.join(missing)}."
    return {"ok": True, "url": h["url"], "sensors": sens, "summary": summary}


class _Server(ThreadingHTTPServer):
    daemon_threads = True
    allow_reuse_address = os.name != "nt"


def start_web(app: App, host: str, port: int):
    class Handler(BaseHTTPRequestHandler):
        server_version = "powermeter"

        def log_message(self, *_):
            pass

        def _send(self, code, body, ctype, extra=None):
            data = body.encode("utf-8")
            self.send_response(code)
            self.send_header("Content-Type", ctype + "; charset=utf-8")
            self.send_header("Content-Length", str(len(data)))
            self.send_header("Cache-Control", "no-store")
            for k, v in (extra or {}).items():
                self.send_header(k, v)
            self.end_headers()
            self.wfile.write(data)

        def _json(self, obj, code=200):
            self._send(code, json.dumps(obj, ensure_ascii=False), "application/json")

        def _redirect(self, to):
            self._send(303, "", "text/plain", {"Location": to})

        def do_GET(self):
            u = urllib.parse.urlsplit(self.path)
            q = urllib.parse.parse_qs(u.query)
            try:
                if u.path == "/api/live":
                    self._json(app.meter.snapshot())
                    return
                db = app.connect()
                try:
                    if u.path in ("/", "/api/month"):
                        y, m = parse_month(q.get("month", [""])[0]) or parse_month("")
                        if u.path == "/":
                            self._send(200, render_month(db, y, m, app.meter.snapshot()), "text/html")
                        else:
                            self._json(month_json(month_report(db, y, m)))
                    elif u.path == "/hosts":
                        edit = get_host(db, q["edit"][0]) if "edit" in q else None
                        saved = q.get("saved", [""])[0]
                        notice = f"Сохранено: «{saved}». Логгер уже опрашивает по-новому." if saved else None
                        self._send(200, render_hosts(db, app.meter.snapshot(), edit=edit, notice=notice,
                                                     app=app), "text/html")
                    elif u.path == "/api/hosts":
                        self._json([{k: v for k, v in h.items() if k != "password"} for h in load_hosts(db)])
                    else:
                        self._send(404, "not found", "text/plain")
                finally:
                    db.close()
            except Exception as ex:
                log.exception("ошибка странички")
                self._send(500, f"ошибка: {ex}", "text/plain")

        def _same_origin(self) -> bool:
            # чтобы чужой сайт не мог из твоего браузера поменять список хостов
            if self.headers.get("Sec-Fetch-Site") in ("cross-site", "same-site"):
                return False
            origin = self.headers.get("Origin")
            if not origin:
                return True
            return urllib.parse.urlsplit(origin).netloc == self.headers.get("Host", "")

        def do_POST(self):
            u = urllib.parse.urlsplit(self.path)
            if not self._same_origin():
                self._send(403, "запрос с чужого сайта", "text/plain")
                return
            try:
                n = int(self.headers.get("Content-Length") or 0)
                if n > 65536:
                    self._send(413, "слишком много", "text/plain")
                    return
                form = urllib.parse.parse_qs(self.rfile.read(n).decode("utf-8", "replace"),
                                             keep_blank_values=True)
                name = (form.get("name") or [""])[0]
                db = app.connect()
                try:
                    if u.path == "/api/probe":
                        self._json(probe(db, form))
                    elif u.path == "/hosts/save":
                        existing = get_host(db, name) if name else None
                        if name and not existing:
                            self._redirect("/hosts")
                            return
                        try:
                            h = host_from_form(form, existing)
                        except FormError as ex:
                            vals = {k: v[0] for k, v in form.items() if k != "password"}
                            self._send(400, render_hosts(db, app.meter.snapshot(), edit=existing,
                                                         vals=vals, error=str(ex), app=app), "text/html")
                            return
                        h["name"] = existing["name"] if existing else make_name(db, h["label"])
                        save_host(db, h, new=existing is None)
                        app.changed.set()
                        log.info("хост %s «%s» %s: %s", h["name"], h["label"],
                                 "изменён" if existing else "добавлен", h["url"])
                        self._redirect("/hosts?saved=" + urllib.parse.quote(h["label"]))
                    elif u.path == "/hosts/toggle":
                        with db:
                            db.execute("UPDATE hosts SET enabled = 1 - enabled WHERE name = ?", (name,))
                        app.changed.set()
                        self._redirect("/hosts")
                    elif u.path == "/restart":
                        self._send(200, page("Перезапуск · powermeter", RESTART_PAGE), "text/html",
                                   {"Connection": "close"})
                        self.close_connection = True
                        log.info("перезапуск по кнопке на страничке")
                        app.restart.set()
                        app.changed.set()
                    elif u.path == "/hosts/delete":
                        with db:
                            db.execute("DELETE FROM hosts WHERE name = ?", (name,))
                        app.changed.set()
                        log.info("хост %s удалён из опроса", name)
                        self._redirect("/hosts")
                    else:
                        self._send(404, "not found", "text/plain")
                finally:
                    db.close()
            except Exception as ex:
                log.exception("ошибка странички")
                self._send(500, f"ошибка: {ex}", "text/plain")

    try:
        srv = _Server((host, port), Handler)
    except OSError as ex:
        log.warning("страничка не запустилась на %s:%s (%s) — логгер работает без неё", host, port, ex)
        return None
    threading.Thread(target=srv.serve_forever, name="web", daemon=True).start()
    shown = "127.0.0.1" if host in ("", "0.0.0.0") else host
    log.info("страничка: http://%s:%s/  (хосты: /hosts)", shown, port)
    return srv


# ══════════════════════════════ sensors / report ══════════════════════════════

def cmd_sensors(args) -> int:
    db = open_db(args.db)
    hosts = load_hosts(db)
    db.close()
    if not hosts:
        print("Хостов нет — добавь их на странице /hosts")
    for h in hosts:
        print(f"\n{h['label']} [{h['name']}]  {h['url']}" + ("" if h["enabled"] else "  (выключен)"))
        modes = {k: sensor_mode(h[k.lower()]) for k in KINDS}
        try:
            tree = fetch_lhm(h["url"], h["username"], h["password"])
        except LHMError as ex:
            print(f"  ✗ {ex}")
            continue
        picked = pick_sensors(tree, modes)
        watts = channel_watts(picked)
        mark = {i[0]: k for k, items in picked.items() for i in items}
        for k in KINDS:
            if modes[k] == "off":
                print(f"  {k}: нет (считается 0)")
            elif picked[k]:
                print(f"  {k} = {'—' if watts[k] is None else num(watts[k], 1) + ' Вт'}")
            else:
                print(f"  ⚠ {k}: сенсор не найден — выбери вручную на /hosts")
        for s in power_sensors(tree):
            val = "—" if s["value"] is None else num(s["value"], 1) + " Вт"
            tag = f"  ← {mark[s['id']]}" if s["id"] in mark else ""
            print(f"    {s['id']:<34} {s['text'][:22]:<22} {val:>10}  {s['hw']}{tag}")
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
    labels = [c[:11] for c in rep["labels"]]
    print(f"\n  {month_title(y, m)}: кВт·ч по датчикам LHM\n")
    if rep["secs"] <= 0:
        print("  Нет данных за этот месяц.\n")
    else:
        print(f"  {'День':<6}" + "".join(f"{c:>12}" for c in labels)
              + f"{'Всего':>9}{'Ср. Вт':>8}{'Часов':>7}")
        top = max(sum(d["wh"]) for d in rep["days"]) or 1.0
        for d in rep["days"]:
            if d["future"]:
                continue
            lab = f"{d['day']:02d} {WEEKDAYS[d['date'].weekday()]}"
            if not d["has"]:
                print(f"  {lab:<6}" + f"{'—':>12}" * len(labels) + f"{'—':>9}")
                continue
            tot = sum(d["wh"])
            print(f"  {lab:<6}" + "".join(f"{num(w / 1000, 3):>12}" for w in d["wh"])
                  + f"{num(tot / 1000, 3):>9}{num(avg_w(tot, d['secs']), 0):>8}"
                  f"{num(d['secs'] / 3600, 1):>7}  {text_bar(tot / top, 20)}")
        tot = rep["total_wh"]
        print(f"  {'Итого':<6}" + "".join(f"{num(w / 1000, 2):>12}" for w in rep["wh"])
              + f"{num(tot / 1000, 2):>9}{num(avg_w(tot, rep['secs']), 0):>8}{num(rep['secs'] / 3600, 0):>7}\n")
        print(f"  ≈ от розетки: {num(rep['wall_kwh'], 1)} кВт·ч ≈ {num(rep['wall_kwh'] * TARIFF, 0)} {CURRENCY}"
              f"   (+ прочее железо и КПД БП каждого хоста, {num(TARIFF, 2)} {CURRENCY}/кВт·ч)")
        p = rep["projection"]
        if p:
            print(f"  Прогноз на весь месяц: ≈ {num(p['total_kwh'], 1)} кВт·ч по датчикам, "
                  f"≈ {num(p['wall_kwh'], 1)} кВт·ч ≈ {num(p['wall_kwh'] * TARIFF, 0)} {CURRENCY} от розетки")
        print()
    mseries, months = months_report(db)
    if months:
        print(f"  {'Месяц':<15}" + "".join(f"{s['label'][:11]:>12}" for s in mseries)
              + f"{'Всего':>9}{'≈ розетка':>11}{'≈ ' + CURRENCY:>9}{'Часов':>7}")
        for mo in months[:24]:
            yy, mm = map(int, mo["ym"].split("-"))
            print(f"  {month_title(yy, mm):<15}" + "".join(f"{num(w / 1000, 2):>12}" for w in mo["wh"])
                  + f"{num(mo['total_wh'] / 1000, 2):>9}{num(mo['wall_kwh'], 1):>11}"
                  f"{num(mo['wall_kwh'] * TARIFF, 0):>9}{num(mo['secs'] / 3600, 0):>7}")
        print()
    db.close()
    return 0


def main(argv=None) -> int:
    for stream in (sys.stdout, sys.stderr):
        if stream is not None and hasattr(stream, "reconfigure"):
            try:
                stream.reconfigure(errors="replace")
            except (OSError, ValueError):
                pass
    common = argparse.ArgumentParser(add_help=False)
    common.add_argument("--db", default=str(DB_PATH), help="файл базы SQLite")
    p = argparse.ArgumentParser(prog="powermeter", description=__doc__,
                                formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = p.add_subparsers(dest="cmd", metavar="команда")
    sub.add_parser("sensors", parents=[common], help="проверить связь с хостами, показать power-сенсоры")
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
