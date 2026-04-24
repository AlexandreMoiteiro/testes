# app_navlog_ifr_low_portugal.py
# ---------------------------------------------------------------
# NAVLOG Streamlit — VFR + IFR Low Portugal
# - Carrega pontos IFR oficiais da eAIP Portugal ENR 4.4 (cache local)
# - Carrega rotas RNAV/ATS da eAIP Portugal ENR 3.3 (cache local)
# - Mantém CSVs locais: aeródromos/helis, localidades e VOR já existente
# - Permite rotas DCT, airways, fixes por radial/DME, tracking inbound/outbound
# - Gera navlog, mapa Folium, FPL item 15 e PDFs NAVLOG se os templates existirem
# ---------------------------------------------------------------
# Requisitos sugeridos:
# streamlit pandas folium streamlit-folium requests beautifulsoup4 pdfrw reportlab
# ---------------------------------------------------------------

from __future__ import annotations

import datetime as dt
import difflib
import json
import math
import os
import re
import tempfile
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Dict, Iterable, List, Optional, Tuple

import pandas as pd
import requests
import streamlit as st

import folium
from folium.plugins import Fullscreen, MarkerCluster, MeasureControl
from streamlit_folium import st_folium

try:
    from bs4 import BeautifulSoup
except Exception:
    BeautifulSoup = None

try:
    from pdfrw import PdfDict, PdfName, PdfReader, PdfWriter
except Exception:
    PdfDict = PdfName = PdfReader = PdfWriter = None

# ===============================================================
# CONFIG
# ===============================================================
st.set_page_config(page_title="NAVLOG IFR Low Portugal", page_icon="✈️", layout="wide", initial_sidebar_state="expanded")

APP_TITLE = "NAVLOG IFR Low Portugal"
APP_VERSION = "2026.04"

EARTH_NM = 3440.065
ROUND_TIME_SEC = 60
ROUND_DIST_NM = 0.5
ROUND_FUEL_L = 1.0
NBSP_THIN = "&#8239;"

CACHE_DIR = Path(".navlog_cache")
CACHE_DIR.mkdir(exist_ok=True)

AIP_ENR44_URL = "https://ais.nav.pt/wp-content/uploads/AIS_Files/eAIP_Current/eAIP_Online/eAIP/html/eAIP/LP-ENR-4.4-en-PT.html?amdt=show"
AIP_ENR33_URL = "https://ais.nav.pt/wp-content/uploads/AIS_Files/eAIP_Current/eAIP_Online/eAIP/html/eAIP/LP-ENR-3.3-en-PT.html?amdt=show"

AD_CSV = "AD-HEL-ULM.csv"
LOC_CSV = "Localidades-Nova-versao-230223.csv"
VOR_CSV = "NAVAIDS_VOR.csv"

TEMPLATE_MAIN = "NAVLOG_FORM.pdf"
TEMPLATE_CONT = "NAVLOG_FORM_1.pdf"

PROFILE_COLORS = {
    "CLIMB": "#f97316",
    "LEVEL": "#7c3aed",
    "DESCENT": "#059669",
    "STOP": "#dc2626",
    "AIRWAY": "#2563eb",
}

AIRCRAFT_PROFILES = {
    "Tecnam P2008": {
        "climb_tas": 70.0,
        "cruise_tas": 90.0,
        "descent_tas": 90.0,
        "fuel_flow_lh": 20.0,
        "regs": ["CS-DHS", "CS-DHT", "CS-DHU", "CS-DHV", "CS-DHW", "CS-ECC", "CS-ECD"],
    },
    "Piper PA-28": {
        "climb_tas": 76.0,
        "cruise_tas": 110.0,
        "descent_tas": 100.0,
        "fuel_flow_lh": 38.0,
        "regs": ["OE-KPD", "OE-KPE", "OE-KPG", "OE-KPP", "OE-KPJ", "OE-KPF"],
    },
}

PORTUGAL_MAINLAND_BBOX = {
    "lat_min": 36.6,
    "lat_max": 42.4,
    "lon_min": -10.6,
    "lon_max": -6.0,
}

# ===============================================================
# CSS / UI HELPERS
# ===============================================================
st.markdown(
    """
<style>
:root{
  --bg:#f8fafc;--card:#ffffff;--line:#e5e7eb;--muted:#64748b;--ink:#0f172a;
  --blue:#2563eb;--green:#059669;--orange:#f97316;--violet:#7c3aed;--red:#dc2626;
}
.block-container{padding-top:1.2rem;padding-bottom:3rem;}
section[data-testid="stSidebar"]{background:#0f172a;color:white;}
section[data-testid="stSidebar"] label, section[data-testid="stSidebar"] p, section[data-testid="stSidebar"] span{color:inherit;}
.hero{border:1px solid var(--line);border-radius:24px;padding:18px 20px;margin-bottom:14px;background:linear-gradient(135deg,#ffffff 0%,#eff6ff 100%);box-shadow:0 10px 30px rgba(15,23,42,.06)}
.hero h1{font-size:28px;margin:0;color:#0f172a;letter-spacing:-.03em}
.hero p{margin:.25rem 0 0 0;color:#475569}
.card{border:1px solid var(--line);border-radius:18px;padding:14px 16px;background:var(--card);box-shadow:0 4px 20px rgba(15,23,42,.04);margin:.45rem 0}
.small{font-size:12px;color:#64748b}
.badge{display:inline-flex;align-items:center;gap:4px;border-radius:999px;padding:3px 9px;font-size:12px;font-weight:800;border:1px solid #cbd5e1;background:#f8fafc;color:#0f172a;margin-right:6px}
.badge.ifr{border-color:#bfdbfe;background:#dbeafe;color:#1d4ed8}.badge.vor{border-color:#fecaca;background:#fee2e2;color:#b91c1c}.badge.ad{border-color:#bbf7d0;background:#dcfce7;color:#166534}.badge.loc{border-color:#e9d5ff;background:#f3e8ff;color:#6b21a8}.badge.airway{border-color:#bfdbfe;background:#eff6ff;color:#1e40af}.badge.warn{border-color:#fed7aa;background:#ffedd5;color:#9a3412}
.kvrow{display:flex;gap:8px;flex-wrap:wrap}.kv{background:#fff;border:1px solid var(--line);border-radius:14px;padding:8px 10px;font-size:13px;box-shadow:0 2px 10px rgba(15,23,42,.03)}
hr{border:none;border-top:1px solid var(--line);margin:1rem 0}.mono{font-family:ui-monospace,SFMono-Regular,Menlo,Monaco,Consolas,monospace}.warnbox{border:1px solid #fed7aa;background:#fff7ed;color:#9a3412;border-radius:14px;padding:10px 12px;font-size:13px}
</style>
""",
    unsafe_allow_html=True,
)


def ui_card(html: str):
    st.markdown(f"<div class='card'>{html}</div>", unsafe_allow_html=True)


def badge(src: str) -> str:
    cls = {
        "IFR": "ifr",
        "VOR": "vor",
        "AD": "ad",
        "LOC": "loc",
        "AIRWAY": "airway",
    }.get(src, "")
    return f"<span class='badge {cls}'>{src}</span>"

# ===============================================================
# MATH / GEO
# ===============================================================

def ens(k: str, v: Any) -> Any:
    return st.session_state.setdefault(k, v)


def round_to_step(x: float, step: float) -> float:
    if step <= 0:
        return x
    return round(x / step) * step


def rt(sec: float) -> int:
    return int(round_to_step(float(sec), ROUND_TIME_SEC))


def rdist(nm: float) -> float:
    return round_to_step(float(nm), ROUND_DIST_NM)


def rfuel(l: float) -> float:
    return round_to_step(float(l), ROUND_FUEL_L)


def mmss(sec: float) -> str:
    total_min = int(round(float(sec) / 60.0))
    return f"{total_min:02d}:00" if total_min < 60 else f"{total_min//60:02d}:{total_min%60:02d}:00"


def pdf_time(sec: float) -> str:
    total_min = int(round(float(sec) / 60.0))
    return f"{total_min:02d}:00" if total_min < 60 else f"{total_min//60:02d}h{total_min%60:02d}"


def wrap360(x: float) -> float:
    return (float(x) % 360.0 + 360.0) % 360.0


def angdiff(a: float, b: float) -> float:
    return (float(a) - float(b) + 180.0) % 360.0 - 180.0


def deg3(v: float) -> str:
    return f"{int(round(v)) % 360:03d}°"


def gc_dist_nm(lat1: float, lon1: float, lat2: float, lon2: float) -> float:
    phi1, lam1, phi2, lam2 = map(math.radians, [lat1, lon1, lat2, lon2])
    dphi, dlam = phi2 - phi1, lam2 - lam1
    a = math.sin(dphi / 2) ** 2 + math.cos(phi1) * math.cos(phi2) * math.sin(dlam / 2) ** 2
    return EARTH_NM * 2 * math.atan2(math.sqrt(a), math.sqrt(1 - a))


def gc_course_tc(lat1: float, lon1: float, lat2: float, lon2: float) -> float:
    phi1, lam1, phi2, lam2 = map(math.radians, [lat1, lon1, lat2, lon2])
    dlam = lam2 - lam1
    y = math.sin(dlam) * math.cos(phi2)
    x = math.cos(phi1) * math.sin(phi2) - math.sin(phi1) * math.cos(phi2) * math.cos(dlam)
    return wrap360(math.degrees(math.atan2(y, x)))


def dest_point(lat: float, lon: float, bearing_deg: float, dist_nm: float) -> Tuple[float, float]:
    theta = math.radians(bearing_deg)
    delta = dist_nm / EARTH_NM
    phi1, lam1 = math.radians(lat), math.radians(lon)
    sin_phi2 = math.sin(phi1) * math.cos(delta) + math.cos(phi1) * math.sin(delta) * math.cos(theta)
    phi2 = math.asin(max(-1.0, min(1.0, sin_phi2)))
    y = math.sin(theta) * math.sin(delta) * math.cos(phi1)
    x = math.cos(delta) - math.sin(phi1) * math.sin(phi2)
    lam2 = lam1 + math.atan2(y, x)
    return math.degrees(phi2), ((math.degrees(lam2) + 540) % 360) - 180


def point_along_gc(lat1: float, lon1: float, lat2: float, lon2: float, dist_from_start_nm: float) -> Tuple[float, float]:
    total = gc_dist_nm(lat1, lon1, lat2, lon2)
    if total <= 0:
        return lat1, lon1
    return dest_point(lat1, lon1, gc_course_tc(lat1, lon1, lat2, lon2), min(total, max(0, dist_from_start_nm)))


def wind_triangle(tc: float, tas: float, wind_from: float, wind_kt: float) -> Tuple[float, float, float]:
    if tas <= 0:
        return 0.0, wrap360(tc), 0.0
    d = math.radians(angdiff(wind_from, tc))
    cross = wind_kt * math.sin(d)
    s = max(-1.0, min(1.0, cross / max(tas, 1e-9)))
    wca = math.degrees(math.asin(s))
    th = wrap360(tc + wca)
    gs = max(0.0, tas * math.cos(math.radians(wca)) - wind_kt * math.cos(d))
    return wca, th, gs


def apply_var(true_heading: float, variation: float, east_is_negative: bool) -> float:
    return wrap360(true_heading - variation if east_is_negative else true_heading + variation)

# ===============================================================
# COORD PARSERS
# ===============================================================

def dms_compact_to_dd(token: str, is_lon: bool = False) -> Optional[float]:
    token = str(token).strip().upper().replace(" ", "")
    m = re.match(r"^(\d+(?:\.\d+)?)([NSEW])$", token)
    if not m:
        return None
    value, hemi = m.groups()
    if is_lon:
        deg = int(value[0:3]); minutes = int(value[3:5]); seconds = float(value[5:] or 0)
    else:
        deg = int(value[0:2]); minutes = int(value[2:4]); seconds = float(value[4:] or 0)
    dd = deg + minutes / 60.0 + seconds / 3600.0
    return -dd if hemi in ("S", "W") else dd


def dms_spaced_to_dd(text: str) -> Optional[float]:
    s = str(text).strip().upper().replace("º", " ").replace("'", " ").replace('"', " ")
    m = re.match(r"^(\d{1,3})\s+(\d{1,2})\s+(\d{1,2})(?:\.\d+)?\s*([NSEW])$", s)
    if not m:
        return dms_compact_to_dd(s, is_lon=("E" in s or "W" in s))
    d, mi, se, hemi = m.groups()
    dd = int(d) + int(mi) / 60.0 + int(se) / 3600.0
    return -dd if hemi in ("S", "W") else dd


def icao_latlon(lat: float, lon: float) -> str:
    lat_abs, lon_abs = abs(lat), abs(lon)
    lat_deg, lon_deg = int(lat_abs), int(lon_abs)
    lat_min = int(round((lat_abs - lat_deg) * 60))
    lon_min = int(round((lon_abs - lon_deg) * 60))
    if lat_min == 60:
        lat_deg += 1; lat_min = 0
    if lon_min == 60:
        lon_deg += 1; lon_min = 0
    return f"{lat_deg:02d}{lat_min:02d}{'N' if lat >= 0 else 'S'}{lon_deg:03d}{lon_min:02d}{'E' if lon >= 0 else 'W'}"

# ===============================================================
# DATA LOADING: LOCAL CSVs
# ===============================================================

def parse_ad_df(df: pd.DataFrame) -> pd.DataFrame:
    rows = []
    if df.empty:
        return pd.DataFrame(columns=["src", "code", "name", "city", "lat", "lon", "alt", "routes", "remarks"])
    for line in df.iloc[:, 0].dropna().tolist():
        s = str(line).strip()
        if not s or s.startswith(("Ident", "DEP/")):
            continue
        tokens = s.split()
        coord_toks = [t for t in tokens if re.match(r"^\d+(?:\.\d+)?[NSEW]$", t, re.I)]
        if len(coord_toks) >= 2:
            lat_tok, lon_tok = coord_toks[-2], coord_toks[-1]
            lat = dms_compact_to_dd(lat_tok, is_lon=False)
            lon = dms_compact_to_dd(lon_tok, is_lon=True)
            if lat is None or lon is None:
                continue
            ident = tokens[0] if re.match(r"^[A-Z0-9]{4,}$", tokens[0]) else None
            try:
                name = " ".join(tokens[1:tokens.index(coord_toks[0])]).strip()
            except Exception:
                name = " ".join(tokens[1:]).strip()
            try:
                lon_idx = tokens.index(lon_tok)
                city = " ".join(tokens[lon_idx + 1:]) or ""
            except Exception:
                city = ""
            rows.append({"src": "AD", "code": ident or name, "name": name or ident or "AD", "city": city, "lat": lat, "lon": lon, "alt": 0.0, "routes": "", "remarks": city})
    return pd.DataFrame(rows).dropna(subset=["lat", "lon"])


def parse_loc_df(df: pd.DataFrame) -> pd.DataFrame:
    rows = []
    if df.empty:
        return pd.DataFrame(columns=["src", "code", "name", "sector", "lat", "lon", "alt", "routes", "remarks"])
    for line in df.iloc[:, 0].dropna().tolist():
        s = str(line).strip()
        if not s or "Total de registos" in s:
            continue
        tokens = s.split()
        coord_toks = [t for t in tokens if re.match(r"^\d{6,7}(?:\.\d+)?[NSEW]$", t, re.I)]
        if len(coord_toks) >= 2:
            lat_tok, lon_tok = coord_toks[0], coord_toks[1]
            lat = dms_compact_to_dd(lat_tok, is_lon=False)
            lon = dms_compact_to_dd(lon_tok, is_lon=True)
            if lat is None or lon is None:
                continue
            try:
                lon_idx = tokens.index(lon_tok)
                code = tokens[lon_idx + 1] if lon_idx + 1 < len(tokens) else None
                sector = " ".join(tokens[lon_idx + 2:]) if lon_idx + 2 < len(tokens) else ""
                name = " ".join(tokens[:tokens.index(lat_tok)]).strip()
            except Exception:
                continue
            rows.append({"src": "LOC", "code": code or name, "name": name, "sector": sector, "lat": lat, "lon": lon, "alt": 0.0, "routes": "", "remarks": sector})
    return pd.DataFrame(rows).dropna(subset=["lat", "lon"])


def load_csv_safely(path: str) -> pd.DataFrame:
    if not os.path.exists(path):
        return pd.DataFrame()
    for enc in ("utf-8", "latin1", "cp1252"):
        try:
            return pd.read_csv(path, encoding=enc)
        except Exception:
            pass
    return pd.DataFrame()


def load_vor_db(path: str) -> pd.DataFrame:
    if os.path.exists(path):
        try:
            df = pd.read_csv(path)
            df = df.rename(columns={c: c.lower().strip() for c in df.columns})
            # Aceita formatos frequentes: ident/freq_mhz/lat/lon ou id/frequency/latitude/longitude
            ren = {}
            for c in df.columns:
                if c in ("id", "code"):
                    ren[c] = "ident"
                elif c in ("frequency", "freq", "freqmhz"):
                    ren[c] = "freq_mhz"
                elif c in ("latitude",):
                    ren[c] = "lat"
                elif c in ("longitude",):
                    ren[c] = "lon"
            df = df.rename(columns=ren)
            required = {"ident", "lat", "lon"}
            if not required.issubset(df.columns):
                raise ValueError("missing columns")
            df["ident"] = df["ident"].astype(str).str.upper().str.strip()
            if "freq_mhz" not in df.columns:
                df["freq_mhz"] = None
            if "name" not in df.columns:
                df["name"] = df["ident"]
            df["lat"] = pd.to_numeric(df["lat"], errors="coerce")
            df["lon"] = pd.to_numeric(df["lon"], errors="coerce")
            df["freq_mhz"] = pd.to_numeric(df["freq_mhz"], errors="coerce")
            return df.dropna(subset=["ident", "lat", "lon"])[["ident", "name", "freq_mhz", "lat", "lon"]].reset_index(drop=True)
        except Exception:
            pass
    # Fallback pequeno; a tua app deve usar o CSV NAVAIDS_VOR.csv.
    fallback = [
        ("CAS", "Cascais DVOR/DME", 114.30, 38.7483, -9.3619),
        ("ESP", "Espichel DVOR/DME", 112.50, 38.4242, -9.1856),
        ("VFA", "Faro DVOR/DME", 112.80, 37.0136, -7.9750),
        ("FTM", "Fátima DVOR/DME", 113.50, 39.6656, -8.4928),
        ("LIS", "Lisboa DVOR/DME", 114.80, 38.8878, -9.1628),
        ("NSA", "Nisa DVOR/DME", 115.50, 39.5647, -7.9147),
        ("PRT", "Porto DVOR/DME", 114.10, 41.2731, -8.6878),
        ("SGR", "Sagres VOR/DME", 113.90, 37.0839, -8.94639),
        ("SRA", "Sintra VORTAC", 112.10, 38.829201, -9.34),
    ]
    return pd.DataFrame(fallback, columns=["ident", "name", "freq_mhz", "lat", "lon"])

# ===============================================================
# DATA LOADING: OFFICIAL eAIP IFR POINTS + AIRWAYS
# ===============================================================

def fetch_text_with_cache(url: str, cache_name: str, ttl_hours: int = 24, force_refresh: bool = False) -> Tuple[str, str]:
    cache_path = CACHE_DIR / cache_name
    meta_path = CACHE_DIR / f"{cache_name}.meta.json"
    now = dt.datetime.utcnow()

    if cache_path.exists() and not force_refresh:
        try:
            meta = json.loads(meta_path.read_text(encoding="utf-8")) if meta_path.exists() else {}
            ts = dt.datetime.fromisoformat(meta.get("downloaded_utc", "1970-01-01T00:00:00"))
            if (now - ts).total_seconds() < ttl_hours * 3600:
                return cache_path.read_text(encoding="utf-8", errors="ignore"), f"cache {ts.strftime('%Y-%m-%d %H:%MZ')}"
        except Exception:
            return cache_path.read_text(encoding="utf-8", errors="ignore"), "cache"

    try:
        headers = {"User-Agent": f"{APP_TITLE}/{APP_VERSION}"}
        r = requests.get(url, timeout=20, headers=headers)
        r.raise_for_status()
        text = r.text
        cache_path.write_text(text, encoding="utf-8")
        meta_path.write_text(json.dumps({"url": url, "downloaded_utc": now.isoformat(timespec="seconds")}, indent=2), encoding="utf-8")
        return text, f"NAV Portugal {now.strftime('%Y-%m-%d %H:%MZ')}"
    except Exception as e:
        if cache_path.exists():
            return cache_path.read_text(encoding="utf-8", errors="ignore"), f"cache offline ({e})"
        raise RuntimeError(f"Não consegui descarregar {url}: {e}")


def html_to_text(html: str) -> str:
    html = html.replace("\xa0", " ").replace("&nbsp;", " ")
    if BeautifulSoup:
        soup = BeautifulSoup(html, "html.parser")
        text = soup.get_text("\n")
    else:
        text = re.sub(r"<br\s*/?>", "\n", html, flags=re.I)
        text = re.sub(r"<[^>]+>", "\n", text)
    text = text.replace("\xa0", " ")
    text = re.sub(r"[ \t]+", " ", text)
    text = re.sub(r"\n{2,}", "\n", text)
    return text.strip()


ROUTE_TOKEN_RE = re.compile(r"\b(?:U?[A-Z]{1,3}|[A-Z])\d{1,3}\b")


def parse_enr44_points(html: str) -> pd.DataFrame:
    text = html_to_text(html)
    # Entries in ENR 4.4 usually appear as:
    # ABALO\n321952N\n0180749W\nZ220 (RNAV 5), ...\nFRA ...
    entry_re = re.compile(
        r"(?m)^\s*([A-Z]{5})\s*\n\s*(\d{6}[NS])\s*\n\s*(\d{7}[EW])\s*\n(?P<body>.*?)(?=^\s*[A-Z]{5}\s*\n\s*\d{6}[NS]\s*\n\s*\d{7}[EW]\s*\n|\Z)",
        re.S,
    )
    rows = []
    for m in entry_re.finditer(text):
        code, lat_tok, lon_tok, body = m.group(1), m.group(2), m.group(3), m.group("body")
        lat = dms_compact_to_dd(lat_tok, is_lon=False)
        lon = dms_compact_to_dd(lon_tok, is_lon=True)
        if lat is None or lon is None:
            continue
        clean_body = re.sub(r"\n+", " | ", body).strip(" |")
        tokens = sorted(set(t for t in ROUTE_TOKEN_RE.findall(clean_body) if t not in {"NIL"}))
        rows.append({
            "src": "IFR",
            "code": code,
            "name": code,
            "lat": lat,
            "lon": lon,
            "alt": 0.0,
            "routes": ", ".join(tokens),
            "remarks": clean_body,
            "city": "",
            "sector": "",
        })
    return pd.DataFrame(rows).drop_duplicates(subset=["code", "lat", "lon"]).reset_index(drop=True)


def sanitize_route_point_name(raw: str) -> str:
    raw = re.sub(r"^[▲△∆Δ\s]+", "", str(raw)).strip()
    # VOR/NDB entries in ENR 3.3 often appear as "ESPICHEL DVOR/DME (ESP)".
    m = re.search(r"\(([A-Z0-9]{2,5})\)", raw)
    if m:
        return m.group(1).upper()
    m2 = re.search(r"([A-Z]{5})$", raw)
    if m2:
        return m2.group(1).upper()
    raw = re.sub(r"[^A-Z0-9]", "", raw.upper())
    return raw[-5:] if len(raw) > 5 else raw


def parse_enr33_airways(html: str) -> Tuple[Dict[str, List[Dict[str, Any]]], pd.DataFrame]:
    text = html_to_text(html)
    # route designators are lines like UM744, UN873, Y105, Z222, W13, H141...
    header_re = re.compile(r"(?m)^\s*((?:U?[A-Z]{1,3}|[A-Z])\d{1,3})\s*$")
    headers = [(m.group(1), m.start(), m.end()) for m in header_re.finditer(text)]
    airways: Dict[str, List[Dict[str, Any]]] = {}
    segments = []

    # Point lines can be adjacent to coords: ▲ROSAL380117N 0070605W
    point_re = re.compile(r"(?:[▲△∆Δ]\s*)?([A-Z][A-Z0-9 /().\-]{1,80}?)\s*(\d{6}[NS])\s+(\d{7}[EW])")

    for idx, (route, _start, end) in enumerate(headers):
        block_end = headers[idx + 1][1] if idx + 1 < len(headers) else len(text)
        block = text[end:block_end]
        pts: List[Dict[str, Any]] = []
        seen = set()
        for pm in point_re.finditer(block):
            raw, lat_tok, lon_tok = pm.group(1), pm.group(2), pm.group(3)
            name = sanitize_route_point_name(raw)
            if not name:
                continue
            lat = dms_compact_to_dd(lat_tok, is_lon=False)
            lon = dms_compact_to_dd(lon_tok, is_lon=True)
            if lat is None or lon is None:
                continue
            key = (name, round(lat, 5), round(lon, 5))
            if key in seen:
                continue
            seen.add(key)
            pts.append({"name": name, "code": name, "lat": lat, "lon": lon, "route": route})
        if len(pts) >= 2:
            # Some pages repeat a header line and create tiny false route blocks; keep only useful ones.
            if route not in airways or len(pts) > len(airways[route]):
                airways[route] = pts

    for route, pts in airways.items():
        for i in range(len(pts) - 1):
            a, b = pts[i], pts[i + 1]
            segments.append({
                "route": route,
                "seq": i + 1,
                "from": a["name"],
                "to": b["name"],
                "lat1": a["lat"],
                "lon1": a["lon"],
                "lat2": b["lat"],
                "lon2": b["lon"],
                "dist_nm": rdist(gc_dist_nm(a["lat"], a["lon"], b["lat"], b["lon"])),
                "tc": int(round(gc_course_tc(a["lat"], a["lon"], b["lat"], b["lon"]))) % 360,
            })
    seg_df = pd.DataFrame(segments)
    return airways, seg_df


@st.cache_data(show_spinner=False, ttl=3600)
def load_official_ifr_data(force_refresh: bool = False) -> Tuple[pd.DataFrame, Dict[str, List[Dict[str, Any]]], pd.DataFrame, Dict[str, str]]:
    meta = {}
    html44, src44 = fetch_text_with_cache(AIP_ENR44_URL, "LP_ENR_4_4_en_PT.html", force_refresh=force_refresh)
    html33, src33 = fetch_text_with_cache(AIP_ENR33_URL, "LP_ENR_3_3_en_PT.html", force_refresh=force_refresh)
    points = parse_enr44_points(html44)
    airways, segs = parse_enr33_airways(html33)
    meta["points_source"] = src44
    meta["airways_source"] = src33
    return points, airways, segs, meta

# ===============================================================
# VOR / IFR HELPERS
# ===============================================================

def in_mainland_bbox(lat: float, lon: float) -> bool:
    b = PORTUGAL_MAINLAND_BBOX
    return b["lat_min"] <= lat <= b["lat_max"] and b["lon_min"] <= lon <= b["lon_max"]


def make_vor_points_df(vor_db: pd.DataFrame) -> pd.DataFrame:
    rows = []
    for _, r in vor_db.iterrows():
        freq = "" if pd.isna(r.get("freq_mhz")) else f"{float(r['freq_mhz']):.2f}"
        rows.append({
            "src": "VOR",
            "code": str(r["ident"]).upper(),
            "name": str(r.get("name") or r["ident"]),
            "lat": float(r["lat"]),
            "lon": float(r["lon"]),
            "alt": 0.0,
            "routes": "",
            "remarks": f"VOR/DME {freq}".strip(),
            "city": "",
            "sector": "",
        })
    return pd.DataFrame(rows)


def get_vor_by_ident(ident: str, vor_db: Optional[pd.DataFrame] = None) -> Optional[Dict[str, Any]]:
    ident = str(ident or "").strip().upper()
    if not ident:
        return None
    df = vor_db if vor_db is not None else st.session_state.get("vor_db", pd.DataFrame())
    if df.empty:
        return None
    hit = df[df["ident"].astype(str).str.upper().str.strip() == ident]
    if hit.empty:
        return None
    r = hit.iloc[0]
    return {"ident": str(r["ident"]).upper(), "name": str(r.get("name") or r["ident"]), "freq_mhz": None if pd.isna(r.get("freq_mhz")) else float(r["freq_mhz"]), "lat": float(r["lat"]), "lon": float(r["lon"])}


def nearest_vor(lat: float, lon: float, vor_db: Optional[pd.DataFrame] = None) -> Optional[Dict[str, Any]]:
    df = vor_db if vor_db is not None else st.session_state.get("vor_db", pd.DataFrame())
    if df.empty:
        return None
    best = None
    best_d = 1e9
    for _, r in df.iterrows():
        d = gc_dist_nm(lat, lon, float(r["lat"]), float(r["lon"]))
        if d < best_d:
            best_d = d
            best = r
    if best is None:
        return None
    radial = gc_course_tc(float(best["lat"]), float(best["lon"]), lat, lon)
    return {"ident": str(best["ident"]).upper(), "name": str(best.get("name") or best["ident"]), "freq_mhz": None if pd.isna(best.get("freq_mhz")) else float(best["freq_mhz"]), "lat": float(best["lat"]), "lon": float(best["lon"]), "dist_nm": best_d, "radial_deg": int(round(radial)) % 360}


def fmt_vor(vor: Optional[Dict[str, Any]]) -> str:
    if not vor:
        return ""
    freq = vor.get("freq_mhz")
    return f"{freq:.2f} {vor['ident']}" if freq else str(vor["ident"])


def fmt_radial_dme(vor: Optional[Dict[str, Any]], lat: float, lon: float) -> str:
    if not vor:
        return ""
    radial = int(round(gc_course_tc(vor["lat"], vor["lon"], lat, lon))) % 360
    dist = int(round(gc_dist_nm(vor["lat"], vor["lon"], lat, lon)))
    return f"R{radial:03d}/D{dist}"


def detect_leg_tracking(A: Dict[str, Any], B: Dict[str, Any], airway: str = "") -> str:
    if airway:
        return f"AIRWAY {airway}"
    vor_a = get_vor_by_ident(A.get("name", ""))
    vor_b = get_vor_by_ident(B.get("name", ""))
    if vor_a:
        radial = int(round(gc_course_tc(vor_a["lat"], vor_a["lon"], B["lat"], B["lon"]))) % 360
        return f"OUTB R{radial:03d} {vor_a['ident']}"
    if vor_b:
        radial = int(round(gc_course_tc(vor_b["lat"], vor_b["lon"], A["lat"], A["lon"]))) % 360
        return f"INB R{radial:03d} {vor_b['ident']}"
    return "DCT"

# ===============================================================
# SESSION STATE
# ===============================================================

def init_state():
    ens("aircraft_type", "Piper PA-28")
    for k, v in AIRCRAFT_PROFILES[st.session_state.aircraft_type].items():
        if k != "regs":
            ens(f"ac_{k}", v)
    ens("wind_from", 0)
    ens("wind_kt", 0)
    ens("use_global_wind", True)
    ens("mag_var", 1.0)
    ens("mag_is_e", False)
    ens("roc_fpm", 600)
    ens("rod_fpm", 500)
    ens("start_clock", "")
    ens("start_efob", 180.0)
    ens("ck_default", 2)
    ens("wps", [])
    ens("wp_next_id", 1)
    ens("route_nodes", [])
    ens("legs", [])
    ens("map_center", (39.6, -8.2))
    ens("map_zoom", 7)
    ens("map_base", "OpenTopoMap")
    ens("text_scale", 1.0)
    ens("show_ifr_points", False)
    ens("show_airways", True)
    ens("show_doghouses", True)
    ens("show_ticks", True)
    ens("scope", "Continente")
    ens("route_name", "")
    ens("saved_routes", {})


def ensure_wp_ids():
    for w in st.session_state.wps:
        if "id" not in w:
            w["id"] = st.session_state.wp_next_id
            st.session_state.wp_next_id += 1
        w.setdefault("stop_min", 0.0)
        w.setdefault("via", "")
        w.setdefault("nav_vor", "AUTO")
        w.setdefault("kind", "USER")


def make_wp(name: str, lat: float, lon: float, alt: float, *, kind: str = "USER", via: str = "", nav_vor: str = "AUTO") -> Dict[str, Any]:
    wp = {
        "id": st.session_state.wp_next_id,
        "name": str(name).strip().upper() if re.fullmatch(r"[A-Za-z0-9]{2,6}", str(name).strip()) else str(name).strip(),
        "lat": float(lat),
        "lon": float(lon),
        "alt": float(alt),
        "wind_from": int(st.session_state.wind_from),
        "wind_kt": int(st.session_state.wind_kt),
        "stop_min": 0.0,
        "via": str(via or "").upper(),
        "nav_vor": str(nav_vor or "AUTO").upper(),
        "kind": kind,
    }
    st.session_state.wp_next_id += 1
    return wp


def add_wp(name: str, lat: float, lon: float, alt: float, *, kind: str = "USER", via: str = "", nav_vor: str = "AUTO"):
    st.session_state.wps.append(make_wp(name, lat, lon, alt, kind=kind, via=via, nav_vor=nav_vor))


def clear_computed():
    st.session_state.route_nodes = []
    st.session_state.legs = []

# ===============================================================
# ROUTE BUILDING
# ===============================================================

def ac_value(key: str) -> float:
    return float(st.session_state.get(f"ac_{key}", AIRCRAFT_PROFILES[st.session_state.aircraft_type][key]))


def build_route_nodes(user_wps: List[Dict[str, Any]]) -> List[Dict[str, Any]]:
    nodes: List[Dict[str, Any]] = []
    if len(user_wps) < 2:
        return nodes
    climb_tas = ac_value("climb_tas")
    descent_tas = ac_value("descent_tas")
    wf = st.session_state.wind_from
    wk = st.session_state.wind_kt

    for i in range(len(user_wps) - 1):
        A, B = user_wps[i], user_wps[i + 1]
        nodes.append({**A})
        tc = gc_course_tc(A["lat"], A["lon"], B["lat"], B["lon"])
        dist = gc_dist_nm(A["lat"], A["lon"], B["lat"], B["lon"])
        wf_used = wf if st.session_state.use_global_wind else A.get("wind_from", wf)
        wk_used = wk if st.session_state.use_global_wind else A.get("wind_kt", wk)
        _, _, gs_cl = wind_triangle(tc, climb_tas, wf_used, wk_used)
        _, _, gs_de = wind_triangle(tc, descent_tas, wf_used, wk_used)
        if B["alt"] > A["alt"]:
            dh = B["alt"] - A["alt"]
            t_need_min = dh / max(float(st.session_state.roc_fpm), 1.0)
            d_need = gs_cl * t_need_min / 60.0
            if 0.05 < d_need < dist - 0.05:
                lat, lon = point_along_gc(A["lat"], A["lon"], B["lat"], B["lon"], d_need)
                nodes.append(make_wp(f"TOC L{i+1}", lat, lon, B["alt"], kind="TOC", via=B.get("via", "")))
        elif B["alt"] < A["alt"]:
            dh = A["alt"] - B["alt"]
            t_need_min = dh / max(float(st.session_state.rod_fpm), 1.0)
            d_need = gs_de * t_need_min / 60.0
            if 0.05 < d_need < dist - 0.05:
                lat, lon = point_along_gc(A["lat"], A["lon"], B["lat"], B["lon"], max(0, dist - d_need))
                nodes.append(make_wp(f"TOD L{i+1}", lat, lon, A["alt"], kind="TOD", via=B.get("via", "")))
    nodes.append({**user_wps[-1]})
    return nodes


def base_time_from_ui() -> Optional[dt.datetime]:
    txt = str(st.session_state.start_clock or "").strip()
    if not txt:
        return None
    try:
        h, m = map(int, txt.split(":"))
        return dt.datetime.combine(dt.date.today(), dt.time(h, m)) + dt.timedelta(minutes=15)
    except Exception:
        return None


def build_legs_from_nodes(nodes: List[Dict[str, Any]]) -> List[Dict[str, Any]]:
    legs: List[Dict[str, Any]] = []
    if len(nodes) < 2:
        return legs
    climb_tas = ac_value("climb_tas")
    cruise_tas = ac_value("cruise_tas")
    descent_tas = ac_value("descent_tas")
    fuel_flow = ac_value("fuel_flow_lh")
    base_time = base_time_from_ui()
    t_cursor = 0
    carry_efob = max(0.0, float(st.session_state.start_efob) - 5.0)  # taxi/start allowance

    for i in range(len(nodes) - 1):
        A, B = nodes[i], nodes[i + 1]
        tc = gc_course_tc(A["lat"], A["lon"], B["lat"], B["lon"])
        dist = rdist(gc_dist_nm(A["lat"], A["lon"], B["lat"], B["lon"]))
        wf_used = int(st.session_state.wind_from if st.session_state.use_global_wind else A.get("wind_from", st.session_state.wind_from))
        wk_used = int(st.session_state.wind_kt if st.session_state.use_global_wind else A.get("wind_kt", st.session_state.wind_kt))

        if abs(B["alt"] - A["alt"]) < 1e-6:
            profile, tas = "LEVEL", cruise_tas
        elif B["alt"] > A["alt"]:
            profile, tas = "CLIMB", climb_tas
        else:
            profile, tas = "DESCENT", descent_tas
        _, th, gs = wind_triangle(tc, tas, wf_used, wk_used)
        mh = apply_var(th, float(st.session_state.mag_var), bool(st.session_state.mag_is_e))
        time_sec = rt((dist / gs) * 3600.0) if gs > 0 and dist > 0 else 0
        burn = rfuel(fuel_flow * time_sec / 3600.0)
        efob_start = carry_efob
        efob_end = max(0.0, rfuel(efob_start - burn))

        clk_start = (base_time + dt.timedelta(seconds=t_cursor)).strftime("%H:%M") if base_time else f"T+{mmss(t_cursor)}"
        clk_end = (base_time + dt.timedelta(seconds=t_cursor + time_sec)).strftime("%H:%M") if base_time else f"T+{mmss(t_cursor + time_sec)}"

        cps = []
        ck = int(st.session_state.ck_default)
        if ck > 0 and gs > 0 and time_sec > 0:
            k = 1
            while k * ck * 60 <= time_sec:
                t = k * ck * 60
                cps.append({"t": t, "min": int(t / 60), "nm": rdist(gs * t / 3600.0), "eto": (base_time + dt.timedelta(seconds=t_cursor + t)).strftime("%H:%M") if base_time else ""})
                k += 1

        airway = str(B.get("via", "") or "")
        tracking = detect_leg_tracking(A, B, airway=airway if A.get("kind") not in ("TOC", "TOD") and B.get("kind") not in ("TOC", "TOD") else "")

        legs.append({
            "i": len(legs) + 1,
            "A": A,
            "B": B,
            "profile": profile,
            "TC": tc,
            "TH": th,
            "MH": mh,
            "TAS": tas,
            "GS": gs,
            "Dist": dist,
            "time_sec": time_sec,
            "burn": burn,
            "efob_start": efob_start,
            "efob_end": efob_end,
            "clock_start": clk_start,
            "clock_end": clk_end,
            "cps": cps,
            "wind_from": wf_used,
            "wind_kt": wk_used,
            "airway": airway,
            "tracking": tracking,
        })
        t_cursor += time_sec
        carry_efob = efob_end

        # STOP time at arrival WP B, but do not duplicate if B is TOC/TOD synthetic
        stop_min = float(B.get("stop_min", 0.0) or 0.0)
        if stop_min > 0 and B.get("kind") not in ("TOC", "TOD"):
            stop_sec = rt(stop_min * 60.0)
            stop_burn = rfuel(fuel_flow * stop_sec / 3600.0)
            start2 = carry_efob
            end2 = max(0.0, rfuel(start2 - stop_burn))
            clk_start2 = (base_time + dt.timedelta(seconds=t_cursor)).strftime("%H:%M") if base_time else f"T+{mmss(t_cursor)}"
            clk_end2 = (base_time + dt.timedelta(seconds=t_cursor + stop_sec)).strftime("%H:%M") if base_time else f"T+{mmss(t_cursor + stop_sec)}"
            legs.append({
                "i": len(legs) + 1,
                "A": B,
                "B": B,
                "profile": "STOP",
                "TC": 0.0,
                "TH": 0.0,
                "MH": 0.0,
                "TAS": 0.0,
                "GS": 0.0,
                "Dist": 0.0,
                "time_sec": stop_sec,
                "burn": stop_burn,
                "efob_start": start2,
                "efob_end": end2,
                "clock_start": clk_start2,
                "clock_end": clk_end2,
                "cps": [],
                "wind_from": wf_used,
                "wind_kt": wk_used,
                "airway": "",
                "tracking": "STOP",
            })
            t_cursor += stop_sec
            carry_efob = end2
    return legs


def regenerate_route():
    ensure_wp_ids()
    st.session_state.route_nodes = build_route_nodes(st.session_state.wps)
    st.session_state.legs = build_legs_from_nodes(st.session_state.route_nodes)

# ===============================================================
# SEARCH / ROUTE UTILS
# ===============================================================

def score_point(row: pd.Series, query: str, last_wp: Optional[Dict[str, Any]]) -> float:
    q = query.lower().strip()
    code = str(row.get("code") or "").lower()
    name = str(row.get("name") or "").lower()
    routes = str(row.get("routes") or "").lower()
    blob = f"{code} {name} {routes} {row.get('remarks','')}".lower()
    starts = 2.5 if code.startswith(q) or name.startswith(q) else 0.0
    exact = 4.0 if q == code or q == name else 0.0
    contains = 1.0 if q in blob else 0.0
    sim = difflib.SequenceMatcher(None, q, f"{code} {name}").ratio()
    near = 0.0
    if last_wp is not None and not pd.isna(row.get("lat")) and not pd.isna(row.get("lon")):
        near = 1.0 / (1.0 + gc_dist_nm(last_wp["lat"], last_wp["lon"], float(row["lat"]), float(row["lon"])))
    src_bonus = {"IFR": 0.6, "VOR": 0.5, "AD": 0.3}.get(row.get("src"), 0.0)
    return exact + starts + contains + sim + src_bonus + near * 0.35


def search_points(db: pd.DataFrame, query: str, limit: int = 30) -> pd.DataFrame:
    q = str(query or "").strip()
    if not q or db.empty:
        return db.head(0)
    ql = q.lower()
    mask = db.apply(lambda r: ql in " ".join(str(v).lower() for v in r.values), axis=1)
    df = db[mask].copy()
    if df.empty:
        # fuzzy fallback on code/name only
        df = db.copy()
    last = st.session_state.wps[-1] if st.session_state.wps else None
    df["__score"] = df.apply(lambda r: score_point(r, q, last), axis=1)
    return df.sort_values("__score", ascending=False).head(limit)


def get_point_by_code(db: pd.DataFrame, code: str) -> Optional[pd.Series]:
    c = str(code).strip().upper()
    if not c:
        return None
    exact = db[db["code"].astype(str).str.upper() == c]
    if not exact.empty:
        # Prefer IFR/VOR/AD in that order for aviation codes.
        priority = {"IFR": 0, "VOR": 1, "AD": 2, "LOC": 3}
        exact = exact.assign(__p=exact["src"].map(priority).fillna(9)).sort_values("__p")
        return exact.iloc[0]
    res = search_points(db, c, limit=1)
    return None if res.empty else res.iloc[0]


def add_terms_to_route(db: pd.DataFrame, terms: str, alt_ft: float) -> Tuple[List[str], List[str]]:
    added, misses = [], []
    for term in [t for t in re.split(r"[\s,;]+", terms.strip()) if t]:
        r = get_point_by_code(db, term)
        if r is None:
            misses.append(term)
            continue
        add_wp(r.get("code") or r.get("name"), float(r["lat"]), float(r["lon"]), alt_ft, kind=str(r.get("src") or "USER"))
        added.append(str(r.get("code") or r.get("name")))
    clear_computed()
    return added, misses


def route_waypoint_label(w: Dict[str, Any], idx: int) -> str:
    via = f" via {w.get('via')}" if w.get("via") else ""
    stop = f" STOP {float(w.get('stop_min',0)):.0f}m" if float(w.get("stop_min", 0) or 0) > 0 else ""
    return f"{idx+1:02d} — {w['name']} {int(round(w['alt']))} ft{via}{stop}"


def add_airway_between(airways: Dict[str, List[Dict[str, Any]]], route: str, entry: str, exit_: str, alt_ft: float, db: pd.DataFrame) -> Tuple[bool, str]:
    route = str(route).strip().upper()
    entry = str(entry).strip().upper()
    exit_ = str(exit_).strip().upper()
    pts = airways.get(route)
    if not pts:
        return False, f"Airway {route} não encontrada."
    names = [p["name"].upper() for p in pts]
    if entry not in names or exit_ not in names:
        return False, f"{entry} ou {exit_} não pertencem à {route}."
    i, j = names.index(entry), names.index(exit_)
    seq = pts[i:j + 1] if i <= j else list(reversed(pts[j:i + 1]))
    if len(seq) < 2:
        return False, "Sequência vazia."
    # Avoid duplicate first point if already current last WP.
    for k, p in enumerate(seq):
        if st.session_state.wps and k == 0:
            last = st.session_state.wps[-1]
            if str(last["name"]).upper() == p["name"].upper() or gc_dist_nm(last["lat"], last["lon"], p["lat"], p["lon"]) < 0.05:
                continue
        # via belongs to the leg that arrives at this point; first point has no via unless it is not duplicate.
        via = route if k > 0 else ""
        # If point exists in db use the DB coords/name, otherwise use ENR 3.3 coords.
        r = get_point_by_code(db, p["name"])
        if r is not None:
            add_wp(r.get("code") or p["name"], float(r["lat"]), float(r["lon"]), alt_ft, kind=str(r.get("src") or "IFR"), via=via)
        else:
            add_wp(p["name"], float(p["lat"]), float(p["lon"]), alt_ft, kind="IFR", via=via)
    clear_computed()
    return True, f"Adicionada {route}: {seq[0]['name']} → {seq[-1]['name']} ({len(seq)} pontos)."

# ===============================================================
# FPL ITEM 15
# ===============================================================

def is_icao_ad(name: str) -> bool:
    return bool(re.fullmatch(r"[A-Z]{4}", str(name).upper()))


def is_published_token(name: str) -> bool:
    return bool(re.fullmatch(r"[A-Z0-9]{2,5}", str(name).upper()))


def fpl_token(w: Dict[str, Any]) -> str:
    nm = re.sub(r"\s+#\d+$", "", str(w["name"]).upper())
    return nm if is_published_token(nm) else icao_latlon(float(w["lat"]), float(w["lon"]))


def build_fpl_item15(user_wps: List[Dict[str, Any]]) -> str:
    if len(user_wps) < 2:
        return ""
    seq = [w for w in user_wps if w.get("kind") not in ("TOC", "TOD")]
    if seq and is_icao_ad(seq[0]["name"]):
        seq = seq[1:]
    if seq and is_icao_ad(seq[-1]["name"]):
        seq = seq[:-1]
    if not seq:
        return ""

    tokens = [fpl_token(seq[0])]
    i = 1
    while i < len(seq):
        via = str(seq[i].get("via") or "").upper()
        if via:
            j = i
            while j + 1 < len(seq) and str(seq[j + 1].get("via") or "").upper() == via:
                j += 1
            tokens.append(via)
            tokens.append(fpl_token(seq[j]))
            i = j + 1
        else:
            tokens.append("DCT")
            tokens.append(fpl_token(seq[i]))
            i += 1
    return "DCT " + " ".join(tokens) if tokens else ""

# ===============================================================
# MAP RENDERING
# ===============================================================

def html_marker(m: folium.Map, lat: float, lon: float, html: str):
    folium.Marker((lat, lon), icon=folium.DivIcon(html=html, icon_size=(0, 0))).add_to(m)


def doghouse_html(L: Dict[str, Any], scale: float) -> str:
    arrow = {"CLIMB": "⬈", "LEVEL": "⮕", "DESCENT": "⬊", "STOP": "⏸"}.get(L["profile"], "⮕")
    fs1, fs2 = int(15 * scale), int(13 * scale)
    txtshadow = "-2px -2px 0 #fff,2px -2px 0 #fff,-2px 2px 0 #fff,2px 2px 0 #fff,0 0 4px #fff"
    tracking = str(L.get("tracking") or "DCT")
    return f"""
    <div style="transform:translate(-50%,-50%);font-family:ui-monospace,SFMono-Regular,Menlo,Consolas,monospace;white-space:nowrap;line-height:1.25;color:#000;text-shadow:{txtshadow};">
      <div style="font-size:{fs1}px;font-weight:900;">{deg3(L['MH'])}|{deg3(L['TC'])}</div>
      <div style="font-size:{fs2}px;font-weight:800;">{arrow} {int(round(L['A']['alt']))}{NBSP_THIN}ft</div>
      <div style="font-size:{fs2}px;font-weight:800;">{mmss(L['time_sec'])} · {tracking}</div>
    </div>
    """


def wp_label_html(name: str, efob: Optional[float], scale: float) -> str:
    fsn, fsd = int(13 * scale), int(11 * scale)
    txtshadow = "-1px -1px 0 #fff,1px -1px 0 #fff,-1px 1px 0 #fff,1px 1px 0 #fff,0 0 4px #fff"
    detail = "" if efob is None else f"<div style='font-size:{fsd}px;color:#2563eb;font-weight:900;text-shadow:{txtshadow}'>{efob:.0f} L</div>"
    return f"""
    <div style="transform:translate(-50%,-115%);font-family:ui-sans-serif,system-ui;white-space:nowrap;text-align:center;line-height:1.15;">
      <div style="font-size:{fsn}px;font-weight:950;color:#000;text-shadow:{txtshadow};">{name}</div>{detail}
    </div>
    """


def make_base_map() -> folium.Map:
    m = folium.Map(location=list(st.session_state.map_center), zoom_start=st.session_state.map_zoom, tiles=None, control_scale=True, prefer_canvas=True)
    base = st.session_state.map_base
    if base == "OSM Standard":
        folium.TileLayer("https://{s}.tile.openstreetmap.org/{z}/{x}/{y}.png", attr="© OpenStreetMap", name="OSM").add_to(m)
    elif base == "Esri Hillshade":
        folium.TileLayer("https://services.arcgisonline.com/ArcGIS/rest/services/World_Hillshade/MapServer/tile/{z}/{y}/{x}", attr="© Esri", name="Esri Hillshade").add_to(m)
    else:
        folium.TileLayer("https://{s}.tile.opentopomap.org/{z}/{x}/{y}.png", attr="© OpenTopoMap", name="OpenTopoMap").add_to(m)
    Fullscreen(position="topleft", title="Fullscreen", force_separate_button=True).add_to(m)
    MeasureControl(position="topleft", primary_length_unit="nautical_miles").add_to(m)
    return m


def render_route_map(db: pd.DataFrame, seg_df: pd.DataFrame):
    nodes = st.session_state.route_nodes or st.session_state.wps
    legs = st.session_state.legs
    m = make_base_map()

    if st.session_state.show_airways and not seg_df.empty:
        # draw only selected/near airways to avoid map overload
        selected_routes = sorted({str(w.get("via")) for w in st.session_state.wps if w.get("via")})
        if selected_routes:
            for _, s in seg_df[seg_df["route"].isin(selected_routes)].iterrows():
                folium.PolyLine([(s["lat1"], s["lon1"]), (s["lat2"], s["lon2"])], color="#2563eb", weight=2, opacity=0.45, tooltip=f"{s['route']} {s['from']}→{s['to']}").add_to(m)

    if st.session_state.show_ifr_points and not db.empty:
        # MarkerCluster only for IFR/VOR points in selected scope.
        pts = db[db["src"].isin(["IFR", "VOR"])]
        if st.session_state.scope == "Continente":
            pts = pts[pts.apply(lambda r: in_mainland_bbox(float(r["lat"]), float(r["lon"])), axis=1)]
        cl = MarkerCluster(name="IFR/VOR points", disableClusteringAtZoom=9).add_to(m)
        for _, r in pts.head(1500).iterrows():
            col = "#2563eb" if r["src"] == "IFR" else "#dc2626"
            folium.CircleMarker((float(r["lat"]), float(r["lon"])), radius=3, color=col, fill=True, fill_opacity=0.85, tooltip=f"{r['code']} · {r['src']} · {r.get('routes','')}").add_to(cl)

    for L in legs:
        if L["profile"] == "STOP":
            continue
        color = PROFILE_COLORS.get(L["profile"], "#7c3aed")
        if L.get("airway"):
            color = PROFILE_COLORS["AIRWAY"]
        latlngs = [(L["A"]["lat"], L["A"]["lon"]), (L["B"]["lat"], L["B"]["lon"])]
        folium.PolyLine(latlngs, color="#fff", weight=9, opacity=1).add_to(m)
        folium.PolyLine(latlngs, color=color, weight=4, opacity=1, tooltip=f"L{L['i']} {L['A']['name']}→{L['B']['name']} {L.get('tracking','')}").add_to(m)

        if st.session_state.show_ticks and L["cps"]:
            for cp in L["cps"]:
                d = min(L["Dist"], L["GS"] * cp["t"] / 3600.0)
                latm, lonm = point_along_gc(L["A"]["lat"], L["A"]["lon"], L["B"]["lat"], L["B"]["lon"], d)
                llat, llon = dest_point(latm, lonm, L["TC"] - 90, 0.35)
                rlat, rlon = dest_point(latm, lonm, L["TC"] + 90, 0.35)
                folium.PolyLine([(llat, llon), (rlat, rlon)], color="#111", weight=2, opacity=1).add_to(m)

        if st.session_state.show_doghouses and L["Dist"] > 0.2:
            mid = point_along_gc(L["A"]["lat"], L["A"]["lon"], L["B"]["lat"], L["B"]["lon"], L["Dist"] * 0.52)
            side = 1 if (L["i"] % 2) else -1
            anchor = dest_point(mid[0], mid[1], L["TC"] + 90 * side, min(1.8, max(0.8, L["Dist"] / 7)))
            folium.PolyLine([mid, anchor], color="#000", weight=1.5, opacity=0.85).add_to(m)
            html_marker(m, anchor[0], anchor[1], doghouse_html(L, float(st.session_state.text_scale)))

    # waypoint symbols + labels
    efob_by_key = {}
    if legs:
        efob_by_key[(round(legs[0]["A"]["lat"], 6), round(legs[0]["A"]["lon"], 6), legs[0]["A"]["name"])] = legs[0]["efob_start"]
        for L in legs:
            efob_by_key[(round(L["B"]["lat"], 6), round(L["B"]["lon"], 6), L["B"]["name"])] = L["efob_end"]

    for N in nodes:
        kind = str(N.get("kind", "USER"))
        col = "#2563eb" if kind == "IFR" else "#dc2626" if kind == "VOR" else "#111827"
        folium.CircleMarker((N["lat"], N["lon"]), radius=5, color="#fff", weight=3, fill=True, fill_color=col, fill_opacity=1, tooltip=f"{N['name']} {kind}").add_to(m)
        k = (round(N["lat"], 6), round(N["lon"], 6), N["name"])
        html_marker(m, N["lat"], N["lon"], wp_label_html(str(N["name"]), efob_by_key.get(k), float(st.session_state.text_scale)))

    folium.LayerControl(collapsed=False).add_to(m)
    st_folium(m, width=None, height=760, returned_objects=[], key="main_map")

# ===============================================================
# PDF EXPORT
# ===============================================================

def choose_vor_for_point(P: Dict[str, Any]) -> Optional[Dict[str, Any]]:
    nm = str(P.get("name", "")).upper()
    if nm.startswith(("TOC", "TOD")):
        return None
    pref = str(P.get("nav_vor", "AUTO") or "AUTO").upper()
    if pref and pref != "AUTO":
        return get_vor_by_ident(pref)
    if get_vor_by_ident(nm):
        return get_vor_by_ident(nm)
    return nearest_vor(float(P["lat"]), float(P["lon"]))


def fill_pdf(template_path: str, out_path: str, data: Dict[str, Any]) -> Optional[str]:
    if PdfReader is None:
        st.error("pdfrw não está instalado.")
        return None
    if not os.path.exists(template_path):
        st.warning(f"Template PDF não encontrado: {template_path}")
        return None
    pdf = PdfReader(template_path)
    if pdf.Root.AcroForm:
        pdf.Root.AcroForm.update(PdfDict(NeedAppearances=True))
    for page in pdf.pages:
        if not getattr(page, "Annots", None):
            continue
        for a in page.Annots:
            if a.Subtype == PdfName("Widget") and a.T:
                key = str(a.T)[1:-1]
                if key in data:
                    a.update(PdfDict(V=str(data[key])))
                    if "Navaid" in key:
                        a.update(PdfDict(DA="/Helv 5 Tf 0 g"))
    PdfWriter(out_path, trailer=pdf).write()
    return out_path


def fill_leg_line(d: Dict[str, Any], idx: int, L: Dict[str, Any], acc_d: float, acc_t: int, prefix: str = "Leg"):
    P = L["B"]
    d[f"{prefix}{idx:02d}_Waypoint"] = str(P["name"])
    d[f"{prefix}{idx:02d}_Altitude_FL"] = str(int(round(P["alt"])))
    if L["profile"] != "STOP":
        d[f"{prefix}{idx:02d}_True_Course"] = f"{int(round(L['TC'])):03d}"
        d[f"{prefix}{idx:02d}_True_Heading"] = f"{int(round(L['TH'])):03d}"
        d[f"{prefix}{idx:02d}_Magnetic_Heading"] = f"{int(round(L['MH'])):03d}"
        d[f"{prefix}{idx:02d}_True_Airspeed"] = str(int(round(L["TAS"])))
        d[f"{prefix}{idx:02d}_Ground_Speed"] = str(int(round(L["GS"])))
        d[f"{prefix}{idx:02d}_Leg_Distance"] = f"{L['Dist']:.1f}"
    else:
        for fld in ["True_Course", "True_Heading", "Magnetic_Heading", "True_Airspeed", "Ground_Speed"]:
            d[f"{prefix}{idx:02d}_{fld}"] = ""
        d[f"{prefix}{idx:02d}_Leg_Distance"] = "0.0"
    d[f"{prefix}{idx:02d}_Cumulative_Distance"] = f"{acc_d:.1f}"
    d[f"{prefix}{idx:02d}_Leg_ETE"] = pdf_time(L["time_sec"])
    d[f"{prefix}{idx:02d}_Cumulative_ETE"] = pdf_time(acc_t)
    d[f"{prefix}{idx:02d}_ETO"] = ""
    d[f"{prefix}{idx:02d}_Planned_Burnoff"] = f"{L['burn']:.1f}"
    d[f"{prefix}{idx:02d}_Estimated_FOB"] = f"{L['efob_end']:.1f}"
    vor = choose_vor_for_point(P)
    d[f"{prefix}{idx:02d}_Navaid_Identifier"] = fmt_vor(vor)
    d[f"{prefix}{idx:02d}_Navaid_Frequency"] = fmt_radial_dme(vor, P["lat"], P["lon"])


def build_pdf_payload(legs: List[Dict[str, Any]], header: Dict[str, str]) -> Dict[str, Any]:
    total_sec = sum(L["time_sec"] for L in legs)
    total_dist = rdist(sum(L["Dist"] for L in legs))
    total_burn = rfuel(sum(L["burn"] for L in legs))
    climb_time = sum(L["time_sec"] for L in legs if L["profile"] == "CLIMB")
    level_time = sum(L["time_sec"] for L in legs if L["profile"] == "LEVEL")
    desc_time = sum(L["time_sec"] for L in legs if L["profile"] == "DESCENT")
    climb_burn = rfuel(sum(L["burn"] for L in legs if L["profile"] == "CLIMB"))
    d = {
        "CALLSIGN": header.get("callsign", ""),
        "REGISTRATION": header.get("registration", ""),
        "STUDENT": header.get("student", ""),
        "LESSON": header.get("lesson", ""),
        "INSTRUTOR": header.get("instructor", ""),
        "DEPT": header.get("dept_freq", ""),
        "ENROUTE": header.get("enroute_freq", ""),
        "ARRIVAL": header.get("arrival_freq", ""),
        "ETD/ETA": header.get("etd_eta", ""),
        "Departure_Airfield": str(st.session_state.wps[0]["name"]) if st.session_state.wps else "",
        "Arrival_Airfield": str(st.session_state.wps[-1]["name"]) if st.session_state.wps else "",
        "WIND": f"{int(st.session_state.wind_from):03d}/{int(st.session_state.wind_kt)}",
        "MAG_VAR": f"{abs(float(st.session_state.mag_var)):.0f}°{'E' if st.session_state.mag_is_e else 'W'}",
        "FLT TIME": pdf_time(total_sec),
        "CLIMB FUEL": f"{climb_burn:.1f}",
        "OBSERVATIONS": f"Climb {pdf_time(climb_time)} / Cruise {pdf_time(level_time)} / Descent {pdf_time(desc_time)} · IFR/VOR tracking shown in briefing",
        "Leg_Number": str(len(legs)),
        "AIRCRAFT_TYPE": st.session_state.aircraft_type,
    }
    acc_d, acc_t = 0.0, 0
    for i, L in enumerate(legs[:22], start=1):
        acc_d = rdist(acc_d + L["Dist"])
        acc_t += L["time_sec"]
        fill_leg_line(d, i, L, acc_d, acc_t)
    d["Leg23_Leg_Distance"] = f"{total_dist:.1f}"
    d["Leg23_Leg_ETE"] = pdf_time(total_sec)
    d["Leg23_Planned_Burnoff"] = f"{total_burn:.1f}"
    d["Leg23_Estimated_FOB"] = f"{legs[-1]['efob_end']:.1f}"
    return d


def briefing_rows(legs: List[Dict[str, Any]]) -> List[Dict[str, Any]]:
    out = []
    for L in legs:
        B = L["B"]
        vor = choose_vor_for_point(B)
        out.append({
            "Leg": L["i"],
            "From": L["A"]["name"],
            "To": B["name"],
            "Via": L.get("airway") or "DCT",
            "Tracking": L.get("tracking") or "DCT",
            "TC": f"{int(round(L['TC'])):03d}",
            "MH": f"{int(round(L['MH'])):03d}",
            "Dist": f"{L['Dist']:.1f}",
            "ETE": pdf_time(L["time_sec"]),
            "Alt": f"{int(round(L['A']['alt']))}→{int(round(B['alt']))}",
            "VOR": fmt_vor(vor),
            "Radial/DME": fmt_radial_dme(vor, B["lat"], B["lon"]),
            "EFOB": f"{L['efob_end']:.1f}",
            "Profile": L["profile"],
        })
    return out


def generate_briefing_pdf(path: str, rows: List[Dict[str, Any]]) -> Optional[str]:
    try:
        from reportlab.lib.pagesizes import A4, landscape
        from reportlab.lib.units import mm
        from reportlab.pdfgen import canvas
    except Exception:
        return None
    c = canvas.Canvas(path, pagesize=landscape(A4))
    width, height = landscape(A4)
    x0, y = 10 * mm, height - 12 * mm
    c.setFont("Helvetica-Bold", 14)
    c.drawString(x0, y, f"IFR/VOR Leg Briefing — {st.session_state.aircraft_type}")
    y -= 8 * mm
    headers = ["Leg", "From", "To", "Via", "Tracking", "TC", "MH", "Dist", "ETE", "Alt", "VOR", "Radial/DME", "EFOB"]
    widths = [10, 25, 25, 20, 34, 12, 12, 14, 16, 22, 28, 25, 16]
    widths = [w * mm for w in widths]

    def header_row(ypos: float) -> float:
        c.setFont("Helvetica-Bold", 7)
        x = x0
        for h, w in zip(headers, widths):
            c.drawString(x, ypos, h)
            x += w
        c.line(x0, ypos - 2 * mm, x0 + sum(widths), ypos - 2 * mm)
        return ypos - 6 * mm

    y = header_row(y)
    c.setFont("Helvetica", 7)
    for r in rows:
        if y < 12 * mm:
            c.showPage(); y = height - 12 * mm; y = header_row(y); c.setFont("Helvetica", 7)
        x = x0
        for h, w in zip(headers, widths):
            val = str(r.get(h, ""))[:28]
            c.drawString(x, y, val)
            x += w
        y -= 5 * mm
    c.save()
    return path

# ===============================================================
# SAVED ROUTES: LOCAL JSON OR GIST
# ===============================================================

def route_store_path() -> Path:
    return CACHE_DIR / "routes.json"


def load_saved_routes() -> Dict[str, Any]:
    p = route_store_path()
    if p.exists():
        try:
            return json.loads(p.read_text(encoding="utf-8"))
        except Exception:
            return {}
    return {}


def save_saved_routes(routes: Dict[str, Any]):
    route_store_path().write_text(json.dumps(routes, indent=2, ensure_ascii=False), encoding="utf-8")


def serialize_wp(w: Dict[str, Any]) -> Dict[str, Any]:
    return {k: w.get(k) for k in ["name", "lat", "lon", "alt", "wind_from", "wind_kt", "stop_min", "via", "nav_vor", "kind"]}


def deserialize_wp(d: Dict[str, Any]) -> Dict[str, Any]:
    wp = make_wp(d.get("name", "WP"), float(d.get("lat", 0)), float(d.get("lon", 0)), float(d.get("alt", 0)), kind=d.get("kind", "USER"), via=d.get("via", ""), nav_vor=d.get("nav_vor", "AUTO"))
    wp["wind_from"] = int(d.get("wind_from", st.session_state.wind_from))
    wp["wind_kt"] = int(d.get("wind_kt", st.session_state.wind_kt))
    wp["stop_min"] = float(d.get("stop_min", 0.0))
    return wp

# ===============================================================
# MAIN APP
# ===============================================================
init_state()

st.markdown(
    f"""
<div class='hero'>
  <h1>✈️ {APP_TITLE}</h1>
  <p>Planeamento NAVLOG com pontos IFR da eAIP, airways RNAV, fixes por radial/DME, VOR inbound/outbound, mapa e PDF.</p>
</div>
""",
    unsafe_allow_html=True,
)

# Load data
force_refresh = st.sidebar.button("🔄 Atualizar eAIP/cache", use_container_width=True)
with st.spinner("A carregar dados aeronáuticos..."):
    try:
        ifr_points, airways, airway_segments, ifr_meta = load_official_ifr_data(force_refresh=force_refresh)
    except Exception as e:
        ifr_points = pd.DataFrame(columns=["src", "code", "name", "lat", "lon", "alt", "routes", "remarks", "city", "sector"])
        airways, airway_segments, ifr_meta = {}, pd.DataFrame(), {"points_source": f"erro: {e}", "airways_source": f"erro: {e}"}
        st.error(f"Não consegui carregar ENR 4.4/3.3. Verifica ligação à internet ou cache local. Detalhe: {e}")

ad_df = parse_ad_df(load_csv_safely(AD_CSV))
loc_df = parse_loc_df(load_csv_safely(LOC_CSV))
vor_db = load_vor_db(VOR_CSV)
st.session_state.vor_db = vor_db
vor_df = make_vor_points_df(vor_db)

all_db = pd.concat([ad_df, loc_df, vor_df, ifr_points], ignore_index=True).dropna(subset=["lat", "lon"]).reset_index(drop=True)
if st.session_state.scope == "Continente":
    db = all_db[all_db.apply(lambda r: (r["src"] not in ["IFR"] or in_mainland_bbox(float(r["lat"]), float(r["lon"]))), axis=1)].reset_index(drop=True)
else:
    db = all_db

# Sidebar global settings
with st.sidebar:
    st.markdown(f"### {APP_TITLE}")
    st.caption(f"v{APP_VERSION}")
    st.markdown("---")

    ac_names = list(AIRCRAFT_PROFILES.keys())
    ac_choice = st.selectbox("Aeronave", ac_names, index=ac_names.index(st.session_state.aircraft_type) if st.session_state.aircraft_type in ac_names else 0)
    if ac_choice != st.session_state.aircraft_type:
        st.session_state.aircraft_type = ac_choice
        for k, v in AIRCRAFT_PROFILES[ac_choice].items():
            if k != "regs":
                st.session_state[f"ac_{k}"] = v
        st.rerun()

    with st.expander("Performance", expanded=False):
        st.session_state.ac_climb_tas = st.number_input("TAS subida", 30.0, 300.0, float(st.session_state.ac_climb_tas), step=1.0)
        st.session_state.ac_cruise_tas = st.number_input("TAS cruzeiro", 30.0, 300.0, float(st.session_state.ac_cruise_tas), step=1.0)
        st.session_state.ac_descent_tas = st.number_input("TAS descida", 30.0, 300.0, float(st.session_state.ac_descent_tas), step=1.0)
        st.session_state.ac_fuel_flow_lh = st.number_input("Consumo L/h", 1.0, 200.0, float(st.session_state.ac_fuel_flow_lh), step=0.5)
        st.session_state.roc_fpm = st.number_input("ROC ft/min", 200, 1500, int(st.session_state.roc_fpm), step=50)
        st.session_state.rod_fpm = st.number_input("ROD ft/min", 200, 1500, int(st.session_state.rod_fpm), step=50)

    with st.expander("Vento / tempo / combustível", expanded=True):
        st.session_state.wind_from = st.number_input("Vento FROM °T", 0, 360, int(st.session_state.wind_from), step=5)
        st.session_state.wind_kt = st.number_input("Vento kt", 0, 150, int(st.session_state.wind_kt), step=1)
        st.session_state.use_global_wind = st.toggle("Usar vento global", value=bool(st.session_state.use_global_wind))
        st.session_state.mag_var = st.number_input("Variação magnética °", -30.0, 30.0, float(st.session_state.mag_var), step=0.1)
        st.session_state.mag_is_e = st.toggle("Variação EAST (subtrai)", value=bool(st.session_state.mag_is_e))
        st.session_state.start_clock = st.text_input("Hora off-blocks HH:MM", st.session_state.start_clock)
        st.session_state.start_efob = st.number_input("EFOB inicial L", 0.0, 400.0, float(st.session_state.start_efob), step=1.0)
        st.session_state.ck_default = st.number_input("Checkpoints cada min", 1, 15, int(st.session_state.ck_default), step=1)

    with st.expander("Mapa / dados", expanded=False):
        st.session_state.scope = st.radio("Âmbito IFR", ["Continente", "Todos"], index=0 if st.session_state.scope == "Continente" else 1)
        st.session_state.map_base = st.selectbox("Base", ["OpenTopoMap", "OSM Standard", "Esri Hillshade"], index=["OpenTopoMap", "OSM Standard", "Esri Hillshade"].index(st.session_state.map_base) if st.session_state.map_base in ["OpenTopoMap", "OSM Standard", "Esri Hillshade"] else 0)
        st.session_state.show_ifr_points = st.toggle("Mostrar pontos IFR/VOR", value=bool(st.session_state.show_ifr_points))
        st.session_state.show_airways = st.toggle("Mostrar airways usadas", value=bool(st.session_state.show_airways))
        st.session_state.show_doghouses = st.toggle("Doghouses", value=bool(st.session_state.show_doghouses))
        st.session_state.show_ticks = st.toggle("Riscas CP", value=bool(st.session_state.show_ticks))
        st.session_state.text_scale = st.slider("Escala texto", 0.6, 1.6, float(st.session_state.text_scale), 0.05)

    st.markdown("---")
    if st.button("✅ Gerar / Atualizar rota", type="primary", use_container_width=True):
        regenerate_route()

# Top status metrics
c1, c2, c3, c4, c5 = st.columns(5)
c1.metric("Pontos IFR", len(ifr_points))
c2.metric("Airways", len(airways))
c3.metric("Segmentos", 0 if airway_segments.empty else len(airway_segments))
c4.metric("VOR", len(vor_db))
c5.metric("WPs rota", len(st.session_state.wps))

st.caption(f"ENR 4.4: {ifr_meta.get('points_source','—')} · ENR 3.3: {ifr_meta.get('airways_source','—')}")
st.markdown("<div class='warnbox'>⚠️ Usa sempre eAIP/NOTAM/AIRAC oficial e cartas aprovadas para voo real. Esta app é uma ferramenta de preparação e não substitui briefing operacional, ATC, despacho, minima IFR, performance, combustível legal, alternates e validação IFPS.</div>", unsafe_allow_html=True)

# Tabs
plan_tab, airway_tab, radial_tab, map_tab, navlog_tab, fpl_tab, data_tab = st.tabs([
    "1 · Pontos", "2 · Airways", "3 · Radial/DME", "4 · Mapa", "5 · NAVLOG/PDF", "6 · FPL", "7 · Dados"
])

# ---------------------------------------------------------------
# TAB 1: POINTS / ROUTE EDITOR
# ---------------------------------------------------------------
with plan_tab:
    st.subheader("Adicionar pontos à rota")
    colq, cola, colb = st.columns([3, 1, 1])
    with colq:
        q = st.text_input("Pesquisar AD / VOR / IFR / localidade", placeholder="ex: LPPT, ESP, ROSAL, KELIK...")
    with cola:
        default_alt = st.number_input("Alt p/ novos WPs", 0.0, 45000.0, 3000.0, step=500.0)
    with colb:
        if st.button("Limpar rota", use_container_width=True):
            st.session_state.wps = []
            clear_computed()
            st.rerun()

    if q:
        res = search_points(db, q, limit=25)
        if res.empty:
            st.info("Sem resultados.")
        else:
            for i, r in res.iterrows():
                local = r.get("city") or r.get("sector") or r.get("routes") or ""
                b = badge(str(r.get("src", "")))
                cA, cB = st.columns([0.83, 0.17])
                with cA:
                    st.markdown(
                        f"<div class='card'>{b}<b>{r.get('code','')}</b> — {r.get('name','')}<br><span class='small'>{local}</span><br><span class='small mono'>{float(r['lat']):.5f}, {float(r['lon']):.5f}</span></div>",
                        unsafe_allow_html=True,
                    )
                with cB:
                    if st.button("➕", key=f"add_search_{i}", use_container_width=True):
                        add_wp(r.get("code") or r.get("name"), float(r["lat"]), float(r["lon"]), default_alt, kind=str(r.get("src") or "USER"))
                        clear_computed()
                        st.rerun()

    with st.expander("Adicionar vários por texto", expanded=False):
        terms = st.text_input("Sequência", placeholder="LPPT ESP ROSAL KELIK LPFR")
        if st.button("Adicionar sequência", use_container_width=True):
            added, misses = add_terms_to_route(db, terms, default_alt)
            if added:
                st.success("Adicionados: " + ", ".join(added))
            if misses:
                st.warning("Sem match: " + ", ".join(misses))

    st.markdown("---")
    st.subheader("Rota")
    ensure_wp_ids()
    if not st.session_state.wps:
        st.info("Adiciona pelo menos 2 pontos.")
    else:
        move_up = move_down = delete_id = None
        for idx, w in enumerate(st.session_state.wps):
            title = route_waypoint_label(w, idx)
            with st.expander(title, expanded=False):
                c1, c2, c3, c4 = st.columns([2, 1.2, 1.2, 1])
                with c1:
                    w["name"] = st.text_input("Nome", w["name"], key=f"wp_name_{w['id']}")
                with c2:
                    w["lat"] = st.number_input("Lat", -90.0, 90.0, float(w["lat"]), step=0.0001, format="%.6f", key=f"wp_lat_{w['id']}")
                with c3:
                    w["lon"] = st.number_input("Lon", -180.0, 180.0, float(w["lon"]), step=0.0001, format="%.6f", key=f"wp_lon_{w['id']}")
                with c4:
                    w["alt"] = st.number_input("Alt ft", 0.0, 45000.0, float(w["alt"]), step=100.0, key=f"wp_alt_{w['id']}")
                c5, c6, c7, c8 = st.columns([1, 1, 1, 1])
                with c5:
                    w["via"] = st.text_input("Via airway", w.get("via", ""), key=f"wp_via_{w['id']}").upper().strip()
                with c6:
                    w["stop_min"] = st.number_input("STOP min", 0.0, 480.0, float(w.get("stop_min", 0)), step=1.0, key=f"wp_stop_{w['id']}")
                with c7:
                    vor_options = ["AUTO"] + sorted(vor_db["ident"].astype(str).str.upper().tolist())
                    cur = str(w.get("nav_vor", "AUTO") or "AUTO").upper()
                    w["nav_vor"] = st.selectbox("VOR fix", vor_options, index=vor_options.index(cur) if cur in vor_options else 0, key=f"wp_navvor_{w['id']}")
                with c8:
                    if not st.session_state.use_global_wind:
                        w["wind_from"] = st.number_input("WF", 0, 360, int(w.get("wind_from", st.session_state.wind_from)), key=f"wp_wf_{w['id']}")
                        w["wind_kt"] = st.number_input("WK", 0, 150, int(w.get("wind_kt", st.session_state.wind_kt)), key=f"wp_wk_{w['id']}")
                b1, b2, b3 = st.columns(3)
                if b1.button("↑", key=f"up_{w['id']}", use_container_width=True):
                    move_up = w["id"]
                if b2.button("↓", key=f"down_{w['id']}", use_container_width=True):
                    move_down = w["id"]
                if b3.button("Remover", key=f"del_{w['id']}", use_container_width=True):
                    delete_id = w["id"]

        if move_up:
            i = next((i for i, x in enumerate(st.session_state.wps) if x["id"] == move_up), None)
            if i is not None and i > 0:
                st.session_state.wps[i - 1], st.session_state.wps[i] = st.session_state.wps[i], st.session_state.wps[i - 1]
            clear_computed(); st.rerun()
        if move_down:
            i = next((i for i, x in enumerate(st.session_state.wps) if x["id"] == move_down), None)
            if i is not None and i < len(st.session_state.wps) - 1:
                st.session_state.wps[i], st.session_state.wps[i + 1] = st.session_state.wps[i + 1], st.session_state.wps[i]
            clear_computed(); st.rerun()
        if delete_id:
            st.session_state.wps = [x for x in st.session_state.wps if x["id"] != delete_id]
            clear_computed(); st.rerun()

    with st.expander("Rotas guardadas localmente", expanded=False):
        if not st.session_state.saved_routes:
            st.session_state.saved_routes = load_saved_routes()
        routes = st.session_state.saved_routes
        c1, c2 = st.columns(2)
        with c1:
            name = st.text_input("Nome da rota")
            if st.button("Guardar rota", use_container_width=True):
                if not name.strip() or not st.session_state.wps:
                    st.warning("Dá um nome e cria uma rota primeiro.")
                else:
                    routes[name.strip()] = [serialize_wp(w) for w in st.session_state.wps]
                    save_saved_routes(routes)
                    st.success("Rota guardada.")
        with c2:
            names = sorted(routes.keys())
            choice = st.selectbox("Carregar", ["—"] + names)
            if st.button("Carregar rota", use_container_width=True) and choice != "—":
                st.session_state.wps = [deserialize_wp(w) for w in routes[choice]]
                clear_computed(); st.rerun()
            if st.button("Apagar rota selecionada", use_container_width=True) and choice != "—":
                routes.pop(choice, None); save_saved_routes(routes); st.rerun()

# ---------------------------------------------------------------
# TAB 2: AIRWAYS
# ---------------------------------------------------------------
with airway_tab:
    st.subheader("Adicionar airway IFR/RNAV")
    if not airways:
        st.warning("Sem airways carregadas do ENR 3.3.")
    else:
        routes = sorted(airways.keys())
        route_choice = st.selectbox("Airway", routes, index=routes.index("UM744") if "UM744" in routes else 0)
        pts = airways.get(route_choice, [])
        names = [p["name"] for p in pts]
        c1, c2, c3 = st.columns([1, 1, 1])
        with c1:
            entry = st.selectbox("Entrada", names, index=0)
        with c2:
            exit_ = st.selectbox("Saída", names, index=max(0, len(names) - 1))
        with c3:
            airway_alt = st.number_input("Alt/FL para os pontos", 0.0, 45000.0, 5000.0, step=500.0)
        if st.button("➕ Adicionar airway à rota", type="primary", use_container_width=True):
            ok, msg = add_airway_between(airways, route_choice, entry, exit_, airway_alt, db)
            st.success(msg) if ok else st.error(msg)
        st.markdown("#### Sequência da airway")
        seg_preview = airway_segments[airway_segments["route"] == route_choice] if not airway_segments.empty else pd.DataFrame()
        if not seg_preview.empty:
            st.dataframe(seg_preview[["seq", "from", "to", "tc", "dist_nm"]], use_container_width=True, hide_index=True)
        else:
            st.write(pd.DataFrame(pts))

# ---------------------------------------------------------------
# TAB 3: RADIAL/DME
# ---------------------------------------------------------------
with radial_tab:
    st.subheader("Criar fix por radial/DME e tracking VOR")
    st.write("Usa isto para construir legs do tipo **outbound radial** ou **inbound to station**. Ex.: adicionar VOR → fix radial/DME dá OUTB; fix radial/DME → VOR dá INB.")
    vor_options = sorted(vor_db["ident"].astype(str).str.upper().tolist())
    c1, c2, c3, c4 = st.columns(4)
    with c1:
        vor_ident = st.selectbox("VOR", vor_options)
    with c2:
        radial = st.number_input("Radial", 0, 359, 180, step=1)
    with c3:
        dme = st.number_input("DME nm", 0.0, 250.0, 15.0, step=1.0)
    with c4:
        alt_fix = st.number_input("Alt ft", 0.0, 45000.0, 3000.0, step=500.0, key="rad_alt")
    v = get_vor_by_ident(vor_ident, vor_db)
    if v:
        lat_fix, lon_fix = dest_point(v["lat"], v["lon"], float(radial), float(dme))
        fix_name = st.text_input("Nome do fix", f"{vor_ident}R{int(radial):03d}D{int(round(dme))}")
        st.caption(f"Fix: {lat_fix:.6f}, {lon_fix:.6f} · {fmt_vor(v)} {fmt_radial_dme(v, lat_fix, lon_fix)}")
        b1, b2, b3 = st.columns(3)
        if b1.button("➕ Só fix", use_container_width=True):
            add_wp(fix_name, lat_fix, lon_fix, alt_fix, kind="RADIAL", nav_vor=vor_ident)
            clear_computed(); st.rerun()
        if b2.button("➕ VOR → fix (outbound)", use_container_width=True):
            add_wp(vor_ident, v["lat"], v["lon"], alt_fix, kind="VOR", nav_vor=vor_ident)
            add_wp(fix_name, lat_fix, lon_fix, alt_fix, kind="RADIAL", nav_vor=vor_ident)
            clear_computed(); st.rerun()
        if b3.button("➕ fix → VOR (inbound)", use_container_width=True):
            add_wp(fix_name, lat_fix, lon_fix, alt_fix, kind="RADIAL", nav_vor=vor_ident)
            add_wp(vor_ident, v["lat"], v["lon"], alt_fix, kind="VOR", nav_vor=vor_ident)
            clear_computed(); st.rerun()

# ---------------------------------------------------------------
# TAB 4: MAP
# ---------------------------------------------------------------
with map_tab:
    st.subheader("Mapa")
    if len(st.session_state.wps) >= 2 and not st.session_state.legs:
        st.info("Carrega em **Gerar / Atualizar rota** na sidebar para calcular NAVLOG completo.")
    if st.session_state.wps:
        render_route_map(db, airway_segments)
    else:
        st.info("Adiciona pontos à rota para ver o mapa.")
        m = make_base_map()
        st_folium(m, width=None, height=620, returned_objects=[], key="empty_map")

# ---------------------------------------------------------------
# TAB 5: NAVLOG / PDF
# ---------------------------------------------------------------
with navlog_tab:
    st.subheader("NAVLOG")
    if len(st.session_state.wps) >= 2 and not st.session_state.legs:
        if st.button("Gerar agora", type="primary"):
            regenerate_route(); st.rerun()
    if st.session_state.legs:
        total_sec = sum(L["time_sec"] for L in st.session_state.legs)
        total_burn = rfuel(sum(L["burn"] for L in st.session_state.legs))
        total_dist = rdist(sum(L["Dist"] for L in st.session_state.legs))
        efob_final = st.session_state.legs[-1]["efob_end"]
        st.markdown(
            "<div class='kvrow'>"
            f"<div class='kv'>⏱️ ETE <b>{pdf_time(total_sec)}</b></div>"
            f"<div class='kv'>🧭 Dist <b>{total_dist:.1f} NM</b></div>"
            f"<div class='kv'>⛽ Burn <b>{total_burn:.1f} L</b></div>"
            f"<div class='kv'>🧯 EFOB final <b>{efob_final:.1f} L</b></div>"
            f"<div class='kv'>🛩️ {st.session_state.aircraft_type}</div>"
            f"<div class='kv'>Legs <b>{len(st.session_state.legs)}</b></div>"
            "</div>",
            unsafe_allow_html=True,
        )
        rows = briefing_rows(st.session_state.legs)
        st.dataframe(pd.DataFrame(rows), use_container_width=True, hide_index=True)

        st.markdown("---")
        st.subheader("Cabeçalho PDF")
        regs = AIRCRAFT_PROFILES[st.session_state.aircraft_type]["regs"]
        p1, p2, p3, p4, p5 = st.columns(5)
        callsign = p1.text_input("Callsign", "RVP")
        registration = p2.selectbox("Registration", regs)
        student = p3.text_input("Student", "AMOIT")
        lesson = p4.text_input("Lesson", "")
        instructor = p5.text_input("Instructor", "")
        p6, p7, p8, p9 = st.columns(4)
        etd = p6.text_input("ETD", "")
        eta = p7.text_input("ETA", "")
        dept_freq = p8.text_input("FREQ DEP", "119.805")
        enroute_freq = p9.text_input("FREQ ENR", "123.755")
        arrival_freq = st.text_input("FREQ ARR", "131.675")

        if st.button("Gerar PDF(s)", type="primary", use_container_width=True):
            header = {
                "callsign": callsign,
                "registration": registration,
                "student": student,
                "lesson": lesson,
                "instructor": instructor,
                "dept_freq": dept_freq,
                "enroute_freq": enroute_freq,
                "arrival_freq": arrival_freq,
                "etd_eta": f"{etd}/{eta}" if etd else "",
            }
            payload = build_pdf_payload(st.session_state.legs, header)
            out_main = fill_pdf(TEMPLATE_MAIN, "NAVLOG_FILLED.pdf", payload)
            if out_main and os.path.exists(out_main):
                st.download_button("⬇️ NAVLOG principal", open(out_main, "rb").read(), file_name="NAVLOG_FILLED.pdf", use_container_width=True)
            if len(st.session_state.legs) > 22:
                st.info("A rota tem mais de 22 legs. O template de continuação pode precisar de mapeamento adicional conforme os campos do teu PDF.")
            rows = briefing_rows(st.session_state.legs)
            brief_path = generate_briefing_pdf("NAVLOG_IFR_LEG_BRIEFING.pdf", rows)
            if brief_path:
                st.download_button("⬇️ Briefing IFR/VOR por leg", open(brief_path, "rb").read(), file_name="NAVLOG_IFR_LEG_BRIEFING.pdf", use_container_width=True)
            csv = pd.DataFrame(rows).to_csv(index=False).encode("utf-8")
            st.download_button("⬇️ Briefing CSV", csv, file_name="NAVLOG_IFR_LEG_BRIEFING.csv", use_container_width=True)
    else:
        st.info("Ainda não há legs calculadas.")

# ---------------------------------------------------------------
# TAB 6: FPL
# ---------------------------------------------------------------
with fpl_tab:
    st.subheader("Flight Plan — Item 15")
    route_str = build_fpl_item15(st.session_state.wps)
    if route_str:
        st.code(route_str.upper())
        st.caption("A app tenta compactar segmentos com a mesma airway. Valida sempre contra IFPS/RAD, AIP e disponibilidade operacional.")
    else:
        st.info("Cria uma rota para gerar o Item 15.")
    with st.expander("Explicação da lógica", expanded=False):
        st.write("Aeródromos ICAO no início/fim são removidos do Item 15. Pontos publicados usam o código; pontos custom/radial usam LAT/LON ICAO. Segmentos com `via` preenchido entram como airway; os restantes entram como DCT.")

# ---------------------------------------------------------------
# TAB 7: DATA
# ---------------------------------------------------------------
with data_tab:
    st.subheader("Dados carregados")
    st.write("Fontes e contagens")
    st.json({
        "ENR 4.4 points": ifr_meta.get("points_source"),
        "ENR 3.3 airways": ifr_meta.get("airways_source"),
        "IFR points parsed": int(len(ifr_points)),
        "Airways parsed": int(len(airways)),
        "Airway segments parsed": int(0 if airway_segments.empty else len(airway_segments)),
        "AD CSV rows": int(len(ad_df)),
        "LOC CSV rows": int(len(loc_df)),
        "VOR rows": int(len(vor_db)),
    })
    dtab1, dtab2, dtab3 = st.tabs(["Pontos IFR", "Airways", "DB total"])
    with dtab1:
        st.dataframe(ifr_points, use_container_width=True, hide_index=True)
        st.download_button("⬇️ IFR points CSV", ifr_points.to_csv(index=False).encode("utf-8"), "ifr_points_enr44.csv", use_container_width=True)
    with dtab2:
        if not airway_segments.empty:
            st.dataframe(airway_segments, use_container_width=True, hide_index=True)
            st.download_button("⬇️ Airways segments CSV", airway_segments.to_csv(index=False).encode("utf-8"), "ifr_airways_enr33_segments.csv", use_container_width=True)
        else:
            st.info("Sem segmentos.")
    with dtab3:
        st.dataframe(db, use_container_width=True, hide_index=True)
        st.download_button("⬇️ DB total CSV", db.to_csv(index=False).encode("utf-8"), "navlog_db_total.csv", use_container_width=True)
