# app.py
# ---------------------------------------------------------------
# NAVLOG VFR/IFR Portugal Continental — Streamlit
# ---------------------------------------------------------------
# Objetivo:
# - VFR: aeródromos/heliportos/ULM + localidades + pontos por clique no mapa
# - IFR: pontos ENR 4.4 via CSV local + airways ENR 3.3 via CSV local
# - VOR: fixes por radial/distância e tracking inbound/outbound por radial
# - Navlog: cálculo TT/TH/MH/GS/ETE/Fuel/EFOB, TOC/TOD/STOP
# - PDF: preenche NAVLOG_FORM.pdf e NAVLOG_FORM_1.pdf se existirem no repo
#
# A app NÃO vai buscar o AIP em runtime. Para atualizar dados IFR, corre:
#   python tools/update_ifr_data.py
# e faz commit dos CSV gerados.
# ---------------------------------------------------------------

from __future__ import annotations

import base64
import datetime as dt
import difflib
import io
import json
import math
import os
import re
import zipfile
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Dict, Iterable, List, Optional, Tuple

import folium
import pandas as pd
import streamlit as st
from folium.plugins import Fullscreen, MarkerCluster, MeasureControl
from pdfrw import PdfDict, PdfName, PdfReader, PdfWriter
from streamlit_folium import st_folium

try:
    import requests
except Exception:  # pragma: no cover
    requests = None

# ===============================================================
# CONFIG
# ===============================================================
APP_TITLE = "NAVLOG Portugal — VFR + IFR Low"
ROOT = Path(__file__).parent

CSV_AD = ROOT / "AD-HEL-ULM.csv"
CSV_LOC = ROOT / "Localidades-Nova-versao-230223.csv"
CSV_VOR = ROOT / "NAVAIDS_VOR.csv"
CSV_IFR_POINTS = ROOT / "IFR_POINTS.csv"
CSV_IFR_AIRWAYS = ROOT / "IFR_AIRWAYS.csv"

TEMPLATE_MAIN = ROOT / "NAVLOG_FORM.pdf"
TEMPLATE_CONT = ROOT / "NAVLOG_FORM_1.pdf"

OUTPUT_MAIN = ROOT / "NAVLOG_FILLED.pdf"
OUTPUT_CONT = ROOT / "NAVLOG_FILLED_1.pdf"
OUTPUT_BRIEFING = ROOT / "NAVLOG_LEGS_BRIEFING.pdf"

EARTH_NM = 3440.065
PT_CENTER = (39.55, -8.10)
PT_BOUNDS = [(36.70, -9.85), (42.25, -6.00)]  # Portugal continental + margem FIR terrestre

PROFILE_COLORS = {
    "CLIMB": "#f97316",
    "LEVEL": "#7c3aed",
    "DESCENT": "#059669",
    "STOP": "#dc2626",
}

AIRCRAFT_PROFILES: Dict[str, Dict[str, float]] = {
    "Tecnam P2008": {
        "climb_tas": 70.0,
        "cruise_tas": 90.0,
        "descent_tas": 90.0,
        "fuel_flow_lh": 20.0,
        "taxi_fuel_l": 3.0,
    },
    "Piper PA-28": {
        "climb_tas": 76.0,
        "cruise_tas": 110.0,
        "descent_tas": 100.0,
        "fuel_flow_lh": 38.0,
        "taxi_fuel_l": 5.0,
    },
}

REG_OPTIONS_TECNAM = ["CS-DHS", "CS-DHT", "CS-DHU", "CS-DHV", "CS-DHW", "CS-ECC", "CS-ECD"]
REG_OPTIONS_PIPER = ["OE-KPD", "OE-KPE", "OE-KPG", "OE-KPP", "OE-KPJ", "OE-KPF"]

# Rounding policy
ROUND_TIME_SEC = 60
ROUND_DIST_NM = 0.5
ROUND_FUEL_L = 1.0

# Small built-in fallback, used only if IFR_POINTS.csv is absent.
# Keep the real file in the repo for operational use.
IFR_POINTS_FALLBACK = """code,name,lat,lon,routes,remarks,src
ATECA,ATECA,38.658333,-8.622500,"A975 UN975 UZ218","FRA I",IFR
MAGUM,MAGUM,39.167500,-8.392500,"G52 W7 UN745 UN870 UP600 UZ7 UZ218","FRA I",IFR
ALAGU,ALAGU,38.088611,-7.614444,"W13 A44 Z222 UL14 UM744 UZ222","FRA I AD LPFR",IFR
BIRBA,BIRBA,39.105556,-7.511944,"A975 UN873 UN975 UZ15 UZ222","FRA I",IFR
ROSAL,ROSAL,38.021389,-7.101389,"A44 Z227 UM744 UZ227","MADRID LISBOA FIR BDRY",IFR
EXONA,EXONA,38.904444,-8.016667,"Z227 UZ227","Holding Pattern",IFR
ELVAR,ELVAR,39.219444,-7.223333,"A975 Z219 UL14 UN975 UN979 UZ219","below FL245",IFR
MOMAS,MOMAS,39.319167,-8.016667,"Z219 UN870 UZ219","FRA I",IFR
BUSEN,BUSEN,38.545000,-10.000000,"A44 UM744 UN870 UZ21 UZ22","FRA I",IFR
LIGRA,LIGRA,38.000000,-9.590833,"G52 UN872","FRA I AD LPPT",IFR
NAKOS,NAKOS,38.000000,-9.334444,"W8 UZ4","FRA I AD LPPT",IFR
EVURA,EVURA,38.665000,-7.918611,"R72 UN726 UN873","FRA I D LPFR",IFR
DIGAL,DIGAL,39.740833,-7.989722,"UN726 UZ218 UZ222","FRA I",IFR
CANAR,CANAR,41.385833,-7.469722,"A43 G41 UL155 UN872","FRA I",IFR
BELDU,BELDU,41.358611,-7.777222,"A43 UL155","FRA I D LPPR",IFR
MAPOR,MAPOR,41.614167,-8.058333,"G414","FRA I",IFR
MANIK,MANIK,40.691944,-8.616111,"A5 UP600","FRA I D LPPR",IFR
LULAS,LULAS,40.899722,-9.281111,"","FRA I",IFR
ABETO,ABETO,40.429722,-8.056389,"UN726 UN872","FRA I",IFR
ABLEG,ABLEG,40.722778,-8.431111,"","FRA I A LPPR",IFR
ABRAT,ABRAT,39.821667,-7.654167,"UN745","FRA I",IFR
ABRIL,ABRIL,40.396111,-8.580278,"","NIL",IFR
ABUPI,ABUPI,41.751111,-7.236111,"UN872","Madrid/Lisboa",IFR
ADINO,ADINO,40.017778,-6.373611,"","LECM FIR",IFR
ADORO,ADORO,41.483056,-6.280000,"A43 UL155","FIR BDRY",IFR
ADSAD,ADSAD,38.478056,-8.981111,"","Lisboa TMA Holding",IFR
AGADO,AGADO,41.872778,-8.926667,"UN729","Madrid/Lisboa FIR BDRY",IFR
AIREZ,AIREZ,39.454722,-8.666111,"","FRA I",IFR
AKABO,AKABO,41.321944,-8.700833,"","FRA I",IFR
AKULU,AKULU,40.984167,-8.611944,"","Holding Pattern",IFR
ALAMA,ALAMA,39.223333,-8.550000,"","FRA I",IFR
ARDID,ARDID,41.173333,-6.282222,"","LECM FIR",IFR
ARNIT,ARNIT,38.990833,-8.959444,"","FRA I",IFR
ASMOV,ASMOV,40.969444,-9.346944,"","FRA I AD LPPR",IFR
ASPOR,ASPOR,41.815278,-8.081111,"UT3","FRA E A LPPR",IFR
BABEX,BABEX,41.040278,-7.083889,"UN976 UZ15 UZ218","FRA I",IFR
BABOV,BABOV,39.876389,-6.873611,"","FRA I",IFR
BALNO,BALNO,41.730556,-6.981667,"","Madrid Lisboa FIR",IFR
BARDI,BARDI,40.583611,-6.302500,"","FIR BDRY",IFR
BAROK,BAROK,35.800000,-10.006667,"W8 UN873 UZ4 UZ218","FIR BDRY",IFR
BATAX,BATAX,41.700556,-6.621944,"UZ218","FIR BDRY",IFR
BEVOP,BEVOP,37.599167,-9.387500,"","FRA ID LPPT",IFR
BOMKO,BOMKO,38.953611,-9.043611,"","Lisboa TMA",IFR
CASLU,CASLU,38.540000,-9.810000,"","Holding Pattern",IFR
CEFOX,CEFOX,38.551667,-9.402778,"","NIL",IFR
COCUN,COCUN,39.026667,-9.068611,"","FRA I",IFR
DEKKI,DEKKI,38.963056,-8.695556,"","Holding Pattern",IFR
DEKUS,DEKUS,38.015278,-10.000000,"UN745","NIL",IFR
DIKMO,DIKMO,40.723333,-7.885833,"","NIL",IFR
DIKUV,DIKUV,36.181667,-12.750556,"","Madeira contingency",IFR
DIRMA,DIRMA,40.851667,-9.500833,"B47 G414 UM191 UZ23 UZ25 UZ28 UZ29","FRA I",IFR
DIVUT,DIVUT,41.028611,-8.325833,"","Holding Pattern",IFR
DUZOP,DUZOP,37.669722,-8.651667,"","FRA ID LPPT LPCS",IFR
EKLID,EKLID,39.142500,-9.263611,"","Holding Pattern",IFR
EKMAR,EKMAR,38.557500,-9.521389,"Y207","Holding Pattern",IFR
EKPER,EKPER,38.423056,-10.000000,"","FRA I",IFR
ELDUK,ELDUK,37.811111,-7.940556,"R72 UN726","FRA I",IFR
ELGIX,ELGIX,41.521111,-7.673056,"","FRA I A LPPR",IFR
ELNUB,ELNUB,39.082222,-10.671111,"","FRA ID LPPT",IFR
EMPAD,EMPAD,38.895556,-9.055278,"","FRA I",IFR
ERNIL,ERNIL,38.498056,-9.529722,"","FRA I",IFR
ERTIS,ERTIS,37.416667,-7.614722,"Z222 UZ222 Y105","FRA I",IFR
ERUKU,ERUKU,38.792500,-8.983056,"","Lisboa TMA",IFR
ESEBI,ESEBI,39.403056,-8.666389,"","FRA IA LPPT",IFR
ESUTI,ESUTI,37.860000,-10.430278,"","Holding Pattern",IFR
ETAKA,ETAKA,41.789167,-7.730000,"","FIR BDRY",IFR
EVPAP,EVPAP,39.152500,-8.793889,"","NIL",IFR
FADEF,FADEF,39.195556,-8.913056,"","NIL",IFR
FERFE,FERFE,39.058611,-10.005833,"","FRA I",IFR
FUSSI,FUSSI,39.210833,-8.904722,"","",IFR
GAIOS,GAIOS,38.275556,-8.543056,"A44","FRA I",IFR
"""

IFR_AIRWAYS_FALLBACK = """airway,seq,point,lat,lon,route_type,lower,upper,mea,remarks
UZ218,1,BABEX,41.040278,-7.083889,RNAV5,,,,fallback
UZ218,2,ATECA,38.658333,-8.622500,RNAV5,,,,fallback
UZ218,3,MAGUM,39.167500,-8.392500,RNAV5,,,,fallback
UZ222,1,ERTIS,37.416667,-7.614722,RNAV5,,,,fallback
UZ222,2,ALAGU,38.088611,-7.614444,RNAV5,,,,fallback
UZ222,3,BIRBA,39.105556,-7.511944,RNAV5,,,,fallback
UZ222,4,DIGAL,39.740833,-7.989722,RNAV5,,,,fallback
Z227,1,ROSAL,38.021389,-7.101389,RNAV5,,,,fallback
Z227,2,EXONA,38.904444,-8.016667,RNAV5,,,,fallback
UN870,1,BUSEN,38.545000,-10.000000,RNAV5,,,,fallback
UN870,2,MAGUM,39.167500,-8.392500,RNAV5,,,,fallback
UN870,3,MOMAS,39.319167,-8.016667,RNAV5,,,,fallback
UN872,1,LIGRA,38.000000,-9.590833,RNAV5,,,,fallback
UN872,2,ABETO,40.429722,-8.056389,RNAV5,,,,fallback
UN872,3,CANAR,41.385833,-7.469722,RNAV5,,,,fallback
A44,1,ROSAL,38.021389,-7.101389,ATS,,,,fallback
A44,2,ALAGU,38.088611,-7.614444,ATS,,,,fallback
A44,3,GAIOS,38.275556,-8.543056,ATS,,,,fallback
W13,1,MARIM,37.416667,-7.841111,ATS,,,,fallback
W13,2,ALAGU,38.088611,-7.614444,ATS,,,,fallback
"""

# ===============================================================
# STREAMLIT SETUP + STYLE
# ===============================================================
st.set_page_config(page_title="NAVLOG IFR/VFR", page_icon="🧭", layout="wide", initial_sidebar_state="collapsed")

st.markdown(
    """
<style>
:root{
  --bg:#f8fafc; --card:#ffffff; --line:#e2e8f0; --muted:#64748b;
  --text:#0f172a; --accent:#2563eb; --good:#059669; --warn:#d97706;
}
.block-container{padding-top:1.2rem;padding-bottom:2rem;max-width:1500px;}
.nav-card{background:var(--card);border:1px solid var(--line);border-radius:18px;padding:14px 16px;margin:10px 0;box-shadow:0 1px 2px rgba(15,23,42,.04)}
.nav-hero{background:linear-gradient(135deg,#eff6ff,#ffffff);border:1px solid #bfdbfe;border-radius:22px;padding:18px 20px;margin-bottom:12px;}
.nav-title{font-size:30px;font-weight:850;letter-spacing:-.03em;color:var(--text);margin:0;}
.nav-sub{font-size:14px;color:var(--muted);margin-top:4px;}
.pill{display:inline-flex;align-items:center;gap:6px;border:1px solid var(--line);background:#fff;border-radius:999px;padding:5px 10px;font-size:12px;font-weight:650;margin:3px 4px 3px 0;color:#0f172a;}
.pill-good{border-color:#bbf7d0;background:#f0fdf4;color:#166534;}
.pill-warn{border-color:#fed7aa;background:#fff7ed;color:#9a3412;}
.small-muted{font-size:12px;color:var(--muted)}
.route-token{font-family:ui-monospace,SFMono-Regular,Menlo,Monaco,Consolas,monospace;background:#f1f5f9;border:1px solid #e2e8f0;border-radius:8px;padding:1px 6px;}
hr{border:none;border-top:1px solid var(--line);margin:1rem 0;}
</style>
""",
    unsafe_allow_html=True,
)

# ===============================================================
# DATACLASSES
# ===============================================================
@dataclass
class Point:
    code: str
    name: str
    lat: float
    lon: float
    alt: float = 0.0
    src: str = "USER"
    routes: str = ""
    remarks: str = ""
    stop_min: float = 0.0
    wind_from: Optional[int] = None
    wind_kt: Optional[int] = None
    vor_pref: str = "AUTO"  # AUTO | FIXED | NONE
    vor_ident: str = ""
    uid: Optional[int] = None

    def to_dict(self) -> Dict[str, Any]:
        return self.__dict__.copy()

    @classmethod
    def from_dict(cls, data: Dict[str, Any]) -> "Point":
        return cls(
            code=str(data.get("code") or data.get("name") or "WP").upper(),
            name=str(data.get("name") or data.get("code") or "WP"),
            lat=float(data.get("lat", 0.0)),
            lon=float(data.get("lon", 0.0)),
            alt=float(data.get("alt", 0.0)),
            src=str(data.get("src", "USER")),
            routes=str(data.get("routes", "")),
            remarks=str(data.get("remarks", "")),
            stop_min=float(data.get("stop_min", 0.0)),
            wind_from=data.get("wind_from"),
            wind_kt=data.get("wind_kt"),
            vor_pref=str(data.get("vor_pref", "AUTO")),
            vor_ident=str(data.get("vor_ident", "")),
            uid=data.get("uid"),
        )

# ===============================================================
# GENERAL HELPERS
# ===============================================================
def ss(key: str, default: Any) -> Any:
    if key not in st.session_state:
        st.session_state[key] = default
    return st.session_state[key]


def clean_code(x: Any) -> str:
    return re.sub(r"[^A-Z0-9]", "", str(x or "").upper().strip())


def round_to_step(x: float, step: float) -> float:
    if step <= 0:
        return x
    return round(float(x) / step) * step


def rt(sec: float) -> int:
    return int(round_to_step(sec, ROUND_TIME_SEC))


def rd(nm: float) -> float:
    return round_to_step(nm, ROUND_DIST_NM)


def rf(L: float) -> float:
    return round_to_step(L, ROUND_FUEL_L)


def mmss(sec: float) -> str:
    minutes = int(round(float(sec) / 60.0))
    return f"{minutes:02d}:00" if minutes < 60 else f"{minutes//60:02d}:{minutes%60:02d}:00"


def pdf_time(sec: float) -> str:
    minutes = int(round(float(sec) / 60.0))
    if minutes >= 60:
        return f"{minutes//60:02d}h{minutes%60:02d}"
    return f"{minutes:02d}:00"


def wrap360(x: float) -> float:
    return (float(x) % 360.0 + 360.0) % 360.0


def angdiff(a: float, b: float) -> float:
    return (float(a) - float(b) + 180.0) % 360.0 - 180.0


def deg3(x: float) -> str:
    return f"{int(round(wrap360(x))):03d}°"


def dms_token_to_dd(token: str, is_lon: bool = False) -> Optional[float]:
    token = str(token).strip().upper()
    m = re.match(r"^(\d+(?:\.\d+)?)([NSEW])$", token)
    if not m:
        return None
    value, hemi = m.groups()
    if is_lon:
        deg_len = 3
    else:
        deg_len = 2
    if len(value) < deg_len + 4:
        return None
    deg = int(value[:deg_len])
    minutes = int(value[deg_len : deg_len + 2])
    seconds = float(value[deg_len + 2 :])
    dd = deg + minutes / 60.0 + seconds / 3600.0
    if hemi in {"S", "W"}:
        dd = -dd
    return dd


def dd_to_icao(lat: float, lon: float) -> str:
    lat_abs = abs(lat)
    lon_abs = abs(lon)
    lat_deg = int(lat_abs)
    lon_deg = int(lon_abs)
    lat_min = int(round((lat_abs - lat_deg) * 60))
    lon_min = int(round((lon_abs - lon_deg) * 60))
    if lat_min == 60:
        lat_deg += 1
        lat_min = 0
    if lon_min == 60:
        lon_deg += 1
        lon_min = 0
    return f"{lat_deg:02d}{lat_min:02d}{'N' if lat >= 0 else 'S'}{lon_deg:03d}{lon_min:02d}{'E' if lon >= 0 else 'W'}"

# ===============================================================
# GEO
# ===============================================================
def gc_dist_nm(lat1: float, lon1: float, lat2: float, lon2: float) -> float:
    phi1, lam1, phi2, lam2 = map(math.radians, [lat1, lon1, lat2, lon2])
    dphi, dlam = phi2 - phi1, lam2 - lam1
    a = math.sin(dphi / 2) ** 2 + math.cos(phi1) * math.cos(phi2) * math.sin(dlam / 2) ** 2
    c = 2 * math.atan2(math.sqrt(a), math.sqrt(1 - a))
    return EARTH_NM * c


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
    x = math.cos(delta) - math.sin(phi1) * sin_phi2
    lam2 = lam1 + math.atan2(y, x)
    return math.degrees(phi2), ((math.degrees(lam2) + 540) % 360) - 180


def point_along_gc(lat1: float, lon1: float, lat2: float, lon2: float, dist_from_start_nm: float) -> Tuple[float, float]:
    total = gc_dist_nm(lat1, lon1, lat2, lon2)
    if total <= 0:
        return lat1, lon1
    return dest_point(lat1, lon1, gc_course_tc(lat1, lon1, lat2, lon2), min(total, max(0.0, dist_from_start_nm)))


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


def apply_mag_var(true_heading: float, mag_var: float, is_east: bool) -> float:
    # East variation is subtracted from true to magnetic; West is added.
    return wrap360(true_heading - mag_var if is_east else true_heading + mag_var)

# ===============================================================
# DATA LOADING
# ===============================================================
@st.cache_data(show_spinner=False)
def load_csv_safe(path: Path, fallback_csv: str = "") -> pd.DataFrame:
    if path.exists():
        try:
            return pd.read_csv(path)
        except Exception as e:
            st.warning(f"Não consegui ler {path.name}: {e}")
    if fallback_csv.strip():
        return pd.read_csv(io.StringIO(fallback_csv.strip()))
    return pd.DataFrame()


def parse_ad_df(df: pd.DataFrame) -> pd.DataFrame:
    rows: List[Dict[str, Any]] = []
    if df.empty:
        return pd.DataFrame(columns=["code", "name", "lat", "lon", "alt", "src", "routes", "remarks"])
    for line in df.iloc[:, 0].dropna().tolist():
        s = str(line).strip()
        if not s or s.startswith(("Ident", "DEP/")):
            continue
        tokens = s.split()
        coord_toks = [t for t in tokens if re.match(r"^\d+(?:\.\d+)?[NSEW]$", t, re.I)]
        if len(coord_toks) >= 2:
            lat_tok, lon_tok = coord_toks[-2], coord_toks[-1]
            lat = dms_token_to_dd(lat_tok, is_lon=False)
            lon = dms_token_to_dd(lon_tok, is_lon=True)
            if lat is None or lon is None:
                continue
            ident = tokens[0] if re.match(r"^[A-Z0-9]{3,5}$", tokens[0]) else ""
            try:
                name = " ".join(tokens[1 : tokens.index(coord_toks[0])]).strip()
            except Exception:
                name = ident or " ".join(tokens[:3])
            rows.append(
                {
                    "code": clean_code(ident or name),
                    "name": name or ident,
                    "lat": lat,
                    "lon": lon,
                    "alt": 0.0,
                    "src": "AD",
                    "routes": "",
                    "remarks": "",
                }
            )
    return pd.DataFrame(rows)


def parse_loc_df(df: pd.DataFrame) -> pd.DataFrame:
    rows: List[Dict[str, Any]] = []
    if df.empty:
        return pd.DataFrame(columns=["code", "name", "lat", "lon", "alt", "src", "routes", "remarks"])
    for line in df.iloc[:, 0].dropna().tolist():
        s = str(line).strip()
        if not s or "Total de registos" in s:
            continue
        tokens = s.split()
        coord_toks = [t for t in tokens if re.match(r"^\d{6,7}(?:\.\d+)?[NSEW]$", t, re.I)]
        if len(coord_toks) >= 2:
            lat_tok, lon_tok = coord_toks[0], coord_toks[1]
            lat = dms_token_to_dd(lat_tok, is_lon=False)
            lon = dms_token_to_dd(lon_tok, is_lon=True)
            if lat is None or lon is None:
                continue
            try:
                lon_idx = tokens.index(lon_tok)
                code = tokens[lon_idx + 1] if lon_idx + 1 < len(tokens) else ""
                name = " ".join(tokens[: tokens.index(lat_tok)]).strip()
            except Exception:
                code = ""
                name = s[:32]
            rows.append(
                {
                    "code": clean_code(code or name),
                    "name": name or code,
                    "lat": lat,
                    "lon": lon,
                    "alt": 0.0,
                    "src": "VFR",
                    "routes": "",
                    "remarks": "",
                }
            )
    return pd.DataFrame(rows)


@st.cache_data(show_spinner=False)
def load_vor(path_str: str) -> pd.DataFrame:
    path = Path(path_str)
    if path.exists():
        try:
            df = pd.read_csv(path)
            df = df.rename(columns={c: c.lower().strip() for c in df.columns})
            rename = {"frequency": "freq_mhz", "freq": "freq_mhz", "latitude": "lat", "longitude": "lon"}
            df = df.rename(columns=rename)
            df["ident"] = df["ident"].astype(str).str.upper().str.strip()
            df["freq_mhz"] = pd.to_numeric(df["freq_mhz"], errors="coerce")
            df["lat"] = pd.to_numeric(df["lat"], errors="coerce")
            df["lon"] = pd.to_numeric(df["lon"], errors="coerce")
            if "name" not in df.columns:
                df["name"] = df["ident"]
            return df.dropna(subset=["ident", "freq_mhz", "lat", "lon"])[["ident", "name", "freq_mhz", "lat", "lon"]]
        except Exception:
            pass
    # Fallback is not intended as operational data; your CSV has priority.
    return pd.DataFrame(
        [
            ("CAS", "Cascais DVOR/DME", 114.30, 38.7483, -9.3619),
            ("ESP", "Espichel DVOR/DME", 112.50, 38.4242, -9.1856),
            ("VFA", "Faro DVOR/DME", 112.80, 37.0136, -7.9750),
            ("FTM", "Fátima DVOR/DME", 113.50, 39.6656, -8.4928),
            ("LIS", "Lisboa DVOR/DME", 114.80, 38.8878, -9.1628),
            ("NSA", "Nisa DVOR/DME", 115.50, 39.5647, -7.9147),
            ("PRT", "Porto DVOR/DME", 114.10, 41.2731, -8.6878),
            ("SGR", "Sagres VOR/DME", 113.90, 37.0839, -8.9464),
            ("SRA", "Sintra VORTAC", 112.10, 38.8292, -9.3400),
        ],
        columns=["ident", "name", "freq_mhz", "lat", "lon"],
    )


@st.cache_data(show_spinner=False)
def load_all_data() -> Tuple[pd.DataFrame, pd.DataFrame, pd.DataFrame]:
    ad = parse_ad_df(load_csv_safe(CSV_AD))
    loc = parse_loc_df(load_csv_safe(CSV_LOC))

    vor = load_vor(str(CSV_VOR)).copy()
    vor_points = pd.DataFrame(
        {
            "code": vor["ident"].astype(str),
            "name": vor["name"].astype(str),
            "lat": vor["lat"],
            "lon": vor["lon"],
            "alt": 0.0,
            "src": "VOR",
            "routes": "",
            "remarks": vor["freq_mhz"].map(lambda x: f"{x:.2f} MHz"),
        }
    )

    ifr = load_csv_safe(CSV_IFR_POINTS, IFR_POINTS_FALLBACK).copy()
    if not ifr.empty:
        ifr = ifr.rename(columns={c: c.lower().strip() for c in ifr.columns})
        if "code" not in ifr.columns and "ident" in ifr.columns:
            ifr["code"] = ifr["ident"]
        for col in ["name", "routes", "remarks", "src"]:
            if col not in ifr.columns:
                ifr[col] = "IFR" if col == "src" else ""
        ifr["code"] = ifr["code"].astype(str).str.upper().str.strip()
        ifr["name"] = ifr["name"].fillna(ifr["code"]).astype(str)
        ifr["lat"] = pd.to_numeric(ifr["lat"], errors="coerce")
        ifr["lon"] = pd.to_numeric(ifr["lon"], errors="coerce")
        if "alt" not in ifr.columns:
            ifr["alt"] = 0.0
        ifr = ifr.dropna(subset=["code", "lat", "lon"])[["code", "name", "lat", "lon", "alt", "src", "routes", "remarks"]]

    points = pd.concat([ad, loc, vor_points, ifr], ignore_index=True)
    if points.empty:
        points = pd.DataFrame(columns=["code", "name", "lat", "lon", "alt", "src", "routes", "remarks"])
    points["code"] = points["code"].map(clean_code)
    points["name"] = points["name"].fillna(points["code"]).astype(str)
    points["lat"] = pd.to_numeric(points["lat"], errors="coerce")
    points["lon"] = pd.to_numeric(points["lon"], errors="coerce")
    points = points.dropna(subset=["lat", "lon"]).drop_duplicates(subset=["code", "lat", "lon", "src"]).reset_index(drop=True)

    airways = load_csv_safe(CSV_IFR_AIRWAYS, IFR_AIRWAYS_FALLBACK).copy()
    if not airways.empty:
        airways = airways.rename(columns={c: c.lower().strip() for c in airways.columns})
        needed = ["airway", "seq", "point", "lat", "lon"]
        for col in needed:
            if col not in airways.columns:
                airways[col] = None
        for col in ["route_type", "lower", "upper", "mea", "remarks"]:
            if col not in airways.columns:
                airways[col] = ""
        airways["airway"] = airways["airway"].astype(str).str.upper().str.strip()
        airways["point"] = airways["point"].astype(str).str.upper().str.strip()
        airways["seq"] = pd.to_numeric(airways["seq"], errors="coerce")
        airways["lat"] = pd.to_numeric(airways["lat"], errors="coerce")
        airways["lon"] = pd.to_numeric(airways["lon"], errors="coerce")
        airways = airways.dropna(subset=["airway", "seq", "point", "lat", "lon"]).sort_values(["airway", "seq"])

    return points, vor, airways

POINTS_DF, VOR_DF, AIRWAYS_DF = load_all_data()

# ===============================================================
# VOR HELPERS
# ===============================================================
def get_vor(ident: str) -> Optional[Dict[str, Any]]:
    ident = clean_code(ident)
    if not ident:
        return None
    hit = VOR_DF[VOR_DF["ident"].astype(str).str.upper() == ident]
    if hit.empty:
        return None
    r = hit.iloc[0]
    return {"ident": r["ident"], "name": r["name"], "freq_mhz": float(r["freq_mhz"]), "lat": float(r["lat"]), "lon": float(r["lon"])}


def nearest_vor(lat: float, lon: float, limit_nm: Optional[float] = None) -> Optional[Dict[str, Any]]:
    if VOR_DF.empty:
        return None
    best: Optional[Dict[str, Any]] = None
    best_d = 1e9
    for _, r in VOR_DF.iterrows():
        d = gc_dist_nm(lat, lon, float(r["lat"]), float(r["lon"]))
        if d < best_d:
            best_d = d
            best = {"ident": r["ident"], "name": r["name"], "freq_mhz": float(r["freq_mhz"]), "lat": float(r["lat"]), "lon": float(r["lon"]), "dist_nm": d}
    if limit_nm is not None and best and best["dist_nm"] > limit_nm:
        return None
    return best


def vor_radial_distance(vor: Dict[str, Any], lat: float, lon: float) -> Tuple[int, float]:
    radial = int(round(gc_course_tc(vor["lat"], vor["lon"], lat, lon))) % 360
    dist = gc_dist_nm(vor["lat"], vor["lon"], lat, lon)
    return radial, dist


def format_vor_id(vor: Optional[Dict[str, Any]]) -> str:
    if not vor:
        return ""
    return f"{vor['freq_mhz']:.2f} {vor['ident']}"


def format_radial_dist(vor: Optional[Dict[str, Any]], lat: float, lon: float) -> str:
    if not vor:
        return ""
    radial, dist = vor_radial_distance(vor, lat, lon)
    return f"R{radial:03d}/D{int(round(dist)):02d}"


def make_vor_fix(token: str) -> Optional[Point]:
    """Accepts CAS/R180/D12, CAS-180-12, CAS180012, CAS R180 D12 (handled upstream only as single token)."""
    t = token.strip().upper().replace(" ", "")
    patterns = [
        r"^([A-Z0-9]{2,4})/R?(\d{1,3})/D?(\d+(?:\.\d+)?)$",
        r"^([A-Z0-9]{2,4})-R?(\d{1,3})-D?(\d+(?:\.\d+)?)$",
        r"^([A-Z0-9]{2,4})R(\d{1,3})D(\d+(?:\.\d+)?)$",
    ]
    for pat in patterns:
        m = re.match(pat, t)
        if not m:
            continue
        vor = get_vor(m.group(1))
        if not vor:
            return None
        radial = float(m.group(2))
        dist = float(m.group(3))
        lat, lon = dest_point(vor["lat"], vor["lon"], radial, dist)
        code = f"{vor['ident']}R{int(radial):03d}D{dist:g}"
        return Point(code=code, name=f"{vor['ident']} R{int(radial):03d} D{dist:g}", lat=lat, lon=lon, src="VORFIX", remarks=format_vor_id(vor), vor_pref="FIXED", vor_ident=vor["ident"])
    return None


def tracking_instruction(A: Dict[str, Any], B: Dict[str, Any], preferred_vor: str = "") -> str:
    # If a point has a fixed VOR, use it; otherwise nearest VOR to the midpoint.
    v = get_vor(preferred_vor) if preferred_vor else None
    if not v:
        mid_lat, mid_lon = point_along_gc(A["lat"], A["lon"], B["lat"], B["lon"], gc_dist_nm(A["lat"], A["lon"], B["lat"], B["lon"]) / 2)
        v = nearest_vor(mid_lat, mid_lon)
    if not v:
        return ""
    radial_a, da = vor_radial_distance(v, A["lat"], A["lon"])
    radial_b, db = vor_radial_distance(v, B["lat"], B["lon"])
    if db < da - 0.3:
        # Going toward station: track reciprocal course inbound on current radial.
        return f"INB {v['ident']} R{radial_a:03d} → station"
    if db > da + 0.3:
        return f"OUTB {v['ident']} R{radial_a:03d}"
    return f"X-RAD {v['ident']} R{radial_a:03d}→R{radial_b:03d}"

# ===============================================================
# ROUTE DATABASE / PARSER
# ===============================================================
def df_row_to_point(r: pd.Series, alt: float = 0.0) -> Point:
    p = Point(
        code=clean_code(r.get("code")),
        name=str(r.get("name") or r.get("code")),
        lat=float(r["lat"]),
        lon=float(r["lon"]),
        alt=float(alt if alt is not None else r.get("alt", 0.0) or 0.0),
        src=str(r.get("src") or "DB"),
        routes=str(r.get("routes") or ""),
        remarks=str(r.get("remarks") or ""),
    )
    if p.src == "VOR":
        p.vor_pref = "FIXED"
        p.vor_ident = p.code
    return p


def search_points(query: str, limit: int = 30, last: Optional[Point] = None) -> pd.DataFrame:
    q = query.strip().lower()
    if not q:
        return POINTS_DF.head(0)
    mask = POINTS_DF.apply(lambda r: q in " ".join(str(v).lower() for v in r.values), axis=1)
    df = POINTS_DF[mask].copy()
    if df.empty:
        return df

    def score(row: pd.Series) -> float:
        code = str(row.get("code") or "").lower()
        name = str(row.get("name") or "").lower()
        sim = difflib.SequenceMatcher(None, q, f"{code} {name}").ratio()
        starts = 1.5 if code.startswith(q) or name.startswith(q) else 0.0
        exact = 3.0 if code == q else 0.0
        src_bonus = {"IFR": 0.35, "VOR": 0.30, "AD": 0.20, "VFR": 0.0}.get(str(row.get("src")), 0.0)
        near = 0.0
        if last:
            near = 1.0 / (1.0 + gc_dist_nm(last.lat, last.lon, float(row["lat"]), float(row["lon"])))
        return exact + starts + sim + src_bonus + near * 0.25

    df["_score"] = df.apply(score, axis=1)
    return df.sort_values("_score", ascending=False).head(limit)


def resolve_token(token: str, default_alt: float, last: Optional[Point] = None) -> Tuple[Optional[Point], str]:
    raw = token.strip()
    if not raw or raw.upper() == "DCT":
        return None, ""
    fix = make_vor_fix(raw)
    if fix:
        fix.alt = default_alt
        return fix, ""

    # decimal coordinate: 38.75,-9.12
    m = re.match(r"^(-?\d+(?:\.\d+)?),(-?\d+(?:\.\d+)?)$", raw)
    if m:
        lat, lon = float(m.group(1)), float(m.group(2))
        return Point(code="USERCOORD", name=f"{lat:.4f},{lon:.4f}", lat=lat, lon=lon, alt=default_alt, src="USER"), ""

    # ICAO compact latlon: 3839N00837W or 383930N0083721W
    m = re.match(r"^(\d{4,6}(?:\.\d+)?[NS])(\d{5,7}(?:\.\d+)?[EW])$", raw.upper())
    if m:
        lat = dms_token_to_dd(m.group(1), is_lon=False)
        lon = dms_token_to_dd(m.group(2), is_lon=True)
        if lat is not None and lon is not None:
            return Point(code="LATLON", name=dd_to_icao(lat, lon), lat=lat, lon=lon, alt=default_alt, src="USER"), ""

    q = clean_code(raw)
    exact = POINTS_DF[POINTS_DF["code"].astype(str).str.upper() == q]
    if not exact.empty:
        # Prefer VOR if code is a VOR ident and token is exact VOR, otherwise IFR > AD > VFR.
        priority = {"VOR": 0, "IFR": 1, "AD": 2, "VFR": 3}
        exact = exact.assign(_prio=exact["src"].map(lambda x: priority.get(str(x), 9))).sort_values("_prio")
        return df_row_to_point(exact.iloc[0], alt=default_alt), ""

    fuzzy = search_points(raw, limit=1, last=last)
    if not fuzzy.empty and float(fuzzy.iloc[0].get("_score", 0)) >= 1.1:
        return df_row_to_point(fuzzy.iloc[0], alt=default_alt), f"'{raw}' resolvido como {fuzzy.iloc[0]['code']}"
    return None, f"Não encontrei ponto: {raw}"


def list_airways() -> List[str]:
    if AIRWAYS_DF.empty:
        return []
    return sorted(AIRWAYS_DF["airway"].dropna().astype(str).str.upper().unique().tolist())


def expand_airway(airway: str, start_code: str, end_code: str, default_alt: float) -> Tuple[List[Point], str]:
    airway = airway.upper().strip()
    start_code = clean_code(start_code)
    end_code = clean_code(end_code)
    sub = AIRWAYS_DF[AIRWAYS_DF["airway"].astype(str).str.upper() == airway].sort_values("seq")
    if sub.empty:
        return [], f"Airway {airway} não existe no CSV."
    codes = [clean_code(x) for x in sub["point"].tolist()]
    if start_code not in codes or end_code not in codes:
        return [], f"{airway}: endpoints {start_code}/{end_code} não estão ambos na airway."
    i1, i2 = codes.index(start_code), codes.index(end_code)
    chunk = sub.iloc[min(i1, i2) : max(i1, i2) + 1]
    if i2 < i1:
        chunk = chunk.iloc[::-1]
    pts = [
        Point(code=clean_code(r["point"]), name=clean_code(r["point"]), lat=float(r["lat"]), lon=float(r["lon"]), alt=default_alt, src="IFR", routes=airway, remarks=str(r.get("remarks", "")))
        for _, r in chunk.iterrows()
    ]
    return pts, ""


def tokenize_route_text(text: str) -> List[str]:
    # Keep VOR/R/D tokens intact; split commas, semicolons and whitespace.
    text = text.replace(";", " ").replace(",", " ")
    return [t.strip().upper() for t in re.split(r"\s+", text) if t.strip()]


def parse_route_text(text: str, default_alt: float) -> Tuple[List[Point], List[str]]:
    tokens = tokenize_route_text(text)
    airways_set = set(list_airways())
    out: List[Point] = []
    notes: List[str] = []
    i = 0
    while i < len(tokens):
        tok = tokens[i]
        if tok == "DCT":
            i += 1
            continue
        # POINT AIRWAY POINT syntax. Example: MAGUM UZ218 ATECA
        if i + 2 < len(tokens) and tokens[i + 1] in airways_set:
            p_start, msg1 = resolve_token(tokens[i], default_alt, out[-1] if out else None)
            if msg1:
                notes.append(msg1)
            airway = tokens[i + 1]
            p_end, msg2 = resolve_token(tokens[i + 2], default_alt, p_start)
            if msg2:
                notes.append(msg2)
            if p_start and p_end:
                expanded, msg = expand_airway(airway, p_start.code, p_end.code, default_alt)
                if expanded:
                    if not out or clean_code(out[-1].code) != clean_code(expanded[0].code):
                        out.append(expanded[0])
                    out.extend(expanded[1:])
                else:
                    notes.append(msg + " Usei DCT entre endpoints.")
                    if not out or clean_code(out[-1].code) != p_start.code:
                        out.append(p_start)
                    out.append(p_end)
            i += 3
            continue
        p, msg = resolve_token(tok, default_alt, out[-1] if out else None)
        if msg:
            notes.append(msg)
        if p:
            out.append(p)
        i += 1

    # Assign stable ids
    for p in out:
        p.uid = next_uid()
    return out, notes

# ===============================================================
# ROUTE CALCULATION
# ===============================================================
def next_uid() -> int:
    st.session_state["next_uid"] = int(st.session_state.get("next_uid", 1)) + 1
    return int(st.session_state["next_uid"])


def ensure_point_ids() -> None:
    changed = False
    for i, w in enumerate(st.session_state.get("wps", [])):
        if w.get("uid") is None:
            w["uid"] = next_uid()
            changed = True
    if changed:
        st.session_state.wps = st.session_state.wps


def current_profile() -> Dict[str, float]:
    return {
        "climb_tas": float(st.session_state.climb_tas),
        "cruise_tas": float(st.session_state.cruise_tas),
        "descent_tas": float(st.session_state.descent_tas),
        "fuel_flow_lh": float(st.session_state.fuel_flow_lh),
        "taxi_fuel_l": float(st.session_state.taxi_fuel_l),
    }


def build_route_nodes(user_wps: List[Dict[str, Any]]) -> List[Dict[str, Any]]:
    if len(user_wps) < 2:
        return []
    p = current_profile()
    out: List[Dict[str, Any]] = []
    for i in range(len(user_wps) - 1):
        A = user_wps[i]
        B = user_wps[i + 1]
        out.append(A.copy())
        dist = gc_dist_nm(A["lat"], A["lon"], B["lat"], B["lon"])
        tc = gc_course_tc(A["lat"], A["lon"], B["lat"], B["lon"])
        wf = wind_for_point(A)[0]
        wk = wind_for_point(A)[1]
        if B["alt"] > A["alt"]:
            t_min = (B["alt"] - A["alt"]) / max(float(st.session_state.roc_fpm), 1.0)
            _, _, gs = wind_triangle(tc, p["climb_tas"], wf, wk)
            d_need = gs * t_min / 60.0
            if 0.05 < d_need < dist - 0.05:
                lat, lon = point_along_gc(A["lat"], A["lon"], B["lat"], B["lon"], d_need)
                out.append(
                    Point(code=f"TOC{i+1}", name=f"TOC L{i+1}", lat=lat, lon=lon, alt=B["alt"], src="CALC", uid=next_uid()).to_dict()
                )
        elif B["alt"] < A["alt"]:
            t_min = (A["alt"] - B["alt"]) / max(float(st.session_state.rod_fpm), 1.0)
            _, _, gs = wind_triangle(tc, p["descent_tas"], wf, wk)
            d_need = gs * t_min / 60.0
            if 0.05 < d_need < dist - 0.05:
                lat, lon = point_along_gc(A["lat"], A["lon"], B["lat"], B["lon"], max(0.0, dist - d_need))
                out.append(
                    Point(code=f"TOD{i+1}", name=f"TOD L{i+1}", lat=lat, lon=lon, alt=A["alt"], src="CALC", uid=next_uid()).to_dict()
                )
    out.append(user_wps[-1].copy())
    return out


def wind_for_point(P: Dict[str, Any]) -> Tuple[int, int]:
    if bool(st.session_state.use_global_wind):
        return int(st.session_state.wind_from), int(st.session_state.wind_kt)
    return int(P.get("wind_from") or st.session_state.wind_from), int(P.get("wind_kt") or st.session_state.wind_kt)


def build_legs(nodes: List[Dict[str, Any]]) -> List[Dict[str, Any]]:
    if len(nodes) < 2:
        return []
    p = current_profile()
    base_dt = None
    if str(st.session_state.start_clock).strip():
        try:
            h, m = map(int, str(st.session_state.start_clock).strip().split(":"))
            base_dt = dt.datetime.combine(dt.date.today(), dt.time(hour=h, minute=m))
        except Exception:
            base_dt = None

    t_cursor = 0
    efob = max(0.0, float(st.session_state.start_efob) - p["taxi_fuel_l"])
    legs: List[Dict[str, Any]] = []

    for i in range(len(nodes) - 1):
        A, B = nodes[i], nodes[i + 1]
        dist_raw = gc_dist_nm(A["lat"], A["lon"], B["lat"], B["lon"])
        dist = rd(dist_raw)
        tc = gc_course_tc(A["lat"], A["lon"], B["lat"], B["lon"])
        wf, wk = wind_for_point(A)
        if B["alt"] > A["alt"] + 1:
            profile = "CLIMB"
            tas = p["climb_tas"]
        elif B["alt"] < A["alt"] - 1:
            profile = "DESCENT"
            tas = p["descent_tas"]
        else:
            profile = "LEVEL"
            tas = p["cruise_tas"]
        _, th, gs = wind_triangle(tc, tas, wf, wk)
        mh = apply_mag_var(th, float(st.session_state.mag_var), bool(st.session_state.mag_is_east))
        ete = rt((dist / max(gs, 1e-9)) * 3600.0) if gs > 0 and dist > 0 else 0
        burn = rf(p["fuel_flow_lh"] * ete / 3600.0)
        efob_start = efob
        efob_end = max(0.0, rf(efob_start - burn))
        clk_start = (base_dt + dt.timedelta(seconds=t_cursor)).strftime("%H:%M") if base_dt else f"T+{mmss(t_cursor)}"
        clk_end = (base_dt + dt.timedelta(seconds=t_cursor + ete)).strftime("%H:%M") if base_dt else f"T+{mmss(t_cursor + ete)}"

        pref_vor = A.get("vor_ident") if A.get("vor_pref") == "FIXED" else ""
        track = tracking_instruction(A, B, pref_vor)
        leg = {
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
            "time_sec": ete,
            "burn": burn,
            "efob_start": efob_start,
            "efob_end": efob_end,
            "clock_start": clk_start,
            "clock_end": clk_end,
            "wind_from": wf,
            "wind_kt": wk,
            "tracking": track,
        }
        legs.append(leg)
        t_cursor += ete
        efob = efob_end

        stop_min = float(B.get("stop_min") or 0.0)
        if stop_min > 0:
            stop_sec = rt(stop_min * 60.0)
            stop_burn = rf(p["fuel_flow_lh"] * stop_sec / 3600.0)
            efob_start2 = efob
            efob_end2 = max(0.0, rf(efob_start2 - stop_burn))
            clk_start2 = (base_dt + dt.timedelta(seconds=t_cursor)).strftime("%H:%M") if base_dt else f"T+{mmss(t_cursor)}"
            clk_end2 = (base_dt + dt.timedelta(seconds=t_cursor + stop_sec)).strftime("%H:%M") if base_dt else f"T+{mmss(t_cursor + stop_sec)}"
            legs.append(
                {
                    "i": len(legs) + 1,
                    "A": B,
                    "B": B,
                    "profile": "STOP",
                    "TC": 0,
                    "TH": 0,
                    "MH": 0,
                    "TAS": 0,
                    "GS": 0,
                    "Dist": 0,
                    "time_sec": stop_sec,
                    "burn": stop_burn,
                    "efob_start": efob_start2,
                    "efob_end": efob_end2,
                    "clock_start": clk_start2,
                    "clock_end": clk_end2,
                    "wind_from": wf,
                    "wind_kt": wk,
                    "tracking": "STOP",
                }
            )
            t_cursor += stop_sec
            efob = efob_end2
    return legs


def recalc_route() -> None:
    nodes = build_route_nodes(st.session_state.wps)
    st.session_state.route_nodes = nodes
    st.session_state.legs = build_legs(nodes)

# ===============================================================
# GIST ROUTES
# ===============================================================
def get_gist_credentials() -> Tuple[Optional[str], Optional[str]]:
    token = os.getenv("GITHUB_TOKEN")
    gist_id = os.getenv("ROUTES_GIST_ID")
    try:
        token = st.secrets.get("GITHUB_TOKEN", token)
        gist_id = st.secrets.get("ROUTES_GIST_ID", gist_id)
    except Exception:
        pass
    return token, gist_id


def serialize_route() -> List[Dict[str, Any]]:
    return [
        {
            "code": w.get("code"),
            "name": w.get("name"),
            "lat": w.get("lat"),
            "lon": w.get("lon"),
            "alt": w.get("alt"),
            "src": w.get("src", "USER"),
            "routes": w.get("routes", ""),
            "remarks": w.get("remarks", ""),
            "stop_min": w.get("stop_min", 0.0),
            "vor_pref": w.get("vor_pref", "AUTO"),
            "vor_ident": w.get("vor_ident", ""),
        }
        for w in st.session_state.wps
    ]


def load_routes_from_gist() -> Dict[str, Any]:
    token, gist_id = get_gist_credentials()
    if not token or not gist_id or requests is None:
        return {}
    try:
        r = requests.get(f"https://api.github.com/gists/{gist_id}", headers={"Authorization": f"token {token}"}, timeout=20)
        if r.status_code != 200:
            return {}
        files = r.json().get("files", {})
        if "routes.json" not in files:
            return {}
        return json.loads(files["routes.json"].get("content") or "{}")
    except Exception:
        return {}


def save_routes_to_gist(routes: Dict[str, Any]) -> Tuple[bool, str]:
    token, gist_id = get_gist_credentials()
    if not token or not gist_id or requests is None:
        return False, "GITHUB_TOKEN/ROUTES_GIST_ID não configurados."
    try:
        payload = {"files": {"routes.json": {"content": json.dumps(routes, indent=2, ensure_ascii=False)}}}
        r = requests.patch(f"https://api.github.com/gists/{gist_id}", headers={"Authorization": f"token {token}"}, json=payload, timeout=20)
        if r.status_code not in (200, 201):
            return False, f"Erro GitHub {r.status_code}: {r.text[:200]}"
        return True, "Rotas guardadas."
    except Exception as e:
        return False, str(e)

# ===============================================================
# PDF
# ===============================================================
def _pdf_key_norm(key: Any) -> str:
    """Normalize PDF field names so template variants still get populated."""
    txt = str(key or "").strip()
    txt = txt.strip("()")
    txt = txt.replace("/", "_")
    txt = re.sub(r"[^A-Za-z0-9]+", "_", txt)
    txt = re.sub(r"_+", "_", txt).strip("_")
    return txt.upper()


def expand_pdf_aliases(data: Dict[str, Any]) -> Dict[str, Any]:
    out = dict(data)
    # Explicit aliases for the header fields that differ across NAVLOG_FORM versions.
    alias_groups = [
        ["WIND", "Wind", "WIND_GLOBAL"],
        ["MAG_VAR", "MAGVAR", "MAGNETIC_VARIATION", "MAGNETIC_VAR"],
        ["FLIGHT_LEVEL_ALTITUDE", "FLIGHT_LEVEL/ALTITUDE", "FLIGHT_LEVEL", "FL_ALT", "FLIGHT_LEVEL_ALT"],
        ["TEMP_ISA_DEV", "TEMP/ISA_DEV", "TEMP_ISA", "ISA_DEV", "TEMP"],
    ]
    for group in alias_groups:
        value = None
        for k in group:
            if k in out and str(out[k]) != "":
                value = out[k]
                break
        if value is not None:
            for k in group:
                out[k] = value
    # Normalized lookup catches spaces, slashes and case differences in actual PDF field names.
    for k, v in list(out.items()):
        out[_pdf_key_norm(k)] = v
    return out


def fill_pdf(template: Path, out: Path, data: Dict[str, Any]) -> Path:
    data_expanded = expand_pdf_aliases(data)
    pdf = PdfReader(str(template))
    if pdf.Root.AcroForm:
        pdf.Root.AcroForm.update(PdfDict(NeedAppearances=True))
    for page in pdf.pages:
        annots = getattr(page, "Annots", None)
        if not annots:
            continue
        for a in annots:
            if a.Subtype == PdfName("Widget") and a.T:
                key = str(a.T)[1:-1]
                value = data_expanded.get(key, data_expanded.get(_pdf_key_norm(key)))
                if value is not None:
                    a.update(PdfDict(V=str(value), DV=str(value)))
                    if "Navaid" in key or "NAVAID" in key.upper():
                        a.update(PdfDict(DA="/Helv 5 Tf 0 g"))
    PdfWriter(str(out), trailer=pdf).write()
    return out


def choose_vor_for_point(P: Dict[str, Any]) -> Optional[Dict[str, Any]]:
    if str(P.get("name", "")).upper().startswith(("TOC", "TOD")):
        return None
    if P.get("vor_pref") == "NONE":
        return None
    if P.get("vor_pref") == "FIXED" and P.get("vor_ident"):
        return get_vor(str(P.get("vor_ident")))
    if P.get("src") == "VOR":
        return get_vor(str(P.get("code") or P.get("name")))
    return nearest_vor(float(P["lat"]), float(P["lon"]))


def fill_leg_payload(d: Dict[str, Any], idx: int, L: Dict[str, Any], acc_d: float, acc_t: int, prefix: str = "Leg") -> None:
    P = L["B"]
    d[f"{prefix}{idx:02d}_Waypoint"] = str(P.get("code") or P.get("name"))
    d[f"{prefix}{idx:02d}_Altitude_FL"] = str(int(round(float(P.get("alt", 0)))))
    if L["profile"] != "STOP":
        d[f"{prefix}{idx:02d}_True_Course"] = f"{int(round(L['TC'])):03d}"
        d[f"{prefix}{idx:02d}_True_Heading"] = f"{int(round(L['TH'])):03d}"
        d[f"{prefix}{idx:02d}_Magnetic_Heading"] = f"{int(round(L['MH'])):03d}"
        d[f"{prefix}{idx:02d}_True_Airspeed"] = str(int(round(L["TAS"])))
        d[f"{prefix}{idx:02d}_Ground_Speed"] = str(int(round(L["GS"])))
        d[f"{prefix}{idx:02d}_Leg_Distance"] = f"{L['Dist']:.1f}"
    else:
        for field in ["True_Course", "True_Heading", "Magnetic_Heading", "True_Airspeed", "Ground_Speed"]:
            d[f"{prefix}{idx:02d}_{field}"] = ""
        d[f"{prefix}{idx:02d}_Leg_Distance"] = "0.0"
    d[f"{prefix}{idx:02d}_Cumulative_Distance"] = f"{acc_d:.1f}"
    d[f"{prefix}{idx:02d}_Leg_ETE"] = pdf_time(L["time_sec"])
    d[f"{prefix}{idx:02d}_Cumulative_ETE"] = pdf_time(acc_t)
    d[f"{prefix}{idx:02d}_ETO"] = ""
    d[f"{prefix}{idx:02d}_Planned_Burnoff"] = f"{L['burn']:.1f}"
    d[f"{prefix}{idx:02d}_Estimated_FOB"] = f"{L['efob_end']:.1f}"
    vor = choose_vor_for_point(P)
    d[f"{prefix}{idx:02d}_Navaid_Identifier"] = format_vor_id(vor)
    d[f"{prefix}{idx:02d}_Navaid_Frequency"] = format_radial_dist(vor, float(P["lat"]), float(P["lon"]))


def build_pdf_payload(legs: List[Dict[str, Any]], header: Dict[str, str], start: int = 0, count: int = 22) -> Dict[str, Any]:
    chunk = legs[start : start + count]
    total_sec = sum(L["time_sec"] for L in legs)
    total_burn = rf(sum(L["burn"] for L in legs))
    total_dist = rd(sum(L["Dist"] for L in legs))
    climb_sec = sum(L["time_sec"] for L in legs if L["profile"] == "CLIMB")
    level_sec = sum(L["time_sec"] for L in legs if L["profile"] == "LEVEL")
    desc_sec = sum(L["time_sec"] for L in legs if L["profile"] == "DESCENT")
    climb_burn = rf(sum(L["burn"] for L in legs if L["profile"] == "CLIMB"))
    d: Dict[str, Any] = {
        "CALLSIGN": header.get("callsign", ""),
        "REGISTRATION": header.get("registration", ""),
        "STUDENT": header.get("student", ""),
        "LESSON": header.get("lesson", ""),
        "INSTRUTOR": header.get("instructor", ""),
        "DEPT": header.get("dept_freq", ""),
        "ENROUTE": header.get("enroute_freq", ""),
        "ARRIVAL": header.get("arrival_freq", ""),
        "ETD/ETA": f"{header.get('etd','')}/{header.get('eta','')}".strip("/"),
        "Departure_Airfield": str(st.session_state.wps[0].get("code") or st.session_state.wps[0].get("name")) if st.session_state.wps else "",
        "Arrival_Airfield": str(st.session_state.wps[-1].get("code") or st.session_state.wps[-1].get("name")) if st.session_state.wps else "",
        "WIND": f"{int(st.session_state.wind_from):03d}/{int(st.session_state.wind_kt):02d}",
        "Wind": f"{int(st.session_state.wind_from):03d}/{int(st.session_state.wind_kt):02d}",
        "MAG_VAR": f"{abs(float(st.session_state.mag_var)):.1f}°{'E' if st.session_state.mag_is_east else 'W'}",
        "MAGVAR": f"{abs(float(st.session_state.mag_var)):.1f}°{'E' if st.session_state.mag_is_east else 'W'}",
        "FLIGHT_LEVEL/ALTITUDE": header.get("fl_alt", ""),
        "FLIGHT_LEVEL_ALTITUDE": header.get("fl_alt", ""),
        "FL_ALT": header.get("fl_alt", ""),
        "TEMP/ISA_DEV": header.get("temp_isa", ""),
        "TEMP_ISA_DEV": header.get("temp_isa", ""),
        "ISA_DEV": header.get("temp_isa", ""),
        "FLT TIME": pdf_time(total_sec),
        "CLIMB FUEL": f"{climb_burn:.1f}",
        "OBSERVATIONS": f"Climb {pdf_time(climb_sec)} / Cruise {pdf_time(level_sec)} / Descent {pdf_time(desc_sec)}",
        "Leg_Number": str(len(legs)),
        "AIRCRAFT_TYPE": str(st.session_state.aircraft_type),
    }
    acc_d, acc_t = 0.0, 0
    for i, L in enumerate(chunk, start=1 if start == 0 else 12):
        acc_d = rd(acc_d + L["Dist"])
        acc_t += int(L["time_sec"])
        fill_leg_payload(d, i, L, acc_d, acc_t)
    d["Leg23_Leg_Distance"] = f"{total_dist:.1f}"
    d["Leg23_Leg_ETE"] = pdf_time(total_sec)
    d["Leg23_Planned_Burnoff"] = f"{total_burn:.1f}"
    d["Leg23_Estimated_FOB"] = f"{legs[-1]['efob_end']:.1f}" if legs else ""
    return d


def generate_briefing_pdf(path: Path, rows: List[Dict[str, Any]]) -> Optional[Path]:
    try:
        from reportlab.lib.pagesizes import A4, landscape
        from reportlab.lib.units import mm
        from reportlab.pdfgen import canvas
    except Exception:
        return None
    c = canvas.Canvas(str(path), pagesize=landscape(A4))
    width, height = landscape(A4)
    x0, y = 12 * mm, height - 14 * mm
    c.setFont("Helvetica-Bold", 14)
    c.drawString(x0, y, f"NAVLOG briefing — {st.session_state.aircraft_type}")
    y -= 8 * mm
    headers = ["Leg", "From", "To", "MH", "TC", "Dist", "ETE", "Fuel", "EFOB", "VOR", "Radial/D", "Track"]
    widths = [10, 28, 28, 12, 12, 14, 16, 14, 14, 26, 24, 68]
    widths = [w * mm for w in widths]
    def header_line() -> None:
        nonlocal y
        c.setFont("Helvetica-Bold", 7)
        x = x0
        for h, w in zip(headers, widths):
            c.drawString(x, y, h)
            x += w
        y -= 4 * mm
        c.line(x0, y + 2 * mm, x0 + sum(widths), y + 2 * mm)
        c.setFont("Helvetica", 7)
    header_line()
    for row in rows:
        if y < 12 * mm:
            c.showPage()
            y = height - 14 * mm
            header_line()
        vals = [row.get(h, "") for h in headers]
        x = x0
        for val, w in zip(vals, widths):
            s = str(val)
            if len(s) > 32:
                s = s[:31] + "…"
            c.drawString(x, y, s)
            x += w
        y -= 4.5 * mm
    c.save()
    return path

# ===============================================================
# DISPLAY HELPERS
# ===============================================================
def summary_metrics(legs: List[Dict[str, Any]]) -> Dict[str, Any]:
    return {
        "time": sum(L["time_sec"] for L in legs),
        "dist": rd(sum(L["Dist"] for L in legs)),
        "burn": rf(sum(L["burn"] for L in legs)),
        "efob": legs[-1]["efob_end"] if legs else float(st.session_state.start_efob),
        "legs": len(legs),
    }


def legs_to_dataframe(legs: List[Dict[str, Any]]) -> pd.DataFrame:
    rows = []
    acc_d = 0.0
    acc_t = 0
    for L in legs:
        acc_d = rd(acc_d + L["Dist"])
        acc_t += int(L["time_sec"])
        P = L["B"]
        vor = choose_vor_for_point(P)
        rows.append(
            {
                "Leg": L["i"],
                "From": L["A"].get("code") or L["A"].get("name"),
                "To": L["B"].get("code") or L["B"].get("name"),
                "Profile": L["profile"],
                "TC": f"{int(round(L['TC'])):03d}",
                "TH": f"{int(round(L['TH'])):03d}",
                "MH": f"{int(round(L['MH'])):03d}",
                "TAS": int(round(L["TAS"])),
                "GS": int(round(L["GS"])),
                "Dist": f"{L['Dist']:.1f}",
                "CumDist": f"{acc_d:.1f}",
                "ETE": pdf_time(L["time_sec"]),
                "CumETE": pdf_time(acc_t),
                "Fuel": f"{L['burn']:.1f}",
                "EFOB": f"{L['efob_end']:.1f}",
                "Wind": f"{int(L['wind_from']):03d}/{int(L['wind_kt'])}",
                "VOR": format_vor_id(vor),
                "Radial/Dist": format_radial_dist(vor, float(P["lat"]), float(P["lon"])),
                "Tracking": L.get("tracking", ""),
            }
        )
    return pd.DataFrame(rows)


def route_item15(wps: List[Dict[str, Any]]) -> str:
    if len(wps) < 2:
        return ""
    tokens: List[str] = []
    seq = wps[:]
    # Strip departure/arrival aerodromes if they look like ICAO aerodrome codes.
    if re.fullmatch(r"[A-Z]{4}", clean_code(seq[0].get("code"))):
        seq = seq[1:]
    if seq and re.fullmatch(r"[A-Z]{4}", clean_code(seq[-1].get("code"))):
        seq = seq[:-1]
    for w in seq:
        code = clean_code(w.get("code") or w.get("name"))
        if re.fullmatch(r"[A-Z0-9]{2,5}", code) and w.get("src") in {"IFR", "VOR", "AD"}:
            tokens.append(code)
        else:
            tokens.append(dd_to_icao(float(w["lat"]), float(w["lon"])))
    return "DCT " + " DCT ".join(tokens) if tokens else ""


def html_pills(items: Iterable[Tuple[str, str]]) -> None:
    html = "".join([f"<span class='pill {klass}'>{label}</span>" for label, klass in items])
    st.markdown(html, unsafe_allow_html=True)

# ===============================================================
# MAP
# ===============================================================
def make_base_map() -> folium.Map:
    m = folium.Map(location=PT_CENTER, zoom_start=8, tiles=None, control_scale=True, prefer_canvas=True)
    folium.TileLayer("https://{s}.tile.openstreetmap.org/{z}/{x}/{y}.png", attr="© OpenStreetMap", name="OSM").add_to(m)
    folium.TileLayer("https://{s}.tile.opentopomap.org/{z}/{x}/{y}.png", attr="© OpenTopoMap", name="OpenTopoMap").add_to(m)
    folium.TileLayer(
        "https://services.arcgisonline.com/ArcGIS/rest/services/World_Hillshade/MapServer/tile/{z}/{y}/{x}",
        attr="© Esri",
        name="Hillshade",
    ).add_to(m)
    m.fit_bounds(PT_BOUNDS)
    Fullscreen(position="topleft", title="Fullscreen").add_to(m)
    MeasureControl(position="topleft", primary_length_unit="nautical_miles").add_to(m)
    return m


def add_div_marker(m: folium.Map, lat: float, lon: float, html: str) -> None:
    folium.Marker((lat, lon), icon=folium.DivIcon(html=html, icon_size=(0, 0))).add_to(m)


def render_route_map(wps: List[Dict[str, Any]], nodes: List[Dict[str, Any]], legs: List[Dict[str, Any]], *, key: str = "mainmap") -> Dict[str, Any]:
    m = make_base_map()

    # IFR/VOR reference layer, lightweight and clustered.
    if bool(st.session_state.show_ref_points):
        cluster = MarkerCluster(name="Pontos IFR/VFR/VOR", disableClusteringAtZoom=10).add_to(m)
        ref = POINTS_DF
        src_filter = set(st.session_state.ref_layers)
        ref = ref[ref["src"].isin(src_filter)] if src_filter else ref.head(0)
        for _, r in ref.iterrows():
            src = str(r.get("src"))
            color = {"IFR": "#2563eb", "VOR": "#dc2626", "AD": "#111827", "VFR": "#16a34a"}.get(src, "#334155")
            radius = 4 if src in {"IFR", "VOR"} else 3
            folium.CircleMarker(
                (float(r["lat"]), float(r["lon"])),
                radius=radius,
                color=color,
                weight=1,
                fill=True,
                fill_opacity=0.9,
                tooltip=f"[{src}] {r.get('code')} — {r.get('name')} {r.get('routes','')}",
            ).add_to(cluster)

    # Airways layer from CSV.
    if bool(st.session_state.show_airways) and not AIRWAYS_DF.empty:
        for airway, grp in AIRWAYS_DF.groupby("airway"):
            if airway not in set(st.session_state.selected_airways or []):
                continue
            pts = [(float(r["lat"]), float(r["lon"])) for _, r in grp.sort_values("seq").iterrows()]
            if len(pts) >= 2:
                folium.PolyLine(pts, color="#64748b", weight=2, opacity=0.55, tooltip=airway).add_to(m)

    # Route legs.
    for L in legs:
        if L["profile"] == "STOP":
            folium.CircleMarker((L["A"]["lat"], L["A"]["lon"]), radius=8, color="#dc2626", fill=True, fill_opacity=0.7, tooltip="STOP").add_to(m)
            continue
        color = PROFILE_COLORS.get(L["profile"], "#7c3aed")
        folium.PolyLine([(L["A"]["lat"], L["A"]["lon"]), (L["B"]["lat"], L["B"]["lon"])], color="#ffffff", weight=8, opacity=1).add_to(m)
        folium.PolyLine([(L["A"]["lat"], L["A"]["lon"]), (L["B"]["lat"], L["B"]["lon"])], color=color, weight=4, opacity=1, tooltip=f"L{L['i']} {L['profile']} {pdf_time(L['time_sec'])}").add_to(m)


    # Waypoints.
    for idx, w in enumerate(wps, start=1):
        lat, lon = float(w["lat"]), float(w["lon"])
        src = w.get("src", "USER")
        color = {"IFR": "#2563eb", "VOR": "#dc2626", "AD": "#111827", "VFR": "#16a34a", "USER": "#f97316", "VORFIX": "#be123c"}.get(src, "#0f172a")
        folium.CircleMarker((lat, lon), radius=6, color="#ffffff", weight=3, fill=True, fill_opacity=1).add_to(m)
        folium.CircleMarker((lat, lon), radius=5, color=color, fill=True, fill_opacity=1, tooltip=f"{idx}. {w.get('code') or w.get('name')} [{src}]").add_to(m)
        label = f"{idx}. {w.get('code') or w.get('name')}"
        add_div_marker(
            m,
            lat,
            lon,
            f"<div style='transform:translate(8px,-22px);font-weight:800;font-size:12px;color:#0f172a;text-shadow:-1px -1px 0 white,1px -1px 0 white,-1px 1px 0 white,1px 1px 0 white;white-space:nowrap'>{label}</div>",
        )

    folium.LayerControl(collapsed=False).add_to(m)
    return st_folium(m, width=None, height=720, key=key)

# ===============================================================
# INITIAL SESSION STATE
# ===============================================================
ss("next_uid", 1)
ss("aircraft_type", "Piper PA-28")
if "climb_tas" not in st.session_state:
    prof = AIRCRAFT_PROFILES[st.session_state.aircraft_type]
    st.session_state.climb_tas = prof["climb_tas"]
    st.session_state.cruise_tas = prof["cruise_tas"]
    st.session_state.descent_tas = prof["descent_tas"]
    st.session_state.fuel_flow_lh = prof["fuel_flow_lh"]
    st.session_state.taxi_fuel_l = prof["taxi_fuel_l"]
ss("wind_from", 0)
ss("wind_kt", 0)
ss("use_global_wind", True)
ss("mag_var", 1.0)
ss("mag_is_east", False)
ss("roc_fpm", 600)
ss("rod_fpm", 500)
ss("start_efob", 180.0)
ss("start_clock", "")
ss("default_alt", 3000.0)
ss("wps", [])
ss("route_nodes", [])
ss("legs", [])
ss("show_ref_points", False)
ss("ref_layers", ["IFR", "VOR", "AD"])
ss("show_airways", False)
ss("selected_airways", [])
ss("saved_routes", {})
ensure_point_ids()

# ===============================================================
# HEADER
# ===============================================================
st.markdown(
    f"""
<div class='nav-hero'>
  <div class='nav-title'>🧭 {APP_TITLE}</div>
  <div class='nav-sub'>Planeamento VFR/IFR low offline por CSV local, com airways, VOR radial fixes, navlog e PDF.</div>
</div>
""",
    unsafe_allow_html=True,
)

legs = st.session_state.get("legs", [])
if legs:
    sm = summary_metrics(legs)
    html_pills(
        [
            (f"ETE {pdf_time(sm['time'])}", "pill-good"),
            (f"Dist {sm['dist']:.1f} NM", "pill-good"),
            (f"Fuel {sm['burn']:.1f} L", "pill-good"),
            (f"EFOB final {sm['efob']:.1f} L", "pill-good" if sm["efob"] >= 30 else "pill-warn"),
            (f"{sm['legs']} legs", ""),
            (f"{st.session_state.aircraft_type}", ""),
        ]
    )
else:
    html_pills(
        [
            (f"{len(POINTS_DF[POINTS_DF.src == 'IFR'])} IFR pts", ""),
            (f"{len(AIRWAYS_DF.airway.unique()) if not AIRWAYS_DF.empty else 0} airways", ""),
            (f"{len(VOR_DF)} VOR", ""),
            ("PDF templates OK" if TEMPLATE_MAIN.exists() else "PDF template em falta", "pill-good" if TEMPLATE_MAIN.exists() else "pill-warn"),
        ]
    )

# ===============================================================
# TOP SETUP - no sidebar
# ===============================================================
with st.container():
    st.markdown("#### 1 · Setup do voo")
    setup_a, setup_b, setup_c, setup_d = st.columns([1.15, 1.1, 1.1, 0.8], gap="large")

    with setup_a:
        ac_names = list(AIRCRAFT_PROFILES)
        ac = st.selectbox(
            "Aeronave",
            ac_names,
            index=ac_names.index(st.session_state.aircraft_type) if st.session_state.aircraft_type in ac_names else 0,
            key="setup_aircraft_type",
        )
        if ac != st.session_state.aircraft_type:
            st.session_state.aircraft_type = ac
            prof = AIRCRAFT_PROFILES[ac]
            st.session_state.climb_tas = prof["climb_tas"]
            st.session_state.cruise_tas = prof["cruise_tas"]
            st.session_state.descent_tas = prof["descent_tas"]
            st.session_state.fuel_flow_lh = prof["fuel_flow_lh"]
            st.session_state.taxi_fuel_l = prof["taxi_fuel_l"]
            st.rerun()
        st.number_input("EFOB inicial (L)", 0.0, 300.0, key="start_efob", step=1.0)
        st.text_input("Hora off-blocks / start (HH:MM)", key="start_clock")

    with setup_b:
        b1, b2 = st.columns(2)
        with b1:
            st.number_input("TAS subida", 30.0, 250.0, key="climb_tas", step=1.0)
            st.number_input("TAS descida", 30.0, 250.0, key="descent_tas", step=1.0)
            st.number_input("ROC ft/min", 100, 2000, key="roc_fpm", step=50)
        with b2:
            st.number_input("TAS cruzeiro", 30.0, 300.0, key="cruise_tas", step=1.0)
            st.number_input("Consumo L/h", 1.0, 200.0, key="fuel_flow_lh", step=0.5)
            st.number_input("ROD ft/min", 100, 2000, key="rod_fpm", step=50)

    with setup_c:
        c1, c2 = st.columns(2)
        with c1:
            st.number_input("Wind FROM (°T)", 0, 360, key="wind_from")
            st.number_input("Mag var (°)", -30.0, 30.0, key="mag_var", step=0.1)
        with c2:
            st.number_input("Wind kt", 0, 200, key="wind_kt")
            st.toggle("Variação EAST", key="mag_is_east")
        st.toggle("Usar vento global", key="use_global_wind")
        st.number_input("Altitude default novos pontos", 0.0, 45000.0, key="default_alt", step=100.0)

    with setup_d:
        st.number_input("Taxi fuel (L)", 0.0, 30.0, key="taxi_fuel_l", step=0.5)
        st.markdown("<div style='height:1.75rem'></div>", unsafe_allow_html=True)
        if st.button("Recalcular navlog", type="primary", use_container_width=True):
            recalc_route()
            st.toast("Rota recalculada")

    st.markdown("<hr>", unsafe_allow_html=True)

# ===============================================================
# TABS
# ===============================================================
tab_route, tab_map, tab_navlog, tab_data = st.tabs(["1 · Rota", "2 · Mapa / clique", "3 · Navlog / PDF", "4 · Dados / rotas"])

# ---------------------------------------------------------------
# ROUTE TAB
# ---------------------------------------------------------------
with tab_route:
    st.markdown("#### 2 · Construir rota")
    st.caption("Fluxo recomendado: confirma o setup acima → escreve/cola a rota ou pesquisa pontos → revê waypoints → recalcula → segue para mapa ou PDF.")
    left, right = st.columns([1.05, 0.95], gap="large")

    with left:
        st.markdown("#### Construção rápida por texto")
        st.caption("Exemplos: `LPSO MAGUM UZ218 ATECA LPFR`, `LPCS CAS/R180/D12 ESP/R090/D15 LPFR`, `LPPR MANIK UP600 MAGUM`.")
        route_text = st.text_area("Rota", height=92, placeholder="LPSO MAGUM UZ218 ATECA LPFR")
        c1, c2, c3 = st.columns([1, 1, 1])
        with c1:
            if st.button("Substituir rota", type="primary", use_container_width=True):
                pts, notes = parse_route_text(route_text, float(st.session_state.default_alt))
                st.session_state.wps = [p.to_dict() for p in pts]
                recalc_route()
                for n in notes:
                    st.warning(n)
        with c2:
            if st.button("Acrescentar", use_container_width=True):
                last = Point.from_dict(st.session_state.wps[-1]) if st.session_state.wps else None
                pts, notes = parse_route_text(route_text, float(st.session_state.default_alt))
                st.session_state.wps.extend([p.to_dict() for p in pts])
                recalc_route()
                for n in notes:
                    st.warning(n)
        with c3:
            if st.button("Limpar", use_container_width=True):
                st.session_state.wps = []
                st.session_state.route_nodes = []
                st.session_state.legs = []
                st.rerun()

        st.markdown("#### Pesquisa / adicionar ponto")
        q = st.text_input("Pesquisar por código/nome/rota", placeholder="MAGUM, ATECA, CAS, LPSO, Évora…")
        results = search_points(q, limit=12, last=Point.from_dict(st.session_state.wps[-1]) if st.session_state.wps else None)
        if q and results.empty:
            st.info("Sem resultados. Também podes usar coordenadas decimais ou fix VOR tipo CAS/R180/D12.")
        for i, r in results.iterrows():
            cols = st.columns([0.14, 0.60, 0.16, 0.10])
            with cols[0]:
                st.markdown(f"`{r['src']}`")
            with cols[1]:
                st.markdown(f"**{r['code']}** — {r['name']}  ")
                st.caption(f"{float(r['lat']):.5f}, {float(r['lon']):.5f} · {r.get('routes','')}")
            with cols[2]:
                alt = st.number_input("Alt", 0.0, 45000.0, float(st.session_state.default_alt), 100.0, key=f"alt_search_{i}", label_visibility="collapsed")
            with cols[3]:
                if st.button("➕", key=f"add_search_{i}", use_container_width=True):
                    p = df_row_to_point(r, alt=alt)
                    p.uid = next_uid()
                    st.session_state.wps.append(p.to_dict())
                    recalc_route()
                    st.rerun()

        st.markdown("#### Ponto manual / radial VOR")
        c1, c2, c3, c4 = st.columns([1, 1, 1, 1])
        with c1:
            manual_name = st.text_input("Nome", "WP")
        with c2:
            manual_lat = st.number_input("Lat", -90.0, 90.0, 39.0, step=0.0001, format="%.6f")
        with c3:
            manual_lon = st.number_input("Lon", -180.0, 180.0, -8.0, step=0.0001, format="%.6f")
        with c4:
            manual_alt = st.number_input("Alt ft", 0.0, 45000.0, float(st.session_state.default_alt), step=100.0, key="manual_alt")
        c1, c2 = st.columns([1, 1])
        with c1:
            if st.button("Adicionar coordenada", use_container_width=True):
                p = Point(code=clean_code(manual_name) or "WP", name=manual_name, lat=float(manual_lat), lon=float(manual_lon), alt=float(manual_alt), src="USER", uid=next_uid())
                st.session_state.wps.append(p.to_dict())
                recalc_route()
                st.rerun()
        with c2:
            radial_token = st.text_input("Fix VOR", placeholder="CAS/R180/D12")
            if st.button("Adicionar fix VOR", use_container_width=True):
                p = make_vor_fix(radial_token)
                if not p:
                    st.error("Formato inválido ou VOR desconhecido. Usa, por exemplo, CAS/R180/D12.")
                else:
                    p.alt = float(manual_alt)
                    p.uid = next_uid()
                    st.session_state.wps.append(p.to_dict())
                    recalc_route()
                    st.rerun()

    with right:
        st.markdown("#### Waypoints da rota")
        ensure_point_ids()
        if not st.session_state.wps:
            st.info("Ainda não há waypoints. Usa a caixa de texto, pesquisa ou clica no mapa.")
        remove_idx: Optional[int] = None
        move: Optional[Tuple[int, int]] = None
        for idx, w in enumerate(st.session_state.wps):
            with st.expander(f"{idx+1:02d} · {w.get('code') or w.get('name')} · {w.get('src','')}", expanded=False):
                c1, c2 = st.columns([2, 1])
                with c1:
                    w["code"] = st.text_input("Código", w.get("code") or w.get("name") or "WP", key=f"wp_code_{w['uid']}").upper()
                    w["name"] = st.text_input("Nome", w.get("name") or w.get("code") or "WP", key=f"wp_name_{w['uid']}")
                with c2:
                    w["alt"] = st.number_input("Alt ft", 0.0, 45000.0, float(w.get("alt", 0.0)), step=50.0, key=f"wp_alt_{w['uid']}")
                    w["stop_min"] = st.number_input("STOP min", 0.0, 480.0, float(w.get("stop_min", 0.0)), step=1.0, key=f"wp_stop_{w['uid']}")
                c1, c2 = st.columns(2)
                with c1:
                    w["lat"] = st.number_input("Lat", -90.0, 90.0, float(w.get("lat")), step=0.0001, format="%.6f", key=f"wp_lat_{w['uid']}")
                with c2:
                    w["lon"] = st.number_input("Lon", -180.0, 180.0, float(w.get("lon")), step=0.0001, format="%.6f", key=f"wp_lon_{w['uid']}")
                c1, c2, c3 = st.columns(3)
                with c1:
                    w["vor_pref"] = st.selectbox("VOR ref", ["AUTO", "FIXED", "NONE"], index=["AUTO", "FIXED", "NONE"].index(w.get("vor_pref", "AUTO")) if w.get("vor_pref", "AUTO") in ["AUTO", "FIXED", "NONE"] else 0, key=f"wp_vorpref_{w['uid']}")
                with c2:
                    w["vor_ident"] = st.text_input("VOR ident", w.get("vor_ident", ""), key=f"wp_vorid_{w['uid']}").upper()
                with c3:
                    st.caption(format_radial_dist(choose_vor_for_point(w), float(w["lat"]), float(w["lon"])))
                b1, b2, b3 = st.columns(3)
                with b1:
                    if st.button("↑", key=f"up_{w['uid']}", use_container_width=True) and idx > 0:
                        move = (idx, idx - 1)
                with b2:
                    if st.button("↓", key=f"down_{w['uid']}", use_container_width=True) and idx < len(st.session_state.wps) - 1:
                        move = (idx, idx + 1)
                with b3:
                    if st.button("Remover", key=f"rm_{w['uid']}", use_container_width=True):
                        remove_idx = idx
        if move:
            a, b = move
            st.session_state.wps[a], st.session_state.wps[b] = st.session_state.wps[b], st.session_state.wps[a]
            recalc_route()
            st.rerun()
        if remove_idx is not None:
            st.session_state.wps.pop(remove_idx)
            recalc_route()
            st.rerun()
        if st.session_state.wps:
            c1, c2 = st.columns(2)
            with c1:
                if st.button("Aplicar alterações e recalcular", type="primary", use_container_width=True):
                    recalc_route()
                    st.rerun()
            with c2:
                fpl = route_item15(st.session_state.wps)
                st.code(fpl or "—")

    st.markdown("---")
    st.markdown("#### Rotas padrão")
    st.caption("Guardar/carregar aqui evita voltar à aba de dados durante o planeamento.")
    if not st.session_state.saved_routes:
        st.session_state.saved_routes = load_routes_from_gist()
    routes = st.session_state.saved_routes
    rg1, rg2 = st.columns(2)
    with rg1:
        route_name = st.text_input("Guardar rota atual como", "", key="route_save_name")
        if st.button("Guardar rota padrão", use_container_width=True, key="route_save_btn"):
            if not route_name.strip():
                st.warning("Dá um nome à rota.")
            elif not st.session_state.wps:
                st.warning("Não há rota para guardar.")
            else:
                routes[route_name.strip()] = serialize_route()
                ok, msg = save_routes_to_gist(routes)
                st.session_state.saved_routes = routes
                st.success(msg) if ok else st.warning(msg)
    with rg2:
        names = sorted(routes.keys())
        choice = st.selectbox("Carregar rota padrão", [""] + names, key="route_load_choice")
        b_load, b_delete = st.columns(2)
        with b_load:
            if choice and st.button("Carregar", use_container_width=True, key="route_load_btn"):
                st.session_state.wps = []
                for item in routes.get(choice, []):
                    p = Point.from_dict(item)
                    p.uid = next_uid()
                    st.session_state.wps.append(p.to_dict())
                recalc_route()
                st.rerun()
        with b_delete:
            if choice and st.button("Apagar", use_container_width=True, key="route_delete_btn"):
                routes.pop(choice, None)
                ok, msg = save_routes_to_gist(routes)
                st.session_state.saved_routes = routes
                st.success(msg) if ok else st.warning(msg)

# ---------------------------------------------------------------
# MAP TAB
# ---------------------------------------------------------------
with tab_map:
    st.markdown("#### Mapa e pontos por clique")
    top = st.columns([0.9, 1.2, 0.9, 1.6])
    with top[0]:
        st.toggle("Mostrar pontos ref.", key="show_ref_points")
    with top[1]:
        st.multiselect("Camadas", ["IFR", "VOR", "AD", "VFR"], key="ref_layers")
    with top[2]:
        st.toggle("Mostrar airways", key="show_airways")
    with top[3]:
        st.multiselect("Airways", list_airways(), key="selected_airways", max_selections=12)
    st.caption("Mapa limpo: rota, pontos, airways opcionais e clique para adicionar novos waypoints.")

    out_map = render_route_map(st.session_state.wps, st.session_state.route_nodes, st.session_state.legs, key="map_tab")
    clicked = out_map.get("last_clicked") if out_map else None
    if clicked:
        with st.form("add_click_form"):
            st.markdown("##### Adicionar último clique")
            c1, c2, c3 = st.columns([2, 1, 1])
            with c1:
                nm = st.text_input("Nome", "WP CLICK")
            with c2:
                alt = st.number_input("Alt", 0.0, 45000.0, float(st.session_state.default_alt), step=100.0)
            with c3:
                st.caption(f"{clicked['lat']:.5f}, {clicked['lng']:.5f}")
            if st.form_submit_button("Adicionar clique"):
                p = Point(code=clean_code(nm) or "CLICK", name=nm, lat=float(clicked["lat"]), lon=float(clicked["lng"]), alt=float(alt), src="USER", uid=next_uid())
                st.session_state.wps.append(p.to_dict())
                recalc_route()
                st.rerun()

# ---------------------------------------------------------------
# NAVLOG/PDF TAB
# ---------------------------------------------------------------
with tab_navlog:
    st.markdown("#### 3 · Rever navlog e gerar PDF")
    if not st.session_state.legs:
        st.info("Cria uma rota e carrega em Recalcular/Gerar para ver o navlog.")
    else:
        df_legs = legs_to_dataframe(st.session_state.legs)
        st.dataframe(df_legs, use_container_width=True, hide_index=True)
        csv = df_legs.to_csv(index=False).encode("utf-8")
        st.download_button("⬇️ Navlog CSV", csv, file_name="navlog.csv", mime="text/csv")

        st.markdown("#### Cabeçalho para PDF")
        reg_options = REG_OPTIONS_PIPER if "Piper" in st.session_state.aircraft_type else REG_OPTIONS_TECNAM
        c0, c1, c2, c3, c4 = st.columns(5)
        with c0:
            callsign = st.text_input("Callsign", "RVP")
        with c1:
            registration = st.selectbox("Registration", reg_options)
        with c2:
            student = st.text_input("Student", "")
        with c3:
            lesson = st.text_input("Lesson", "")
        with c4:
            instructor = st.text_input("Instructor", "")
        c5, c6, c7, c8, c9 = st.columns(5)
        with c5:
            etd = st.text_input("ETD", "")
        with c6:
            eta = st.text_input("ETA", "")
        with c7:
            dept_freq = st.text_input("FREQ DEPT", "119.805")
        with c8:
            enroute_freq = st.text_input("FREQ ENROUTE", "123.755")
        with c9:
            arrival_freq = st.text_input("FREQ ARRIVAL", "131.675")
        c10, c11 = st.columns(2)
        suggested_alt = ""
        if st.session_state.route_nodes:
            alts = sorted({int(round(float(n.get("alt", 0)))) for n in st.session_state.route_nodes if float(n.get("alt", 0)) > 0})
            suggested_alt = "/".join(str(a) for a in alts[:4])
        with c10:
            fl_alt = st.text_input("FLIGHT_LEVEL_ALTITUDE", value=suggested_alt, help="Valor que entra no campo FLIGHT_LEVEL_ALTITUDE do formulário.")
        with c11:
            temp_isa = st.text_input("TEMP_ISA_DEV", value="ISA", help="Valor que entra no campo TEMP_ISA_DEV do formulário.")
        mag_txt = f"{abs(float(st.session_state.mag_var)):.1f}°{'E' if st.session_state.mag_is_east else 'W'}"
        st.caption(f"Campos automáticos para o PDF: WIND {int(st.session_state.wind_from):03d}/{int(st.session_state.wind_kt):02d} · MAG_VAR {mag_txt}")

        header = {
            "callsign": callsign,
            "registration": registration,
            "student": student,
            "lesson": lesson,
            "instructor": instructor,
            "etd": etd,
            "eta": eta,
            "dept_freq": dept_freq,
            "enroute_freq": enroute_freq,
            "arrival_freq": arrival_freq,
            "fl_alt": fl_alt,
            "temp_isa": temp_isa,
        }

        c1, c2, c3 = st.columns(3)
        with c1:
            if st.button("Gerar PDF NAVLOG", type="primary", use_container_width=True):
                if not TEMPLATE_MAIN.exists():
                    st.error("NAVLOG_FORM.pdf não existe no repo.")
                else:
                    payload = build_pdf_payload(st.session_state.legs, header, start=0, count=22)
                    fill_pdf(TEMPLATE_MAIN, OUTPUT_MAIN, payload)
                    st.success("PDF principal gerado.")
                    with open(OUTPUT_MAIN, "rb") as f:
                        st.download_button("⬇️ NAVLOG principal", f.read(), file_name="NAVLOG_FILLED.pdf", mime="application/pdf", use_container_width=True)
        with c2:
            if len(st.session_state.legs) > 22:
                if st.button("Gerar continuação", use_container_width=True):
                    if not TEMPLATE_CONT.exists():
                        st.error("NAVLOG_FORM_1.pdf não existe no repo.")
                    else:
                        payload = build_pdf_payload(st.session_state.legs, header, start=22, count=11)
                        fill_pdf(TEMPLATE_CONT, OUTPUT_CONT, payload)
                        with open(OUTPUT_CONT, "rb") as f:
                            st.download_button("⬇️ NAVLOG continuação", f.read(), file_name="NAVLOG_FILLED_1.pdf", mime="application/pdf", use_container_width=True)
            else:
                st.caption("Continuação só necessária acima de 22 legs.")
        with c3:
            if st.button("Gerar briefing PDF", use_container_width=True):
                rows = df_legs.to_dict("records")
                p = generate_briefing_pdf(OUTPUT_BRIEFING, rows)
                if p and p.exists():
                    with open(p, "rb") as f:
                        st.download_button("⬇️ Briefing legs", f.read(), file_name="NAVLOG_LEGS_BRIEFING.pdf", mime="application/pdf", use_container_width=True)
                else:
                    st.error("Instala reportlab para gerar o briefing PDF.")

# ---------------------------------------------------------------
# DATA TAB
# ---------------------------------------------------------------
with tab_data:
    st.markdown("#### 4 · Dados locais e rotas padrão")
    st.caption("Os CSVs IFR ficam no repositório. Só atualizas manualmente com tools/update_ifr_data.py quando quiseres.")
    st.markdown("#### Estado dos dados locais")
    rows = [
        {"Ficheiro": CSV_AD.name, "Existe": CSV_AD.exists(), "Uso": "VFR aeródromos/HEL/ULM"},
        {"Ficheiro": CSV_LOC.name, "Existe": CSV_LOC.exists(), "Uso": "Localidades / pontos VFR"},
        {"Ficheiro": CSV_VOR.name, "Existe": CSV_VOR.exists(), "Uso": "VOR/DME/NAVAIDS"},
        {"Ficheiro": CSV_IFR_POINTS.name, "Existe": CSV_IFR_POINTS.exists(), "Uso": "Pontos IFR ENR 4.4"},
        {"Ficheiro": CSV_IFR_AIRWAYS.name, "Existe": CSV_IFR_AIRWAYS.exists(), "Uso": "Sequências de airways ENR 3.3"},
        {"Ficheiro": TEMPLATE_MAIN.name, "Existe": TEMPLATE_MAIN.exists(), "Uso": "Template NAVLOG principal"},
        {"Ficheiro": TEMPLATE_CONT.name, "Existe": TEMPLATE_CONT.exists(), "Uso": "Template continuação"},
    ]
    st.dataframe(pd.DataFrame(rows), hide_index=True, use_container_width=True)
    st.markdown("#### Amostras")
    c1, c2 = st.columns(2)
    with c1:
        st.caption("Pontos IFR carregados")
        st.dataframe(POINTS_DF[POINTS_DF["src"] == "IFR"].head(100), use_container_width=True, hide_index=True)
    with c2:
        st.caption("Airways carregadas")
        st.dataframe(AIRWAYS_DF.head(120), use_container_width=True, hide_index=True)


# Footer warning
st.markdown(
    """
<hr>
<div class='small-muted'>
Ferramenta de planeamento. Confirma sempre cartas, NOTAM, AIP/AIRAC, meteorologia, mínimos IFR/VFR, autorizações ATC e performance real da aeronave antes do voo.
</div>
""",
    unsafe_allow_html=True,
)
