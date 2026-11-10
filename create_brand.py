#!/usr/bin/env python3
"""OBranding brand creation automation.

Requirements:
    python -m pip install requests Pillow pillow-avif-plugin pymupdf opencv-python rapidocr-onnxruntime
    Use the same Python interpreter to install dependencies and run this script.
    pillow-avif-plugin provides AVIF decoding when Pillow lacks native support.

Data files (place in same folder as this script):
    city.txt     – JSON list [{"name": "...", "id": "..."}]
    category.txt – JSON list [{"id": N, "name": "..."}]
    benefit.txt  – JSON list [{"type": "...", "description": "..."}]

Image folders (place in same folder as this script):
    1/  – logo (square ~1:1) and banner (wide ~3:1)  → overwritten after compress
    2/  – gallery images or ZIP archives              → overwritten after compress

Google Sheet sources (same column layout required):
    https://docs.google.com/spreadsheets/d/13qeFPvCeI7qQfVkCFzk-rL_9ptaOg13HQswdWXs-PSQ
    https://docs.google.com/spreadsheets/d/1weqiVHMJE8g9rxVrEGITEd405YmB2NhCbKL0s9POkgI
    Prefer the BASE "NGUYÊN LIỆU" link; otherwise search old, then new.
    Match a BASE name's numeric prefix to Column B before matching names in Column C.
    Prefixes/STT values are identifiers, not physical sheet row numbers.
    Fall back only when the brand/row is missing; do not merge missing fields.
    Column N gallery links support plain URLs, embedded hyperlinks, and Drive smart chips.
    Address processing expands common KDC/KĐT/KP/TDP abbreviations and infers missing
    street and locality prefixes from the address structure. Administrative prefixes
    such as TP., P., X., T., H., Q., TX., and TT. are expanded before inference.
    Empty trailing Facebook labels are removed without discarding the address.
    House numbers support letter-prefixed slash segments (781/D7); numbered
    streets after building/project details also receive a missing street prefix.
    Numbered locality labels are not treated as streets; an erroneous
    street prefix before an Ap hamlet label is removed.
    Social links are read from the sheet and discovered from the brand homepage;
    homepage links are read from HTML and JSON-LD sameAs metadata, and
    sheet-provided links take precedence when both sources contain a platform.
    All ten social platforms are checked before creation. Explicit unavailable
    pages are skipped; blocked, login-only, or otherwise inconclusive checks are
    retained with a warning and their cleaned brand URLs opened after the website.
    Inconclusive checks fall back to locally installed Chrome or Edge in headless
    mode; browser or network failures do not prove an account is missing.
    Website links using the misspelled instgram.com host are corrected to
    instagram.com with a warning before checking them.
    Facebook page widgets supply profile links through data-href; generic
    facebook.com/facebook links are not treated as brand profiles.
    Facebook page iframe embeds (src or lazy-loaded data-src) supply profile links through their encoded
    href query parameter; plugin URLs themselves are not brand profiles.
    Facebook /messages/t/<recipient> and Messenger /t/<recipient> links are
    converted to profile homepages before creation; numeric recipients resolve
    to public usernames when possible, otherwise the ID-based profile homepage
    is used with a warning.
    LinkedIn company, person, and school links use https://www.linkedin.com
    and retain only the profile identifier, with a trailing slash, including
    links passed directly to the browser for review.
    TikTok verification uses matching account data or an unavailable message.
    Public sheets work without authentication. For private sheets, place a Google
    Desktop OAuth client configuration in client.json beside this script and run:
        python -m pip install google-auth google-auth-oauthlib
    Enable Google Sheets API in that client's Cloud project. On first access,
    sign in with an account that can view the sheet (add it as an OAuth test user
    if the app is in Testing). Only read-only spreadsheet permission is requested.
    Tokens are stored in %LOCALAPPDATA%\\CreateBrand\\google-token.json, not here.
    Gallery Drive downloads use Desktop OAuth with support@obranding.vn.
    Enable Google Drive API in the same Cloud project and add this account as
    an OAuth test user if needed. On first gallery download, select this account
    in the browser and grant read-only Drive access. The account is verified;
    /u/2/ in a Drive URL does not authenticate the script.
    Gallery tokens are stored separately in
    %LOCALAPPDATA%\\CreateBrand\\google-drive-support-token.json.
    Drive folders, nested folders, and individual files are downloaded through
    the Drive API; logo/banner downloads retain their public-download behavior.
    Keep client.json and the token private; do not commit or share either file.
    External Testing apps may require signing in again after seven days.
"""

from __future__ import annotations

import colorsys
import base64
import binascii
import csv
import datetime
import html
import io
import json
import mimetypes
import re
import shutil
import subprocess
import sys
import os
import tempfile
import threading
import time
import unicodedata
import xml.etree.ElementTree as ET
import zipfile
from concurrent.futures import ThreadPoolExecutor, as_completed
from importlib import import_module
from html.parser import HTMLParser
from pathlib import Path
from urllib.parse import urljoin, urlparse, urlunparse, parse_qs, urlencode, quote

import ssl

try:
    import requests
    from requests.adapters import HTTPAdapter
    from urllib3.util.retry import Retry
except ImportError:
    sys.exit("Missing dependency. Run: pip install requests Pillow")

try:
    from PIL import Image, ImageFile, UnidentifiedImageError
    ImageFile.LOAD_TRUNCATED_IMAGES = True
    Image.MAX_IMAGE_PIXELS = None
except ImportError:
    sys.exit("Missing dependency. Run: pip install requests Pillow pymupdf")

try:
    import_module("pillow_avif")
except ImportError:
    pass

Image.init()
_avif_available = "AVIF" in Image.OPEN

try:
    import pymupdf as fitz
except ImportError:
    sys.exit("Missing dependency. Run: pip install pymupdf")

try:
    import cv2
    import numpy as np
except ImportError:
    cv2 = None
    np = None

try:
    from rapidocr_onnxruntime import RapidOCR
    _rapid_ocr = RapidOCR()
except Exception:
    _rapid_ocr = None

try:
    import gdown
except ImportError:
    gdown = None

try:
    import bs4
except ImportError:
    bs4 = None


def _make_session() -> requests.Session:
    """Shared session with retry logic and a relaxed SSL context to handle SSLEOFError."""
    session = requests.Session()
    ctx = ssl.create_default_context()
    try:
        ctx.set_ciphers("DEFAULT:@SECLEVEL=1")
    except ssl.SSLError:
        pass
    if hasattr(ssl, "OP_LEGACY_SERVER_CONNECT"):  # Python 3.12+
        ctx.options |= ssl.OP_LEGACY_SERVER_CONNECT

    class _SSLAdapter(HTTPAdapter):
        def init_poolmanager(self, *args, **kwargs):
            kwargs["ssl_context"] = ctx
            super().init_poolmanager(*args, **kwargs)

    retry = Retry(total=3, backoff_factor=1, status_forcelist=[502, 503, 504])
    adapter = _SSLAdapter(max_retries=retry)
    session.mount("https://", adapter)
    session.mount("http://", adapter)
    return session


_session = _make_session()

# ---------------------------------------------------------------------------
# Constants
# ---------------------------------------------------------------------------

SHEET_ID  = "13qeFPvCeI7qQfVkCFzk-rL_9ptaOg13HQswdWXs-PSQ"
SHEET_GID = "491738540"
FALLBACK_SHEET_ID = "1weqiVHMJE8g9rxVrEGITEd405YmB2NhCbKL0s9POkgI"
SCRIPT_DIR = Path(__file__).parent

# ---------------------------------------------------------------------------
# Terminal UI Formatting
# ---------------------------------------------------------------------------
if os.name == "nt":
    os.system("")  # Enable ANSI escape codes in Windows Command Prompt/PowerShell
    if hasattr(sys.stdout, "reconfigure"):
        try:
            sys.stdout.reconfigure(encoding="utf-8")
        except Exception:
            pass
    if hasattr(sys.stderr, "reconfigure"):
        try:
            sys.stderr.reconfigure(encoding="utf-8")
        except Exception:
            pass

class Colors:
    # Pastel colors using 256-color palette
    HEADER = "\033[38;5;183m"    # Pastel purple
    BLUE = "\033[38;5;117m"      # Pastel blue
    CYAN = "\033[38;5;159m"      # Pastel cyan
    GREEN = "\033[38;5;157m"     # Softer pastel green
    YELLOW = "\033[38;5;229m"    # Pastel yellow
    PINK = "\033[38;5;218m"      # Pastel pink
    PEACH = "\033[38;5;223m"     # Pastel peach
    WARNING = "\033[38;5;222m"   # Pastel orange
    FAIL = "\033[38;5;210m"      # Pastel red
    END = "\033[0m"
    BOLD = "\033[1m"

def print_header(title: str) -> None:
    border = "═" * 80
    print(f"\n{Colors.HEADER}{Colors.BOLD}{border}")
    print(f"  {title}")
    print(f"{border}{Colors.END}")

def print_step(step_name: str) -> None:
    border = "─" * 80
    print(f"\n{Colors.CYAN}{Colors.BOLD}{step_name}")
    print(f"{border}{Colors.END}")

def print_success(msg: str) -> None:
    print(f"  {Colors.GREEN}✔ {msg}{Colors.END}")

def print_info(msg: str) -> None:
    print(f"  {Colors.BLUE}ℹ {msg}{Colors.END}")

def print_warn(msg: str) -> None:
    print(f"  {Colors.WARNING}⚠ {msg}{Colors.END}")

def print_fail(msg: str) -> None:
    print(f"  {Colors.FAIL}❌ {msg}{Colors.END}")

def open_in_chrome(*urls: str) -> None:
    """Open URLs in Chrome as new tabs, one by one, preserving left-to-right order."""
    urls = tuple(
        _clean_social_url(u) if _social_platform_for_url(u) == "linkedin" else u
        for u in urls if u
    )
    if not urls:
        return
    chrome_paths = [
        os.path.expandvars(r"%ProgramFiles%\Google\Chrome\Application\chrome.exe"),
        os.path.expandvars(r"%ProgramFiles(x86)%\Google\Chrome\Application\chrome.exe"),
        os.path.expandvars(r"%LOCALAPPDATA%\Google\Chrome\Application\chrome.exe"),
    ]
    chrome_exe = next((p for p in chrome_paths if os.path.isfile(p)), None)
    try:
        if chrome_exe:
            for url in urls:
                subprocess.Popen([chrome_exe, url], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
                time.sleep(0.3)
            print_success(f"Opened {len(urls)} tab(s) in Chrome.")
            return
        for url in urls:
            os.startfile(url)
            time.sleep(0.3)
        print_success(f"Opened {len(urls)} tab(s) in the default browser.")
    except OSError as exc:
        print_warn(f"Could not open browser: {exc}")


def _brand_review_tabs(
    brand_edit_url: str, homepage_url: str, social_review_urls: list[str],
    benefit_edit_url: str, brand_url: str,
) -> tuple[str, ...]:
    return (brand_edit_url, homepage_url, *social_review_urls, benefit_edit_url, brand_url)


def copy_to_clipboard(text: str) -> None:
    """Copy text to the system clipboard (Windows / macOS / Linux)."""
    try:
        if sys.platform == "win32":
            subprocess.run(
                ["powershell", "-NoProfile", "-Command", f"Set-Clipboard -Value {json.dumps(text)}"],
                check=True,
                capture_output=True,
            )
        elif sys.platform == "darwin":
            subprocess.run(["pbcopy"], input=text.encode("utf-8"), check=True)
        else:
            subprocess.run(
                ["xclip", "-selection", "clipboard"],
                input=text.encode("utf-8"),
                check=True,
            )
        print_success("Brand URL copied to clipboard.")
    except Exception as exc:
        print_warn(f"Could not copy to clipboard: {exc}")


ENVIRONMENTS = {
    "1": ("stg",  "stg-b2c.obranding.vn"),
    "2": ("prod", "obranding.vn"),
}

_SOCIAL_DOMAINS = [
    ("facebook.com",   "facebook"),
    ("messenger.com",  "facebook"),
    ("fb.me",          "facebook"),
    ("t.me",           "telegram"),
    ("telegram.me",    "telegram"),
    ("linkedin.com",   "linkedin"),
    ("youtube.com",    "youtube"),
    ("reddit.com",     "reddit"),
    ("twitter.com",    "twitter"),
    ("x.com",          "twitter"),
    ("discord.com",    "discord"),
    ("discord.gg",     "discord"),
    ("instagram.com",  "instagram"),
    ("tiktok.com",     "tiktok"),
    ("substack.com",   "substack"),
]

_SOCIAL_ACTION_PATHS: dict[str, set[str]] = {
    "facebook": {"share", "share_channel", "share.php", "sharer", "sharer.php", "sharing", "compose", "intent", "dialog", "l.php", "tr", "permalink", "permalink.php"},
    "instagram": {"share", "sharing", "compose"},
    "linkedin": {"share", "sharing", "sharearticle", "compose", "feed"},
    "reddit": {"share", "submit", "submit-link"},
    "telegram": {"share", "sharing", "joinchat", "addstickers", "addemoji", "proxy", "s"},
    "twitter": {"share", "sharing", "compose", "intent"},
    "tiktok": {"share"},
    "youtube": {"share"},
    "substack": {"share", "sharing", "subscribe", "redirect", "publish"},
    "discord": {"invite", "invites"},
}

ALL_SOCIALS = [
    "facebook", "telegram", "linkedin", "youtube",
    "reddit", "twitter", "discord", "instagram", "tiktok", "substack",
]

IMG_EXTS = {".jpg", ".jpeg", ".jfif", ".png", ".webp", ".bmp", ".gif", ".avif"}

# Extensions that are explicitly NOT gallery images.
_NON_IMAGE_EXTS = {
    ".mp4", ".mov", ".avi", ".mkv", ".wmv", ".flv",  # video
    ".pdf", ".doc", ".docx", ".xls", ".xlsx",         # documents
    ".zip", ".rar", ".7z",                             # archives
    ".psd", ".ai", ".eps", ".svg",                     # design files
}


def _normalize_vietnamese(s: str) -> str:
    """Normalize string by lowercasing, removing Vietnamese accents, and collapsing spaces."""
    if not s:
        return ""
    s = s.lower().strip()
    s = unicodedata.normalize("NFD", s)
    s = "".join(c for c in s if unicodedata.category(c) != "Mn")
    s = s.replace("đ", "d").replace("Đ", "d")
    s = re.sub(r"[^\w\s]", " ", s)
    s = re.sub(r"\s+", " ", s).strip()
    return s


def _is_gpkd_or_dkkd(s: str | Path) -> bool:
    """Return True if filename indicates a business registration or business license document
    (GPKD, ĐKKD, Đăng ký kinh doanh, Giấy phép kinh doanh, etc.) which should be excluded from gallery."""
    if isinstance(s, Path):
        s = s.name
    if not s:
        return False
    cleaned = str(s).replace("_", " ").replace("-", " ")
    norm = _normalize_vietnamese(cleaned)
    compact = norm.replace(" ", "")

    phrases = (
        "dang ky kinh doanh",
        "dang ky kd",
        "dang ky ho kinh doanh",
        "dang ky doanh nghiep",
        "giay phep kinh doanh",
        "giay phep kd",
        "giay chung nhan dang ky",
        "gpkd",
        "dkkd",
    )
    if any(p in norm for p in phrases):
        return True

    compact_tokens = (
        "dangkykinhdoanh",
        "dangkykd",
        "dangkyhokinhdoanh",
        "dangkeydoanhnghiep",
        "giayphepkinhdoanh",
        "giayphepkd",
        "giaychungnhandangky",
        "gpkd",
        "dkkd",
    )
    if any(ct in compact for ct in compact_tokens):
        return True

    return False


# ---------------------------------------------------------------------------
# Setup helpers
# ---------------------------------------------------------------------------

def prompt_env() -> tuple[str, str]:
    """Returns (env_key, root_domain)."""
    while True:
        print(f"\n{Colors.HEADER}{Colors.BOLD}{'─' * 80}{Colors.END}")
        print(f"{Colors.HEADER}{Colors.BOLD}🌐 Choose environment:{Colors.END}")
        print(f"{Colors.HEADER}{Colors.BOLD}{'─' * 80}{Colors.END}")
        print(f"  {Colors.GREEN}[1] STG{Colors.END}  → https://stg-b2c.obranding.vn/")
        print(f"  {Colors.GREEN}[2] PROD{Colors.END} → https://obranding.vn/")
        c = input(f"\n  {Colors.BOLD}Enter 1 or 2: {Colors.END}").strip()
        if c in ENVIRONMENTS:
            return ENVIRONMENTS[c]
        print_fail("Invalid choice.")


OBRANDING_AUTH_FILE = SCRIPT_DIR / ".obranding_auth.json"


def prompt_token(env_name: str, force_new: bool = False) -> str:
    cache_file = OBRANDING_AUTH_FILE
    today = datetime.date.today().isoformat()
    cache_data = {}
    if cache_file.exists():
        try:
            cache_data = json.loads(cache_file.read_text(encoding="utf-8"))
            if "date" in cache_data and "token" in cache_data:
                cache_data = {}
                
            env_cache = cache_data.get(env_name, {})
            if not force_new and env_cache.get("date") == today and env_cache.get("token"):
                print_info(f"Using cached token for today ({env_name.upper()}).")
                return env_cache["token"]
        except Exception:
            cache_data = {}

    while True:
        t = input(f"  {Colors.BOLD}🔑 Enter bearer token ({env_name.upper()}): {Colors.END}").strip()
        if t:
            token = t.removeprefix("Bearer ").strip()
            cache_data[env_name] = {"date": today, "token": token}
            try:
                cache_file.write_text(json.dumps(cache_data), encoding="utf-8")
            except Exception as e:
                print_warn(f"Could not save token cache: {e}")
            return token
        print_fail("Token cannot be empty.")


def _headers(token: str) -> dict:
    return {
        "authorization": f"Bearer {token}",
        "accept": "application/json",
        "content-type": "application/json",
        "locale": "vn",
    }


def load_json(filename: str) -> list:
    p = SCRIPT_DIR / filename
    if not p.exists():
        print_warn(f"{filename} not found – returning empty list.")
        return []
    return json.loads(p.read_text(encoding="utf-8-sig"))

# ---------------------------------------------------------------------------
# Google Sheets
# ---------------------------------------------------------------------------

_sheet_rows_cache: dict[tuple[str, str], tuple[float, list[list[str]]]] = {}
_google_sheet_session: requests.Session | None = None
_google_drive_session: requests.Session | None = None
GOOGLE_DRIVE_ACCOUNT = "support@obranding.vn"


def _get_google_sheet_session() -> requests.Session:
    """Create a dedicated OAuth session; never attach Google tokens to other APIs."""
    global _google_sheet_session
    if _google_sheet_session is not None:
        return _google_sheet_session
    _google_sheet_session = _get_google_oauth_session(
        ["https://www.googleapis.com/auth/spreadsheets.readonly"],
        "google-token.json",
        "Opening Google sign-in. Choose an account with access to the private spreadsheet.",
    )
    return _google_sheet_session


def _get_google_drive_session() -> requests.Session:
    """Use a separate, account-verified read-only OAuth session for gallery downloads."""
    global _google_drive_session
    if _google_drive_session is None:
        _google_drive_session = _get_google_oauth_session(
            ["https://www.googleapis.com/auth/drive.readonly"],
            "google-drive-support-token.json",
            f"Opening Google sign-in. Choose {GOOGLE_DRIVE_ACCOUNT} to download gallery images.",
            required_email=GOOGLE_DRIVE_ACCOUNT,
        )
    return _google_drive_session


def _get_google_oauth_session(
    scopes: list[str], token_filename: str, sign_in_message: str,
    required_email: str | None = None,
) -> requests.Session:
    client_path = SCRIPT_DIR / "client.json"
    try:
        credentials_module = import_module("google.oauth2.credentials")
        transport = import_module("google.auth.transport.requests")
        flow_module = import_module("google_auth_oauthlib.flow")
        auth_exceptions = import_module("google.auth.exceptions")
    except ImportError as exc:
        raise RuntimeError(
            f"Google OAuth import failed: {exc}. In PowerShell, run: "
            f'& "{sys.executable}" -m pip install google-auth google-auth-oauthlib'
        ) from exc

    token_dir = Path(os.environ.get("LOCALAPPDATA") or (Path.home() / ".config")) / "CreateBrand"
    token_path = token_dir / token_filename
    credentials = None
    if token_path.exists():
        credentials = credentials_module.Credentials.from_authorized_user_file(str(token_path))
        if not credentials.has_scopes(scopes):
            print_warn("Cached Google authorization lacks the required permissions. Please sign in again.")
            credentials = None

    def account_matches(session: requests.Session) -> bool:
        response = _google_drive_api_get(
            session, "about", params={"fields": "user/emailAddress"},
        )
        email = response.json().get("user", {}).get("emailAddress", "")
        return email.casefold() == (required_email or "").casefold()

    if credentials is None or not credentials.valid:
        if credentials and credentials.expired and credentials.refresh_token:
            try:
                credentials.refresh(transport.Request())
            except auth_exceptions.RefreshError:
                print_warn("Google authorization expired or was revoked. Please sign in again.")
                credentials = None
    if credentials and credentials.valid and required_email:
        with transport.AuthorizedSession(credentials) as check_session:
            if not account_matches(check_session):
                print_warn(f"Cached Google account is not {required_email}. Please select the required account.")
                credentials = None
    if credentials is None or not credentials.valid:
        if not client_path.exists():
            raise RuntimeError("Place a Google Desktop OAuth client configuration in client.json beside this script.")
        print_info(sign_in_message)
        flow = flow_module.InstalledAppFlow.from_client_secrets_file(str(client_path), scopes)
        login_options = {"login_hint": required_email} if required_email else {}
        credentials = flow.run_local_server(
            host="localhost", port=0, access_type="offline",
            prompt="consent select_account" if required_email else "consent",
            timeout_seconds=180, **login_options,
        )
        if required_email:
            with transport.AuthorizedSession(credentials) as check_session:
                if not account_matches(check_session):
                    raise RuntimeError(
                        f"Wrong Google account selected. Run again and sign in as {required_email}. "
                        "The incorrect account token was not saved."
                    )
    token_dir.mkdir(parents=True, exist_ok=True)
    token_path.write_text(credentials.to_json(), encoding="utf-8")
    return transport.AuthorizedSession(credentials)


def _google_drive_api_get(
    session: requests.Session, endpoint: str, *,
    params: dict | None = None, stream: bool = False,
) -> requests.Response:
    response = session.get(
        f"https://www.googleapis.com/drive/v3/{endpoint}",
        params=params, stream=stream, timeout=30,
    )
    if response.status_code in (401, 403, 404):
        status = response.status_code
        response.close()
        raise RuntimeError(
            f"Google Drive request failed (HTTP {status}, {endpoint}). "
            f"Enable Google Drive API in the client.json Cloud project, sign in as "
            f"{GOOGLE_DRIVE_ACCOUNT}, and ensure that account can view and download the item. "
            "Also check OAuth permissions and any owner download restrictions."
        )
    response.raise_for_status()
    return response


def _fetch_google_sheet_data(sheet_id: str, sheet_gid: str) -> list[list[str]]:
    """Read formatted cells and rich-text links for the exact tab through Sheets API."""
    session = _get_google_sheet_session()
    url = f"https://sheets.googleapis.com/v4/spreadsheets/{sheet_id}"
    metadata = session.get(url, params={"fields": "sheets.properties"}, timeout=30)
    if metadata.status_code in (401, 403):
        raise RuntimeError(
            "Google Sheets access denied. Enable Google Sheets API in your OAuth project "
            "and sign in with an account that has Viewer access to this spreadsheet."
        )
    metadata.raise_for_status()
    selected = next((
        sheet["properties"] for sheet in metadata.json().get("sheets", [])
        if str(sheet["properties"]["sheetId"]) == sheet_gid
    ), None)
    if selected is None:
        raise ValueError(f"Tab gid={sheet_gid} does not exist in spreadsheet {sheet_id}.")
    title = selected["title"].replace("'", "''")
    response = session.get(
        url, params={
            "ranges": f"'{title}'",
            "includeGridData": "true",
            "fields": "sheets(data(startRow,startColumn,rowData(values(formattedValue,hyperlink,textFormatRuns,chipRuns))))",
        }, timeout=30,
    )
    response.raise_for_status()
    rows: list[list[str]] = []
    links: dict[str, str] = {}
    for sheet in response.json().get("sheets", []):
        for grid in sheet.get("data", []):
            start_col = grid.get("startColumn", 0)
            for idx, row_data in enumerate(grid.get("rowData", []), grid.get("startRow", 0)):
                while len(rows) <= idx:
                    rows.append([])
                cells = row_data.get("values", [])
                rows[idx] = [""] * start_col + [cell.get("formattedValue", "") for cell in cells]
                for col_idx, cell in enumerate(cells, start_col + 1):
                    urls = [cell["hyperlink"]] if cell.get("hyperlink") else []
                    for run in cell.get("textFormatRuns", []):
                        uri = run.get("format", {}).get("link", {}).get("uri")
                        if uri and uri not in urls:
                            urls.append(uri)
                    for run in cell.get("chipRuns", []):
                        uri = run.get("chip", {}).get("richLinkProperties", {}).get("uri")
                        if uri and uri not in urls:
                            urls.append(uri)
                    if urls:
                        letters = ""
                        column = col_idx
                        while column:
                            column, remainder = divmod(column - 1, 26)
                            letters = chr(65 + remainder) + letters
                        links[f"{letters}{idx + 1}"] = "\n".join(urls)
    key = (sheet_id, sheet_gid)
    now = time.time()
    _sheet_rows_cache[key] = (now, rows)
    _sheet_hyperlinks_cache[key] = (now, links)
    return rows


def _strip_parenthetical_postfix(name: str) -> str:
    """Remove a trailing parenthetical suffix from a brand name.

    Examples:
        'BỘT NGŨ CỐC KHÁNH GIANG (HỘ KINH DOANH SẢN XUẤT KHÁNH GIANG)'
            → 'BỘT NGŨ CỐC KHÁNH GIANG'
        'CÔNG TY TNHH ABC (CÔNG TY ABC)'  → 'CÔNG TY TNHH ABC'
    """
    return re.sub(r"\s*\([^)]*\)\s*$", "", name).strip()


def fetch_all_sheet_rows(
    force_refresh: bool = False, *, sheet_id: str = SHEET_ID, sheet_gid: str = SHEET_GID,
) -> list[list[str]]:
    """Fetch formatted rows with OAuth when client.json exists, otherwise public CSV."""
    key = (sheet_id, sheet_gid)
    now = time.time()
    cached = _sheet_rows_cache.get(key)
    if not force_refresh and cached is not None and now - cached[0] < 60:
        return cached[1]
    if (SCRIPT_DIR / "client.json").exists():
        return _fetch_google_sheet_data(sheet_id, sheet_gid)

    url = (
        f"https://docs.google.com/spreadsheets/d/{sheet_id}/export"
        f"?format=csv&gid={sheet_gid}"
    )
    resp = _session.get(url, timeout=30)
    if resp.status_code in (401, 403) or "accounts.google.com" in resp.url:
        raise RuntimeError(
            f"Cannot access sheet {sheet_id} (gid={sheet_gid}). Make sure it is set to "
            "'Anyone with the link can view', or configure client.json for Google OAuth."
        )
    resp.raise_for_status()
    rows = list(csv.reader(io.StringIO(resp.content.decode("utf-8-sig"))))
    _sheet_rows_cache[key] = (now, rows)
    return rows


def fetch_row(
    row_num: int, *, sheet_id: str = SHEET_ID, sheet_gid: str = SHEET_GID,
) -> list[str]:
    """Fetch 1-indexed row from Google Sheet as CSV."""
    rows = fetch_all_sheet_rows(sheet_id=sheet_id, sheet_gid=sheet_gid)
    if not (1 <= row_num <= len(rows)):
        raise ValueError(f"Row {row_num} out of range (sheet has {len(rows)} rows).")
    return rows[row_num - 1]


_sheet_hyperlinks_cache: dict[tuple[str, str], tuple[float, dict[str, str]]] = {}


def fetch_cell_hyperlink(
    row_num: int, col_letter: str = "N", force_refresh: bool = False, *,
    sheet_id: str = SHEET_ID, sheet_gid: str = SHEET_GID,
) -> str | None:
    """Fetch embedded links or Drive smart chips through OAuth, or public XLSX hyperlinks.

    Useful when a Google Sheet cell has display text (like 'HỘ KINH DOANH...') with an embedded URL
    which is stripped out by standard CSV export.
    """
    key = (sheet_id, sheet_gid)
    now = time.time()

    cached = _sheet_hyperlinks_cache.get(key)
    if not force_refresh and cached is not None and now - cached[0] < 60:
        return cached[1].get(f"{col_letter.upper()}{row_num}")
    if (SCRIPT_DIR / "client.json").exists():
        _fetch_google_sheet_data(sheet_id, sheet_gid)
        return _sheet_hyperlinks_cache[key][1].get(f"{col_letter.upper()}{row_num}")

    try:
        url = f"https://docs.google.com/spreadsheets/d/{sheet_id}/export?format=xlsx&gid={sheet_gid}"
        resp = _session.get(url, timeout=30)
        resp.raise_for_status()

        zf = zipfile.ZipFile(io.BytesIO(resp.content))

        wb_xml = zf.read("xl/workbook.xml")
        wb_root = ET.fromstring(wb_xml)
        ns_main = {"main": "http://schemas.openxmlformats.org/spreadsheetml/2006/main"}

        rels_xml = zf.read("xl/_rels/workbook.xml.rels")
        rels_root = ET.fromstring(rels_xml)
        rel_ns = {"rel": "http://schemas.openxmlformats.org/package/2006/relationships"}
        rel_map = {
            rel.attrib["Id"]: rel.attrib["Target"]
            for rel in rels_root.findall(".//rel:Relationship", rel_ns)
        }

        hyperlinks_map: dict[str, str] = {}
        sheets = wb_root.findall(".//main:sheet", ns_main)
        # XLSX exports can include every tab. Identify the selected tab from its CSV row.
        selected_row = fetch_row(row_num, sheet_id=sheet_id, sheet_gid=sheet_gid)
        shared_strings = []
        if "xl/sharedStrings.xml" in zf.namelist():
            strings_root = ET.fromstring(zf.read("xl/sharedStrings.xml"))
            shared_strings = [
                "".join(t.text or "" for t in item.findall(".//main:t", ns_main))
                for item in strings_root.findall("main:si", ns_main)
            ]
        matching_maps = []

        for s in sheets:
            r_id = s.attrib.get("{http://schemas.openxmlformats.org/officeDocument/2006/relationships}id")
            if not r_id or r_id not in rel_map:
                continue
            target_path = rel_map[r_id]
            sheet_target = target_path.lstrip("/") if target_path.startswith("/") else "xl/" + target_path
            sheet_file = sheet_target.split("/")[-1]
            sheet_rels_target = f"xl/worksheets/_rels/{sheet_file}.rels"

            rels_data = {}
            if sheet_rels_target in zf.namelist():
                srels_root = ET.fromstring(zf.read(sheet_rels_target))
                for rel in srels_root.findall(".//rel:Relationship", rel_ns):
                    rels_data[rel.attrib["Id"]] = rel.attrib.get("Target", "")

            if sheet_target in zf.namelist():
                s_xml = zf.read(sheet_target)
                s_root = ET.fromstring(s_xml)
                if len(sheets) > 1:
                    values = {}
                    for cell in s_root.findall(f".//main:row[@r='{row_num}']/main:c", ns_main):
                        value = cell.findtext("main:v", "", ns_main)
                        if cell.attrib.get("t") == "s":
                            value = shared_strings[int(value)]
                        elif cell.attrib.get("t") == "inlineStr":
                            value = "".join(t.text or "" for t in cell.findall(".//main:t", ns_main))
                        values[cell.attrib.get("r")] = value.strip()
                    if not _cell(selected_row, 2) or any(
                        values.get(f"{col}{row_num}", "") != _cell(selected_row, idx)
                        for col, idx in (("C", 2), ("N", 13))
                    ):
                        continue
                hyperlinks_map = {}
                for hl in s_root.findall(".//main:hyperlink", ns_main):
                    ref = hl.attrib.get("ref", "")
                    r_hl_id = hl.attrib.get("{http://schemas.openxmlformats.org/officeDocument/2006/relationships}id", "")
                    target = rels_data.get(r_hl_id, "")
                    if ref and target:
                        cell_key = ref.split(":")[0].upper()
                        hyperlinks_map[cell_key] = target
                matching_maps.append(hyperlinks_map)

        if len(matching_maps) != 1:
            raise ValueError(f"Cannot uniquely identify tab gid={sheet_gid} in XLSX export.")
        hyperlinks_map = matching_maps[0]
        _sheet_hyperlinks_cache[key] = (now, hyperlinks_map)
        return hyperlinks_map.get(f"{col_letter.upper()}{row_num}")
    except Exception as e:
        print_warn(f"Failed to fetch embedded cell hyperlink: {e}")
        return None


def _cell(row: list[str], idx: int) -> str:
    v = row[idx].strip() if idx < len(row) else ""
    # Treat placeholder text as empty
    if re.search(r"đang\s+cập\s+nhật", v, flags=re.IGNORECASE):
        return ""
    return v


def _format_phone(number: str) -> str:
    """Format a single Vietnamese phone number.

    Redundant leading zeros are stripped first so that padded inputs like
    '000392773199' or '001900558824' are normalised before formatting.

    After stripping, the number of significant digits determines the format:
      • 8 digits  → XXXX XXXX          (1900 / 1800 toll-free hotlines)
      • 10 digits → XXXX XXX XXX       (standard Vietnamese mobile/landline)
      • 11 digits → XXXX XXXX XXX      (old 11-digit format)

    Examples:
        '000019000053' → '1900 0053'
        '000392773199' → '0392 773 199'
        '001900558824' → '1900 558 824'
    """
    digits = "".join(c for c in number if c.isdigit())
    # Strip redundant leading zeros.
    # Toll-free hotlines (1900, 1800, …) start with '1' and carry no leading zero.
    # Vietnamese mobile/landline numbers (03x, 07x, 08x, 09x, …) carry exactly
    # one leading '0'.  Spreadsheet cells often pad numbers with extra leading
    # zeros (e.g. '000392773199') – strip all of them first, then restore the
    # correct prefix.
    stripped = digits.lstrip("0")
    if not stripped:
        # All-zero input – keep as-is (fall through to unrecognised format).
        pass
    elif stripped[0] == "1":
        # Toll-free hotline (1900 / 1800): no leading zero needed.
        digits = stripped
    else:
        # Mobile / landline: must start with exactly one '0'.
        digits = "0" + stripped

    if len(digits) == 8:
        return f"{digits[:4]} {digits[4:]}"
    if len(digits) == 10:
        return f"{digits[:4]} {digits[4:7]} {digits[7:]}"
    if len(digits) == 11:
        return f"{digits[:4]} {digits[4:8]} {digits[8:]}"
    return number.strip()  # unrecognised format – keep as-is


def _format_phones(raw: str) -> str:
    """Split on common separators, format each number, re-join with ' - '."""
    parts = re.split(r"[\-\/,;\n]+", raw)
    formatted = [_format_phone(p) for p in parts if p.strip()]
    return " - ".join(formatted)


def _parse_emails(raw: str) -> list[str]:
    """Extract individual email addresses from raw text, preserving order and removing duplicates.
    Splits on common separators such as semicolons, commas, slashes, or newlines."""
    if not raw:
        return []
    parts = re.split(r"[\r\n;,/]+", raw)
    emails: list[str] = []
    seen: set[str] = set()
    for p in parts:
        for token in p.strip().split():
            clean = token.strip().strip("<>(),;:\"'")
            if "@" in clean:
                lower = clean.lower()
                if lower not in seen:
                    seen.add(lower)
                    emails.append(clean)
    return emails


def _format_emails(raw: str) -> str:
    """Split on common separators, clean each email, re-join with ' - '."""
    emails = _parse_emails(raw)
    return " - ".join(emails)



def _normalize_url(url: str) -> str:
    """Ensure a URL has a scheme (https://).  Bare domains like 'olatacos.com' become 'https://olatacos.com'."""
    if not url:
        return url
    if not re.match(r"https?://", url, re.IGNORECASE):
        url = "https://" + url
    return url


_BROWSER_HEADERS = {
    "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/122.0.0.0 Safari/537.36",
    "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8",
}

def _has_tiktok_account(page: str, url: str) -> bool | None:
    username = urlparse(url).path.strip("/").split("/")[0].removeprefix("@").casefold()
    missing_messages = (
        "couldn't find this account", "couldn't find account",
        "account not found", "user not found", "user doesn't exist",
    )
    visible_page = re.sub(
        r"<(script|style)\b[^>]*>.*?</\1\s*>", "", page,
        flags=re.DOTALL | re.IGNORECASE,
    )
    visible_text = html.unescape(re.sub(r"<[^>]+>", " ", visible_page)).casefold().replace("\u2019", "'")
    if any(message in visible_text for message in missing_messages):
        return False
    for script_id in ("__UNIVERSAL_DATA_FOR_REHYDRATION__", "SIGI_STATE"):
        match = re.search(
            r'<script\b[^>]*\bid=["\']' + script_id + r'["\'][^>]*>(.*?)</script\s*>',
            page,
            re.DOTALL | re.IGNORECASE,
        )
        if not match:
            continue
        try:
            state = json.loads(match.group(1))
        except json.JSONDecodeError as exc:
            print_warn(f"Invalid TikTok account data for {url}: {exc}")
            continue
        if not isinstance(state, dict):
            continue
        if script_id == "__UNIVERSAL_DATA_FOR_REHYDRATION__":
            scope = state.get("__DEFAULT_SCOPE__", {})
            detail = scope.get("webapp.user-detail", {}) if isinstance(scope, dict) else {}
            status_message = detail.get("statusMsg", "") if isinstance(detail, dict) else ""
            if isinstance(status_message, str) and any(
                message in status_message.casefold().replace("\u2019", "'")
                for message in missing_messages
            ):
                return False
            info = detail.get("userInfo", {}) if isinstance(detail, dict) else {}
            user = info.get("user", {}) if isinstance(info, dict) else {}
            users = [user]
        else:
            module = state.get("UserModule", {})
            user_map = module.get("users", {}) if isinstance(module, dict) else {}
            users = list(user_map.values()) if isinstance(user_map, dict) else []
        for user in users:
            if isinstance(user, dict):
                unique_id = user.get("uniqueId")
                if isinstance(unique_id, str) and unique_id.casefold() == username and user.get("id"):
                    return True
    return None


def _social_page_availability(page: str, url: str) -> bool | None:
    """Recognize platform-specific public profile evidence, not generic page text."""
    platform = _social_platform_for_url(url)
    if platform == "tiktok":
        return _has_tiktok_account(page, url)
    visible_page = re.sub(
        r"<(script|style)\b[^>]*>.*?</\1\s*>", " ", page,
        flags=re.DOTALL | re.IGNORECASE,
    )
    text = " ".join(html.unescape(re.sub(r"<[^>]+>", " ", visible_page)).split())
    text = text.casefold().replace("\u2019", "'")
    missing_messages = {
        "facebook": (
            "this content isn't available at the moment",
            "this page isn't available",
        ),
        "youtube": ("this page isn't available", "this channel does not exist"),
        "twitter": ("this account doesn't exist", "user profile not found"),
        "linkedin": ("this page doesn't exist", "page not found"),
        "instagram": ("sorry, this page isn't available",),
        "reddit": ("sorry, nobody on reddit goes by that name", "this account has been suspended"),
        "telegram": ("this username is not occupied",),
        "substack": ("the page you are attempting to access is not found",),
    }
    if any(message in text for message in missing_messages.get(platform, ())):
        return False
    if platform == "facebook":
        title_match = re.search(r"<title\b[^>]*>(.*?)</title\s*>", page, re.I | re.S)
        if title_match:
            title = html.unescape(title_match.group(1)).strip().casefold()
            if title.endswith("| facebook") and not any(
                phrase in title for phrase in ("log in", "sign up", "error", "not available")
            ):
                return True
    if platform == "telegram" and re.search(
        r'<div\b[^>]*class=["\'][^"\']*\btgme_page_title\b', page, re.I
    ):
        return True
    parser = _SocialMetadataParser()
    parser.feed(page)
    if platform == "youtube" and parser.metadata.get("og:type", "").casefold() == "profile":
        return True
    if platform in {"linkedin", "twitter", "instagram", "reddit", "substack"}:
        canonical = parser.metadata.get("og:url") or parser.canonical
        title = parser.metadata.get("og:title", "").strip()
        generic_titles = {
            "linkedin", "twitter", "x", "instagram", "reddit", "substack",
            "discord", "log in", "sign in", "page not found",
        }
        title_lower = title.casefold()
        if canonical and title and title_lower not in generic_titles and not any(
            phrase in title_lower for phrase in ("log in", "sign in", "not found", "access denied")
        ):
            original = urlparse(url)
            target = urlparse(canonical)
            if (
                (original.hostname or "").lower().removeprefix("www.")
                == (target.hostname or "").lower().removeprefix("www.")
                and original.path.rstrip("/").casefold() == target.path.rstrip("/").casefold()
            ):
                return True
    return None


class _SocialMetadataParser(HTMLParser):
    def __init__(self) -> None:
        super().__init__()
        self.metadata: dict[str, str] = {}
        self.canonical = ""

    def handle_starttag(self, tag: str, attrs: list[tuple[str, str | None]]) -> None:
        attributes = dict(attrs)
        if tag == "meta":
            key = attributes.get("property") or attributes.get("name")
            value = attributes.get("content")
            if key and value:
                self.metadata[key.casefold()] = value
        elif tag == "link" and "canonical" in (attributes.get("rel") or "").lower().split():
            self.canonical = attributes.get("href") or ""


def _headless_social_availability(url: str, timeout: int = 40) -> bool | None:
    """Check a public page in a fresh browser profile; None means inconclusive."""
    candidates = [shutil.which("chrome"), shutil.which("msedge"), shutil.which("chromium")]
    for root in (os.environ.get("PROGRAMFILES"), os.environ.get("PROGRAMFILES(X86)"),
                 os.environ.get("LOCALAPPDATA")):
        if root:
            candidates.extend([
                str(Path(root) / "Google" / "Chrome" / "Application" / "chrome.exe"),
                str(Path(root) / "Microsoft" / "Edge" / "Application" / "msedge.exe"),
            ])
    browser = next((path for path in candidates if path and Path(path).is_file()), None)
    if not browser:
        print_warn(f"Cannot check {url} in a browser: Chrome or Edge was not found.")
        return None
    try:
        with tempfile.TemporaryDirectory(prefix="brand-social-check-") as profile:
            result = subprocess.run(
                [
                    browser, "--headless=new", "--disable-gpu", "--no-first-run",
                    "--no-default-browser-check", f"--user-data-dir={profile}",
                    "--virtual-time-budget=8000", "--dump-dom", url,
                ],
                capture_output=True, timeout=timeout, check=False,
            )
        if result.returncode != 0:
            print_warn(f"Browser check failed for {url} (exit code {result.returncode}).")
            return None
        page = result.stdout.decode("utf-8", errors="replace")
        availability = _social_page_availability(page, url)
        if availability is None:
            print_warn(f"Browser could not determine whether this social link exists: {url}")
        return availability
    except (OSError, subprocess.TimeoutExpired) as exc:
        print_warn(f"Browser check failed for {url}: {type(exc).__name__}: {exc}")
        return None


def _is_url_reachable(url: str, timeout: int = 20) -> bool:
    """Return True if the URL responds. Uses a one-shot request (no retries)
    so a slow first TLS handshake is not retried into a false timeout.
    SSL verification is disabled to handle sites with expired/self-signed certs.
    This generic check is used for the brand homepage, not social profiles."""
    if not url:
        return False
    try:
        import urllib3
        urllib3.disable_warnings(urllib3.exceptions.InsecureRequestWarning)
        resp = requests.get(
            url,
            timeout=timeout,
            allow_redirects=True,
            stream=True,
            headers=_BROWSER_HEADERS,
            verify=False,
        )
        try:
            if resp.status_code >= 400:
                print_warn(f"Website returned HTTP {resp.status_code}")
                return False
            return True
        finally:
            resp.close()
    except requests.RequestException as e:
        print_warn(f"Website check failed: {type(e).__name__}: {e}")
        return False


def _check_social_availability(url: str, timeout: int = 20) -> bool | None:
    """Return True for available, False for unavailable, None for inconclusive."""
    try:
        response = requests.get(
            url, timeout=timeout, allow_redirects=True, stream=True,
            headers=_BROWSER_HEADERS,
        )
        try:
            final_url = response.url or url
            final_platform = _social_platform_for_url(final_url)
            original_platform = _social_platform_for_url(url)
            if final_platform != original_platform or not _is_social_profile_url(final_url):
                print_warn(f"Social check redirected away from the profile: {url} -> {final_url}")
            elif (
                urlparse(final_url).path.rstrip("/").casefold() != urlparse(url).path.rstrip("/").casefold()
                or (
                    original_platform == "substack"
                    and urlparse(final_url).hostname != urlparse(url).hostname
                )
            ):
                print_warn(f"Social check redirected to a different profile path: {url} -> {final_url}")
                return None
            elif response.status_code in (404, 410):
                return False
            elif response.status_code < 400:
                availability = _social_page_availability(response.text, url)
                if availability is not None:
                    return availability
            else:
                print_warn(f"Social check returned HTTP {response.status_code}: {url}")
        finally:
            response.close()
    except requests.RequestException as exc:
        print_warn(f"Social check failed for {url}: {type(exc).__name__}: {exc}")
    return _headless_social_availability(url)


# ---------------------------------------------------------------------------
# Social URL normalisation — platform-aware sub-path stripping & share resolution
# ---------------------------------------------------------------------------

# Sub-path segments to strip for each platform.
# After stripping, only the base profile/channel URL remains.
# Key = partial domain string matched with `in netloc`.
_PLATFORM_STRIP_SUBPATHS: dict[str, set[str]] = {
    # Facebook: /username/photos, /username/videos, etc.
    "facebook.com": {
        "photos", "photo", "videos", "video", "posts", "about", "reviews",
        "services", "events", "community", "followers", "following", "friends",
        "reels", "groups", "mentions", "tagged", "map", "notes", "offers",
    },
    # YouTube: /@channel/videos, /@channel/playlists, /channel/UCxxx/shorts, etc.
    "youtube.com": {
        "videos", "playlists", "shorts", "community", "about", "featured",
        "streams", "memberships", "channels", "search", "live",
    },
    # X / Twitter: /username/status/xxx, /username/media, etc.
    "twitter.com": {
        "status", "statuses", "with_replies", "media", "likes",
        "following", "followers", "lists", "moments", "i",
    },
    "x.com": {
        "status", "statuses", "with_replies", "media", "likes",
        "following", "followers", "lists", "moments", "i",
    },
    # Instagram: /username/p/xxx, /username/reel/xxx, etc.
    "instagram.com": {
        "p", "reel", "tv", "reels", "tagged", "saved",
        "followers", "following", "explore", "stories", "highlights", "share",
    },
    # TikTok: /@username/video/xxx, /@username/live
    "tiktok.com": {
        "video", "live", "foryou", "following", "explore",
    },
}

# Path prefixes that indicate a share/redirect link needing HTTP resolution.
# Key = partial domain string matched with `in netloc`.
_PLATFORM_SHARE_PREFIXES: dict[str, tuple[str, ...]] = {
    "facebook.com":  ("/share/", "/sharer", "/l.php", "/tr", "/permalink"),
    "instagram.com": ("/share/",),
    # YouTube, X, TikTok don't use path-based share redirects on the main domain.
}

# Short-link domains that always need HTTP resolution to reach the real page.
# Key = exact netloc (lowercased); value = expected final domain substring.
_SOCIAL_SHORT_DOMAINS: dict[str, str] = {
    "vm.tiktok.com":  "tiktok.com",    # TikTok mobile short links
    "vt.tiktok.com":  "tiktok.com",    # TikTok video short links
    "t.co":           "twitter.com",   # Twitter/X URL shortener
    "youtu.be":       "youtube.com",   # YouTube video short links
    "fb.me":          "facebook.com",  # Facebook profile/page short links
}

# Paths that indicate the URL is a login/error page redirect — reject resolved result.
_BAD_REDIRECT_PATHS: dict[str, tuple[str, ...]] = {
    "facebook.com":  ("/login", "/checkpoint", "/recover", "/sorry", "/unsupportedbrowser"),
    "instagram.com": ("/accounts/login", "/challenge"),
    "youtube.com":   ("/watch",),   # youtu.be/xxx resolves to /watch?v=... — not a profile
    "twitter.com":   ("/login", "/i/flow"),
    "x.com":         ("/login", "/i/flow"),
    "tiktok.com":    ("/login",),
}


def _resolve_social_url(url: str, timeout: int = 10) -> str:
    """Follow HTTP redirects to resolve a shortened/share URL to its final destination.

    Handles:
        Facebook share links:  https://www.facebook.com/share/1Drxf8JJeo/?mibextid=wwXIfr
        Instagram share links: https://www.instagram.com/share/...
        TikTok short links:    https://vm.tiktok.com/xxx  /  https://vt.tiktok.com/xxx
        Twitter short links:   https://t.co/xxx
        YouTube short links:   https://youtu.be/xxx

    Returns the original URL unchanged if resolution fails or the resolved page
    is a login/error redirect.
    """
    try:
        import urllib3
        urllib3.disable_warnings(urllib3.exceptions.InsecureRequestWarning)

        parsed_in = urlparse(url)
        netloc_in = parsed_in.netloc.lower()

        # Facebook blocks Chrome desktop user-agents in python requests with HTTP 400.
        # Using facebookexternalhit/1.1 immediately yields the 302 redirect with Location.
        # Stopping at the first hop avoids Facebook's secondary redirect to /people/<slug>/<id>.
        if "facebook.com" in netloc_in:
            headers = {"User-Agent": "facebookexternalhit/1.1"}
            resp = requests.get(
                url,
                timeout=timeout,
                allow_redirects=False,
                headers=headers,
                verify=False,
            )
            try:
                if resp.status_code in (301, 302, 303, 307, 308) and "Location" in resp.headers:
                    from urllib.parse import urljoin
                    loc = urljoin(url, resp.headers["Location"])
                    parsed_loc = urlparse(loc)
                    if not any(parsed_loc.path.lower().startswith(p) for p in _BAD_REDIRECT_PATHS.get("facebook.com", ())):
                        return loc
                return url
            finally:
                resp.close()

        resp = requests.get(
            url,
            timeout=timeout,
            allow_redirects=True,
            stream=True,
            headers=_BROWSER_HEADERS,
            verify=False,
        )
        resp.close()
        final_url = resp.url
        parsed = urlparse(final_url)
        netloc_lower = parsed.netloc.lower()

        # Check bad redirect paths for the resolved domain
        for domain_key, bad_paths in _BAD_REDIRECT_PATHS.items():
            if domain_key in netloc_lower:
                if any(parsed.path.lower().startswith(p) for p in bad_paths):
                    return url   # redirected to a login/error page — discard
                break

        return final_url
    except Exception:
        return url


def _platform_key(netloc: str) -> str | None:
    """Return the matching platform key from *_PLATFORM_STRIP_SUBPATHS* for a netloc, or None."""
    netloc_lower = netloc.lower()
    for key in _PLATFORM_STRIP_SUBPATHS:
        if key in netloc_lower:
            return key
    return None


def _clean_social_url(url: str) -> str:
    """Normalise a social URL to its clean base profile form.

    Steps applied to all supported platforms
    (Facebook, YouTube, X/Twitter, Instagram, TikTok):

    1. Resolve short-link domains (``vm.tiktok.com``, ``t.co``, ``youtu.be``, …)
       and share/redirect paths (``/share/``, ``/sharer``, …) via HTTP redirect.
    2. Strip URL fragments and query params; retain only the Facebook
       ``profile.php?id=...`` identifier needed to identify a profile.
    4. Strip known non-profile sub-path segments to keep only the base profile URL.

    Examples — Facebook:
        'https://facebook.com/page/?fbclid=abc'           → 'https://facebook.com/page/'
        'https://facebook.com/loveandspicevn#'            → 'https://facebook.com/loveandspicevn'
        'https://facebook.com/loveandspicevn/photos'      → 'https://facebook.com/loveandspicevn'
        'https://facebook.com/share/1Drxf8JJeo/'          → 'https://facebook.com/loveandspicevn'
        'https://facebook.com/share/1EtoEntCe3/'          → 'https://facebook.com/profile.php?id=61553272866909'
        'https://facebook.com/profile.php?id=100000...'   → 'https://facebook.com/profile.php?id=100000...'

    Examples — YouTube:
        'https://youtube.com/@channel/videos'             → 'https://youtube.com/@channel'
        'https://youtube.com/channel/UCxxx/playlists'     → 'https://youtube.com/channel/UCxxx'

    Examples — X / Twitter:
        'https://x.com/username/status/123456'            → 'https://x.com/username'
        'https://twitter.com/username/media'              → 'https://twitter.com/username'

    Examples — Instagram:
        'https://instagram.com/username/p/Cxxx/'          → 'https://instagram.com/username'
        'https://instagram.com/username/reels/'           → 'https://instagram.com/username'

    Examples — TikTok:
        'https://tiktok.com/@username/video/123456'       → 'https://tiktok.com/@username'
        'https://vm.tiktok.com/ZMxxxxx/'                  → 'https://tiktok.com/@username'  (resolved)
    """
    if not url:
        return url

    parsed = urlparse(url)
    netloc_lower = parsed.netloc.lower()

    hostname = (parsed.hostname or "").lower().rstrip(".")
    is_facebook_host = hostname == "facebook.com" or hostname.endswith(".facebook.com")
    is_messenger_host = hostname == "messenger.com" or hostname.endswith(".messenger.com")
    if is_facebook_host or is_messenger_host:
        message_path = r"/messages/t/([A-Za-z0-9.]+)/?" if is_facebook_host else r"/t/([A-Za-z0-9.]+)/?"
        message_match = re.fullmatch(message_path, parsed.path, re.IGNORECASE)
        if message_match:
            recipient = message_match.group(1)
            if recipient.isdigit():
                profile_url = f"https://www.facebook.com/profile.php?id={recipient}"
                resolved = _resolve_social_url(profile_url)
                if (
                    resolved != profile_url
                    and _social_platform_for_url(resolved) == "facebook"
                    and _is_social_profile_url(resolved)
                ):
                    return _clean_social_url(resolved)
                print_warn(
                    f"Could not resolve Facebook message recipient to a public username; "
                    f"using profile homepage: {url} -> {profile_url}"
                )
                return profile_url
            profile_url = f"https://www.facebook.com/{recipient}"
            if _is_social_profile_url(profile_url):
                return profile_url

    if hostname == "linkedin.com" or hostname.endswith(".linkedin.com"):
        segments = [segment for segment in parsed.path.split("/") if segment]
        if len(segments) >= 2 and segments[0].lower() in {"company", "in", "school"}:
            return f"https://www.linkedin.com/{segments[0].lower()}/{segments[1]}/"

    # --- Step 1a: Resolve full short-link domains ---
    if netloc_lower in _SOCIAL_SHORT_DOMAINS:
        resolved = _resolve_social_url(url)
        if resolved != url:
            return _clean_social_url(resolved)
        # Resolution failed — return as-is (can't clean a short link without resolving it)
        return url

    # --- Step 1b: Resolve share/redirect paths on the main domain ---
    platform = _platform_key(netloc_lower)
    share_prefixes = _PLATFORM_SHARE_PREFIXES.get(platform or "", ())
    if share_prefixes and any(parsed.path.lower().startswith(p) for p in share_prefixes):
        resolved = _resolve_social_url(url)
        if resolved != url:
            return _clean_social_url(resolved)
        # Resolution failed — fall through and clean what we have
        parsed = urlparse(url)

    path = parsed.path

    # --- Step 1c: Platform-specific structural normalization (Facebook) ---
    if platform == "facebook.com":
        # /people/<slug>/<id> or /p/<slug>-<id> -> canonical /profile.php?id=<id>
        m_people = re.match(r"^/people/[^/]+/(\d+)/?$", path)
        if m_people:
            return f"{parsed.scheme}://{parsed.netloc}/profile.php?id={m_people.group(1)}"
        m_p = re.match(r"^/p/[^/]+-(\d+)/?$", path)
        if m_p:
            return f"{parsed.scheme}://{parsed.netloc}/profile.php?id={m_p.group(1)}"
        # profile.php -> keep only id parameter
        if path.rstrip("/").endswith("profile.php"):
            params = parse_qs(parsed.query)
            pid = params.get("id", [None])[0]
            if pid:
                return f"{parsed.scheme}://{parsed.netloc}/profile.php?id={pid}"

    # Keep only the profile/channel path; query parameters and fragments are not
    # part of the public profile link. Facebook profile.php?id=... returned above.
    query = ""

    # --- Step 3: Strip non-profile sub-paths ---
    if platform:
        strip_set = _PLATFORM_STRIP_SUBPATHS[platform]
        # Path segments: e.g. /loveandspicevn/photos → ['', 'loveandspicevn', 'photos']
        #                      /@channel/videos      → ['', '@channel', 'videos']
        #                      /channel/UCxxx/about  → ['', 'channel', 'UCxxx', 'about']
        segments = path.rstrip("/").split("/")
        # Find first segment (from index 2 onward) that belongs to strip_set and trim there.
        for cut in range(2, len(segments)):
            if segments[cut].lower() in strip_set:
                path = "/".join(segments[:cut])
                break

    return urlunparse((parsed.scheme, parsed.netloc, path.rstrip("/"), '', query, ''))


def _clean_address(addr: str) -> str:
    """Remove leading markers/labels and trailing punctuation from an address line.

    Examples:
        '- Kênh bán lẻ: 3 Nguyễn Đỗ Cung, ...'  →  '3 Nguyễn Đỗ Cung, ...'
        '- 123 Main St'                            →  '123 Main St'
        '+ Showroom: 45 Lý Tự Trọng'              →  '45 Lý Tự Trọng'
        'Cơ sở 2: Khu 4 Đồng Xuân, ...'           →  'Khu 4 Đồng Xuân, ...'
        '80A Huỳnh Văn Bánh, TP. Hồ Chí Minh - Fb (nếu có):'
            → '80A Huỳnh Văn Bánh, TP. Hồ Chí Minh'
        'Thôn Thượng Giang, Xã Lệ Thủy, Tỉnh Quảng Trị.' → 'Thôn Thượng Giang, Xã Lệ Thủy, Tỉnh Quảng Trị'
        'Thôn Thượng Giang, Xã Lệ Thủy, Tỉnh Quảng Trị,' → 'Thôn Thượng Giang, Xã Lệ Thủy, Tỉnh Quảng Trị'
    """
    # NFC-normalise first so that diacritic regexes (e.g. Việt Nam strip) work
    # regardless of the Unicode form returned by the Google Sheets CSV export.
    addr = unicodedata.normalize("NFC", addr)
    addr = re.sub(
        r"\s*[-–—]\s*(?:fb|facebook)\s*(?:\([^)]*\))?\s*:\s*$",
        "", addr, flags=re.IGNORECASE,
    )
    # Strip leading bullet chars (-, +, *, •, etc.)
    addr = re.sub(r"^[\-\+\*•·▪▸►]\s*", "", addr).strip()
    # Strip any label before a colon (including labels with numbers like "Cơ sở 2:")
    # Match from start of string to first colon, then remove it
    addr = re.sub(r"^[^:]+:\s*", "", addr).strip()
    # Strip trailing punctuation (including an unmatched closing parenthesis).
    addr = re.sub(r"[\s.,;:!\-–—/)]+$", "", addr).strip()
    return addr


_EMOJI_RE = re.compile(
    "["
    "\u00a9\u00ae\u203c\u2049\u2122\u2139"
    "\u2194-\u21ff\u2300-\u23ff\u25aa-\u25ff"
    "\u2600-\u27ff\u2b00-\u2bff\u3030\u303d\u3297\u3299"
    "\ufe0e\ufe0f\u200d\u20e3"
    "\U0001f000-\U0001faff\U000e0020-\U000e007f"
    "]+"
)


def _remove_emojis(text: str) -> str:
    """Remove emoji characters and presentation/joiner characters from text."""
    text = re.sub(r"[#*0-9]\ufe0f?\u20e3", "", text)
    return _EMOJI_RE.sub("", text)



def _enrich(text: str) -> str:
    """Plain-text enrichment (for tos): add 🔸 prefix to every non-empty line.
    Removes trailing '.' from each line. If a line is ALL UPPERCASE, converts it to
    sentence casing, keeping the first character of each sentence/clause capitalized."""
    pattern = r'(^|[\n\r.!?;\u2013\u2014|/:(“"\'\[]\s*|\s+[-–—]\s*|[•*+🔸\-]\s*|\d+\.\s*)([a-zà-ỹđ])'
    result = []
    for line in text.splitlines():
        line = line.strip()
        if not line:
            continue
        line = re.sub(r"\s*\.+$", "", line).strip()
        if not line:
            continue
        if line.isupper():
            line = line.lower()
            line = re.sub(pattern, lambda m: m.group(1) + m.group(2).upper(), line, flags=re.IGNORECASE | re.UNICODE)
        if not line.startswith("🔸"):
            line = "🔸" + line
        result.append(line)
    return "\n".join(result)


def _enrich_html(text: str, brand_name: str) -> str:
    """HTML enrichment for description: wraps each line in <p>, adds 🔸 prefix.
    Bolds the full brand name and its final two words, preserves explicit
    Markdown bold spans, and italicizes text in double quotes.
    If text already contains HTML tags it is returned unchanged."""
    if re.search(r"<p>|<strong>|<em>|<br|<ul>|<li>", text, flags=re.IGNORECASE):
        return text  # already HTML – leave as-is

    # --- Build bold patterns from the full brand name and its public-name suffix ---
    # Strategy: normalise everything to lowercase before comparing.
    # Python's str.lower() handles Vietnamese diacritics correctly (Ự→ự, Ề→ề …),
    # unlike re.IGNORECASE which only does ASCII case-folding.
    # We search on block.lower() but splice from the original block so the
    # author's chosen casing is preserved in the HTML output.
    bold_patterns_lower: list[str] = []
    if brand_name:
        bn_lower = brand_name.lower()
        bold_patterns_lower.append(bn_lower)
        words = brand_name.split()
        if len(words) >= 3:
            bold_patterns_lower.append(" ".join(word.lower() for word in words[-2:]))

    bold_re_lower = None
    if bold_patterns_lower:
        bold_patterns_lower = sorted(set(bold_patterns_lower), key=len, reverse=True)
        combined = "|".join(re.escape(p) for p in bold_patterns_lower)
        bold_re_lower = re.compile(rf"(?<!\w)({combined})(?!\w)", re.UNICODE)

    def _apply_bold(block: str) -> str:
        """Bold brand-name occurrences while preserving original casing."""
        if not bold_re_lower:
            return block
        lower_block = block.lower()
        parts: list[str] = []
        last = 0
        for m in bold_re_lower.finditer(lower_block):
            parts.append(block[last:m.start()])
            parts.append(f"<strong>{block[m.start():m.end()]}</strong>")
            last = m.end()
        parts.append(block[last:])
        return "".join(parts)

    # --- Collect non-empty paragraphs and lines ---
    _SHORT_LINE_THRESHOLD = 250  # characters (excluding the 🔸 prefix)
    raw_paragraphs = [
        [line.strip() for line in paragraph.splitlines() if line.strip()]
        for paragraph in re.split(r"\n\s*\n", text.strip())
    ]

    # --- Merge consecutive short lines into groups ---
    # A line is "short" when its plain-text length (without the 🔸 bullet) is
    # below the threshold. Short consecutive lines are joined with a space and
    # share a single 🔸 prefix / <p> wrapper.
    groups: list[str] = []
    current_parts: list[str] = []

    def _plain_len(s: str) -> int:
        """Length without leading 🔸 bullet."""
        return len(s.lstrip("🔸").strip())

    def _flush_group() -> None:
        if current_parts:
            groups.append(" ".join(current_parts))
            current_parts.clear()

    for paragraph in raw_paragraphs:
        if not paragraph:
            continue
        for raw in paragraph:
            # Strip existing 🔸 prefix so we can re-add it uniformly later.
            plain = raw.lstrip("🔸").strip()
            if _plain_len(plain) < _SHORT_LINE_THRESHOLD:
                # Short line — accumulate within the current paragraph.
                current_parts.append(plain)
            else:
                # Long line — flush pending text, then emit it on its own.
                _flush_group()
                groups.append(plain)
        _flush_group()

    # --- Build HTML from groups ---
    result = []
    for group in groups:
        block = "🔸" + group

        explicit_bold: list[str] = []

        def _stash_explicit_bold(match: re.Match) -> str:
            explicit_bold.append(match.group(1))
            return f"\x00EXPLICIT_BOLD_{len(explicit_bold) - 1}\x00"

        block = re.sub(r"\*\*(.+?)\*\*", _stash_explicit_bold, block)
        block = _apply_bold(block)
        for index, value in enumerate(explicit_bold):
            block = block.replace(
                f"\x00EXPLICIT_BOLD_{index}\x00", f"<strong>{value}</strong>"
            )

        # Italicise text in double quotes – ASCII " and Unicode \u201c \u201d
        # Strip any <strong> tags inside quotes so quoted text is italic-only.
        block = re.sub(
            r'[\u201c\u201d"][^\u201c\u201d"]*[\u201c\u201d"]',
            lambda m: '<em>' + m.group(0).replace('<strong>', '').replace('</strong>', '') + '</em>',
            block,
        )

        result.append(f"<p>{block}</p>")
    return "".join(result)


def parse_row(row: list[str], brand_name: str = "") -> dict:
    name_val = brand_name.strip() if brand_name else _cell(row, 2).strip()
    raw_email = _cell(row, 5)
    parsed_emails = _parse_emails(raw_email)
    d = {
        "name":          name_val,
        "phone":         _format_phones(_cell(row, 4)),
        "email":         _format_emails(raw_email),
        "emails":        parsed_emails,
        "description":   _enrich_html(_cell(row, 7), name_val),
        "benefit_tos":   _enrich(_cell(row, 8)),
        "homepage":      _normalize_url(_cell(row, 9)),
        "socials_raw":   _cell(row, 10),
        "addresses_raw": _remove_emojis(_cell(row, 18)),
    }
    # Strip leading/trailing whitespace from every text field.
    return {k: v.strip() if isinstance(v, str) else v for k, v in d.items()}

# ---------------------------------------------------------------------------
# Image compression
# ---------------------------------------------------------------------------

def _ensure_image_extension(path: Path) -> Path:
    """Restore missing/unrecognized image extensions using file content, not Drive titles."""
    if path.suffix.lower() in IMG_EXTS | _NON_IMAGE_EXTS:
        return path
    try:
        with Image.open(path) as image:
            image_format = image.format
    except UnidentifiedImageError:
        return path
    except OSError as exc:
        print_warn(f"Could not inspect image {path.name}: {exc}")
        return path

    extensions = {
        fmt: ext for ext, fmt in Image.registered_extensions().items()
        if ext in IMG_EXTS
    }
    extensions["JPEG"] = ".jpg"
    extension = extensions.get(image_format)
    if not extension:
        return path

    # Append rather than replace: dots can be part of a product's title.
    destination = path.with_name(path.name + extension)
    counter = 1
    while destination.exists():
        destination = path.with_name(f"{path.name}_{counter}{extension}")
        counter += 1
    try:
        path.rename(destination)
    except OSError as exc:
        print_warn(f"Could not restore image extension for {path.name}: {exc}")
        return path
    return destination


def flatten_subfolders(folder: Path, verbose: bool = False) -> tuple[int, int]:
    """Copy all images and PDFs from subfolders to parent folder, replacing duplicates, then remove subfolders.
    Returns (num_subfolders, num_files_copied)."""
    if not folder.exists():
        return 0, 0

    # Normalize before flattening so extensionless images are not discarded.
    for path in folder.rglob("*"):
        if path.is_file():
            _ensure_image_extension(path)
    
    # Find all subfolders
    subfolders = [d for d in folder.iterdir() if d.is_dir()]
    if not subfolders:
        return 0, 0
    
    if verbose:
        print_info(f"Found {len(subfolders)} subfolder(s) in '{folder.name}'. Flattening...")
    
    files_copied = 0
    # Copy all images & PDFs from subfolders to parent
    for subfolder in subfolders:
        files_in_subfolder = [
            f for f in subfolder.rglob("*")
            if f.is_file() and (f.suffix.lower() in IMG_EXTS or f.suffix.lower() == ".pdf")
        ]
        for file_path in files_in_subfolder:
            dest_path = folder / file_path.name
            try:
                shutil.copy2(file_path, dest_path)
                files_copied += 1
                if verbose:
                    print(f"      {Colors.GREEN}✓{Colors.END} Copied {Colors.CYAN}{file_path.name}{Colors.END} from {Colors.BLUE}{subfolder.name}{Colors.END}")
            except Exception as e:
                print_warn(f"Failed to copy {file_path.name}: {e}")
    
    # Remove all subfolders
    for subfolder in subfolders:
        try:
            shutil.rmtree(subfolder)
            if verbose:
                print_success(f"Removed subfolder: {Colors.BLUE}{subfolder.name}{Colors.END}")
        except Exception as e:
            print_warn(f"Failed to remove subfolder {subfolder.name}: {e}")

    return len(subfolders), files_copied


def convert_pdfs_in_folder(folder: Path, verbose: bool = False) -> set[str]:
    """Convert every PDF in folder to PNG images (all pages), then delete the PDF.
    Returns a set of generated image stems for tracking."""
    converted_stems: set[str] = set()
    if not folder.exists():
        return converted_stems
    # Use case-insensitive set comprehension to prevent duplicate matches on Windows
    pdfs = sorted({p for p in folder.iterdir() if p.is_file() and p.suffix.lower() == ".pdf"})
    if not pdfs:
        return converted_stems
    if verbose:
        print_info(f"Found {len(pdfs)} PDF file(s) in '{folder.name}'. Converting to images...")
    for pdf_path in pdfs:
        # Ignore and remove business registration/license PDFs in gallery folder ('2')
        if folder.name == "2" and _is_gpkd_or_dkkd(pdf_path.name):
            try:
                pdf_path.unlink()
            except Exception:
                pass
            continue
        try:
            doc = fitz.open(str(pdf_path))
            total = len(doc)
            for page_num in range(total):
                page = doc.load_page(page_num)
                mat = fitz.Matrix(2, 2)  # 2× zoom → ~150 dpi effective
                pix = page.get_pixmap(matrix=mat)
                if total == 1:
                    out_path = pdf_path.with_suffix(".png")
                else:
                    out_path = pdf_path.with_name(f"{pdf_path.stem}_page{page_num + 1}.png")
                pix.save(str(out_path))
                converted_stems.add(out_path.stem)
                if verbose:
                    print(f"      {Colors.GREEN}✓{Colors.END} Converted {Colors.CYAN}{pdf_path.name}{Colors.END} → {Colors.BLUE}{out_path.name}{Colors.END}")
            doc.close()
            pdf_path.unlink()
        except Exception as e:
            print_warn(f"Failed to convert {pdf_path.name}: {e}")
    return converted_stems



def _list_images(folder: Path) -> list[Path]:
    if not folder.exists():
        return []
    for path in folder.iterdir():
        if path.is_file():
            _ensure_image_extension(path)
    # Deduplicate files sharing the same stem (e.g. .png and .jpg) to prevent
    # multiple threads concurrently writing to the same destination .jpg file.
    files = [
        f for f in folder.iterdir()
        if f.is_file() and f.suffix.lower() in IMG_EXTS
        and not (folder.name == "2" and _is_gpkd_or_dkkd(f.name))
    ]
    by_stem: dict[str, Path] = {}
    for f in sorted(files, key=lambda p: (p.stem.lower(), 0 if p.suffix.lower() == ".png" else 1)):
        stem_key = f.stem.lower()
        if stem_key not in by_stem:
            by_stem[stem_key] = f
        else:
            try:
                f.unlink()
            except Exception:
                pass
    return sorted(by_stem.values(), key=lambda p: p.name)


def compress_in_place(path: Path, max_kb: int = 600, quality: int = 85, max_dimension: int = 2100, verbose: bool = False) -> Path:
    """Compress image to JPEG in-place atomically. Returns the (possibly renamed) path."""
    if path.suffix.lower() == ".avif" and not _avif_available:
        raise RuntimeError(
            "AVIF decoding is unavailable. Install the decoder with: "
            f'"{sys.executable}" -m pip install pillow-avif-plugin'
        )
    out = path.with_suffix(".jpg")
    tmp_out = path.with_name(f".tmp_{path.stem}_{threading.get_ident()}.jpg")
    try:
        with Image.open(path) as img:
            if img.mode in ("RGBA", "P"):
                img = img.convert("RGBA")
                bg = Image.new("RGB", img.size, (255, 255, 255))
                bg.paste(img, mask=img.getchannel("A"))
                img = bg
            elif img.mode != "RGB":
                img = img.convert("RGB")
            # Cap pixel dimensions so the upload payload stays manageable.
            w, h = img.size
            if max(w, h) > max_dimension:
                scale = max_dimension / max(w, h)
                img = img.resize((int(w * scale), int(h * scale)), Image.LANCZOS)
                if verbose:
                    print_info(f"  Resized {path.name}: {w}×{h} → {img.size[0]}×{img.size[1]}")
            img.save(tmp_out, "JPEG", quality=quality, optimize=True)

        q = quality
        while tmp_out.stat().st_size / 1024 > max_kb and q > 60:
            q -= 10
            with Image.open(tmp_out) as img:
                img.save(tmp_out, "JPEG", quality=q, optimize=True)

        if path.suffix.lower() != ".jpg" and path.exists():
            path.unlink()
        tmp_out.replace(out)
        return out
    finally:
        if tmp_out.exists():
            try:
                tmp_out.unlink()
            except Exception:
                pass


def _compress_single(p: Path, max_kb: int, quality: int, max_dimension: int, verbose: bool = False) -> Path:
    """Compress a single image (thread-safe wrapper for compress_in_place)."""
    if verbose:
        print(f"    {Colors.PEACH}⚡{Colors.END} Compressing {Colors.BLUE}{p.name}{Colors.END} ...")
    result = compress_in_place(p, max_kb=max_kb, quality=quality, max_dimension=max_dimension, verbose=verbose)
    if verbose:
        print_success(f"Compressed {Colors.BLUE}{result.name}{Colors.END} → {result.stat().st_size / 1024:.0f} KB")
    return result


def compress_folder(folder: Path, max_kb: int, quality: int, max_dimension: int = 2100, workers: int = 5) -> list[Path]:
    images = _list_images(folder)
    if not images:
        return []
    active_workers = min(len(images), workers)
    print_info(f"Compressing {len(images)} image(s) using {active_workers} thread(s)...")
    result: list[Path] = []
    with ThreadPoolExecutor(max_workers=active_workers) as ex:
        futures = {
            ex.submit(_compress_single, p, max_kb, quality, max_dimension): p
            for p in images
        }
        for fut in as_completed(futures):
            src = futures[fut]
            try:
                result.append(fut.result())
            except Exception as e:
                print_warn(f"Failed to compress {src.name}: {e}")
    # Preserve original file order (sorted by name).
    result.sort(key=lambda p: p.name)
    return result


_PROMO_KEYWORDS = (
    "%", "uu dai", "uu_dai", "uudai", "voucher", "khuyen mai", "khuyenmai",
    "giam gia", "giamgia", "sale", "official store", "officialstore",
    "mien phi", "mienphi", "free", "dong gia", "combo", "khach hang",
    "chao mung", "ap dung", "hotline", "tang ngay"
)


def _evaluate_logo_cand(p: Path, ratio: float, stem_norm: str) -> float:
    """Evaluate how well an image fits as a brand Logo (lower score is better).

    Considers:
    - Distance from square aspect ratio (1.0).
    - Filename keywords ('logo' bonus, 'banner'/'poster' penalty).
    - Border margin cleanliness & edge density (logos have clean margins/padding).
    - Uniform background ratio (whitespace/transparency/solid borders).
    - OCR promotional text (promotional posters with discounts/% are penalized).
    """
    dist = abs(ratio - 1.0)
    if "logo" in stem_norm and ratio < 1.6:
        return dist * 0.1
    if any(k in stem_norm for k in ("banner", "cover", "poster", "pano", "quang_cao", "quangcao")):
        dist += 5.0

    score = dist

    # Image analysis cues (border margins, whitespace, edge density)
    if cv2 is not None and np is not None:
        try:
            img_bytes = np.fromfile(str(p), dtype=np.uint8)
            img = cv2.imdecode(img_bytes, cv2.IMREAD_UNCHANGED)
            if img is not None:
                h, w = img.shape[:2]
                mh, mw = max(1, int(h * 0.05)), max(1, int(w * 0.05))

                if img.ndim == 3 and img.shape[2] == 4:
                    bgr = img[:, :, :3]
                    alpha = img[:, :, 3]
                    is_bg = (alpha < 10) | ((bgr[:, :, 0] > 240) & (bgr[:, :, 1] > 240) & (bgr[:, :, 2] > 240))
                    white_ratio = float(np.mean(is_bg))
                    gray = cv2.cvtColor(bgr, cv2.COLOR_BGR2GRAY)
                    border_pixels = bgr
                else:
                    bgr = img if img.ndim == 3 else cv2.cvtColor(img, cv2.COLOR_GRAY2BGR)
                    white_ratio = float(np.mean(np.all(bgr > 240, axis=2)))
                    gray = cv2.cvtColor(bgr, cv2.COLOR_BGR2GRAY) if img.ndim == 3 else img
                    border_pixels = bgr

                edges = cv2.Canny(gray, 50, 150)
                mask_border = np.zeros((h, w), dtype=bool)
                mask_border[:mh, :] = True
                mask_border[-mh:, :] = True
                mask_border[:, :mw] = True
                mask_border[:, -mw:] = True

                border_edges = float(np.mean(edges[mask_border] > 0))
                total_edges = float(np.mean(edges > 0))
                border_std = float(np.std(border_pixels[mask_border]))

                # Edge / border margin penalties & bonuses
                if border_edges > 0.015:
                    score += 2.0 + border_edges * 10.0
                elif border_edges < 0.002:
                    score -= 0.5  # clean margin bonus

                if border_std < 15.0:
                    score -= 0.5  # uniform solid margin
                elif border_std > 50.0:
                    score += 1.0  # busy/colored border

                if white_ratio > 0.60:
                    score -= 1.0  # dominant clean canvas
                elif white_ratio > 0.30:
                    score -= 0.3

                if total_edges < 0.015:
                    score -= 0.2  # simple logo vector mark
                elif total_edges > 0.035:
                    score += 0.5  # complex poster/photo
        except Exception:
            pass

    # OCR cues: penalize promotional banners / posters
    if _rapid_ocr is not None and (0.70 <= ratio <= 1.50):
        try:
            res, _ = _rapid_ocr(str(p))
            if res:
                ocr_lines = len(res)
                text_blob = " ".join(r[1].lower() for r in res)
                norm_blob = _normalize_vietnamese(text_blob)
                if any(kw in norm_blob for kw in _PROMO_KEYWORDS):
                    score += 10.0  # definitely promotional poster, not logo
                elif ocr_lines > 5:
                    score += 3.0  # heavy text poster
        except Exception:
            pass

    return score


def detect_logo_banner(folder: Path) -> tuple[Path | None, Path | None]:
    """Detect logo (1x1 ratio) and banner (close to 21x7 / 3:1 ratio) by aspect ratio and keywords."""
    imgs = sorted(
        p for p in folder.iterdir()
        if p.is_file() and p.suffix.lower() in IMG_EXTS and p.suffix.lower() not in _NON_IMAGE_EXTS
    ) if folder.exists() else []

    if not imgs:
        return None, None

    img_info: list[tuple[Path, int, int, float, str]] = []  # (path, w, h, ratio, stem_norm)
    for p in imgs:
        try:
            with Image.open(p) as im:
                w, h = im.size
            ratio = w / h if h else 1.0
            stem_norm = _normalize_filename(p.stem)
            img_info.append((p, w, h, ratio, stem_norm))
        except Exception as e:
            print_warn(f"Could not read image {p.name}: {e}")

    if not img_info:
        return None, None

    if len(img_info) == 1:
        p, w, h, ratio, _ = img_info[0]
        if abs(ratio - 1.0) <= abs(ratio - 3.0):
            return p, None
        else:
            return None, p

    # 1. Select best Logo (target ratio: 1.0, evaluated by shape, margin & content)
    best_logo_item = min(
        img_info,
        key=lambda item: (
            0 if "logo" in item[4] and item[3] < 1.6 else 1,
            abs(item[3] - 1.0),
            _evaluate_logo_cand(item[0], item[3], item[4]),
        ),
    )
    logo_cand = (best_logo_item[0], best_logo_item[1], best_logo_item[2], best_logo_item[3])

    # 2. Select best Banner from remaining images (target ratio: 21 / 7 = 3.0)
    rem = [item for item in img_info if item[0] != logo_cand[0]]
    banner_cand: tuple[Path, int, int, float] | None = None

    def banner_score(item: tuple[Path, int, int, float, str]) -> float:
        p, w, h, ratio, stem_norm = item
        dist = abs(ratio - 3.0)
        has_kw = any(kw in stem_norm for kw in ("banner", "cover", "poster", "pano"))
        if has_kw and ratio > 1.8:
            return dist * 0.1
        return dist

    if rem:
        best_banner_item = min(rem, key=banner_score)
        banner_cand = (best_banner_item[0], best_banner_item[1], best_banner_item[2], best_banner_item[3])

    logo = logo_cand[0] if logo_cand else None
    banner = banner_cand[0] if banner_cand else None

    if logo:
        print_success(f"Selected Logo: {Colors.CYAN}{logo.name}{Colors.END} ({logo_cand[1]}x{logo_cand[2]}, ratio {logo_cand[3]:.2f} ≈ 1x1)")
    if banner:
        print_success(f"Selected Banner: {Colors.CYAN}{banner.name}{Colors.END} ({banner_cand[1]}x{banner_cand[2]}, ratio {banner_cand[3]:.2f} ≈ 21x7)")

    return logo, banner

# ---------------------------------------------------------------------------
# Multi-signal image similarity (pHash + Color Histogram + dHash)
# ---------------------------------------------------------------------------

def _phash(image_path: Path, hash_size: int = 16) -> int:
    """Perceptual hash using DCT (frequency-domain).

    Converts image to grayscale, resizes to (hash_size*4)×(hash_size*4),
    applies a 2-D DCT, keeps the top-left hash_size×hash_size low-frequency
    coefficients, and compares each against the mean — producing a
    hash_size²-bit integer.  More robust to JPEG compression, brightness
    shifts, and minor crops than dHash.
    """
    size = hash_size * 4  # work on a larger canvas for better DCT quality
    with Image.open(image_path) as img:
        img = img.convert("L").resize((size, size), Image.LANCZOS)
        pixels = np.array(img, dtype=float)

    # 2-D DCT via separable 1-D DCT (no scipy needed)
    def _dct1d(v: np.ndarray) -> np.ndarray:
        N = len(v)
        n = np.arange(N)
        k = n[:, None]
        M = np.cos(np.pi * k * (2 * n + 1) / (2 * N))
        return M @ v

    dct_rows = np.apply_along_axis(_dct1d, 1, pixels)
    dct_2d  = np.apply_along_axis(_dct1d, 0, dct_rows)

    # Keep only the top-left (low-frequency) block
    low_freq = dct_2d[:hash_size, :hash_size].flatten()
    mean_val = low_freq.mean()

    hash_val = 0
    for idx, v in enumerate(low_freq):
        if v > mean_val:
            hash_val |= 1 << idx
    return hash_val


def _dhash(image_path: Path, hash_size: int = 16) -> int:
    """Difference hash (dHash) — horizontal gradient fingerprint.

    Fast and good at detecting structural layout changes.  Used as one of
    three signals in the combined similarity score.
    """
    with Image.open(image_path) as img:
        img = img.convert("L").resize((hash_size + 1, hash_size), Image.LANCZOS)
        pixels = list(img.getdata())
    hash_val = 0
    for row in range(hash_size):
        for col in range(hash_size):
            offset = row * (hash_size + 1) + col
            if pixels[offset] < pixels[offset + 1]:
                hash_val |= 1 << (row * hash_size + col)
    return hash_val


def _hamming_distance(h1: int, h2: int) -> int:
    """Count the number of differing bits between two integer hashes."""
    return bin(h1 ^ h2).count("1")


def _color_histogram_similarity(p1: Path, p2: Path, bins: int = 64) -> float:
    """Histogram intersection similarity using RGB channels (0.0 – 1.0).

    Splits each image into R, G, B channels, builds a normalised histogram
    for each, and returns the sum of per-channel intersection values averaged
    across channels.  Catches colour-shifted duplicates that structural hashes
    (dHash / pHash) miss entirely because they operate in grayscale.
    """
    def _hist(p: Path) -> np.ndarray:
        with Image.open(p) as img:
            img = img.convert("RGB").resize((128, 128), Image.LANCZOS)
            arr = np.array(img)
        hists = []
        for ch in range(3):
            h, _ = np.histogram(arr[:, :, ch], bins=bins, range=(0, 256))
            total = h.sum()
            hists.append(h / total if total > 0 else h.astype(float))
        return np.concatenate(hists)  # shape: (bins*3,)

    h1 = _hist(p1)
    h2 = _hist(p2)
    return float(np.minimum(h1, h2).sum() / 3)  # normalise back to [0, 1]


_ImageFingerprint = tuple[Path, int, int]  # (path, phash, dhash)


def _combined_similarity(
    fp1: _ImageFingerprint,
    fp2: _ImageFingerprint,
    total_bits: int,
) -> float:
    """Weighted combination of three similarity signals.

    Weights:
        50 % pHash   — frequency-domain structural similarity
        30 % Color   — RGB histogram intersection (colour fidelity)
        20 % dHash   — gradient layout similarity

    Returns a value in [0.0, 1.0].
    """
    p1, ph1, dh1 = fp1
    p2, ph2, dh2 = fp2

    phash_sim = 1.0 - _hamming_distance(ph1, ph2) / total_bits
    dhash_sim  = 1.0 - _hamming_distance(dh1, dh2) / total_bits
    color_sim  = _color_histogram_similarity(p1, p2)

    return 0.50 * phash_sim + 0.30 * color_sim + 0.20 * dhash_sim


def dedup_similar_images(
    folder: Path,
    threshold: float = 0.90,
    hash_size: int = 16,
    verbose: bool = False,
) -> list[Path]:
    """Remove visually-similar duplicate images from *folder*.

    Uses a three-signal combined similarity score:
        • pHash (50 %) – DCT frequency-domain fingerprint; robust to JPEG
          compression, minor crops, and brightness shifts.
        • Color Histogram (30 %) – RGB channel histogram intersection;
          catches colour-shifted / colour-overlay duplicates that pHash and
          dHash miss because both operate in grayscale.
        • dHash (20 %) – horizontal gradient fingerprint; fast structural
          sanity check.

    For every pair whose combined score ≥ *threshold*, the later file
    (by sorted name) is deleted from disk.

    Args:
        folder:    Directory containing image files.
        threshold: Combined similarity ratio (0.0 – 1.0) above which two
                   images are considered duplicates.
        hash_size: Hash grid side length.  16 → 256-bit hashes (default).

    Returns:
        List of *remaining* image paths (sorted).
    """
    if not folder.exists():
        return []

    # numpy is required for pHash and colour histogram
    if np is None:
        print_warn("numpy not available — falling back to dHash-only dedup.")
        # minimal fallback (original behaviour)
        images = sorted(
            p for p in folder.iterdir()
            if p.suffix.lower() in IMG_EXTS and p.suffix.lower() not in _NON_IMAGE_EXTS
        )
        return images

    images = sorted(
        p for p in folder.iterdir()
        if p.suffix.lower() in IMG_EXTS and p.suffix.lower() not in _NON_IMAGE_EXTS
    )
    if len(images) < 2:
        return images

    # 1. Compute pHash + dHash fingerprints in parallel
    fingerprints: list[_ImageFingerprint] = []
    def _fingerprint(p: Path) -> _ImageFingerprint | None:
        try:
            return (p, _phash(p, hash_size), _dhash(p, hash_size))
        except Exception as e:
            print_warn(f"Could not fingerprint {p.name}: {e}")
            return None

    with ThreadPoolExecutor(max_workers=min(len(images), 8)) as ex:
        results = list(ex.map(_fingerprint, images))
    fingerprints = [r for r in results if r is not None]

    # 2. Pairwise compare — mark later duplicates for deletion
    total_bits = hash_size * hash_size
    to_delete: set[Path] = set()
    for i in range(len(fingerprints)):
        if fingerprints[i][0] in to_delete:
            continue
        for j in range(i + 1, len(fingerprints)):
            if fingerprints[j][0] in to_delete:
                continue
            score = _combined_similarity(fingerprints[i], fingerprints[j], total_bits)
            if score >= threshold:
                to_delete.add(fingerprints[j][0])
                if verbose:
                    print(
                        f"      {Colors.WARNING}\U0001f5d1{Colors.END}  "
                        f"Duplicate: {Colors.CYAN}{fingerprints[j][0].name}{Colors.END} "
                        f"\u2248 {Colors.BLUE}{fingerprints[i][0].name}{Colors.END} "
                        f"({score:.0%} combined similarity) — deleted"
                    )

    # 3. Delete from disk
    for p in to_delete:
        try:
            p.unlink()
        except Exception as e:
            print_warn(f"Could not delete {p.name}: {e}")

    remaining = [p for p in images if p not in to_delete]
    if to_delete:
        print_success(
            f"Removed {Colors.BOLD}{len(to_delete)}{Colors.END} duplicate(s), "
            f"{Colors.BOLD}{len(remaining)}{Colors.END} image(s) remaining"
        )
    else:
        print_info("No visually-similar duplicates found.")
    return remaining


# ---------------------------------------------------------------------------
# Gallery Image Categorization and Reordering (Fast Multi-Threaded)
# ---------------------------------------------------------------------------

_PLACE_KEYWORDS = (
    "place", "dia_diem", "diadiem", "dia-diem",
    "co_so", "coso", "co-so", "tru_so", "truso", "tru-so",
    "nha_xuong", "nhaxuong", "nha-xuong", "phan_xuong", "phanxuong",
    "mat_tien", "mattien", "mat-tien", "face_house", "house_face", "facade",
    "cua_hang", "cuahang", "cua-hang", "showroom", "store", "shop", "factory",
    "building", "street", "duong_pho", "duongpho", "duong-pho", "khu_pho", "khupho", "pho_co",
    "truoc_nha", "truocnha", "ngoai_troi", "outdoor",
    "van_phong", "vanphong", "van-phong", "office",
    "trang_trai", "trangtrai", "trang-trai", "farm", "vung_trong", "vungtrong",
    "kho_bai", "khobai", "kho-bai", "nha_kho", "nhakho", "warehouse", "canh_quan", "canhquan",
    "co_quan", "coquan", "toa_nha", "toanha", "cong_chao", "congchao",
    "truoc_cong", "truoccong", "khu_san_xuat", "khusanxuat", "nha_may", "nhamay",
)

_PLACE_ESTABLISHMENT_WORDS = (
    "hop tac xa", "htx", "cong ty", "doanh nghiep", "co so", "nha may",
    "phan xuong", "nha xuong", "van phong", "tru so", "chi nhanh",
    "cua hang", "showroom", "dai ly", "trung tam", "nong trai", "trang trai",
)

_PLACE_LOCATION_WORDS = (
    "dia chi", "diachi", "dc:", "d/c:", "ap ", "ap-", "xa ", "huyen ",
    "tinh ", "phuong ", "quan ", "thanh pho", "tp.", "duong ", "so ",
    "khu pho", "to ", "website", "dt:", "sdt", "hotline",
)

_PACKAGING_EXCLUDE_WORDS = (
    "khoi luong tinh", "klt", "net weight", "net wt", "thanh phan", "ingredient",
    "huong dan su dung", "hdsu", "ngay san xuat", "han su dung", "nsx", "hsd",
    "huong dan bao quan", "dinh duong", "nutrition", "cach dung", "cach su dung",
    "san xuat tai", "sanxuat tai", "san xuat boi", "produced at", "producedat", "produced by",
    "dong goi tai", "donggoi tai", "packed by", "nha phan phoi", "distributed by",
    "prawn cracker", "crab cracker", "snack",
    "the tich", "thetich", "the-tich", "chi tieu chat luong", "ham luong",
    # Warranty receipts and anti-counterfeiting stamps are product accessories, not certificates
    "tem chong hang gia", "temchonghanggia",
    "tiep nhan bao hanh", "phieu bao hanh", "the bao hanh", "warranty card",
)

_BANNER_KEYWORDS = (
    "banner", "cover", "poster", "pano", "quang_cao", "quangcao", "quang-cao",
    "standee", "billboard", "bang_ron", "bangron", "bang-ron", "bien_hieu", "bienhieu",
    "bien-hieu", "header", "slider", "slide", "backdrop", "panel", "bandroll", "bandrol",
)

_CERT_KEYWORDS = (
    "ocop", "chung_nhan", "chungnhan", "chung-nhan", "chung_chi", "chungchi", "chung-chi",
    # Common OCR variations for 'chứng nhận' ('ứ' -> 'it' or 'i')
    "chitng_nhan", "chitngnhan", "chitng-nhan",
    "ching_nhan", "chingnhan", "ching-nhan",
    "gcn", "gcb", "bang_khen", "bangkhen", "bang-khen", "giay_khen", "giaykhen", "giay-khen",
    "giay_phep", "giayphep", "giay-phep",
    "iso", "haccp", "vietgap", "globalgap", "fda", "gmp", "halal", "usda", "organic",
    "kiem_nghiem", "kiemnghiem", "kiem-nghiem", "kiem_dinh", "kiemdinh", "kiem-dinh",
    "cert", "certificate", "certification", "license", "accreditation",
    "an_toan_thuc_pham", "attp", "vsattp", "cbcl", "one commune one product", "one_commune_one_product",
    "tieu chuan", "tieuchuan", "tieu_chuan", "tcvn", "qcvn",
    # Awards / trophies / prizes from provincial or national bodies
    "giai_thuong", "giai-thuong", "giai thuong",
    "cup", "trophy", "award", "prize",
    "phan_thuong", "phanthuong", "phan-thuong",
    "tieu_bieu", "tieubieu", "tieu-bieu",
    "san_pham_tieu_bieu", "sanphamtieubieu",
    "uy_ban_nhan_dan", "uybannhanddan", "ubnd",
    "nong_thon", "nongthon", "cong_nghiep_nong_thon", "congnghiepnongthon",
    "vinh_danh", "vinhdanh", "vinh-danh",
    "bien_ban_ghi_nhan", "ghi_nhan",
    "nhan_duoc", "nhanduoc",
    "bo_nong_nghiep", "bongnghiep",
    "cap_tinh", "captinh", "cap_quoc_gia", "capquocgia",
    # Committee / Decision / Brand accreditation terms on official certificates
    "ban_to_chuc", "bantochuc", "ban-to-chuc",
    "quyet_dinh", "quyetdinh", "quyet-dinh", "quyetdjnh",
    "thuong_hieu_doc_quyen", "thuong_hieu_ua_chuong", "thuong_hieu_noi_tieng",
)

_CERT_FILENAME_KEYWORDS = (
    "gcn", "gcb", "chung_nhan", "chungnhan", "chung-nhan",
    "chung_chi", "chungchi", "chung-chi",
    "bang_khen", "bangkhen", "bang-khen", "giay_khen", "giaykhen",
    "giay_phep", "giayphep", "giay-phep",
    "cert", "certificate", "certification", "license", "accreditation",
    "kiem_nghiem", "kiemnghiem", "kiem-nghiem",
    "kiem_dinh", "kiemdinh", "kiem-dinh",
)

_CERT_DOCUMENT_TITLES = (
    "giay chung nhan", "giaychungnhan",
    "chung nhan", "chungnhan",
    "chitng nhan", "chitngnhan",
    "ching nhan", "chingnhan",
    "chung chi", "chungchi",
    "bang khen", "bangkhen",
    "giay khen", "giaykhen",
    "giay phep", "giayphep",
    "chung nhan phu hop",
    "co so du dieu kien",
    "certificate of", "certificate for",
    "certification and testing",
    "certificate of registration",
    "registration certificate",
    "fda registration",
    "food and drug administration",
    "certificate number",
    "validity of certificate",
    "certificate of conformity",
    "certificate of compliance",
    "certificate of analysis",
    "bang vinh danh", "vinh danh",
    "thuong hieu doc quyen",
    "thuong hieu ua chuong",
    "thuong hieu noi tieng",
    "thuong hieu tieu bieu",
    "top 10 thuong hieu",
    "top 50 thuong hieu",
    "top 100 thuong hieu",
    "dat top 10", "dat top 50", "dat top 100",
)


def _has_cert_document_title(norm_full: str) -> bool:
    """Check if normalized OCR text contains official certificate/standard titles (handles merged tokens)."""
    norm_compact = re.sub(r"\s+", "", norm_full)
    for dt in _CERT_DOCUMENT_TITLES:
        dt_norm = _normalize_ocr_text(dt)
        if dt_norm in norm_full:
            return True
        dt_compact = re.sub(r"\s+", "", dt_norm)
        if len(dt_compact) >= 5 and dt_compact in norm_compact:
            return True
    if re.search(r"\bcertificate\b", norm_full):
        return True
    return False

_PEOPLE_KEYWORDS = (
    "nguoi", "founder", "ceo", "staff", "nhan_vien", "nhanvien", "chan_dung", "portrait",
    "team", "chu_doanh_nghiep", "giam_doc", "giamdoc", "leader", "ban_lanh_dao", "member"
)

_cv_thread_local = threading.local()

_YUNET_MODEL_NAME = "face_detection_yunet_2023mar.onnx"
_YUNET_MODEL_URL = "https://media.githubusercontent.com/media/opencv/opencv_zoo/main/models/face_detection_yunet/face_detection_yunet_2023mar.onnx"
_YUNET_MODEL_PATH = Path(__file__).resolve().parent / _YUNET_MODEL_NAME


def _ensure_yunet_model() -> Path | None:
    """Ensure the YuNet ONNX model exists locally, downloading it once if necessary."""
    if _YUNET_MODEL_PATH.exists() and _YUNET_MODEL_PATH.stat().st_size > 10000:
        return _YUNET_MODEL_PATH
    try:
        resp = requests.get(_YUNET_MODEL_URL, timeout=20)
        if resp.status_code == 200 and len(resp.content) > 10000:
            _YUNET_MODEL_PATH.write_bytes(resp.content)
            return _YUNET_MODEL_PATH
    except Exception:
        pass
    return _YUNET_MODEL_PATH if _YUNET_MODEL_PATH.exists() else None


def _get_thread_face_detector():
    """Cache OpenCV YuNet DNN and Haar cascades per thread to avoid disk re-reads."""
    if not hasattr(_cv_thread_local, "face_detector_init"):
        _cv_thread_local.face_detector_init = True
        _cv_thread_local.yunet = None
        _cv_thread_local.cascades = []

        model_path = _ensure_yunet_model()
        if cv2 is not None and hasattr(cv2, "FaceDetectorYN") and model_path is not None:
            try:
                _cv_thread_local.yunet = cv2.FaceDetectorYN.create(
                    str(model_path), "", (300, 300), score_threshold=0.80, nms_threshold=0.3
                )
            except Exception:
                _cv_thread_local.yunet = None

        if cv2 is not None:
            for cascade_name in ("haarcascade_frontalface_alt2.xml", "haarcascade_frontalface_alt.xml"):
                path_str = cv2.data.haarcascades + cascade_name
                if os.path.exists(path_str):
                    _cv_thread_local.cascades.append(cv2.CascadeClassifier(path_str))

    return _cv_thread_local.yunet, _cv_thread_local.cascades


def _detect_human_faces(img: np.ndarray, gray: np.ndarray) -> bool:
    """Robust human face detection using YuNet DNN (primary) with refined Haar fallback.
    Avoids false positives from text/packaging, round logos, cashew/macadamia nuts, and hands.
    """
    if cv2 is None or img is None or gray is None:
        return False

    h, w = img.shape[:2]
    min_dim = min(h, w)
    yunet, cascades = _get_thread_face_detector()

    # 1. Primary: YuNet DNN (deep learning, robust against packaging, text, hands, and nuts)
    if yunet is not None:
        try:
            scale = 640.0 / max(h, w) if max(h, w) > 640 else 1.0
            sw, sh = int(w * scale), int(h * scale)
            img_s = cv2.resize(img, (sw, sh), interpolation=cv2.INTER_AREA) if scale != 1.0 else img
            yunet.setInputSize((sw, sh))
            _, faces = yunet.detect(img_s)
            if faces is not None:
                min_dim = min(sw, sh)
                valid_faces = [
                    f for f in faces
                    if float(f[-1]) >= 0.80 and min(float(f[2]), float(f[3])) >= 10
                ]
                # Group / team photos: multiple people in frame with smaller relative face sizes
                if len(valid_faces) >= 2:
                    if any(min(float(f[2]), float(f[3])) >= min_dim * 0.02 for f in valid_faces):
                        return True
                # Single face / portraits: require face size >= 2.5% of image dimensions
                if any(min(float(f[2]), float(f[3])) >= min_dim * 0.025 for f in valid_faces):
                    return True
            return False
        except Exception:
            pass

    # 2. Fallback: Refined Haar Cascades with variance filtering to reject text & flat textures
    if cascades:
        try:
            min_s = max(45, int(min_dim * 0.08))
            for cascade in cascades:
                faces = cascade.detectMultiScale(gray, scaleFactor=1.08, minNeighbors=7, minSize=(min_s, min_s))
                for x, y, fw, fh in faces:
                    roi = gray[y : y + fh, x : x + fw]
                    var = cv2.Laplacian(roi, cv2.CV_64F).var()
                    # Real faces have smooth gradations (var roughly 50 to 1000). Text on packaging is > 1500.
                    if 50 < var < 1000:
                        return True
        except Exception:
            pass

    return False


def _normalize_filename(stem: str) -> str:
    """Normalize string by removing diacritics, converting to lowercase, replacing punctuation."""
    norm = unicodedata.normalize("NFKD", stem).encode("ASCII", "ignore").decode("utf-8").lower()
    return re.sub(r"[^\w\s]", "_", norm)


def _normalize_ocr_text(s: str) -> str:
    """Normalize OCR text for keyword searching."""
    norm = unicodedata.normalize("NFKD", s).encode("ASCII", "ignore").decode("utf-8").lower()
    return re.sub(r"[^\w\s]", " ", norm)


def _matches_filename_keyword(stem: str, keywords: tuple[str, ...]) -> bool:
    """Check if any keyword matches as a whole word, token, or phrase in the filename stem.
    Prevents accidental substring matches (e.g. 'pho' in 'dau_phong' or 'kho' in 'keo_khom')."""
    words = " " + " ".join(re.findall(r"[a-zA-Z0-9]+", stem.lower())) + " "
    stem_compact = re.sub(r"[^a-zA-Z0-9]", "", stem.lower())
    for kw in keywords:
        clean_kw = " " + " ".join(re.findall(r"[a-zA-Z0-9]+", kw.lower())) + " "
        if clean_kw in words:
            return True
        kw_compact = re.sub(r"[^a-zA-Z0-9]", "", kw.lower())
        if len(kw_compact) >= 5 and f" {kw_compact} " in words:
            return True
        if len(kw_compact) >= 6 and kw_compact in stem_compact:
            return True
    return False


# Additional OCR phrase patterns for awards/rewards that may not appear verbatim in filenames.
# These are checked against the full OCR text block (already ASCII-normalised).
_CERT_OCR_PHRASES = (
    "tieu bieu",       # tiêu biểu
    "uy ban nhan dan", # ủy ban nhân dân
    "ubnd",
    "giai thuong",     # giải thưởng
    "bang khen",       # bằng khen
    "giay khen",       # giấy khen
    "cup vang",        # cúp vàng
    "phan thuong",     # phần thưởng
    "vinh danh",       # vinh danh
    "nong thon tieu bieu",  # nông thôn tiêu biểu
    "san pham tieu bieu",   # sản phẩm tiêu biểu
    "cap tinh",        # cấp tỉnh
    "cap quoc gia",    # cấp quốc gia
    "ghi nhan",        # ghi nhận
    "chitng nhan",     # OCR variation for chứng nhận
    "ching nhan",
    "ban to chuc",     # ban tổ chức
    "truong ban to chuc", # trưởng ban tổ chức
    "quyet dinh",      # quyết định
    "quyetdjnh",
    "quyetdinh",
    "thuong hieu doc quyen", # thương hiệu độc quyền
    "thuong hieu ua chuong", # thương hiệu ưa chuộng
    "thuong hieu noi tieng", # thương hiệu nổi tiếng
    "top 10 thuong hieu",
    "dat top 10",
    "cong hoa xa hoi chu nghia viet nam",
    "doc lap tu do hanh phuc",
)


def _has_cert_text(text: str) -> bool:
    """Check if text contains any certificate / standard / quality / award keywords."""
    norm = _normalize_ocr_text(text)
    for kw in _CERT_KEYWORDS:
        kw_clean = kw.replace("_", " ").replace("-", " ")
        if re.search(r"\b" + re.escape(kw_clean) + r"\b", norm) or (len(kw_clean) >= 4 and kw_clean in norm):
            return True
    # Also check extra OCR phrases (award/trophy language not covered by filename keywords)
    for phrase in _CERT_OCR_PHRASES:
        if phrase in norm:
            return True
    return False


def _is_real_photo(img: np.ndarray) -> bool:
    """Check if image is a real-world photograph rather than animated/vector/clipart."""
    try:
        small = cv2.resize(img, (250, 250), interpolation=cv2.INTER_AREA)
        unique_colors = len(np.unique(small.reshape(-1, 3), axis=0))
        if unique_colors < 3500:
            return False
        std_rgb = np.std(small, axis=(0, 1))
        if float(np.mean(std_rgb)) < 18.0:
            return False
        gray = cv2.cvtColor(small, cv2.COLOR_BGR2GRAY)
        lap_var = float(cv2.Laplacian(gray, cv2.CV_64F).var())
        if lap_var < 50.0:
            return False
        return True
    except Exception:
        return True


def _is_place_image(norm_stem: str, img: np.ndarray, ocr_boxes: list) -> bool:
    """Detect if an image depicts a physical place/facade/street (Category 4).
    Must be a real camera photograph (not animated/clipart).
    Detects storefront signboards, banners/logos on building facades, or street/facility signage.
    Excludes product packaging that merely lists manufacturer addresses.
    """
    # 0. Exclude certificate files (certificates are documents, never physical places)
    if _matches_filename_keyword(norm_stem, _CERT_FILENAME_KEYWORDS):
        return False

    # 1. Filename keyword match
    if _matches_filename_keyword(norm_stem, _PLACE_KEYWORDS):
        return True

    if img is None or not _is_real_photo(img):
        return False

    # 2. If no text is detected via OCR, the image cannot be confirmed as a
    #    storefront / facade / facility with signage. Product photos (especially
    #    food/produce or items on white/light backgrounds in landscape ratio)
    #    have no OCR text and must NOT be misclassified as a place.
    if not ocr_boxes:
        return False

    full_text = " ".join(b[1] for b in ocr_boxes)
    norm_full = _normalize_ocr_text(full_text)
    # Also build a compact (no-space) version to match against OCR tokens that were
    # merged without spaces (e.g. "CONGTYTNHH..." instead of "CONG TY TNHH ...").
    norm_compact = re.sub(r"\s+", "", norm_full)

    # Normalize the keyword sets the same way as OCR text (non-alphanum → space)
    # so that keywords like "dc:" correctly match the normalized text "dc ".
    _norm_est_words  = [_normalize_ocr_text(w) for w in _PLACE_ESTABLISHMENT_WORDS]
    _norm_loc_words  = [_normalize_ocr_text(w) for w in _PLACE_LOCATION_WORDS]
    _norm_est_compact = [re.sub(r"\s+", "", w) for w in _norm_est_words]

    # Exclude certificate documents (contain official titles like "giay chung nhan", "certificate", etc.)
    if _has_cert_document_title(norm_full):
        return False

    # Exclude food packaging / product bags – product labels commonly print the manufacturer
    # address ("Cong ty", "Dia chi", "Duong"…) which would otherwise fool the place detector.
    if any(pw in norm_full for pw in _PACKAGING_EXCLUDE_WORDS):
        return False

    def _has_est(text_norm: str, text_compact: str) -> bool:
        """True if any establishment word matches in either spaced or compact OCR text."""
        for ew, ew_c in zip(_norm_est_words, _norm_est_compact):
            if ew and ew in text_norm:
                return True
            if ew_c and len(ew_c) >= 4 and ew_c in text_compact:
                return True
        return False

    def _has_loc(text_norm: str) -> bool:
        """True if any location keyword matches (with normalized colons/punctuation)."""
        return any(lw and lw in text_norm for lw in _norm_loc_words)

    # Check for storefront / facade signboard.
    # A genuine place photo has a wide signboard (>= 55% of image width) in the upper
    # portion of the image that contains an establishment name.  The 55 % threshold is
    # stricter than the old 45 % to avoid matching text banners on product packaging.
    h, w = img.shape[:2]
    has_facade_signboard = False
    for box in ocr_boxes:
        coords, text, conf = box
        xs = [pt[0] for pt in coords]
        ys = [pt[1] for pt in coords]
        bw = max(xs) - min(xs)
        bh = max([pt[1] for pt in coords]) - min([pt[1] for pt in coords])
        cy = (max(ys) + min(ys)) / 2.0
        # Wide text box (>= 55% of image width) in upper 70% of image
        if bw >= w * 0.55 and cy <= h * 0.70:
            norm_t = _normalize_ocr_text(text)
            norm_t_c = re.sub(r"\s+", "", norm_t)
            if _has_est(norm_t, norm_t_c):
                has_facade_signboard = True
                break

    has_est = _has_est(norm_full, norm_compact)
    has_loc = _has_loc(norm_full)

    # A genuine place photo must have ALL THREE signals present:
    #   1. A wide facade signboard (>= 55% of image width) with an establishment name
    #   2. Additional establishment-type words in the full OCR text
    #   3. Location / address words in the full OCR text
    # This triple requirement prevents product labels (which often print the manufacturer
    # name + address) from being mistaken for a storefront photograph.
    if has_facade_signboard and has_est and has_loc:
        return True

    return False


# ---------------------------------------------------------------------------
# Manual classification overrides
# Maps normalized filename stems → (category_id, cert_prominence_score).
# Use this to correct images that the automated classifier gets wrong.
#   Category 0 = Banner, 1 = Certificate, 2 = People, 3 = Products / Other, 4 = Place
# ---------------------------------------------------------------------------
# Add entries here only when the automated classifier gets a specific image wrong:
# e.g.  _normalize_filename("some filename stem"): (1, 0.02),  # Certificate
_CLASSIFICATION_OVERRIDES: dict[str, tuple[int, float]] = {}


def _is_document_like(img: "np.ndarray") -> bool:
    """Return True when an image looks like a scanned/photographed flat document.

    Real certificates, awards, and official papers are printed on white/off-white
    paper: the vast majority of pixels have very low HSV saturation (≈ grey/white).
    Product packaging photos, by contrast, have rich, varied colors and will have
    a noticeably higher median saturation.

    Threshold: median HSV-Saturation < 30 out of 255  (≈ 12% saturation).
    Also requires at least 60% of pixels to be "near-white" (Value > 180) to
    confirm the document has a bright paper background rather than a dark product.
    """
    if cv2 is None or np is None or img is None:
        return True  # no CV2 – cannot distinguish, allow cert fallback
    try:
        small = cv2.resize(img, (200, 200), interpolation=cv2.INTER_AREA)
        hsv = cv2.cvtColor(small, cv2.COLOR_BGR2HSV)
        sat = hsv[:, :, 1].flatten()    # Saturation channel 0-255
        val = hsv[:, :, 2].flatten()    # Value channel 0-255
        median_sat = float(np.median(sat))
        bright_fraction = float(np.mean(val > 180))
        return median_sat < 30 and bright_fraction >= 0.60
    except Exception:
        return True


def _classify_single_image(
    path: Path,
    converted_pdf_stems: set[str] | None = None
) -> tuple[Path, int, float]:
    """Classify a single image: returns (path, category_id, cert_prominence_score)
       Category 4: Place (real photo of house facade, street, storefront with banner/logo)
       Category 0: Banner (cover, poster, pano, digital graphics, etc.)
       Category 1: Certificate (including products/labels with certificate logos/OCOP/ISO/ATTP/etc.)
       Category 2: People
       Category 3: Products / Other

       cert_prominence_score measures keyword size (e.g. OCOP) relative to image dimensions.
       Larger words get higher priority and display first (leftmost in certificates cluster).
    """
    norm = _normalize_filename(path.stem)

    # 0. Manual override (highest priority – corrects known misclassifications)
    if norm in _CLASSIFICATION_OVERRIDES:
        cat, score = _CLASSIFICATION_OVERRIDES[norm]
        return path, cat, score

    # 1. Check Place keywords first (highest priority cluster before Banner)
    if _matches_filename_keyword(norm, _PLACE_KEYWORDS):
        return path, 4, 0.0

    # 2. Check Banner keywords
    if _matches_filename_keyword(norm, _BANNER_KEYWORDS):
        return path, 0, 0.0

    # 2b. Check aspect ratio for wide banners / Facebook covers / panoramic banners
    try:
        with Image.open(path) as img:
            w, h = img.size
        ratio = w / h if h else 1.0
    except Exception:
        ratio = 1.0

    # Non-square logo keyword or ultra-wide aspect ratio (>= 1.9)
    # Defer returning Banner until after Place check in step 3 so panoramic place photos aren't hijacked
    is_wide_ratio = (ratio >= 1.9) or ("logo" in norm and (ratio < 0.85 or ratio > 1.20))

    is_known_cert = bool(
        (converted_pdf_stems and path.stem in converted_pdf_stems)
        or _matches_filename_keyword(norm, _CERT_FILENAME_KEYWORDS)
    )

    # 3. Visual & OCR inspection (detect Place, certificate logos, OCOP, seals, text)
    if cv2 is not None and np is not None:
        try:
            # Read image via buffer to support unicode/diacritic paths on Windows
            data = np.frombuffer(path.read_bytes(), dtype=np.uint8)
            img = cv2.imdecode(data, cv2.IMREAD_COLOR)
            if img is not None:
                h, w = img.shape[:2]
                # Downscale to max 960px for fast, accurate OCR & computer vision
                max_dim = 960
                if max(h, w) > max_dim:
                    scale = max_dim / max(h, w)
                    img_small = cv2.resize(img, (int(w * scale), int(h * scale)), interpolation=cv2.INTER_AREA)
                else:
                    img_small = img
                sh, sw = img_small.shape[:2]
                img_area = sw * sh
                min_dim = min(sw, sh)
                gray = cv2.cvtColor(img_small, cv2.COLOR_BGR2GRAY)

                ocr_boxes = []
                if _rapid_ocr is not None:
                    try:
                        res, _ = _rapid_ocr(img_small)
                        if res:
                            ocr_boxes = res
                    except Exception:
                        pass

                full_text = " ".join(b[1] for b in ocr_boxes)
                norm_full = _normalize_ocr_text(full_text)
                norm_compact = re.sub(r"\s+", "", norm_full)
                has_cert_title = _has_cert_document_title(norm_full)
                has_pkg = any(pw in norm_full or pw in norm_compact for pw in _PACKAGING_EXCLUDE_WORDS)

                # Detect official Vietnamese National Header on documents
                has_nat_header = (
                    ("cong hoa xa hoi" in norm_full or "chunghiavietnam" in norm_compact or "chu nghia viet nam" in norm_full or "conghoa" in norm_compact)
                    and ("doc lap" in norm_full or "tu do" in norm_full or "hanh phuc" in norm_full or "doclap" in norm_compact or "hanhphuc" in norm_compact)
                )

                # 3a. Check Place first (real photo of house facade / street / storefront with banner/logo)
                # Never classify known certificates or documents with certificate titles as Place!
                if not is_known_cert and not has_cert_title and not has_pkg and not has_nat_header:
                    if _is_place_image(norm, img_small, ocr_boxes):
                        return path, 4, 0.0

                # If wide ratio and NOT a place, classify as Banner.
                # Skip Banner for product packaging images (wide product shots are not banners).
                if is_wide_ratio and not has_pkg:
                    return path, 0, 0.0

                # 3b. Detect People keywords / faces
                is_people_kw = _matches_filename_keyword(norm, _PEOPLE_KEYWORDS)
                has_faces = _detect_human_faces(img_small, gray)

                # 3c. Certificate classification:
                # Must be a known cert file (PDF/filename) OR have explicit certificate document titles
                # without commercial packaging markers.
                is_cert_doc = is_known_cert or (has_cert_title and not has_pkg and (_is_document_like(img_small) or np.mean(gray) >= 140 or is_known_cert))

                # Official certificate documents with National Header + cert/award keywords
                if not is_cert_doc and not has_pkg and has_nat_header:
                    if has_cert_title or _has_cert_text(full_text) or any(
                        kw in norm_full or kw in norm_compact for kw in (
                            "chitng", "chung", "khen", "thuong hieu", "ban to chuc", "quyet dinh", "quyetdjnh", "top 10", "top 50", "cup", "vinh danh"
                        )
                    ):
                        is_cert_doc = True

                # Visual check for award/certificate documents (bright document paper + cert keywords in OCR)
                if not is_cert_doc and not has_pkg and np.mean(gray) >= 140:
                    if ("uy ban nhan dan" in norm_full or "ubnd" in norm_full) and (
                        "chung nhan" in norm_full or "khen" in norm_full or "tieu bieu" in norm_full
                    ):
                        # Authority-issued certificate (UBND + cert phrase)
                        is_cert_doc = True
                    elif _has_cert_text(full_text) and _is_document_like(img_small):
                        # Bright-paper document with cert/standard/award keywords in OCR —
                        # covers ISO, HACCP, FDA, ATTP, OCOP etc. even when the seal is
                        # rectangular/square (not a circular red stamp), so the old
                        # circularity contour check would have missed it.
                        # _is_document_like() guards against product photos that merely
                        # display cert logos/seals on colorful packaging labels.
                        is_cert_doc = True
                    else:
                        # Fallback: look for a circular red seal as a visual cert indicator
                        hsv = cv2.cvtColor(img_small, cv2.COLOR_BGR2HSV)
                        mask_r = cv2.bitwise_or(
                            cv2.inRange(hsv, np.array([0, 70, 50]), np.array([10, 255, 255])),
                            cv2.inRange(hsv, np.array([170, 70, 50]), np.array([180, 255, 255]))
                        )
                        contours, _ = cv2.findContours(mask_r, cv2.RETR_EXTERNAL, cv2.CHAIN_APPROX_SIMPLE)
                        for c in contours:
                            area = cv2.contourArea(c)
                            if (sh * sw * 0.002) < area < (sh * sw * 0.12):
                                peri = cv2.arcLength(c, True)
                                if peri > 0 and 4 * np.pi * (area / (peri * peri)) > 0.45:
                                    if _has_cert_text(full_text):
                                        is_cert_doc = True
                                        break

                if is_cert_doc:
                    max_cert_score = 0.0
                    for box in ocr_boxes:
                        coords, text, conf = box
                        if _has_cert_text(text) or _has_cert_document_title(_normalize_ocr_text(text)):
                            xs = [pt[0] for pt in coords]
                            ys = [pt[1] for pt in coords]
                            box_w = max(xs) - min(xs)
                            box_h = max(ys) - min(ys)
                            char_h = min(box_w, box_h)
                            font_ratio = char_h / min_dim
                            area_ratio = (box_w * box_h) / img_area
                            ocop_bonus = 1.2 if "ocop" in _normalize_ocr_text(text) else 1.0
                            prominence = (font_ratio * 0.7 + area_ratio * 0.3) * ocop_bonus
                            if prominence > max_cert_score:
                                max_cert_score = prominence
                    if max_cert_score == 0:
                        max_cert_score = 0.02
                    return path, 1, max_cert_score

                if is_people_kw or has_faces:
                    return path, 2, 0.0
        except Exception:
            pass

    if is_wide_ratio:
        return path, 0, 0.0

    if is_known_cert:
        return path, 1, 0.02

    # If filename matches people keywords even without CV2
    if _matches_filename_keyword(norm, _PEOPLE_KEYWORDS):
        return path, 2, 0.0

    return path, 3, 0.0


def _get_image_color_sort_key(path: Path) -> tuple:
    """Extract dominant/average color features of an image to sort by color similarity.
    Groups grayscale/achromatic images first (sorted by brightness), followed by
    chromatic images sorted smoothly by Hue, Saturation, and Brightness.
    """
    try:
        # Open and resize to small thumbnail for fast color analysis
        with Image.open(path) as img:
            img_rgb = img.convert("RGB").resize((50, 50))
            pixels = list(img_rgb.getdata())

        if not pixels:
            return (2, 0.0, 0.0, 0.0, path.name)

        # Ignore pure/near-white background pixels if image is a product/cutout on white
        fg_pixels = [p for p in pixels if not (p[0] > 240 and p[1] > 240 and p[2] > 240)]
        target_pixels = fg_pixels if len(fg_pixels) >= len(pixels) * 0.05 else pixels

        n = len(target_pixels)
        r = sum(p[0] for p in target_pixels) / n / 255.0
        g = sum(p[1] for p in target_pixels) / n / 255.0
        b = sum(p[2] for p in target_pixels) / n / 255.0

        h, s, v = colorsys.rgb_to_hsv(r, g, b)

        # Grayscale / Low saturation (achromatic: black -> gray -> white)
        if s < 0.12 or v < 0.10:
            return (0, round(v, 2), round(s, 2), 0.0, path.name)
        else:
            # Chromatic: group by Hue (0-360), Saturation, and Value
            return (1, round(h * 360, 1), round(s, 2), round(v, 2), path.name)
    except Exception:
        return (2, 0.0, 0.0, 0.0, path.name)


def _sort_images_by_color(images: list[Path]) -> list[Path]:
    """Sort a list of image paths so that images with same or similar colors are placed together."""
    return sorted(images, key=_get_image_color_sort_key)


def reorder_gallery_images(
    images: list[Path],
    converted_pdf_stems: set[str] | None = None,
    workers: int = 6,
) -> tuple[list[Path], list[Path], list[Path], list[Path], list[Path], list[Path]]:
    """Classify gallery images in parallel into 5 categories:
       1. Place (storefront, building facade, street view, facility with signage/banner/logo)
       2. Banners (Banner, cover, poster, etc.)
       3. Certificates (OCOP, Giấy chứng nhận, etc.)
       4. People
       5. Products and other

    Within certificates, images with bigger certificate keywords (like OCOP) have higher
    priority and are displayed leftmost (immediately following the logo / banners).
    Ties within certificates and images within other categories are sorted by color.

    Returns:
       (place_paths, banner_paths, cert_paths, people_paths, product_paths, upload_paths)
       where upload_paths is [place + banners + certs + people + products]
       so that the website renders [place] first, then [banners], then [certs], then [people], then [products].
    """
    places: list[Path] = []
    banners: list[Path] = []
    certs_scored: list[tuple[Path, float]] = []
    people: list[Path] = []
    products: list[Path] = []

    if not images:
        return [], [], [], [], [], []

    # Run fast parallel classification across threads
    active_workers = min(len(images), workers)
    with ThreadPoolExecutor(max_workers=active_workers) as ex:
        classified = list(ex.map(lambda p: _classify_single_image(p, converted_pdf_stems), images))

    for p, cat, score in classified:
        if cat == 4:
            places.append(p)
        elif cat == 0:
            banners.append(p)
        elif cat == 1:
            certs_scored.append((p, score))
        elif cat == 2:
            people.append(p)
        else:
            products.append(p)

    # Sort each category:
    places = _sort_images_by_color(places)
    banners = _sort_images_by_color(banners)
    # Certificates: sort by descending keyword prominence score (bigger OCOP/cert words first); tie-break by color
    certs_sorted = sorted(certs_scored, key=lambda item: (-round(item[1], 4), _get_image_color_sort_key(item[0])))
    certs = [p for p, _ in certs_sorted]
    people = _sort_images_by_color(people)
    products = _sort_images_by_color(products)

    # Desired visual order from Left to Right: Place -> Banners -> Certs -> People -> Products
    display_order = places + banners + certs + people + products

    return places, banners, certs, people, products, display_order


# ---------------------------------------------------------------------------
# Image uploads
# ---------------------------------------------------------------------------

def _strip_s3(location: str) -> str:
    """Strip S3/CloudFront prefix to get a relative path."""
    for delim in (".amazonaws.com/", "cloudfront.net/"):
        if delim in location:
            return location.split(delim, 1)[1]
    return location


_CLOUDFRONT = "https://d2x9yynu7r2rki.cloudfront.net"


def _to_cloudfront(location: str) -> str:
    """Convert any S3/CloudFront URL to the canonical CloudFront full URL."""
    relative = _strip_s3(location)
    if not relative:
        return location
    return f"{_CLOUDFRONT}/{relative}"


def _upload_headers(token: str, base: str) -> dict:
    return {
        "authorization": f"Bearer {token}",
        "accept": "application/json",
        "locale": "vn",
        "origin": f"https://{base}",
        "referer": f"https://{base}/",
        "user-agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/125.0.0.0 Safari/537.36",
    }


def _raise_with_body(resp: requests.Response) -> None:
    """Like raise_for_status but also prints the server error body."""
    if resp.status_code >= 400:
        body = resp.text[:500]
        raise requests.HTTPError(
            f"{resp.status_code} {resp.reason} for url: {resp.url}\nServer response: {body}",
            response=resp,
        )


# SSLEOFError and stale-pool ConnectionError are not retried by urllib3 on
# POST requests, so we handle them manually with exponential back-off.
_SSL_ERRORS = (requests.exceptions.SSLError, requests.exceptions.ConnectionError)


def _post_with_retry(url: str, *, files=None, json=None, headers: dict, timeout: int | tuple[float, float], retries: int = 3):
    if retries < 1:
        raise ValueError("retries must be at least 1")
    file_items = files.items() if isinstance(files, dict) else (files or [])
    streams = []
    for _, value in file_items:
        stream = value[1] if isinstance(value, tuple) else value
        if hasattr(stream, "tell") and hasattr(stream, "seek"):
            streams.append((stream, stream.tell()))
    delay = 2
    for attempt in range(retries):
        if attempt:
            for stream, position in streams:
                stream.seek(position)
        try:
            return _session.post(url, files=files, json=json, headers=headers, timeout=timeout)
        except _SSL_ERRORS + (requests.exceptions.Timeout,) as exc:
            if attempt == retries - 1:
                raise
            print_warn(f"Upload connection/timeout error (attempt {attempt + 1}/{retries}), retrying in {delay}s: {exc}")
            time.sleep(delay)
            delay *= 2


def upload_resize(
    base: str, token: str, path: Path,
    entity: str, origin: bool, size: str | None = None
) -> dict:
    params = f"entity={entity}&targetFileType=webp&origin={'true' if origin else 'false'}"
    if size:
        params += f"&size={size}"
    url = f"https://{base}/api/uploadImageResize?{params}"
    mime = mimetypes.guess_type(path.name)[0] or "image/jpeg"
    with open(path, "rb") as fh:
        resp = _post_with_retry(
            url,
            files={"file": (path.name, fh, mime)},
            headers=_upload_headers(token, base),
            timeout=(15, 120),
        )
    _raise_with_body(resp)
    return resp.json()


def upload_gallery_batch(base: str, token: str, paths: list[Path]) -> list[dict]:
    url = f"https://{base}/api/uploadFiles"
    fhs: list = []
    files: list = []
    try:
        for p in paths:
            mime = mimetypes.guess_type(p.name)[0] or "image/jpeg"
            fh = open(p, "rb")
            fhs.append(fh)
            files.append(("files", (p.name, fh, mime)))
        resp = _post_with_retry(
            url,
            files=files,
            headers=_upload_headers(token, base),
            timeout=120,
        )
        _raise_with_body(resp)
        return resp.json()
    finally:
        for fh in fhs:
            fh.close()

# ---------------------------------------------------------------------------
# Lookup helpers
# ---------------------------------------------------------------------------

def _strip_punctuation(text: str) -> str:
    """Remove all punctuation from text, keeping only letters, numbers, and spaces.
    This helps match Vietnamese city names that may differ in diacritics.
    Examples:
        'Thanh Hóa' → 'Thanh Hoa'
        'Thanh Hoá' → 'Thanh Hoa'
    """
    return re.sub(r'[^\w\s]', '', text)


CITY_ALIASES: list[tuple[str, str]] = [
    # Thừa Thiên Huế (addresses commonly write "Thành phố Huế", "TP Huế", "Huế")
    (r"\b(tỉnh\s+)?thừa\s+thiên\s+huế\b", "Tỉnh Thừa Thiên Huế"),
    (r"\b(thành\s+phố|tp\.?)\s+huế\b", "Tỉnh Thừa Thiên Huế"),
    (r"(?<!phố\s)\bhuế\b", "Tỉnh Thừa Thiên Huế"),
    
    # Hồ Chí Minh
    (r"\b(thành\s+phố|tp\.?)\s+hồ\s+chí\s+minh\b", "Thành Phố Hồ Chí Minh"),
    (r"\b(tp\.?\s*hcm|tphcm|sài\s+gòn)\b", "Thành Phố Hồ Chí Minh"),
    
    # Hà Nội
    (r"\b(thành\s+phố|tp\.?)\s+hà\s+nội\b", "Thành Phố Hà Nội"),
    
    # Bà Rịa - Vũng Tàu
    (r"\bbà\s+rịa\s*[-–]?\s*vũng\s+tàu\b", "Tỉnh Bà Rịa - Vũng Tàu"),
    (r"\b(thành\s+phố|tp\.?)\s+vũng\s+tàu\b", "Tỉnh Bà Rịa - Vũng Tàu"),
    (r"\b(thành\s+phố|tp\.?)\s+bà\s+rịa\b", "Tỉnh Bà Rịa - Vũng Tàu"),
    (r"\bvũng\s+tàu\b", "Tỉnh Bà Rịa - Vũng Tàu"),
    
    # Lâm Đồng (Đà Lạt, Bảo Lộc)
    (r"\b(thành\s+phố|tp\.?)\s+(đà\s+lạt|bảo\s+lộc)\b", "Tỉnh Lâm Đồng"),
    (r"\bđà\s+lạt\b", "Tỉnh Lâm Đồng"),
    
    # Khánh Hòa (Nha Trang, Cam Ranh)
    (r"\b(thành\s+phố|tp\.?)\s+(nha\s+trang|cam\s+ranh)\b", "Tỉnh Khánh Hòa"),
    (r"\bnha\s+trang\b", "Tỉnh Khánh Hòa"),
    
    # Bình Định (Quy Nhơn)
    (r"\b(thành\s+phố|tp\.?)\s+quy\s+nhơn\b", "Tỉnh Bình Định"),
    (r"\bquy\s+nhơn\b", "Tỉnh Bình Định"),
    
    # Bình Thuận (Phan Thiết)
    (r"\b(thành\s+phố|tp\.?)\s+phan\s+thiết\b", "Tỉnh Bình Thuận"),
    (r"\bphan\s+thiết\b", "Tỉnh Bình Thuận"),
    
    # Đắk Lắk (Buôn Ma Thuột)
    (r"\b(thành\s+phố|tp\.?)\s+buôn\s+ma\s+thuột\b", "Tỉnh Đắk Lắk"),
    (r"\bbuôn\s+ma\s+thuột\b", "Tỉnh Đắk Lắk"),
    
    # Gia Lai (Pleiku)
    (r"\b(thành\s+phố|tp\.?)\s+pleiku\b", "Tỉnh Gia Lai"),
    (r"\bpleiku\b", "Tỉnh Gia Lai"),
    
    # Quảng Ninh (Hạ Long, Cẩm Phả, Móng Cái, Uông Bí)
    (r"\b(thành\s+phố|tp\.?)\s+(hạ\s+long|cẩm\s+phả|móng\s+cái|uông\s+bí)\b", "Tỉnh Quảng Ninh"),
    (r"\bhạ\s+long\b", "Tỉnh Quảng Ninh"),
    
    # Kiên Giang (Phú Quốc, Rạch Giá, Hà Tiên)
    (r"\b(thành\s+phố|tp\.?)\s+(phú\s+quốc|rạch\s+giá|hà\s+tiên)\b", "Tỉnh Kiên Giang"),
]


def get_city_name(city_id: str, city_data: list) -> str:
    """Return the display name of a city given its ID."""
    for entry in city_data:
        if entry.get("id") == city_id:
            return entry.get("name", "")
    return ""


def lookup_city(address: str, city_data: list) -> str:
    low = unicodedata.normalize("NFC", address.lower())
    low_no_punct = _strip_punctuation(low)
    
    # 1. Exact match against full province / city names
    for entry in city_data:
        name = unicodedata.normalize("NFC", entry.get("name", "").lower())
        name_no_punct = _strip_punctuation(name)
        if name_no_punct and name_no_punct in low_no_punct:
            return entry["id"]
    
    # 2. Check aliases / known patterns (e.g. "Thành phố Huế" → "Tỉnh Thừa Thiên Huế")
    for pattern, target_name in CITY_ALIASES:
        if re.search(pattern, low, re.IGNORECASE):
            for entry in city_data:
                if entry.get("name") == target_name:
                    return entry["id"]

    # 3. Retry with short names (strip "tỉnh ", "thành phố ", etc.)
    for entry in city_data:
        name = unicodedata.normalize("NFC", entry.get("name", "").lower())
        short = re.sub(r"^(tỉnh|thành phố|đặc khu)\s+", "", name).strip()
        short_no_punct = _strip_punctuation(short)
        if short_no_punct and short_no_punct in low_no_punct:
            return entry["id"]
    
    return "0008400079"  # fallback: Thành Phố Hồ Chí Minh


# Administrative & geographical address keywords whose first letter should always be capitalized.
# Sorted by length descending so multi-word units (e.g. "khu dân cư", "cụm công nghiệp") match first.
_ADDRESS_KEYWORDS = [
    "cụm công nghiệp", "khu công nghiệp", "khu công nghệ cao", "khu kinh tế",
    "khu chế xuất", "khu tái định cư", "khu dân cư", "cụm dân cư",
    "khu đô thị", "khu nhà ở",
    "tòa nhà", "khu phố", "tổ dân phố", "thị trấn", "thị xã", "thành phố", "đặc khu",
    "tỉnh", "quận", "huyện", "phường", "xã", "thôn", "ấp", "bản", "buôn",
    "sóc", "làng", "xóm", "đội", "tổ", "khóm", "khu", "cụm",
    "đường", "phố", "ngõ", "ngách", "hẻm", "kiệt",
    "phòng", "tầng", "lô", "số",
]
_ADDRESS_KEYWORDS.sort(key=len, reverse=True)
_ADDRESS_KEYWORDS_RE = re.compile(
    r"\b(" + "|".join(re.escape(k) for k in _ADDRESS_KEYWORDS) + r")\b",
    re.IGNORECASE,
)


def _split_address_parts(addr: str) -> list[str]:
    """Split comma-separated address parts without splitting decimal area values."""
    return [
        part.strip()
        for part in re.split(r",\s*(?!\d+\s*ha\b)", addr, flags=re.IGNORECASE)
        if part.strip()
    ]


def _capitalize_address_keywords(addr: str) -> str:
    """Ensure administrative and address keywords (Thôn, Ấp, Xã, Tỉnh, Thành phố,
    Khu dân cư, Cụm công nghiệp, Tổ, etc.) always have their first letter capitalized."""
    def _cap(m: re.Match) -> str:
        s = m.group(0)
        return s[0].upper() + s[1:]
    return _ADDRESS_KEYWORDS_RE.sub(_cap, addr)


def _title_address(addr: str) -> str:
    """Capitalise the first letter of each comma-separated segment and strip trailing punctuation,
    and capitalise the first letter of administrative/address keywords (Thôn, Ấp, Xã, Tỉnh, Thành phố,
    Khu dân cư, Cụm công nghiệp, Tổ, etc.).

    e.g. '160/3F tổ 15, ấp Thới Tây 2, xã Hóc Môn, thành Phố Hồ Chí Minh'
         → '160/3F Tổ 15, Ấp Thới Tây 2, Xã Hóc Môn, Thành Phố Hồ Chí Minh'
    """
    addr = re.sub(r"[\s.,;:!\-–—/]+$", "", addr).strip()
    parts = _split_address_parts(addr)
    result = []
    for idx, part in enumerate(parts):
        if idx == len(parts) - 1:
            part = re.sub(r"[\s.,;:!\-–—/]+$", "", part).strip()
        if len(part) > 1:
            part = part[0].upper() + part[1:]
        elif part:
            part = part.upper()
        result.append(part)
    res = ", ".join(result)
    res = _capitalize_address_keywords(res)
    return re.sub(r"[\s.,;:!\-–—/]+$", "", res).strip()


# Regex that matches any abbreviated province/city prefix at the start of a string.
# Covers: T., Tp., Tp, TP., TP, tp., tp, T.P., t.p.
_PROVINCE_ABBR_RE = re.compile(
    r"""^\s*
    (?:
        t\.?\s*p(?:\.|\s+) # tp / tp. / t.p. / T.P. / TP / TP.
        | t\.\s+      # T.  (Tỉnh)
    )\s*""",
    re.IGNORECASE | re.VERBOSE,
)

# Full prefixes already correct – nothing to do.
_PROVINCE_FULL_PREFIX_RE = re.compile(
    r"^\s*(tỉnh|thành\s+phố|đặc\s+khu)\s+",
    re.IGNORECASE,
)


def _normalize_province_prefix(addr: str, city_data: list) -> str:
    """Ensure the province/city segment at the end of an address has a full
    Vietnamese administrative prefix ("Tỉnh" / "Thành phố").

    Rules applied to the *last* comma-separated segment:
    1. Abbreviated prefixes (T., TP, Tp, tp, TP., Tp., T.P., …) are expanded
       to the correct full prefix by looking up the city in *city_data*.
    2. If no recognised prefix is present at all, the city name is matched
       against *city_data* and the stored full name (which includes the prefix)
       is substituted.

    The rest of the address (all segments before the province) is unchanged.

    Examples::

        '9A Ngõ 6 Đặng Thùy Trâm, Phường Nghĩa Đô, Hà Nội'
            → '9A Ngõ 6 Đặng Thùy Trâm, Phường Nghĩa Đô, Thành Phố Hà Nội'

        '32 Ngõ 50 Nguyễn Hữu Thọ, Sơn La'
            → '32 Ngõ 50 Nguyễn Hữu Thọ, Tỉnh Sơn La'

        '123 Lê Lợi, TP Đà Nẵng'
            → '123 Lê Lợi, Thành Phố Đà Nẵng'
    """
    if not addr:
        return addr

    # Strip any trailing punctuation first so parts are clean
    addr = re.sub(r"[\s.,;:!\-–—/]+$", "", addr).strip()
    parts = _split_address_parts(addr)
    if not parts:
        return addr

    province_part = re.sub(r"[\s.,;:!\-–—/]+$", "", parts[-1]).strip()
    prefix_parts = parts[:-1]

    # If the last segment already has a proper full prefix, return stripped addr.
    if _PROVINCE_FULL_PREFIX_RE.match(province_part):
        new_parts = prefix_parts + [province_part]
        return ", ".join(new_parts)

    # Detect whether there is an abbreviated prefix and strip it.
    abbr_match = _PROVINCE_ABBR_RE.match(province_part)
    raw_abbr = province_part[:abbr_match.end()].strip() if abbr_match else None
    bare_name = province_part[abbr_match.end():].strip() if abbr_match else province_part

    # Determine whether abbreviation indicates "thành phố" or "tỉnh".
    # tp / TP / T.P. / Tp → Thành phố; T. alone → Tỉnh
    if abbr_match:
        abbr_text = raw_abbr.lower().replace(".", "").replace(" ", "")
        is_tp_abbr = "tp" in abbr_text  # tp, t.p., TP
    else:
        is_tp_abbr = None  # unknown – must look up

    # Normalise the bare name for matching (NFC, lowercase, no punctuation)
    bare_norm = _strip_punctuation(unicodedata.normalize("NFC", bare_name.lower()))
    bare_norm = {
        "hcm": "hồ chí minh",
        "hcmc": "hồ chí minh",
        "tphcm": "hồ chí minh",
        "sai gon": "hồ chí minh",
        "hn": "hà nội",
    }.get(bare_norm, bare_norm)

    # Try to find the entry in city_data whose *short* name matches bare_name.
    matched_full_name: str | None = None
    for entry in city_data:
        city_name_raw = entry.get("name", "")
        city_name_low = unicodedata.normalize("NFC", city_name_raw.lower())
        # Strip known prefix to get the short name.
        short = re.sub(r"^(tỉnh|thành phố|đặc khu)\s+", "", city_name_low).strip()
        short_no_punct = _strip_punctuation(short)
        if short_no_punct and short_no_punct == bare_norm:
            matched_full_name = city_name_raw  # e.g. "Thành Phố Hà Nội" / "Tỉnh Sơn La"
            break

    if matched_full_name:
        # Use the canonical full name from city_data (which already has the right prefix).
        new_province = re.sub(
            r"^thành\s+phố\b", "Thành phố", matched_full_name, flags=re.IGNORECASE
        )
    elif abbr_match:
        # We know the abbreviation type but couldn't find the city – reconstruct.
        prefix_word = "Thành phố" if is_tp_abbr else "Tỉnh"
        new_province = f"{prefix_word} {bare_name}"
    else:
        # No abbreviation and no match → cannot determine prefix; leave as-is without trailing punctuation.
        new_parts = prefix_parts + [province_part]
        return ", ".join(new_parts)

    new_parts = prefix_parts + [new_province]
    return ", ".join(new_parts)


_ADDRESS_PREFIX_START_RE = re.compile(
    r"^\s*(?:" + "|".join(re.escape(k) for k in _ADDRESS_KEYWORDS) + r")\b",
    re.IGNORECASE,
)


def _normalize_local_address_prefixes(addr: str) -> str:
    """Expand address abbreviations and infer missing locality labels."""
    if not addr:
        return addr

    parts = _split_address_parts(addr)
    administrative_prefixes = {
        "tp": "Thành phố",
        "tx": "Thị xã",
        "tt": "Thị trấn",
        "p": "Phường",
        "x": "Xã",
        "t": "Tỉnh",
        "q": "Quận",
        "h": "Huyện",
    }
    abbreviation_re = re.compile(
        r"^\s*(?P<prefix>t\.?p|t\.?x|t\.?t|p|x|t|q|h)\.?\s+(?P<name>.+)$",
        re.IGNORECASE,
    )
    for index, part in enumerate(parts):
        # A city-level TP prefix supersedes an accidentally added ward/commune prefix.
        part = re.sub(
            r"^\s*(?:xã|phường)\s+(?=t\.?\s*p\.?\s+)",
            "",
            part,
            flags=re.IGNORECASE,
        )
        abbreviation = abbreviation_re.match(part)
        if abbreviation:
            prefix = abbreviation.group("prefix").lower().replace(".", "")
            parts[index] = (
                f"{administrative_prefixes[prefix]} {abbreviation.group('name')}"
            )
    addr = ", ".join(parts)

    addr = re.sub(
        r"\b(?:xã|phường)\s+KCN\b",
        "Khu công nghiệp",
        addr,
        flags=re.IGNORECASE,
    )
    addr = re.sub(r"\bKCN\b", "Khu công nghiệp", addr, flags=re.IGNORECASE)
    addr = re.sub(r"\bKDC\b", "Khu dân cư", addr, flags=re.IGNORECASE)
    addr = re.sub(r"\bKĐT\b", "Khu đô thị", addr, flags=re.IGNORECASE)
    addr = re.sub(r"\bKCX\b", "Khu chế xuất", addr, flags=re.IGNORECASE)
    addr = re.sub(r"\bKP\b", "Khu phố", addr, flags=re.IGNORECASE)
    addr = re.sub(r"\bTDP\b", "Tổ dân phố", addr, flags=re.IGNORECASE)
    parts = _split_address_parts(addr)
    if len(parts) < 2:
        return ", ".join(parts)

    house_number = r"\d+[a-z]?(?:/[a-z]?\d+[a-z]?)*"
    for index, part in enumerate(parts[:-1]):
        part = re.sub(
            rf"^(\s*(?:số\s+)?{house_number}\s+)đường\s+(?=ấp\b)",
            r"\1",
            part,
            flags=re.IGNORECASE,
        )
        parts[index] = part
        numbered_street = re.match(
            rf"^\s*(?:phường|xã)\s+số\s+({house_number})"
            r"\s+(.+?)\s*$",
            part,
            re.IGNORECASE,
        )
        if numbered_street:
            place_name = numbered_street.group(2).strip()
            street_prefix = "" if _ADDRESS_PREFIX_START_RE.match(place_name) else "Đường "
            parts[index] = (
                f"Số {numbered_street.group(1)} "
                f"{street_prefix}{place_name}"
            )
        elif index > 0:
            secondary_street = re.match(
                rf"^\s*({house_number})\s+(.+)$", part, re.IGNORECASE,
            )
            if secondary_street and not _ADDRESS_PREFIX_START_RE.match(secondary_street.group(2)):
                parts[index] = (
                    f"{secondary_street.group(1)} Đường {secondary_street.group(2)}"
                )

    province = parts[-1]
    locality_parts = parts[:-1]
    is_city_province = bool(re.match(r"^\s*thành\s+phố\b", province, re.IGNORECASE))
    urban_clue = any(
        re.match(r"^\s*khu\s+(?:dân\s+cư|phố)\b", part, re.IGNORECASE)
        for part in locality_parts
    )

    street_index: int | None = None
    if locality_parts and not _ADDRESS_PREFIX_START_RE.match(locality_parts[0]):
        numbered_address_match = re.match(
            rf"^\s*(số\s+{house_number})(?:\s+(.+))?$",
            locality_parts[0],
            re.IGNORECASE,
        )
        street_match = re.match(
            rf"^\s*({house_number})\s+(.+)$",
            locality_parts[0],
            re.IGNORECASE,
        )
        numbered_place_prefix = re.match(
            rf"^\s*{house_number}\s+(.+)$",
            locality_parts[0],
            re.IGNORECASE,
        )
        if numbered_place_prefix and not _ADDRESS_PREFIX_START_RE.match(numbered_place_prefix.group(1)):
            numbered_place_prefix = None
        if numbered_address_match:
            street_index = 0
            street_name = numbered_address_match.group(2)
            if street_name:
                street_name = street_name.strip()
                matching_locality = any(
                    re.sub(
                        r"^\s*(?:phường|xã|quận|huyện|thị\s+trấn|thị\s+xã)\s+",
                        "",
                        part,
                        flags=re.IGNORECASE,
                    ).strip().casefold() == street_name.casefold()
                    for part in locality_parts[1:]
                )
                if not matching_locality and not _ADDRESS_PREFIX_START_RE.match(street_name):
                    street_prefix = "Phố" if re.search(r"\bhà\s+nội\b", province, re.IGNORECASE) else "Đường"
                    locality_parts[0] = (
                        f"{numbered_address_match.group(1).strip()} "
                        f"{street_prefix} {street_name}"
                    )
        elif numbered_place_prefix:
            street_index = 0
        elif street_match and not numbered_place_prefix:
            street_index = 0
            street_prefix = "Phố" if re.search(r"\bhà\s+nội\b", province, re.IGNORECASE) else "Đường"
            locality_parts[0] = f"{street_match.group(1)} {street_prefix} {street_match.group(2)}"

    has_explicit_address_prefix = any(
        _ADDRESS_PREFIX_START_RE.match(part) for part in locality_parts
    )
    unlabelled = [] if has_explicit_address_prefix else [
        index for index, part in enumerate(locality_parts)
        if index != street_index and not _ADDRESS_PREFIX_START_RE.match(part)
    ]
    if unlabelled:
        locality_index = unlabelled[-1]
        locality_prefix = "Phường" if is_city_province or urban_clue else "Xã"
        locality_parts[locality_index] = f"{locality_prefix} {locality_parts[locality_index]}"

        if not (is_city_province or urban_clue) and len(unlabelled) > 1:
            village_index = unlabelled[-2]
            if village_index != street_index:
                locality_parts[village_index] = f"Thôn {locality_parts[village_index]}"

    return ", ".join(locality_parts + [province])


class _SocialLinkParser(HTMLParser):
    def __init__(self) -> None:
        super().__init__(convert_charrefs=True)
        self.hrefs: list[str] = []
        self._ignored_text_depth = 0
        self._jsonld_data: list[str] | None = None

    def handle_starttag(self, tag: str, attrs: list[tuple[str, str | None]]) -> None:
        tag = tag.lower()
        attributes = dict(attrs)
        if tag in {"script", "style"}:
            self._ignored_text_depth += 1
        if (
            tag == "script"
            and (attributes.get("type") or "").split(";", 1)[0].strip().lower()
            == "application/ld+json"
        ):
            self._jsonld_data = []
        is_facebook_page = "fb-page" in (attributes.get("class") or "").split()
        for name, value in attrs:
            if tag == "iframe" and name.lower() in {"src", "data-src"} and value:
                embed = urlparse(value.strip())
                if (
                    _social_platform_for_url(value.strip()) == "facebook"
                    and embed.path.rstrip("/").lower() == "/plugins/page.php"
                ):
                    for profile_url in parse_qs(embed.query).get("href", []):
                        if (
                            _social_platform_for_url(profile_url) == "facebook"
                            and _is_social_profile_url(profile_url)
                        ):
                            self.hrefs.append(profile_url.strip())
            if value and (
                name.lower() == "href"
                or (is_facebook_page and name.lower() == "data-href")
            ):
                self.hrefs.append(value.strip())

    def handle_endtag(self, tag: str) -> None:
        tag = tag.lower()
        if tag == "script" and self._jsonld_data is not None:
            jsonld_data = "".join(self._jsonld_data)
            self._jsonld_data = None
            try:
                structured_data = json.loads(jsonld_data)
            except json.JSONDecodeError as exc:
                print_warn(f"Could not parse website JSON-LD social metadata: {exc}")
            else:
                self._collect_jsonld_same_as(structured_data)
        if tag in {"script", "style"} and self._ignored_text_depth:
            self._ignored_text_depth -= 1

    def handle_data(self, data: str) -> None:
        if self._jsonld_data is not None:
            self._jsonld_data.append(data)
        if self._ignored_text_depth:
            return
        for url in re.findall(r"https?://[^\s\"'<>]+", data):
            self.hrefs.append(url.rstrip(".,;:!?)]}"))

    def _collect_jsonld_same_as(self, value: object) -> None:
        if isinstance(value, dict):
            for key, child in value.items():
                if key.casefold() == "sameas":
                    if isinstance(child, str):
                        self.hrefs.append(child.strip())
                    elif isinstance(child, list):
                        self.hrefs.extend(
                            item.strip() for item in child
                            if isinstance(item, str) and item.strip()
                        )
                self._collect_jsonld_same_as(child)
        elif isinstance(value, list):
            for item in value:
                self._collect_jsonld_same_as(item)


def _social_platform_for_url(url: str) -> str | None:
    hostname = (urlparse(url).hostname or "").lower().rstrip(".")
    if hostname.startswith("www."):
        hostname = hostname[4:]
    for domain, name in _SOCIAL_DOMAINS:
        if hostname == domain or hostname.endswith("." + domain):
            if name == "youtube":
                segments = [segment for segment in urlparse(url).path.split("/") if segment]
                is_channel_path = bool(segments) and (
                    segments[0].startswith("@")
                    or (segments[0].lower() in {"channel", "c", "user"} and len(segments) > 1)
                )
                if not is_channel_path:
                    return None
            return name
    return None


def _is_social_action_url(url: str, platform: str | None = None) -> bool:
    platform = platform or _social_platform_for_url(url)
    if not platform:
        return False
    segments = [segment.lower() for segment in urlparse(url).path.split("/") if segment]
    if not segments:
        return False
    first = segments[0]
    return first in _SOCIAL_ACTION_PATHS.get(platform, ()) or (
        platform == "telegram" and first.startswith("+")
    )


def _is_social_profile_url(url: str) -> bool:
    """Return whether a supported social URL identifies a profile or channel."""
    platform = _social_platform_for_url(url)
    if not platform:
        return False

    parsed = urlparse(url)
    hostname = (parsed.hostname or "").lower().removeprefix("www.")
    segments = [segment.lower() for segment in parsed.path.split("/") if segment]
    if hostname == "messenger.com" or hostname.endswith(".messenger.com"):
        return False
    if not segments:
        return platform == "substack" and hostname.endswith(".substack.com")

    first = segments[0]
    if _is_social_action_url(url, platform):
        return False
    if platform == "facebook":
        if first in {
            "watch", "reel", "messages", "groups", "marketplace",
            "gaming", "events", "login", "help", "photo", "photos", "videos",
            "facebook",
            "plugins",
        }:
            return False
        if first == "profile.php":
            return bool(parse_qs(parsed.query).get("id"))
        return True
    if platform == "youtube":
        return first.startswith("@") or (
            first in {"channel", "c", "user"} and len(segments) > 1
        )
    if platform == "instagram":
        return first not in {
            "accounts", "about", "developer", "explore", "legal", "p",
            "privacy", "reel", "reels", "stories", "web",
        }
    if platform == "linkedin":
        return first in {"company", "in", "school"} and len(segments) > 1
    if platform == "reddit":
        return first in {"u", "user"} and len(segments) > 1
    if platform == "discord":
        return hostname == "discord.com" and first == "users" and len(segments) > 1
    if platform == "tiktok":
        return first.startswith("@")
    if platform in {"twitter", "telegram"}:
        return first not in {
            "about", "explore", "hashtag", "home", "intent", "i", "login",
            "privacy", "share", "status", "statuses", "terms",
        }
    if platform == "substack":
        return hostname != "substack.com" or first not in {
            "about", "account", "archive", "home", "login", "publish",
        }
    return True


def _fetch_website_social_links(website_url: str, timeout: int = 15) -> list[str]:
    """Extract supported social links from a website's homepage."""
    if not website_url:
        return []

    response = None
    try:
        response = requests.get(
            website_url,
            timeout=timeout,
            allow_redirects=True,
            headers=_BROWSER_HEADERS,
            verify=False,
        )
        response.raise_for_status()
        parser = _SocialLinkParser()
        parser.feed(response.text)
        base_url = getattr(response, "url", None) or website_url

        links: list[str] = []
        seen: set[str] = set()
        for href in parser.hrefs:
            link = urljoin(base_url, href)
            parsed_link = urlparse(link)
            if parsed_link.hostname in {"instgram.com", "www.instgram.com"}:
                corrected_link = parsed_link._replace(netloc="www.instagram.com").geturl()
                print_warn(f"Correcting misspelled website Instagram link: {link} -> {corrected_link}")
                link = corrected_link
            platform = _social_platform_for_url(link)
            if platform and link not in seen:
                seen.add(link)
                links.append(link)
        return links
    except Exception as exc:
        print_warn(f"Could not read social links from {website_url}: {type(exc).__name__}: {exc}")
        return []
    finally:
        if response is not None:
            response.close()


def build_socials(
    links_raw: str, homepage_url: str = "", *, review_urls: list[str] | None = None,
) -> list[dict]:
    mapping: dict[str, str] = {}
    checked_urls: set[str] = set()
    links = [link.strip() for link in links_raw.splitlines() if link.strip()]
    links.extend(_fetch_website_social_links(homepage_url))
    for link in links:
        # Ensure https:// prefix if missing
        normalized_link = _normalize_url(link)
        name = _social_platform_for_url(normalized_link)
        if name:
            if _is_social_action_url(normalized_link, name):
                continue
            profile_url = _clean_social_url(normalized_link)
            if (
                _is_social_profile_url(profile_url)
                and name not in mapping
                and profile_url not in checked_urls
            ):
                checked_urls.add(profile_url)
                availability = _check_social_availability(profile_url)
                if availability is not False:
                    mapping[name] = profile_url
                    if availability is None:
                        print_warn(f"Keeping unverified {name} social link for manual review: {profile_url}")
                        if review_urls is not None:
                            review_urls.append(profile_url)
                else:
                    print_warn(f"Skipping unavailable {name} social link: {profile_url}")
    return [
        {"socialId": i, "socialName": n, "socialUrl": mapping.get(n, "")}
        for i, n in enumerate(ALL_SOCIALS)
    ]

# ---------------------------------------------------------------------------
# Base.vn Workflow API & Mapping Helpers
# ---------------------------------------------------------------------------

BASE_AUTH_FILE = SCRIPT_DIR / ".base_auth.json"

DEFAULT_BASE_COOKIES = {
    "allow_gzip": "1",
    "ajs_user_id": "759189",
    "ajs_group_id": "10503",
    "_ga": "GA1.2.1758276911.1768447928",
    "ajs_anonymous_id": "4d2c7a3e-bc5e-424a-9fbf-3b5cc7a7293f",
    "_ga_EWZV34DCTZ": "GS2.2.s1768449992$o2$g1$t1768450675$j60$l0$h0",
    "_ga_7ZLQM5JV1Z": "GS2.1.s1768449991$o2$g1$t1768450676$j60$l0$h0",
    "cached_pp": "1",
    "capp": "",
    "basessid": "bqqdd5f2bunaihdkqoagbr3mpkke2qhr36rs9dpnsth3o7osf9a002i1ulf4gfqp9jj9ub8jgfegpulo",
    "savelogin": "44753609-39e1fce81dac718f2b059c05ea187693690349641338413fbb9bfaafac744ba9-VELQPQBRCZR2MXCD7UP4HJ8R2FAM22NB",
    "__channel": "120333",
    "hc_daily": "22/09/2026",
    "system_state": "BPBVXIAM2J3CD6KX5DIRHXB18ZCJFM66",
    "appid": "workflow",
    "tabid": "_uuid63534_15234_1790046532",
    "__ln": "1273c22c1a7cb3873f0d05388d2381fa.1790050143",
    "active": "1",
}

DEFAULT_BASE_DATA = {
    "from": "",
    "__s": "jobs",
    "_rt": "f9111380e46b5f86b208ab4cf4759052",
    "direct_load": "true",
    "__code": "f97587021876e270010c0263a26fd63e",
    "__sessionid": "bqqdd5f2bunaihdkqoagbr3mpkke2qhr36rs9dpnsth3o7osf9a002i1ulf4gfqp9jj9ub8jgfegpulo",
    "__otp": "364fff052d352fdc9db2aca47d2b7736",
    "assignment_type": "keep_previous",
    "assignee": "Giữ nguyên người nhận việc ở giai đoạn trước (@thangnguyen)",
}


def load_base_auth() -> tuple[dict, dict]:
    """Load Base.vn authentication cookies and post-data from cache file."""
    if BASE_AUTH_FILE.exists():
        try:
            d = json.loads(BASE_AUTH_FILE.read_text(encoding="utf-8"))
            cookies = d.get("cookies") or DEFAULT_BASE_COOKIES
            data = d.get("data") or DEFAULT_BASE_DATA
            return cookies, data
        except Exception:
            pass
    return dict(DEFAULT_BASE_COOKIES), dict(DEFAULT_BASE_DATA)


def save_base_auth(cookies: dict, data: dict) -> None:
    """Save Base.vn authentication to cache file."""
    try:
        payload = {"cookies": cookies, "data": data}
        BASE_AUTH_FILE.write_text(json.dumps(payload, indent=2, ensure_ascii=False), encoding="utf-8")
    except Exception as exc:
        print_warn(f"Could not save .base_auth.json: {exc}")


def parse_curl_command(curl_text: str) -> tuple[dict, dict]:
    """Parse a curl command copied from browser DevTools into cookies and form data dictionaries."""
    cookies: dict = {}
    data: dict = {}

    cookie_match = re.search(r'''(?:-b|--cookie|-H\s+['"]cookie:)\s*['"]([^'"]+)['"]''', curl_text, re.IGNORECASE)
    if not cookie_match:
        cookie_match = re.search(r'''(?:-b|--cookie)\s+([^\s]+)''', curl_text)
    if cookie_match:
        for part in cookie_match.group(1).split(";"):
            if "=" in part:
                k, v = part.strip().split("=", 1)
                cookies[k.strip()] = v.strip()

    data_match = re.search(r'''(?:--data-raw|--data|-d)\s*['"]([^'"]+)['"]''', curl_text)
    if not data_match:
        data_match = re.search(r'''(?:--data-raw|--data|-d)\s+([^\s]+)''', curl_text)
    if data_match:
        raw_body = data_match.group(1)
        qs = parse_qs(raw_body, keep_blank_values=True)
        for k, v in qs.items():
            data[k] = v[0] if v else ""

    return cookies, data


def prompt_update_base_auth() -> tuple[dict, dict]:
    """Prompt user to update Base.vn session by pasting a curl command or raw cookie."""
    print_warn("\nBase.vn session is expired or authorization is invalid.")
    print_info("To update, copy any request to workflow.base.vn from Chrome DevTools (Network tab -> Copy as cURL).")
    while True:
        raw = input(f"\n  {Colors.BOLD}📋 Paste Base.vn cURL command (or press Enter to cancel): {Colors.END}").strip()
        if not raw:
            return load_base_auth()
        cookies, data = parse_curl_command(raw)
        if cookies or data:
            current_cookies, current_data = load_base_auth()
            if cookies:
                current_cookies.update(cookies)
            if data:
                current_data.update(data)
            save_base_auth(current_cookies, current_data)
            print_success("Base.vn credentials updated and saved to .base_auth.json!")
            return current_cookies, current_data
        print_fail("Could not extract cookies or POST data from input. Please paste a valid cURL command.")


def query_base_workflow(
    brand_name: str, cookies: dict, data: dict
) -> tuple[str, list[dict]]:
    """Query workflow.base.vn/home?q={brand_name} for jobs.
    Returns (status, list_of_jobs) where status is 'OK', 'INVALID_SESSION', 'NO_DATA', or 'ERROR'.

    Uses a fresh per-request session to avoid RemoteDisconnected errors caused by
    the global session reusing a stale keep-alive connection that Base.vn has closed.
    """
    headers = {
        "accept": "*/*",
        "accept-language": "en-US,en;q=0.9,vi;q=0.8",
        "cache-control": "no-cache",
        "content-type": "application/x-www-form-urlencoded; charset=UTF-8",
        "origin": "https://workflow.base.vn",
        "referer": "https://workflow.base.vn/home",
        "user-agent": (
            "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
            "(KHTML, like Gecko) Chrome/153.0.0.0 Safari/537.36"
        ),
        "x-requested-with": "XMLHttpRequest",
        "connection": "close",  # Don't reuse connections to Base.vn
    }
    url = f"https://workflow.base.vn/home?q={quote(brand_name)}"

    _CONNECTION_ERRORS = (
        "RemoteDisconnected", "ConnectionError", "ConnectionReset",
        "BrokenPipe", "Connection aborted",
    )

    def _do_post(session: requests.Session) -> requests.Response:
        return session.post(url, headers=headers, cookies=cookies, data=data, timeout=20)

    resp = None
    for attempt in range(1, 4):  # up to 3 attempts
        try:
            if attempt == 1:
                resp = _do_post(_session)
            else:
                # Fresh session to force a new TCP connection
                with _make_session() as fresh:
                    resp = _do_post(fresh)
            break  # success
        except Exception as exc:
            exc_str = str(exc)
            is_conn_err = any(e in type(exc).__name__ or e in exc_str for e in _CONNECTION_ERRORS)
            if is_conn_err and attempt < 3:
                print_warn(f"Base.vn connection dropped (attempt {attempt}/3), retrying with fresh connection...")
                time.sleep(1 * attempt)
                continue
            return f"ERROR: {exc}", []

    if resp is None:
        return "ERROR: No response after retries", []

    if "Invalid session" in resp.text:
        return "INVALID_SESSION", []

    try:
        j = resp.json()
        pd = j.get("_page_data", "")
        m = re.search(r'Client\.pageData\s*=\s*(\{.*)', pd, re.DOTALL)
        if m:
            decoder = json.JSONDecoder()
            obj, _ = decoder.raw_decode(m.group(1).rstrip(";"))
            jobs = obj.get("jobs", [])
            return "OK", jobs
    except Exception as exc:
        return f"ERROR: {exc}", []

    return "NO_DATA", []


def fetch_base_job(
    job_id: str | int, cookies: dict, data: dict
) -> tuple[str, dict | None]:
    """Fetch a single Base workflow job directly by its ID (/job/{id})."""
    url = f"https://workflow.base.vn/job/{job_id}"
    headers = {
        "accept": "*/*",
        "accept-language": "en-US,en;q=0.9,vi;q=0.8",
        "cache-control": "no-cache",
        "content-type": "application/x-www-form-urlencoded; charset=UTF-8",
        "origin": "https://workflow.base.vn",
        "referer": url,
        "user-agent": (
            "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
            "(KHTML, like Gecko) Chrome/153.0.0.0 Safari/537.36"
        ),
        "x-requested-with": "XMLHttpRequest",
        "connection": "close",
    }
    _CONNECTION_ERRORS = (
        "RemoteDisconnected", "ConnectionError", "ConnectionReset",
        "BrokenPipe", "Connection aborted",
    )
    def _do_post(session: requests.Session) -> requests.Response:
        return session.post(url, headers=headers, cookies=cookies, data=data, timeout=20)

    resp = None
    for attempt in range(1, 4):
        try:
            if attempt == 1:
                resp = _do_post(_session)
            else:
                with _make_session() as fresh:
                    resp = _do_post(fresh)
            break
        except Exception as exc:
            exc_str = str(exc)
            is_conn_err = any(e in type(exc).__name__ or e in exc_str for e in _CONNECTION_ERRORS)
            if is_conn_err and attempt < 3:
                time.sleep(1 * attempt)
                continue
            return f"ERROR: {exc}", None

    if resp is None:
        return "ERROR: No response after retries", None
    if "Invalid session" in resp.text:
        return "INVALID_SESSION", None

    try:
        j = resp.json()
        pd = j.get("_page_data", "")
        m = re.search(r'Client\.pageData\s*=\s*(\{.*)', pd, re.DOTALL)
        if m:
            decoder = json.JSONDecoder()
            obj, _ = decoder.raw_decode(m.group(1).rstrip(";"))
            job = obj.get("job")
            if job:
                return "OK", job
    except Exception as exc:
        return f"ERROR: {exc}", None

    return "NO_DATA", None


def get_base_otp_and_code(cookies: dict, job_id: str | int = "") -> tuple[str, str]:
    """Fetch secureData (otp, session) and code from Base HTML page."""
    headers = {
        "user-agent": (
            "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
            "(KHTML, like Gecko) Chrome/153.0.0.0 Safari/537.36"
        )
    }
    url = f"https://workflow.base.vn/job/{job_id}" if job_id else "https://workflow.base.vn/home"
    try:
        resp = requests.get(url, headers=headers, cookies=cookies, timeout=10)
        otp = ""
        code = ""
        m_sec = re.search(r'"secureData"\s*:\s*(\{[^}]+\})', resp.text)
        if m_sec:
            sec = json.loads(m_sec.group(1))
            otp = sec.get("otp", "")
        m_code = re.search(r'"code"\s*:\s*"([a-f0-9]{32})"', resp.text)
        if m_code:
            code = m_code.group(1)
        return otp, code
    except Exception:
        return "", ""


def api_base_job_next(
    job_id: str | int,
    job_token: str,
    brand_url: str,
    cookies: dict,
    data: dict,
) -> tuple[str, str]:
    """Advance Base.vn Workflow job to the next stage and update custom_link_gian_hang.

    Endpoint: https://workflow.base.vn/ajax/api/job/next
    Returns (status, message) where status is 'OK', 'INVALID_SESSION', or 'FAIL'.
    """
    url = "https://workflow.base.vn/ajax/api/job/next"
    headers = {
        "accept": "*/*",
        "accept-language": "en-US,en;q=0.9,vi;q=0.8",
        "cache-control": "no-cache",
        "content-type": "application/x-www-form-urlencoded; charset=UTF-8",
        "origin": "https://workflow.base.vn",
        "referer": f"https://workflow.base.vn/job/{job_id}",
        "user-agent": (
            "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
            "(KHTML, like Gecko) Chrome/153.0.0.0 Safari/537.36"
        ),
        "x-requested-with": "XMLHttpRequest",
        "connection": "close",
    }

    code_val = data.get("__code") or ""
    session_id = data.get("__sessionid") or cookies.get("basessid", "")
    otp_val = data.get("__otp") or ""

    if not otp_val or not code_val:
        dyn_otp, dyn_code = get_base_otp_and_code(cookies, job_id)
        if not otp_val:
            otp_val = dyn_otp
        if not code_val:
            code_val = dyn_code

    payload = {
        "id": str(job_id),
        "token": str(job_token),
        "assignment_type": data.get("assignment_type") or "keep_previous",
        "assignee": data.get("assignee") or "Giữ nguyên người nhận việc ở giai đoạn trước (@thangnguyen)",
        "note": data.get("note") or "",
        "custom_link_gian_hang": brand_url,
        "__code": code_val,
        "__sessionid": session_id,
        "__otp": otp_val,
    }

    for k, v in data.items():
        if k.startswith("_uuid"):
            payload[k] = v

    try:
        with _make_session() as s:
            resp = s.post(url, headers=headers, cookies=cookies, data=payload, timeout=20)
    except Exception as exc:
        return "FAIL", f"Connection error: {exc}"

    if "Invalid session" in resp.text:
        return "INVALID_SESSION", "Invalid or expired Base.vn session."

    try:
        j = resp.json()
        resp_code = j.get("code")
        msg = j.get("message") or ""
        if resp_code == 1:
            return "OK", msg or "Success"
        else:
            return "FAIL", msg or str(j)
    except Exception:
        if resp.status_code == 200 and not resp.text.strip():
            return "OK", "Success"
        return "FAIL", f"HTTP {resp.status_code}: {resp.text[:200]}"


def _strip_base_forward_prefix(name: str) -> str:
    return re.sub(
        r"^\s*(?:#\s*)?(?:\[\s*fwd\s*\]\s*)+",
        "", html.unescape(name).strip(), flags=re.IGNORECASE,
    )


def extract_base_brand_prefix(name: str) -> str:
    """Extract the leading brand identifier, ignoring BASE's forwarding markers."""
    name = _strip_base_forward_prefix(name)
    match = re.match(
        r"^\s*\[?\s*(?:(?:STT|ID|NO|MS|MÃ|MA|#)\s*[:.]?\s*)?(\d+)",
        name, flags=re.IGNORECASE,
    )
    return match.group(1) if match else ""


def clean_base_brand_name(name: str) -> str:
    """Clean brand name directly from Base by removing leading ID / STT / counter prefixes.
    If the name ends with a trailing parenthetical like '(NUTSHEALTH)', the content
    inside the parentheses is returned as the brand name (short brand alias takes priority).
    If no trailing parenthetical is present, the full cleaned name is returned.

    Examples:
        '3220 - CÁ HỒI THỨC MAI'                                                              -> 'CÁ HỒI THỨC MAI'
        '3257. CÔNG TY TNHH BẢO AN'                                                            -> 'CÔNG TY TNHH BẢO AN'
        '3252 - HỘ KINH DOANH COSMETIC'                                                        -> 'HỘ KINH DOANH COSMETIC'
        '3220 - CÁ HỒI THỨC MAI (SAPA)'                                                       -> 'SAPA'
        '[3220] - CÁ HỒI THỨC MAI'                                                            -> 'CÁ HỒI THỨC MAI'
        'STT 3220 - CÁ HỒI THỨC MAI'                                                          -> 'CÁ HỒI THỨC MAI'
        '3281 CÔNG TY TNHH SẢN XUẤT THƯƠNG MẠI DỊCH VỤ ĐÀO TIÊN'                             -> 'CÔNG TY TNHH SẢN XUẤT THƯƠNG MẠI DỊCH VỤ ĐÀO TIÊN'
        '3301HỢP TÁC XÃ DỊCH VỤ NUÔI TRỒNG VÀ SINH THÁI KHUỔI SAO'                           -> 'HỢP TÁC XÃ DỊCH VỤ NUÔI TRỒNG VÀ SINH THÁI KHUỔI SAO'
        'CÔNG TY TNHH SẢN XUẤT THƯƠNG MẠI DỊCH VỤ XUẤT NHẬP KHẨU NUTSHEALTH(NUTSHEALTH)'     -> 'NUTSHEALTH'
        'CÁ HỒI THỨC MAI'                                                                      -> 'CÁ HỒI THỨC MAI'
    """
    if not name:
        return ""
    s = _strip_base_forward_prefix(name)
    # Pattern 1: [xxx] with optional following separator
    s = re.sub(r'^\s*\[\s*(?:(?:STT|ID|NO|MS|MÃ|MA|#)\s*[:.]?\s*)?\w+\s*\]\s*[-–—:./|]?\s*', '', s, flags=re.IGNORECASE)
    # Pattern 2: STT / ID / NO / # with optional number and separator
    s = re.sub(r'^\s*(?:STT|ID|NO|MS|MÃ|MA|#)\s*[:.]?\s*\d*\s*[-–—:./|]?\s*', '', s, flags=re.IGNORECASE)
    # Pattern 3: Number followed by separator: -, –, —, :, ., /, |
    s = re.sub(r'^\s*\d+\s*[-–—:./|]\s*', '', s)
    # Pattern 4: Number followed by only whitespace (no separator), e.g. '3281 CÔNG TY TNHH...'
    s = re.sub(r'^\s*\d+\s+', '', s)
    # Pattern 5: Number glued directly to text (no separator, no space), e.g. '3301HỢP TÁC XÃ...'
    s = re.sub(r'^\d+(?=[^\d])', '', s)
    # Clean up any leftover leading separators or spaces
    s = re.sub(r'^\s*[-–—:./|]\s*', '', s)
    s = s.strip()
    # If a trailing parenthetical exists, extract its content as the brand name.
    # e.g. 'CÔNG TY TNHH ... NUTSHEALTH(NUTSHEALTH)' -> 'NUTSHEALTH'
    m = re.search(r'\(([^)]+)\)\s*$', s)
    if m:
        return m.group(1).strip()
    return s


def parse_sheet_link(text: str) -> tuple[str, str, int | None] | None:
    """Read spreadsheet, tab, and optional row from a plain or HTML-embedded URL."""
    match = re.search(
        r'https?://docs\.google\.com/spreadsheets/d/([A-Za-z0-9_-]+)([^\s<>"\']*)',
        html.unescape(text),
    )
    if not match:
        return None
    parsed = urlparse(match.group(0))
    params = parse_qs(parsed.query)
    params.update(parse_qs(parsed.fragment))
    gid = params.get("gid", [SHEET_GID])[0]
    cell_range = params.get("range", [""])[0].replace("$", "")
    row_match = re.match(r"(?:[^!]+!)?[A-Za-z]*(\d+)(?::[A-Za-z]*\d+)?$", cell_range)
    row_num = int(row_match.group(1)) if row_match else None
    return match.group(1), gid, row_num


def base_job_id_from_url(text: str) -> str | None:
    """Support direct workflow URLs and Xspace's base64-encoded embed URLs."""
    parsed = urlparse(text)
    path = parsed.path
    if parsed.hostname == "xspace.base.vn" and path == "/embed":
        encoded = parse_qs(parsed.query).get("path", [""])[0]
        try:
            path = base64.b64decode(encoded + "=" * (-len(encoded) % 4), validate=True).decode("utf-8")
        except (binascii.Error, UnicodeDecodeError) as exc:
            raise ValueError(f"Invalid BASE embed job path: {exc}") from exc
    elif parsed.hostname != "workflow.base.vn":
        return None
    match = re.fullmatch(r"/?job/(\d+)/?", path)
    return match.group(1) if match else None


def extract_base_job_info(job: dict) -> dict:
    """Extract category, benefit, brand name, and spreadsheet link/row from a Base workflow job object.

    Logo/banner download logic:
        - If only "LINK SẢN PHẨM" is present  → use product_link
        - If "LINK SẢN PHẨM LẦN 2" is present → use product_link_2 (takes priority)
    """
    title = job.get("title", "")
    raw_job_name = job.get("name", "")
    info = {
        "job_id": job.get("id"),
        "job_token": job.get("token", ""),
        "job_name": raw_job_name,
        "brand_name": clean_base_brand_name(raw_job_name),
        "last_update": int(job.get("last_update") or job.get("since") or 0),
        "raw_category": "",
        "raw_benefit": "",
        "sheet_link": "",
        "sheet_row": None,
        "product_link": "",    # LINK SẢN PHẨM (first/only)
        "product_link_2": "",  # LINK SẢN PHẨM LẦN 2 (revision, takes priority)
    }
    for f in job.get("form", []):
        fid = f.get("id", "")
        fname = f.get("name") or f.get("label") or f.get("title") or ""
        fname_norm = _normalize_vietnamese(str(fname))
        fval = str(f.get("value") or "").strip()
        if fid == "link_nguyen_lieu" or fname_norm in ("nguyen lieu", "link nguyen lieu"):
            info["sheet_link"] = fval
        elif fid == "danh_muc_nganh_hang":
            info["raw_category"] = fval
        elif fid == "nhom_uu_dai":
            info["raw_benefit"] = fval
        elif (
            fid in ("link_san_pham_lan_2", "link_sp_lan_2")
            or "lan 2" in fname_norm
            or "lần 2" in str(fname).lower()
        ):
            info["product_link_2"] = fval
        elif fid in ("link_san_pham", "link_sp") or "link san pham" in fname_norm or fname_norm == "san pham":
            info["product_link"] = fval

    if not info["sheet_link"]:
        m = re.search(r'(?:LINK\s+)?NGUYÊN LIỆU[:\s]*(.*?)(?:·|$)', title, re.IGNORECASE | re.DOTALL)
        if m:
            section = html.unescape(m.group(1))
            url_match = re.search(r'https?://[^\s<>"\']+', section)
            if url_match:
                info["sheet_link"] = url_match.group(0)
    if not info["raw_category"]:
        m = re.search(r'Danh mục ngành hàng[:\s]+([^·<]+)', title, re.IGNORECASE)
        if m:
            info["raw_category"] = m.group(1).strip()
    if not info["raw_benefit"]:
        m = re.search(r'Nhóm ƯU ĐÃI[:\s]+([^·<]+)', title, re.IGNORECASE)
        if m:
            info["raw_benefit"] = m.group(1).strip()
    # Fallback: scrape links from job title text
    if not info["product_link_2"]:
        m = re.search(r'LINK\s+SẢN\s+PHẨM\s+LẦN\s+2[:\s]+([^\s·<]+)', title, re.IGNORECASE)
        if m:
            info["product_link_2"] = m.group(1).strip()
    if not info["product_link"]:
        m = re.search(r'(?:LINK SẢN PHẨM|SẢN PHẨM)[:\s]+([^\s·<]+)', title, re.IGNORECASE)
        if m:
            info["product_link"] = m.group(1).strip()

    linked_source = parse_sheet_link(info["sheet_link"])
    if linked_source:
        info["sheet_row"] = linked_source[2]
    return info


def _normalize_search_string(s: str) -> str:
    """Normalize string for brand search by removing parenthetical postfix, lowercasing, and removing accents."""
    if not s:
        return ""
    s = _strip_parenthetical_postfix(s)
    return _normalize_vietnamese(s)


def find_latest_sheet_row_for_brand(
    brand_name: str, rows: list[list[str]]
) -> tuple[int | None, str]:
    """Search Google Sheet rows for matching brand names in column 2.
    If multiple rows match, returns the latest (highest row number).
    Returns (latest_row_num, raw_brand_name).
    """
    target = _normalize_search_string(brand_name)
    if not target:
        return None, ""
    exact_matches: list[tuple[int, str]] = []
    partial_matches: list[tuple[int, str]] = []

    for idx, row in enumerate(rows):
        if idx == 0:  # Header row
            continue
        raw_name = _cell(row, 2)
        norm_row = _normalize_search_string(raw_name)
        if not norm_row:
            continue
        row_num = idx + 1
        if norm_row == target:
            exact_matches.append((row_num, raw_name))
        elif target in norm_row or norm_row in target:
            partial_matches.append((row_num, raw_name))

    if exact_matches:
        return exact_matches[-1]
    if partial_matches:
        return partial_matches[-1]
    return None, ""


def resolve_sheet_rows(
    job_info: dict, brand_name: str = "", row_num: int | None = None,
) -> tuple[str, str, list[list[str]], int | None]:
    """Prefer BASE's source, then old/new sheets. Never reuse a linked row in another source."""
    linked = parse_sheet_link(job_info.get("sheet_link", ""))
    sources = []
    if linked:
        sources.append((linked[0], linked[1]))
    elif job_info.get("sheet_link"):
        print_warn("BASE NGUYÊN LIỆU is not a Google Sheets URL; searching configured spreadsheets.")
    sources.extend(((SHEET_ID, SHEET_GID), (FALLBACK_SHEET_ID, SHEET_GID)))
    first_available = None
    target_name = job_info.get("brand_name") or brand_name
    target_prefix = extract_base_brand_prefix(job_info.get("job_name") or brand_name)
    if target_prefix and not job_info.get("brand_name"):
        target_name = clean_base_brand_name(brand_name)
    linked_row = (linked[2] or job_info.get("sheet_row")) if linked else None
    for sheet_id, sheet_gid in dict.fromkeys(sources):
        try:
            rows = fetch_all_sheet_rows(sheet_id=sheet_id, sheet_gid=sheet_gid)
        except (requests.RequestException, RuntimeError) as exc:
            print_warn(f"Cannot read spreadsheet {sheet_id} (gid={sheet_gid}): {exc}")
            continue
        if first_available is None:
            first_available = (sheet_id, sheet_gid, rows, None)
        if target_prefix:
            for idx in range(len(rows) - 1, 0, -1):
                if _cell(rows[idx], 1) == target_prefix:
                    print_info(f"Matched prefix {target_prefix} to Column B at row {idx + 1}.")
                    return sheet_id, sheet_gid, rows, idx + 1
        candidate = None
        if linked and (sheet_id, sheet_gid) == linked[:2]:
            candidate = linked_row
        elif not target_name and not linked:
            candidate = row_num
        if not target_prefix and candidate and 1 < candidate <= len(rows) and _cell(rows[candidate - 1], 2):
            return sheet_id, sheet_gid, rows, candidate
        if target_name:
            matched_row, _ = find_latest_sheet_row_for_brand(target_name, rows)
            if matched_row:
                return sheet_id, sheet_gid, rows, matched_row
        print_info(f"No matching brand/row in spreadsheet {sheet_id} (gid={sheet_gid}); trying next source.")
    if first_available is None:
        raise RuntimeError("Cannot access any spreadsheet source. Check sharing permissions and network access.")
    print_warn("No matching brand/row found in the available spreadsheets; select a row manually.")
    return first_available


CATEGORY_SYNONYMS: dict[int, list[str]] = {
    2: [
        "am thuc", "thuc pham", "do an", "an uong", "do uong", "f&b", "f & b",
        "nha hang", "quan an", "cafe", "ca phe", "tra", "banh", "nuoc giai khat",
        "ruou", "bia", "lau", "nuong", "buffet", "dac san"
    ],
    7: [
        "du lich", "tour", "ve may bay", "lu hanh", "travel", "nghi duong", "trai nghiem"
    ],
    9: [
        "thoi trang", "quan ao", "giay dep", "tui xach", "phu kien", "dong ho",
        "trang suc", "fashion", "may mac"
    ],
    13: [
        "cong nghe", "dien tu", "phan mem", "it", "thiet bi so", "dien thoai",
        "may tinh", "laptop", "cong nghe thong tin"
    ],
    25: [
        "suc khoe", "y te", "duoc pham", "thuoc", "thuc pham chuc nang",
        "tpcn", "benh vien", "phong kham", "nha thuoc", "dong y", "cham soc suc khoe"
    ],
    26: [
        "giao duc", "dao tao", "truong hoc", "khoa hoc", "hoc tieng anh",
        "ngoai ngu", "trung tam", "du hoc"
    ],
    29: [
        "lam dep", "sac dep", "my pham", "spa", "tham my", "tham my vien",
        "cham soc da", "skincare", "nail", "toc", "hair", "salon", "beauty"
    ],
    30: [
        "khach san", "hotel", "resort", "homestay", "nha nghi", "luu tru"
    ],
    31: [
        "gia dung", "noi that", "do gia dung", "dien gia dung", "nha cua",
        "doi song", "bep", "trang tri nha cua"
    ],
    32: [
        "nghe thuat", "hoi hoa", "tranh anh", "am nhac", "giai tri", "studio"
    ],
    33: [
        "the thao", "gym", "fitness", "yoga", "bong da", "the duc", "cau long", "pickleball"
    ],
    37: [
        "quang cao", "marketing", "truyen thong", "media", "agency", "in an", "su kien"
    ],
    27: [
        "khac", "other"
    ],
}


def _contains_phrase(text: str, phrase: str) -> bool:
    """Check if normalized phrase appears as whole words in normalized text."""
    pattern = r'(?:\b|^)' + re.escape(phrase) + r'(?:\b|$)'
    return bool(re.search(pattern, text))


def map_base_categories(raw_text: str, cat_data: list) -> list[int]:
    """Map raw category text from Base to category IDs from category.txt."""
    if not raw_text:
        return []
    parts = re.split(r'[,;/|&]+|\s+va\s+|\s+và\s+', raw_text, flags=re.IGNORECASE)
    matched_ids: list[int] = []

    cat_items = []
    for e in cat_data:
        cid = e["id"]
        cname = _normalize_vietnamese(e["name"])
        cat_items.append((len(cname), cid, cname))
    cat_items.sort(key=lambda x: x[0], reverse=True)

    syn_items = []
    for cid, syns in CATEGORY_SYNONYMS.items():
        for s in syns:
            norm_s = _normalize_vietnamese(s)
            syn_items.append((len(norm_s), cid, norm_s))
    syn_items.sort(key=lambda x: x[0], reverse=True)

    for part in parts:
        norm_part = _normalize_vietnamese(part)
        if not norm_part:
            continue
        found = False

        for _, cid, cname in cat_items:
            if cid == 27:
                continue
            if _contains_phrase(norm_part, cname) or _contains_phrase(cname, norm_part):
                if cid not in matched_ids:
                    matched_ids.append(cid)
                found = True
                break
        if found:
            continue

        for _, cid, syn in syn_items:
            if cid == 27:
                continue
            if _contains_phrase(norm_part, syn):
                if cid not in matched_ids:
                    matched_ids.append(cid)
                found = True
                break
        if found:
            continue

        if _contains_phrase(norm_part, "khac") or _contains_phrase(norm_part, "other"):
            if 27 not in matched_ids:
                matched_ids.append(27)

    return matched_ids


def map_base_benefit(raw_text: str, ben_data: list) -> str:
    """Map raw benefit text from Base to benefit type from benefit.txt."""
    if not raw_text:
        return ben_data[0]["type"] if ben_data else "OTHER"
    norm = _normalize_vietnamese(raw_text)
    if "tong hoa don" in norm or "tong bill" in norm or "tong" in norm:
        return "DISCOUNT_ORDER_TOTAL"
    if "theo sp" in norm or "theo san pham" in norm or "sp/ dv" in norm or "sp/dv" in norm:
        return "DISCOUNT_BY_PRODUCT"
    if "tang" in norm:
        return "BUY_X_FREE_Y"
    if "giam" in norm:
        return "BUY_X_DISCOUNT_Y"
    if "khac" in norm:
        return "OTHER"
    return ben_data[0]["type"] if ben_data else "OTHER"


def prompt_brand_lookup() -> tuple[str, bool]:
    """Ask user to enter brand name (or row number).
    Returns (input_string, is_pure_number).
    """
    while True:
        raw = input(f"\n  {Colors.BOLD}🏢 Enter brand name (or row number): {Colors.END}").strip()
        if raw:
            if raw.isdigit() and int(raw) > 0:
                return raw, True
            return raw, False
        print_fail("Input cannot be empty.")


def prompt_review_row(detected_row: int | None, total_rows: int) -> int:
    """Review auto-detected row number, allowing user to confirm or change."""
    prompt_msg = f"  {Colors.BOLD}📋 Row number"
    if detected_row:
        prompt_msg += f" [{Colors.CYAN}{detected_row}{Colors.END}{Colors.BOLD}] (press Enter to keep): {Colors.END}"
    else:
        prompt_msg += f": {Colors.END}"

    while True:
        raw = input(prompt_msg).strip()
        if not raw and detected_row:
            return detected_row
        if raw.isdigit() and 1 <= int(raw) <= total_rows:
            return int(raw)
        print_fail(f"Please enter a valid row number between 1 and {total_rows}.")


def _has_confident_row_match(
    user_input: str,
    is_pure_number: bool,
    detected_row: int | None,
    rows: list[list[str]],
    job_info: dict,
) -> bool:
    """Return whether the selected sheet row is explicitly or exactly matched."""
    if not detected_row:
        return False
    if is_pure_number:
        return (
            user_input.isdigit()
            and int(user_input) == detected_row
            and detected_row <= len(rows)
        )
    linked_source = parse_sheet_link(job_info.get("sheet_link", ""))
    if linked_source and linked_source[2] == detected_row:
        return True
    return (
        0 < detected_row <= len(rows)
        and _normalize_search_string(_cell(rows[detected_row - 1], 2))
        == _normalize_search_string(user_input)
    )


def _has_recognized_base_benefit(raw_text: str) -> bool:
    """Check that Base benefit text matched a rule rather than the fallback."""
    norm = _normalize_vietnamese(raw_text)
    return any(
        _contains_phrase(norm, phrase)
        for phrase in (
            "tong hoa don", "tong bill", "tong", "theo sp",
            "theo san pham", "sp/ dv", "sp/dv", "tang", "giam", "khac",
        )
    )


def print_category_and_benefit_reference_lists(cat_data: list, ben_data: list) -> None:
    """Print available categories and benefit types for user reference before review."""
    if cat_data:
        print(f"\n{Colors.HEADER}{Colors.BOLD}🏷️  Available Categories:{Colors.END}")
        for i, e in enumerate(cat_data, 1):
            print(f"  • [{Colors.CYAN}{i}{Colors.END}] {e['name']}")
    if ben_data:
        print(f"\n{Colors.HEADER}{Colors.BOLD}🎁 Available Benefit Types:{Colors.END}")
        for i, e in enumerate(ben_data, 1):
            print(f"  • [{Colors.CYAN}{i}{Colors.END}] {e['description']}")
    print()


def _parse_category_input(raw: str, cat_data: list) -> list[int]:
    """Parse category input by 1-based index (1..N), name, or ID (comma-separated)."""
    if not raw.strip():
        return []
    parts = [p.strip() for p in raw.split(",") if p.strip()]
    matched_ids: list[int] = []
    for part in parts:
        if part.isdigit():
            idx = int(part)
            if 1 <= idx <= len(cat_data):
                matched_ids.append(cat_data[idx - 1]["id"])
                continue
            if any(e["id"] == idx for e in cat_data):
                matched_ids.append(idx)
                continue
        part_norm = _normalize_vietnamese(part)
        found = False
        for e in cat_data:
            ename_norm = _normalize_vietnamese(e["name"])
            if part_norm == ename_norm or (len(part_norm) >= 3 and part_norm in ename_norm):
                matched_ids.append(e["id"])
                found = True
                break
        if not found:
            print_warn(f"Category '{part}' not recognized.")
    return matched_ids


def prompt_review_categories(detected_cats: list[int], cat_data: list) -> list[int]:
    """Review auto-detected categories, allowing user to confirm or change by number."""
    if detected_cats:
        cat_names = [e["name"] for e in cat_data if e["id"] in detected_cats]
        cat_str = ", ".join(cat_names)
        # Find index in cat_data for display
        cat_idx = next((i for i, e in enumerate(cat_data, 1) if e["id"] in detected_cats), None)
        idx_label = f"[{cat_idx}] " if cat_idx else ""
        if cat_str:
            raw = input(f"  {Colors.BOLD}🏷️  Category [{Colors.CYAN}{idx_label}{cat_str}{Colors.END}{Colors.BOLD}] (Enter to keep, or enter number): {Colors.END}").strip()
            if not raw:
                return detected_cats
            parsed = _parse_category_input(raw, cat_data)
            if parsed:
                return parsed
            print_fail(f"Invalid category. Enter 1–{len(cat_data)} or category name.")
            return detected_cats

    return prompt_categories(cat_data)


def _parse_benefit_input(raw: str, ben_data: list) -> str | None:
    """Parse benefit input by number (1..N) or description text."""
    raw = raw.strip()
    if not raw:
        return None
    if raw.isdigit():
        idx = int(raw)
        if 1 <= idx <= len(ben_data):
            return ben_data[idx - 1]["type"]
        return None
    raw_norm = _normalize_vietnamese(raw)
    for e in ben_data:
        desc_norm = _normalize_vietnamese(e["description"])
        if raw_norm == desc_norm or (len(raw_norm) >= 3 and raw_norm in desc_norm):
            return e["type"]
    return None


def prompt_review_benefit_type(detected_ben: str, ben_data: list) -> str:
    """Review auto-detected benefit type, allowing user to confirm or change by number."""
    if detected_ben:
        ben_desc = next((e["description"] for e in ben_data if e["type"] == detected_ben), "")
        ben_idx = next((i for i, e in enumerate(ben_data, 1) if e["type"] == detected_ben), None)
        if ben_desc:
            idx_label = f"[{ben_idx}] " if ben_idx else ""
            raw = input(f"  {Colors.BOLD}🎁 Benefit [{Colors.CYAN}{idx_label}{ben_desc}{Colors.END}{Colors.BOLD}] (Enter to keep, or enter number): {Colors.END}").strip()
            if not raw:
                return detected_ben
            if raw.isdigit():
                idx = int(raw)
                if 1 <= idx <= len(ben_data):
                    return ben_data[idx - 1]["type"]
                print_fail(f"Invalid number. Enter 1–{len(ben_data)}.")
            return detected_ben

    return prompt_benefit_type(ben_data)


# ---------------------------------------------------------------------------
# Interactive prompts
# ---------------------------------------------------------------------------

def prompt_row() -> int:
    while True:
        raw = input(f"\n  {Colors.BOLD}📋 Enter Google Sheet row number: {Colors.END}").strip()
        if raw.isdigit() and int(raw) > 0:
            return int(raw)
        print_fail("Invalid row number.")



def prompt_categories(cat_data: list) -> list[int]:
    while True:
        raw = input(f"\n  {Colors.BOLD}Enter category number(s) or name(s) (e.g. 1 or Ẩm Thực): {Colors.END}").strip()
        parsed = _parse_category_input(raw, cat_data)
        if parsed:
            return parsed
        print_fail("Please enter a valid category number or name from the list above.")


def prompt_benefit_type(ben_data: list) -> str:
    while True:
        raw = input(f"\n  {Colors.BOLD}Enter benefit number or description: {Colors.END}").strip()
        res = _parse_benefit_input(raw, ben_data)
        if res:
            return res
        print_fail("Invalid. Please select a valid benefit from the list above.")


def extract_discount_from_tos(tos: str) -> float:
    """Extract the highest discount percentage from the benefit TOS text.
    Handles both dot and comma decimal separators (e.g. 12.7% or 12,7%).
    Returns the largest percentage found as a float, or 0 if none."""
    matches = re.findall(r'(\d+(?:[.,]\d+)?)\s*%', tos)
    if matches:
        return max(float(m.replace(',', '.')) for m in matches)
    return 0

# ---------------------------------------------------------------------------
# API calls
# ---------------------------------------------------------------------------

def validate_token(base: str, token: str) -> bool:
    """Validate token by making a simple API call to fetch brands.
    Returns True if token is valid, False otherwise."""
    h = {k: v for k, v in _headers(token).items() if k != "content-type"}
    try:
        resp = _session.get(
            f"https://{base}/api/admin/brands?page=0&size=1",
            headers=h, timeout=30,
        )
        return resp.status_code == 200
    except Exception:
        return False


def api_create_brand(base: str, token: str, payload: dict) -> dict:
    resp = _session.post(
        f"https://{base}/api/brand",
        json=payload, headers=_headers(token), timeout=30
    )
    _raise_with_body(resp)
    return resp.json()


def _get_latest_brand(base: str, token: str) -> dict:
    h = {k: v for k, v in _headers(token).items() if k != "content-type"}
    resp = _session.get(
        f"https://{base}/api/admin/brands"
        "?page=0&size=1&keyword=&orderField=updatedAt&order=DESC",
        headers=h, timeout=30,
    )
    _raise_with_body(resp)
    return resp.json()["data"][0]


def api_update_status(base: str, token: str, brand_id: int, status: int = 0) -> None:
    resp = _session.put(
        f"https://{base}/api/admin/brand/status",
        json={"status": status, "brandId": brand_id},
        headers=_headers(token), timeout=30,
    )
    _raise_with_body(resp)


def api_create_benefit(base: str, token: str, payload: dict) -> dict:
    resp = _session.post(
        f"https://{base}/api/admin/brand-benefit",
        json=payload, headers=_headers(token), timeout=30,
    )
    _raise_with_body(resp)
    return resp.json()


def api_get_latest_benefit_id(base: str, token: str) -> int | None:
    """Return the newest brand-benefit id (first item of the admin list)."""
    h = {k: v for k, v in _headers(token).items() if k != "content-type"}
    resp = _session.get(
        f"https://{base}/api/admin/brand-benefit?page=0&size=30&keyword=",
        headers=h, timeout=30,
    )
    _raise_with_body(resp)
    items = resp.json().get("data") or []
    if not items:
        return None
    return items[0].get("id")


DOC_EXTS = {".doc", ".docx", ".txt", ".rtf", ".odt", ".gdoc", ".pages", ".csv", ".xls", ".xlsx"}


def clear_folder_contents(folder: Path) -> None:
    """Delete all files and subfolders inside folder (creating folder if not exist)."""
    if not folder.exists():
        folder.mkdir(parents=True, exist_ok=True)
        return
    for item in list(folder.iterdir()):
        try:
            if item.is_file() or item.is_symlink():
                item.unlink()
            elif item.is_dir():
                shutil.rmtree(item)
        except Exception as e:
            print_warn(f"Could not delete {item.name} in '{folder.name}': {e}")


def _extract_gdrive_folder_id(url: str) -> str | None:
    """Extract folder ID from various Google Drive folder URL formats."""
    m = re.search(
        r'drive\.google\.com/(?:drive/(?:u/\d+/)?folders/|embeddedfolderview\?[^"]*id=)([-\w]{25,})(?=$|[/?#&])',
        url,
    )
    if m:
        return m.group(1)
    m = re.search(r'id=([-\w]{25,})(?=$|[/?#&])', url)
    if m and ("folder" in url.lower() or "folders" in url.lower()):
        return m.group(1)
    return None


def _extract_gdrive_file_id(url: str) -> str | None:
    """Extract file ID from various Google Drive file URL formats."""
    m = re.search(
        r'drive\.google\.com/(?:file/d/|open\?[^"]*id=|uc\?[^"]*id=)([-\w]{25,})(?=$|[/?#&])',
        url,
    )
    if m:
        return m.group(1)
    m = re.search(r'id=([-\w]{25,})(?=$|[/?#&])', url)
    if m and "folder" not in url.lower():
        return m.group(1)
    return None


def _extract_urls(text: str) -> list[str]:
    """Extract separate URLs even when adjacent links have no whitespace between them."""
    urls = re.findall(r'https?://[^\s,<>"]*?(?=https?://|[\s,<>"]|$)', text)
    cleaned_urls = []
    for url in urls:
        clean_url = url.rstrip(".,;>\"')")
        if clean_url and clean_url not in cleaned_urls:
            cleaned_urls.append(clean_url)
    return cleaned_urls


def _list_gdrive_folder_items(
    folder_id: str,
    session: requests.Session,
    subpath: str = "",
    depth: int = 0,
    max_depth: int = 5,
) -> list[tuple[str, str, str]]:
    """Recursively list (file_id, filename, relative_subpath) from a public Google Drive folder."""
    if depth > max_depth or not bs4:
        return []
    url = f"https://drive.google.com/embeddedfolderview?id={folder_id}"
    headers = {
        "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/125.0.0.0 Safari/537.36",
        "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8",
    }
    try:
        r = session.get(url, headers=headers, timeout=20)
        if r.status_code != 200:
            return []
    except Exception:
        return []

    soup = bs4.BeautifulSoup(r.text, "html.parser")
    items: list[tuple[str, str, str]] = []

    for a in soup.find_all("a"):
        href = a.get("href", "")
        if not href:
            continue
        # Check for file
        m_file = re.search(r"/file/d/([-\w]{25,})", href)
        if m_file:
            fid = m_file.group(1)
            name = a.get_text(strip=True) or f"{fid}.jpg"
            items.append((fid, name, subpath))
            continue
        # Check for subfolder
        m_folder = re.search(r"/drive/folders/([-\w]{25,})", href)
        if m_folder:
            sub_id = m_folder.group(1)
            sub_name = a.get_text(strip=True) or sub_id
            if sub_id != folder_id:
                new_subpath = f"{subpath}/{sub_name}".strip("/")
                sub_items = _list_gdrive_folder_items(sub_id, session, new_subpath, depth + 1, max_depth)
                items.extend(sub_items)

    # Deduplicate items by file_id
    dedup: list[tuple[str, str, str]] = []
    seen = set()
    for item in items:
        if item[0] not in seen:
            seen.add(item[0])
            dedup.append(item)
    return dedup


def _drive_local_name(name: str, file_id: str) -> str:
    """Keep Drive names within the download directory and valid on Windows."""
    name = re.sub(r'[<>:"/\\|?*\x00-\x1f]', "_", name).rstrip(" .")
    if not name:
        return file_id
    if name.split(".")[0].upper() in {
        "CON", "PRN", "AUX", "NUL",
        *(f"COM{i}" for i in range(1, 10)), *(f"LPT{i}" for i in range(1, 10)),
    }:
        name = "_" + name
    return name


def _list_authenticated_gdrive_folder_items(
    folder_id: str, session: requests.Session, subpath: str = "",
    depth: int = 0, max_depth: int = 5,
) -> list[tuple[str, str, str]]:
    """List private Drive folders recursively, including every result page."""
    if depth > max_depth:
        print_warn(f"Skipping Drive subfolder {folder_id}: maximum nesting depth {max_depth} exceeded.")
        return []
    with _google_drive_api_get(
        session, f"files/{folder_id}",
        params={"fields": "id,mimeType", "supportsAllDrives": "true"},
    ) as response:
        if response.json().get("mimeType") != "application/vnd.google-apps.folder":
            raise RuntimeError(f"Google Drive item {folder_id} is not a folder.")
    items: list[tuple[str, str, str]] = []
    page_token = ""
    while True:
        params = {
            "q": f"'{folder_id}' in parents and trashed = false",
            "fields": "nextPageToken,files(id,name,mimeType)",
            "pageSize": 1000, "supportsAllDrives": "true",
            "includeItemsFromAllDrives": "true",
        }
        if page_token:
            params["pageToken"] = page_token
        with _google_drive_api_get(session, "files", params=params) as response:
            data = response.json()
        for item in data.get("files", []):
            file_id = item["id"]
            name = _drive_local_name(item["name"], file_id)
            mime_type = item.get("mimeType", "")
            if mime_type == "application/vnd.google-apps.folder":
                items.extend(_list_authenticated_gdrive_folder_items(
                    file_id, session, str(Path(subpath) / name),
                    depth + 1, max_depth,
                ))
            elif not mime_type.startswith("application/vnd.google-apps."):
                items.append((file_id, name, subpath))
            else:
                print_info(f"Skipping non-downloadable Google Drive item: {name}")
        page_token = data.get("nextPageToken", "")
        if not page_token:
            return items


def _download_single_gdrive_file(
    file_id: str,
    out_path: Path,
    session: requests.Session | None = None,
    max_attempts: int = 3,
    *,
    authenticated: bool = False,
) -> Path | None:
    """Download a single Google Drive file safely using direct multi-endpoint HTTP downloads."""
    out_path.parent.mkdir(parents=True, exist_ok=True)
    # Ensure unique filename to prevent collision and Windows file locking
    final_path = out_path
    counter = 1
    while final_path.exists():
        final_path = out_path.parent / f"{out_path.stem}_{counter}{out_path.suffix}"
        counter += 1

    tmp_path = final_path.with_name(f".tmp_{final_path.name}_{threading.get_ident()}")
    sess = session or requests.Session()
    headers = {
        "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/125.0.0.0 Safari/537.36",
        "Accept": "*/*",
    }
    if authenticated:
        try:
            with _google_drive_api_get(
                sess, f"files/{file_id}",
                params={"alt": "media", "supportsAllDrives": "true"}, stream=True,
            ) as response:
                if "text/html" in response.headers.get("Content-Type", "").lower():
                    raise RuntimeError(f"Google Drive returned HTML instead of file content for {file_id}.")
                with tmp_path.open("wb") as output:
                    for chunk in response.iter_content(chunk_size=65536):
                        if chunk:
                            output.write(chunk)
            if tmp_path.stat().st_size == 0:
                raise RuntimeError(f"Google Drive returned an empty file for {file_id}.")
            tmp_path.replace(final_path)
            return _ensure_image_extension(final_path)
        finally:
            tmp_path.unlink(missing_ok=True)

    candidate_urls = [
        f"https://drive.usercontent.google.com/download?id={file_id}&export=download&authuser=0",
        f"https://drive.google.com/uc?export=download&id={file_id}",
        f"https://drive.google.com/thumbnail?id={file_id}&sz=w2500",
        f"https://lh3.googleusercontent.com/d/{file_id}",
    ]

    for attempt in range(1, max_attempts + 1):
        for url in candidate_urls:
            try:
                r = sess.get(url, headers=headers, stream=True, timeout=30)
                if r.status_code == 200:
                    ct = r.headers.get("Content-Type", "")
                    if "text/html" in ct:
                        # Follow virus scan / large file confirmation if present
                        m = re.search(r'href="(/uc\?export=download[^"]+)"', r.text)
                        if m:
                            confirm_url = "https://drive.google.com" + m.group(1).replace("&amp;", "&")
                            r2 = sess.get(confirm_url, headers=headers, stream=True, timeout=35)
                            if r2.status_code == 200 and "text/html" not in r2.headers.get("Content-Type", ""):
                                r = r2
                        else:
                            continue

                    with open(tmp_path, "wb") as f:
                        for chunk in r.iter_content(chunk_size=65536):
                            if chunk:
                                f.write(chunk)

                    if tmp_path.exists() and tmp_path.stat().st_size > 0:
                        tmp_path.replace(final_path)
                        return _ensure_image_extension(final_path)
            except Exception:
                pass
            finally:
                if tmp_path.exists():
                    try:
                        tmp_path.unlink()
                    except Exception:
                        pass
        # Fallback to gdown if direct HTTP attempts failed
        if gdown:
            try:
                res = gdown.download(id=file_id, output=str(final_path), quiet=True, use_cookies=False)
                if res and Path(res).exists() and Path(res).stat().st_size > 0:
                    return _ensure_image_extension(Path(res))
            except Exception:
                pass
        if attempt < max_attempts:
            time.sleep(1)

    return None


def download_gdrive_urls(urls: str | list[str], target_dir: Path) -> list[Path]:
    """Download Google Drive folders or files into target_dir.
    - Gallery downloads use account-verified support@obranding.vn Drive OAuth.
    - Public logo/banner downloads retain multi-endpoint HTTP and gdown fallbacks.
    - Uses paginated Drive API listings for galleries, public scraping otherwise.
    - Restores missing image extensions from downloaded content before processing.
    - Filters unwanted gallery files (banner/logo/GPKD/ĐKKD/docs) when target_dir is '2'.
    - Parallel downloads with ThreadPoolExecutor.
    - Extracts any downloaded ZIP files automatically.
    - Returns list of downloaded file paths.
    """
    if isinstance(urls, str):
        url_list = _extract_urls(urls)
        if not url_list:
            url_list = [urls.strip()]
    else:
        url_list = []
        for url in urls:
            clean_url = url.rstrip('.,;>"\')')
            if clean_url and clean_url not in url_list:
                url_list.append(clean_url)

    target_dir.mkdir(parents=True, exist_ok=True)
    downloaded_files: list[Path] = []
    is_gallery = (target_dir.name == "2")
    sess = None

    for url in url_list:
        clean_url = url.strip().rstrip(",")
        if not clean_url:
            continue
        if "drive.google.com" not in clean_url:
            print_info(f"Ignoring non-Google Drive URL: {clean_url}")
            continue
        print_info(f"Downloading from: {Colors.CYAN}{clean_url}{Colors.END}")
        if sess is None:
            sess = _get_google_drive_session() if is_gallery else requests.Session()

        folder_id = _extract_gdrive_folder_id(clean_url)
        if folder_id:
            # 1. Discover items in folder
            items = (
                _list_authenticated_gdrive_folder_items(folder_id, sess)
                if is_gallery else _list_gdrive_folder_items(folder_id, sess)
            )
            if not items and gdown and not is_gallery:
                try:
                    # Secondary fallback for listing folder contents
                    gd_items = gdown.download_folder(clean_url, skip_download=True, quiet=True, use_cookies=False)
                    if gd_items:
                        items = [(it.id, Path(it.path).name, str(Path(it.path).parent) if str(Path(it.path).parent) != "." else "") for it in gd_items]
                except Exception:
                    pass

            if items:
                print_info(f"Found {len(items)} item(s) in Drive folder. Starting download...")
                tasks = []
                for fid, fname, fsub in items:
                    # Filter for gallery folder
                    if is_gallery:
                        f_stem_norm = _normalize_vietnamese(Path(fname).stem.replace("_", " ").replace("-", " "))
                        f_ext = Path(fname).suffix.lower()
                        if "banner" in f_stem_norm or "logo" in f_stem_norm or _is_gpkd_or_dkkd(fname):
                            continue
                        if f_ext in DOC_EXTS:
                            continue

                    dest_folder = target_dir / fsub if fsub else target_dir
                    target_file = dest_folder / fname
                    tasks.append((fid, target_file))

                if tasks:
                    max_w = min(len(tasks), max(4, min(8, os.cpu_count() or 4)))
                    with ThreadPoolExecutor(max_workers=max_w) as ex:
                        futures = {
                            ex.submit(
                                _download_single_gdrive_file, fid, dest_f, sess,
                                authenticated=is_gallery,
                            ): dest_f for fid, dest_f in tasks
                        }
                        for fut in as_completed(futures):
                            dest_f = futures[fut]
                            try:
                                res = fut.result()
                                if res and res.exists() and res.stat().st_size > 0:
                                    downloaded_files.append(res)
                            except Exception as e:
                                print_warn(f"Failed to download {dest_f.name}: {e}")
                else:
                    print_info("No matching image files found to download after filtering.")
            else:
                if is_gallery:
                    print_warn("No downloadable files found in the Google Drive folder.")
                # If folder listing failed, try gdown.download_folder as fallback
                if gdown and not is_gallery:
                    try:
                        res = gdown.download_folder(clean_url, output=str(target_dir), quiet=True, use_cookies=False)
                        if res:
                            downloaded_files.extend(_ensure_image_extension(Path(p)) for p in res if p and Path(p).exists())
                    except Exception as exc:
                        print_warn(f"Fallback folder download failed: {exc}")
        else:
            # Single file or direct file link
            file_id = _extract_gdrive_file_id(clean_url)
            if file_id:
                filename = f"{file_id}.jpg"
                if is_gallery:
                    with _google_drive_api_get(
                        sess, f"files/{file_id}",
                        params={"fields": "name", "supportsAllDrives": "true"},
                    ) as response:
                        filename = _drive_local_name(response.json()["name"], file_id)
                target_file = target_dir / filename
                res = _download_single_gdrive_file(
                    file_id, target_file, sess, authenticated=is_gallery,
                )
                if res:
                    downloaded_files.append(res)
            else:
                print_warn(f"Could not extract Google Drive folder or file ID from: {clean_url}")

    # Extract any downloaded ZIP files (and delete the archive)
    for zip_path in list(target_dir.rglob("*.zip")):
        try:
            print_info(f"Extracting {zip_path.name} in '{target_dir.name}'...")
            with zipfile.ZipFile(zip_path, "r") as zf:
                zf.extractall(zip_path.parent)
            zip_path.unlink()
            print_success(f"Extracted and unzipped {zip_path.name} successfully.")
        except Exception as e:
            print_warn(f"Failed to extract {zip_path.name}: {e}")

    return downloaded_files


def clean_gallery_folder(folder: Path, verbose: bool = False) -> None:
    """Filter out banner folders/files, docs files, and GPKD/ĐKKD files from gallery folder '2'."""
    if not folder.exists():
        return

    # First pass: check subfolders
    for sub in sorted(list(folder.glob("**/")), reverse=True):
        if sub == folder:
            continue
        sub_norm = _normalize_vietnamese(sub.name.replace("_", " ").replace("-", " "))
        if "banner" in sub_norm or "logo" in sub_norm or _is_gpkd_or_dkkd(sub.name):
            if verbose:
                print_info(f"Excluding/removing folder matching filter: {Colors.YELLOW}{sub.name}{Colors.END}")
            try:
                shutil.rmtree(sub)
            except Exception as e:
                print_warn(f"Could not remove folder {sub.name}: {e}")

    # Second pass: check files
    for p in list(folder.rglob("*")):
        if not p.is_file():
            continue
        p_stem_norm = _normalize_vietnamese(p.stem.replace("_", " ").replace("-", " "))
        ext = p.suffix.lower()

        should_remove = False
        reason = ""

        if "banner" in p_stem_norm:
            should_remove = True
            reason = "contains 'banner'"
        elif "logo" in p_stem_norm:
            should_remove = True
            reason = "contains 'logo'"
        elif _is_gpkd_or_dkkd(p.name):
            should_remove = True
            reason = "GPKD / ĐKKD / Đăng ký kinh doanh file"
        elif ext in DOC_EXTS:
            should_remove = True
            reason = "document file"

        if should_remove:
            if verbose:
                print_info(f"Excluding/removing {reason}: {Colors.YELLOW}{p.name}{Colors.END}")
            try:
                p.unlink()
            except Exception as e:
                print_warn(f"Could not remove {p.name}: {e}")


def _extract_zip_files(folder: Path) -> None:
    """Extract ZIP files found under a folder, stopping if an archive is invalid."""
    if not folder.exists():
        return

    for zip_path in sorted(
        (path for path in folder.rglob("*") if path.is_file() and path.suffix.lower() == ".zip"),
        key=lambda path: len(path.parts),
    ):
        print_info(f"Extracting {zip_path.name} in '{zip_path.parent.name}'...")
        try:
            with zipfile.ZipFile(zip_path, "r") as archive:
                root = zip_path.parent.resolve()
                for member in archive.infolist():
                    destination = (root / member.filename).resolve()
                    if os.path.normcase(os.path.commonpath((str(root), str(destination)))) != os.path.normcase(str(root)):
                        raise ValueError(f"Archive member escapes its folder: {member.filename}")
                archive.extractall(root)
            zip_path.unlink()
            print_success(f"Extracted {zip_path.name} successfully.")
        except Exception as exc:
            print_fail(f"Failed to extract {zip_path.name}: {exc}")
            raise RuntimeError(f"Could not extract gallery archive {zip_path}") from exc


def prepare_folders_with_zip(folders: list[Path]) -> None:
    """Prepare image folders before processing.

    Rules:
      • If a folder contains a ZIP file  → delete all other files/dirs in that
        folder, then extract the ZIP.  (Old behaviour — ZIP takes priority.)
      • If a folder has NO ZIP file      → leave it completely untouched so the
        user's manually-extracted images are preserved.
    """
    # Separate folders into those that have a ZIP and those that don't.
    folders_with_zip:    list[tuple[Path, list[Path]]] = []
    folders_without_zip: list[Path] = []

    for folder in folders:
        if not folder.exists():
            continue
        zips = [p for p in folder.iterdir() if p.is_file() and p.suffix.lower() == ".zip"]
        if zips:
            folders_with_zip.append((folder, zips))
        else:
            folders_without_zip.append(folder)

    # Report folders that will be left as-is.
    for folder in folders_without_zip:
        imgs = [
            p for p in folder.iterdir()
            if p.is_file() and p.suffix.lower() in IMG_EXTS
        ]
        print_info(
            f"Folder '{folder.name}' has no ZIP — keeping {len(imgs)} existing image(s)."
        )

    if not folders_with_zip:
        return

    print(f"\n{Colors.WARNING}{Colors.BOLD}⚠ Found ZIP file(s) in folders – extracting automatically:{Colors.END}")
    for folder, zips in folders_with_zip:
        zip_names = ", ".join(z.name for z in zips)
        print(f"  • '{folder.name}': {zip_names}")

    # Process only the folders that actually have a ZIP.
    for folder, folder_zips_list in folders_with_zip:
        # Delete everything except the ZIP file(s) themselves.
        for f in list(folder.iterdir()):
            if f not in folder_zips_list:
                try:
                    if f.is_file() or f.is_symlink():
                        f.unlink()
                    elif f.is_dir():
                        shutil.rmtree(f)
                except Exception as e:
                    print_warn(f"Could not delete {f.name} in '{folder.name}': {e}")

        # Extract each ZIP.
        for zip_path in folder_zips_list:
            print_info(f"Extracting {zip_path.name} in '{folder.name}'...")
            try:
                with zipfile.ZipFile(zip_path, 'r') as zip_ref:
                    zip_ref.extractall(folder)
                zip_path.unlink()
                print_success(f"Extracted {zip_path.name} and cleaned folder '{folder.name}'.")
            except Exception as e:
                print_fail(f"Failed to extract {zip_path.name}: {e}")


# ---------------------------------------------------------------------------
# Main brand flow
# ---------------------------------------------------------------------------

def process_brand(
    base: str, token: str,
    city_data: list, cat_data: list, ben_data: list,
) -> None:
    # ── 1. Brand lookup & Google Sheet data ──────────────────────────────────
    print_step("🔍 [Step 1] Looking up brand from Base & Google Sheet...")
    user_input, is_pure_number = prompt_brand_lookup()
    total_rows = 0
    if is_pure_number:
        # Preserve numeric row/job-ID detection without requiring Sheets for BASE URLs.
        try:
            _, _, initial_rows, _ = resolve_sheet_rows({}, row_num=int(user_input))
            total_rows = len(initial_rows)
        except RuntimeError as exc:
            print_warn(f"{exc} Trying the number as a BASE job ID.")

    detected_row: int | None = None
    detected_cats: list[int] = []
    detected_ben: str = ""
    job_info: dict = {}

    base_job_id = base_job_id_from_url(user_input)
    is_base_job_id = is_pure_number and int(user_input) > total_rows

    if base_job_id or is_base_job_id:
        job_id = base_job_id or user_input
        print_info(f"Fetching Base.vn Workflow job ID: {job_id}...")
        base_cookies, base_data = load_base_auth()
        status, job = fetch_base_job(job_id, base_cookies, base_data)
        if status == "INVALID_SESSION":
            base_cookies, base_data = prompt_update_base_auth()
            status, job = fetch_base_job(job_id, base_cookies, base_data)
        if status == "OK" and job:
            job_info = extract_base_job_info(job)
            print_success(f"Found on Base: '{job_info['job_name']}' -> Brand Name: '{job_info['brand_name']}' (ID: {job_info['job_id']})")
            if job_info["raw_category"]:
                detected_cats = map_base_categories(job_info["raw_category"], cat_data)
            if job_info["raw_benefit"]:
                detected_ben = map_base_benefit(job_info["raw_benefit"], ben_data)
            if job_info["sheet_row"]:
                detected_row = job_info["sheet_row"]
        elif status == "OK" and not job:
            print_warn(f"No job found on Base.vn for ID {job_id}.")
        else:
            print_warn(f"Base.vn lookup status: {status}")
    elif is_pure_number:
        detected_row = int(user_input)
    else:
        # 1. Base.vn API search
        print_info(f"Searching Base.vn Workflow for: '{user_input}'...")
        base_cookies, base_data = load_base_auth()
        status, jobs = query_base_workflow(user_input, base_cookies, base_data)

        if status == "INVALID_SESSION":
            base_cookies, base_data = prompt_update_base_auth()
            status, jobs = query_base_workflow(user_input, base_cookies, base_data)

        if status == "OK" and jobs:
            # Sort jobs by date descending (latest first)
            jobs.sort(key=lambda j: int(j.get("last_update") or j.get("since") or 0), reverse=True)
            latest_job = jobs[0]
            job_info = extract_base_job_info(latest_job)
            print_success(f"Found on Base: '{job_info['job_name']}' -> Brand Name: '{job_info['brand_name']}' (ID: {job_info['job_id']})")
            if job_info["raw_category"]:
                detected_cats = map_base_categories(job_info["raw_category"], cat_data)
            if job_info["raw_benefit"]:
                detected_ben = map_base_benefit(job_info["raw_benefit"], ben_data)
            if job_info["sheet_row"]:
                detected_row = job_info["sheet_row"]
        elif status == "OK" and not jobs:
            print_warn("No matching brand job found on Base.vn.")
        else:
            print_warn(f"Base.vn lookup status: {status}")

    sheet_id, sheet_gid, rows, detected_row = resolve_sheet_rows(
        job_info, "" if is_pure_number or base_job_id else user_input,
        row_num=detected_row,
    )
    total_rows = len(rows)
    print_info(f"Selected spreadsheet: https://docs.google.com/spreadsheets/d/{sheet_id}/edit#gid={sheet_gid}")
    if detected_row:
        print_success(f"Found row {detected_row}: '{_cell(rows[detected_row - 1], 2)}'")

    # Review only when the row was not selected explicitly or matched exactly.
    if _has_confident_row_match(
        user_input, is_pure_number and not is_base_job_id, detected_row, rows, job_info
    ):
        row_num = detected_row
        print_success(f"Using matched Google Sheet row {row_num} automatically.")
    else:
        row_num = prompt_review_row(detected_row, total_rows)
    print_info(f"Fetching row {row_num} from Google Sheet...")
    row = fetch_row(row_num, sheet_id=sheet_id, sheet_gid=sheet_gid)

    # Ensure Base job info is retrieved for this row if not already found or if row changed
    if not job_info or row_num != detected_row:
        job_info = {}
        detected_cats = []
        detected_ben = ""
        try:
            base_cookies, base_data = load_base_auth()
            stt_val = _cell(row, 1).strip()
            b_status, b_jobs = ("NO_DATA", [])
            # Try 1: Search by STT from Column B
            if stt_val and stt_val.isdigit():
                b_status, b_jobs = query_base_workflow(stt_val, base_cookies, base_data)
            # Try 2: If not found, search by stripped brand name from Column C
            if b_status != "OK" or not b_jobs:
                clean_query = _strip_parenthetical_postfix(_cell(row, 2)).strip()
                if clean_query:
                    b_status, b_jobs = query_base_workflow(clean_query, base_cookies, base_data)

            if b_status == "OK" and b_jobs:
                matching_job = None
                b_jobs.sort(key=lambda j: int(j.get("last_update") or j.get("since") or 0), reverse=True)
                for j in b_jobs:
                    if stt_val and extract_base_brand_prefix(j.get("name", "")) == stt_val:
                        matching_job = j
                        break
                if not matching_job:
                    for j in b_jobs:
                        extracted = extract_base_job_info(j)
                        source = parse_sheet_link(extracted.get("sheet_link", ""))
                        if (
                            extracted.get("sheet_row") == row_num
                            and source and source[:2] == (sheet_id, sheet_gid)
                        ):
                            matching_job = j
                            break
                if not matching_job:
                    matching_job = b_jobs[0]

                job_info = extract_base_job_info(matching_job)
                print_success(f"Found on Base: '{job_info['job_name']}' -> Brand Name: '{job_info['brand_name']}' (ID: {job_info['job_id']})")
                if not detected_cats and job_info.get("raw_category"):
                    detected_cats = map_base_categories(job_info["raw_category"], cat_data)
                if not detected_ben and job_info.get("raw_benefit"):
                    detected_ben = map_base_benefit(job_info["raw_benefit"], ben_data)
        except Exception as exc:
            print_warn(f"Base.vn lookup warning: {exc}")

    # Set brand name directly from Base if available, removing prefixes and preserving ()
    if job_info and job_info.get("brand_name"):
        brand_name = job_info["brand_name"]
    else:
        # Fallback to Google Sheet Column C if Base lookup was not found
        brand_name = clean_base_brand_name(_cell(row, 2).strip())

    d = parse_row(row, brand_name=brand_name)

    print_header(f"📄 Brand Details (Row {row_num})")
    print(f"  • {Colors.BOLD}Name{Colors.END}      : {Colors.CYAN}{d['name']}{Colors.END}")
    print(f"  • {Colors.BOLD}Email{Colors.END}     : {Colors.BLUE}{d['email']}{Colors.END}")
    print(f"  • {Colors.BOLD}Address{Colors.END}   : {Colors.PEACH}{d['addresses_raw'][:100]}...{Colors.END}")

    # ── 2. User selections & review ─────────────────────────────────────────
    print_step("🏷️  [Step 2] Matching categories & benefit...")
    raw_benefit = job_info.get("raw_benefit", "")
    benefit_matched = bool(
        detected_ben and _has_recognized_base_benefit(raw_benefit)
    )
    if not detected_cats or not benefit_matched:
        print_category_and_benefit_reference_lists(cat_data, ben_data)

    if detected_cats:
        categories = detected_cats
        category_names = [
            entry["name"] for entry in cat_data if entry["id"] in categories
        ]
        print_success(
            "Using matched categor"
            f"{'ies' if len(category_names) != 1 else 'y'} automatically: "
            f"{', '.join(category_names)}"
        )
    else:
        print_warn("Category could not be matched automatically; please review.")
        categories = prompt_review_categories([], cat_data)

    if benefit_matched:
        benefit_type = detected_ben
        benefit_description = next(
            (
                entry["description"]
                for entry in ben_data
                if entry["type"] == detected_ben
            ),
            detected_ben,
        )
        print_success(f"Using matched benefit automatically: {benefit_description}")
    else:
        if detected_ben:
            print_warn("Benefit text did not match a known rule; please review.")
        else:
            print_warn("Benefit could not be matched automatically; please review.")
        benefit_type = prompt_review_benefit_type("", ben_data)
    
    # Extract discount % automatically from benefit_tos description
    discount = extract_discount_from_tos(d["benefit_tos"])
    if discount > 0:
        print_success(f"Automatically extracted discount: {Colors.BOLD}{discount}%{Colors.END} from benefit description")
    else:
        print_warn("No discount percentage found in benefit description, using 0%")

    # ── 3. Folder preparation & compression ─────────────────────────────────
    f1 = SCRIPT_DIR / "1"
    f2 = SCRIPT_DIR / "2"

    # Auto-download from Base logo/banner link into folder 1.
    # Priority rule:
    #   • "LINK SẢN PHẨM LẦN 2" present → use it (revised upload)
    #   • otherwise fall back to "LINK SẢN PHẨM"
    _pl1 = job_info.get("product_link", "") if job_info else ""
    _pl2 = job_info.get("product_link_2", "") if job_info else ""
    if _pl2:
        product_link = _pl2
        print_info(f"Using {Colors.BOLD}LINK SẢN PHẨM LẦN 2{Colors.END} for logo/banner: {Colors.CYAN}{_pl2}{Colors.END}")
    elif _pl1:
        product_link = _pl1
        print_info(f"Using {Colors.BOLD}LINK SẢN PHẨM{Colors.END} for logo/banner: {Colors.CYAN}{_pl1}{Colors.END}")
    else:
        product_link = ""
    if product_link:
        clear_folder_contents(f1)
        download_gdrive_urls(product_link, f1)
        # After gdown, unzip anything that landed in folder 1
        for _zp in list(f1.rglob("*.zip")):
            try:
                with zipfile.ZipFile(_zp, "r") as _zf:
                    _zf.extractall(_zp.parent)
                _zp.unlink()
            except Exception:
                pass
        flatten_subfolders(f1)
        # Chrome fallback: if folder 1 is still empty after gdown, open link manually
        f1_images = list(f1.rglob("*")) if f1.exists() else []
        f1_has_files = any(p.is_file() and p.suffix.lower() in (IMG_EXTS | {".pdf"}) for p in f1_images)
        if not f1_has_files:
            _pl_urls = re.findall(r'https?://[^\s,<>"]+', product_link) if isinstance(product_link, str) else list(product_link)
            _pl_urls = [u.rstrip('.,;>"\')') for u in _pl_urls if u.strip() and "drive.google.com" in u]
            if _pl_urls:
                print_warn("gdown could not download folder 1 (rate-limited or restricted). Opening in Chrome...")
                open_in_chrome(*_pl_urls)
                print_info(f"Download the logo/banner files into: {Colors.CYAN}{f1}{Colors.END}")
                input(f"  {Colors.BOLD}⏳ Press Enter when folder '1' is ready: {Colors.END}")
                for _zp in list(f1.rglob("*.zip")):
                    try:
                        with zipfile.ZipFile(_zp, "r") as _zf:
                            _zf.extractall(_zp.parent)
                        _zp.unlink()
                    except Exception:
                        pass
                flatten_subfolders(f1)

    # Auto-download from Google Sheet Column N (index 13) into folder 2
    raw_col_n = _cell(row, 13)
    col_n_all_urls = _extract_urls(raw_col_n) if raw_col_n else []

    # Keep only Google Drive links; ignore all other links (e.g. Shopee, web, Facebook, etc.)
    col_n_urls = [u for u in col_n_all_urls if "drive.google.com" in u]
    non_drive_urls = [u for u in col_n_all_urls if "drive.google.com" not in u]
    if non_drive_urls:
        print_info(f"Ignoring non-Google Drive link(s) in Column N: {', '.join(non_drive_urls)}")

    # If Column N doesn't contain a direct Google Drive link, check for embedded hyperlink in cell
    if not col_n_urls:
        if raw_col_n:
            print_info(f"Checking for embedded hyperlink in cell N{row_num}...")
        embedded_link = fetch_cell_hyperlink(row_num, "N", sheet_id=sheet_id, sheet_gid=sheet_gid)
        if embedded_link:
            embedded_urls = _extract_urls(embedded_link)
            col_n_urls = list(dict.fromkeys(u for u in embedded_urls if "drive.google.com" in u))
            if col_n_urls:
                print_success(f"Found embedded Drive link in cell N{row_num}: {Colors.CYAN}{embedded_link}{Colors.END}")
            else:
                print_info(f"Ignoring non-Google Drive embedded link in cell N{row_num}: {embedded_link}")

    # Always clear folder 2 first to prevent stale images from the previous brand
    clear_folder_contents(f2)

    if col_n_urls:
        # Auto-download from Column N into folder 2.
        drive_download_failed = False
        try:
            download_gdrive_urls(col_n_urls, f2)
        except Exception as exc:
            drive_download_failed = True
            print_warn(f"Automatic Google Drive download failed: {exc}")

        if not drive_download_failed:
            _extract_zip_files(f2)
            clean_gallery_folder(f2)
            flatten_subfolders(f2)
            clean_gallery_folder(f2)
        # Chrome fallback: if folder 2 is still empty of images after gdown, open link manually
        f2_has_files = any(p.is_file() and p.suffix.lower() in (IMG_EXTS | {".pdf"}) for p in f2.rglob("*")) if f2.exists() else False
        if drive_download_failed or not f2_has_files:
            print_warn("Google Drive download did not complete automatically. Opening the link for manual download...")
            open_in_chrome(*col_n_urls)
            print_info(f"Sign in to Drive as {GOOGLE_DRIVE_ACCOUNT} for manual downloads.")
            print_info(f"Download the gallery files into: {Colors.CYAN}{f2}{Colors.END}")
            print_info("Tip: Right-click the folder in Drive → Download → saves as ZIP. Move it into the folder above.")
            input(f"  {Colors.BOLD}⏳ Press Enter when folder '2' is ready: {Colors.END}")
            _extract_zip_files(f2)
            clean_gallery_folder(f2)
            flatten_subfolders(f2)
            clean_gallery_folder(f2)
    else:
        print_warn("No Google Drive link found in Column N — folder '2' cleared. Place gallery images or ZIP files there before continuing.")
        input(f"  {Colors.BOLD}Press Enter when folder '2' is ready: {Colors.END}")
        _extract_zip_files(f2)
        clean_gallery_folder(f2)
        flatten_subfolders(f2)
        clean_gallery_folder(f2)

    prepare_folders_with_zip([f1, f2])

    print_step("📁 [Step 3] Flattening subfolders in folder '2' (gallery)...")
    if f2.exists():
        clean_gallery_folder(f2)
        sub_count, files_moved = flatten_subfolders(f2)
        clean_gallery_folder(f2)
        if sub_count > 0:
            print_success(f"Flattened {sub_count} subfolder(s) ({files_moved} file(s) moved).")
        else:
            print_success("Folder '2' is ready (no subfolders to flatten).")
    else:
        print_warn("Folder '2' not found.")

    print_step("📄 [Step 4] Converting PDF files to images...")
    stems_f1: set[str] = set()
    if f1.exists():
        stems_f1 = convert_pdfs_in_folder(f1)
    converted_pdf_stems_f2: set[str] = set()
    if f2.exists():
        converted_pdf_stems_f2 = convert_pdfs_in_folder(f2)
    total_pdf_pages = len(stems_f1) + len(converted_pdf_stems_f2)
    if total_pdf_pages > 0:
        print_success(f"Converted PDF file(s) to {total_pdf_pages} image(s).")
    else:
        print_success("No PDF files found to convert.")

    print_step("🖼️  [Step 5+6] Compressing images in folders '1' and '2' (parallel)...")
    # Collect all images from both folders into a single flat task list
    _comp_tasks: list[tuple[Path, int, int, int]] = []  # (path, max_kb, quality, max_dim)
    if f1.exists():
        for _p in _list_images(f1):
            _comp_tasks.append((_p, 1500, 95, 2100))
    else:
        print_warn("Folder '1' not found.")
    if f2.exists():
        for _p in _list_images(f2):
            _comp_tasks.append((_p, 1000, 92, 2100))
    else:
        print_warn("Folder '2' not found.")

    if _comp_tasks:
        _max_workers = min(len(_comp_tasks), max(8, os.cpu_count() or 4))
        compressed_count = 0
        with ThreadPoolExecutor(max_workers=_max_workers) as comp_ex:
            comp_futures = {
                comp_ex.submit(_compress_single, _p, _mk, _q, _md): _p
                for _p, _mk, _q, _md in _comp_tasks
            }
            for fut in as_completed(comp_futures):
                src = comp_futures[fut]
                try:
                    fut.result()
                    compressed_count += 1
                except Exception as e:
                    print_warn(f"Failed to compress {src.name}: {e}")
        print_success(f"Compressed {compressed_count}/{len(_comp_tasks)} image(s) across folders '1' and '2'.")
    else:
        print_info("No images found to compress.")

    print_step("🔍 [Step 7+8] Dedup, detect logo/banner & classify gallery (parallel)...")
    # Run dedup (folder 2) and detect_logo_banner (folder 1) in parallel
    with ThreadPoolExecutor(max_workers=2) as step78_ex:
        dedup_fut = step78_ex.submit(dedup_similar_images, f2, 0.93) if f2.exists() else None
        logo_fut = step78_ex.submit(detect_logo_banner, f1)

        logo_path, banner_path = logo_fut.result()
        if dedup_fut:
            dedup_fut.result()  # wait for dedup to finish before classifying

    # Now classify & reorder gallery (needs dedup to be done first)
    raw_gallery_paths = []
    if f2.exists():
        for p in f2.iterdir():
            if p.suffix.lower() in IMG_EXTS and p.suffix.lower() not in _NON_IMAGE_EXTS:
                if _is_gpkd_or_dkkd(p.name):
                    try:
                        p.unlink()
                    except Exception:
                        pass
                    continue
                raw_gallery_paths.append(p)
        raw_gallery_paths.sort()

    place_paths, banner_paths, cert_paths, people_paths, product_paths, gallery_paths = reorder_gallery_images(
        raw_gallery_paths, converted_pdf_stems_f2
    )

    print_success(
        f"Gallery classified ({len(gallery_paths)} image(s)): "
        f"{len(place_paths)} Place, {len(banner_paths)} Banner(s), "
        f"{len(cert_paths)} Certificate(s), {len(people_paths)} People, "
        f"{len(product_paths)} Product(s) & Other"
    )

    # Fallback: if LINK SẢN PHẨM LẦN 2 was used but yielded no logo/banner,
    # retry with the original LINK SẢN PHẨM.
    if (not logo_path and not banner_path) and _pl2 and _pl1:
        print_warn("No logo/banner found in LINK SẢN PHẨM LẦN 2. Falling back to LINK SẢN PHẨM...")
        print_info(f"Downloading from LINK SẢN PHẨM: {Colors.CYAN}{_pl1}{Colors.END}")
        clear_folder_contents(f1)
        download_gdrive_urls(_pl1, f1)
        for _zp in list(f1.rglob("*.zip")):
            try:
                with zipfile.ZipFile(_zp, "r") as _zf:
                    _zf.extractall(_zp.parent)
                _zp.unlink()
            except Exception:
                pass
        flatten_subfolders(f1)
        f1_has_files_fb = any(p.is_file() for p in f1.rglob("*")) if f1.exists() else False
        if not f1_has_files_fb:
            _fb_urls = re.findall(r'https?://[^\s,<>"]+', _pl1) if isinstance(_pl1, str) else list(_pl1)
            _fb_urls = [u.rstrip('.,;>"\')') for u in _fb_urls if u.strip()]
            if _fb_urls:
                print_warn("gdown could not download fallback folder 1. Opening in Chrome...")
                open_in_chrome(*_fb_urls)
                print_info(f"Download the logo/banner files into: {Colors.CYAN}{f1}{Colors.END}")
                input(f"  {Colors.BOLD}⏳ Press Enter when folder '1' is ready (fallback): {Colors.END}")
                for _zp in list(f1.rglob("*.zip")):
                    try:
                        with zipfile.ZipFile(_zp, "r") as _zf:
                            _zf.extractall(_zp.parent)
                        _zp.unlink()
                    except Exception:
                        pass
                flatten_subfolders(f1)
        logo_path, banner_path = detect_logo_banner(f1)

    if not logo_path:
        print_warn("No square image (logo) found in folder '1'.")
    if not banner_path:
        print_warn("No wide image (banner) found in folder '1'.")

    # ── 4. Upload images (parallel, max 3 workers to avoid 502s) ───────────
    print_step("📤 [Step 9] Uploading images...")
    logo_url              = ""
    banner_url            = ""
    benefit_image_url     = ""
    logo_gallery_entries: list[dict] = []
    gallery_entries: list[dict]      = []

    gallery_batches = [
        gallery_paths[i : i + 5]
        for i in range(0, len(gallery_paths), 5)
    ]

    # Build task list: (label, callable, *args)
    tasks: list[tuple] = []
    if logo_path:
        tasks.append(("logo_resize",   upload_resize,       base, token, logo_path,   "brand",      True,  "300x300"))
        tasks.append(("logo_gallery",  upload_gallery_batch, base, token, [logo_path]))
    if banner_path:
        tasks.append(("banner_resize",  upload_resize,       base, token, banner_path, "brand",      False, "2100x700"))
        tasks.append(("membership",     upload_resize,       base, token, banner_path, "membership", True,  None))
    for i, batch in enumerate(gallery_batches):
        tasks.append((f"gallery_{i:03d}", upload_gallery_batch, base, token, batch))

    with ThreadPoolExecutor(max_workers=3) as ex:
        futures = {
            ex.submit(fn, *args): label
            for (label, fn, *args) in tasks
        }
        gallery_batch_results: dict[str, list] = {}
        for fut in as_completed(futures):
            label = futures[fut]
            try:
                result = fut.result()
                if label == "logo_resize":
                    logo_url = _strip_s3(result.get("300x300", {}).get("Location", ""))
                elif label == "banner_resize":
                    banner_url = _strip_s3(result.get("2100x700", {}).get("Location", ""))
                elif label == "membership":
                    raw_location = result.get("convertedOrigin", {}).get("Location", "")
                    benefit_image_url = raw_location if "stg" in base else _to_cloudfront(raw_location)
                elif label == "logo_gallery":
                    for item in result:
                        logo_gallery_entries.append({
                            "id":    item.get("originalname", item.get("key", "")),
                            "image": item.get("key", ""),
                        })
                else:  # gallery_N
                    gallery_batch_results[label] = result
            except Exception as e:
                print_warn(f"{label} upload failed: {e}")
                if label.startswith("gallery_"):
                    gallery_batch_results[label] = []

    # 1. Start with logo from folder 1 (displayed on the far left)
    gallery_entries.extend(logo_gallery_entries)

    # 2. Append folder 2 gallery batches (certificates -> people -> products/others)
    for label in sorted(gallery_batch_results):
        for item in gallery_batch_results[label]:
            gallery_entries.append({
                "id":    item.get("originalname", item.get("key", "")),
                "image": item.get("key", ""),
            })

    print_success(
        f"All images uploaded: Logo ({'✓' if logo_url else '✗'}), "
        f"Banner ({'✓' if banner_url else '✗'}), "
        f"Benefit image ({'✓' if benefit_image_url else '✗'}), "
        f"Gallery ({len(gallery_entries)} image(s))."
    )

    # ── 5. Build brand payload ──────────────────────────────────────────────
    # Split addresses on newlines and semicolons
    _raw_addr_lines = []
    for _line in d["addresses_raw"].splitlines():
        for _part in _line.split(";"):
            _part = _part.strip()
            if _part:
                _raw_addr_lines.append(_part)
    addresses = [
        re.sub(r"[\s.,;:!\-–—/]+$", "",
            _title_address(
                _normalize_local_address_prefixes(
                    _normalize_province_prefix(
                        re.sub(r",?\s*Việt\s+Nam[\s.,;:!\-–—/]*$", "",
                               _clean_address(a), flags=re.IGNORECASE).strip(),
                        city_data,
                    )
                )
            )
        ).strip()
        for a in _raw_addr_lines if a.strip()
    ]
    addresses = [a for a in addresses if a]
    # If column 'S' (addresses_raw) is empty, send a single whitespace for `address`
    # instead of an empty string (keeps behavior identical for non-empty cells).
    main_addr = addresses[0] if addresses else (" " if not d["addresses_raw"] else "")
    city_id   = lookup_city(main_addr, city_data)
    city_name = get_city_name(city_id, city_data)
    if city_name:
        print_info(f"City mapped: {Colors.BOLD}{city_name}{Colors.END} (ID: {city_id})")

    stores = []
    for idx, addr in enumerate(addresses, start=1):
        stores.append({
            "city": {"id": None},
            "name": f"Chi nhánh {idx}",
            "address": addr,
            "contactNumber": d["phone"],
            "saved": True,
            "geographyCityId": lookup_city(addr, city_data),
        })

    _fallback_email = "brand20236868@gmail.com"
    email_list = d.get("emails") or (_parse_emails(d.get("email", "")) if d.get("email") else [])
    if email_list:
        _staff_email = email_list[0]
        _brand_staffs = [{"email": em, "primary": (i == 0)} for i, em in enumerate(email_list)]
    else:
        _staff_email = _fallback_email
        _brand_staffs = [{"email": _fallback_email, "primary": True}]

    homepage_url = d["homepage"]
    if homepage_url:
        if _is_url_reachable(homepage_url):
            print_success(f"Website reachable: {Colors.CYAN}{homepage_url}{Colors.END}")
        else:
            print_warn(f"Skipping homepageUrl (unreachable): {homepage_url}")
            homepage_url = ""

    social_review_urls: list[str] = []
    brand_payload = {
        "name":               d["name"],
        "description":        d["description"],
        "logoUrl":            logo_url,
        "coverPhotoUrl":      banner_url,
        "smallPhotoUrl":      "",
        "gallery":            gallery_entries,
        "homepageUrl":        homepage_url,
        "address":            main_addr,
        "geographyCountryId": "00084",
        "geographyCityId":    city_id,
        "contactNumber":      d["phone"],
        "contactEmail":       d["email"],
        "socialPortfolios":   build_socials(d["socials_raw"], homepage_url, review_urls=social_review_urls),
        "email":              _staff_email,
        "brandStaffs":        _brand_staffs,
        "featured":           True,
        "newBrand":           True,
        "categories":         categories,
        "suppliers":          [],
        "demands":            [],
        "status":             "1",
        "bankInfo":           '{"name":"","accountNumber":"","accountHolderName":""}',
        "receiveWallet":      "",
        "brandStores":        stores,
    }

    # ── 6. Create brand ─────────────────────────────────────────────────────
    print_step("🚀 [Step 10] Creating brand...")
    create_resp = api_create_brand(base, token, brand_payload)

    # Extract brand ID + slug from the create response first;
    # fall back to querying the brand list only if not returned.
    brand_id: int | None = None
    slug: str = ""
    if isinstance(create_resp, dict):
        brand_id = create_resp.get("id") or (create_resp.get("data") or {}).get("id")
        slug     = create_resp.get("slug", "") or (create_resp.get("data") or {}).get("slug", "")

    if not brand_id:
        print_warn("Create response did not contain ID, querying brand list...")
        latest   = _get_latest_brand(base, token)
        brand_id = latest["id"]
        slug     = latest.get("slug", "")

    print_success(f"Brand created successfully! ID = {Colors.BOLD}{brand_id}{Colors.END} | Slug = {Colors.CYAN}{slug}{Colors.END}")

    # ── 7+8. Update status & Create brand benefit (parallel) ────────────────
    # benefit_image_url was uploaded in parallel during Step 9.
    # Build benefit payload first so both API calls can fire concurrently.
    _pct_matches = re.findall(r'(\d+(?:[.,]\d+)?)\s*%', d["benefit_tos"])
    _pct_value = max((float(v.replace(',', '.')) for v in _pct_matches), default=0)
    _is_high_discount = _pct_value >= 10

    benefit_payload = {
        "benefitTypes": [{
            "benefitType": benefit_type,
            "discount":    discount,
            "tos":         d["benefit_tos"],
        }],
        "brandId":      brand_id,
        "discount":     discount,
        "tos":          d["benefit_tos"],
        "featured":     _is_high_discount,
        "newBrand":     not _is_high_discount,
        "image":        benefit_image_url,
        "isShowHomePage": True,
    }

    print_step("⚙️🎁 [Step 11+12] Updating status & creating benefit (parallel)...")
    with ThreadPoolExecutor(max_workers=2) as final_ex:
        status_fut = final_ex.submit(api_update_status, base, token, brand_id, 0)
        benefit_fut = final_ex.submit(api_create_benefit, base, token, benefit_payload)

        status_fut.result()
        benefit_fut.result()

    benefit_id = api_get_latest_benefit_id(base, token)
    if benefit_id:
        print_success(f"Status active & Benefit created successfully! (ID: {Colors.BOLD}{benefit_id}{Colors.END})")
    else:
        print_success("Status active & Benefit created successfully.")

    # ── 9. Print brand URL + open review tabs ──────────────────────────────
    # Slug may still be empty if the create response didn't include it;
    # fetch it from the brand list as a last resort.
    if not slug:
        slug = _get_latest_brand(base, token).get("slug", "")
    brand_url = f"https://{base}/the-sanh/brand/{slug}"
    brand_edit_url = f"https://{base}/the-sanh/admin/brand/{brand_id}/edit"
    benefit_edit_url = (
        f"https://{base}/the-sanh/admin/brand-privileges/{benefit_id}/edit"
        if benefit_id else ""
    )
    if not benefit_id:
        print_warn("Could not resolve latest benefit ID; skipping privilege edit tab.")

    border_len = len(brand_url) + 30
    print(f"\n{Colors.GREEN}{Colors.BOLD}{'═' * (border_len + 4)}")
    print(f"  🎉 BRAND URL CREATED: {brand_url}")
    print("═" * (border_len + 4) + f"{Colors.END}\n")

    copy_to_clipboard(brand_url)
    tab_thread = threading.Thread(
        target=open_in_chrome,
        args=_brand_review_tabs(brand_edit_url, homepage_url, social_review_urls, benefit_edit_url, brand_url),
        daemon=True,
    )
    tab_thread.start()

    # ── 13. Update brand link to Base.vn Workflow ────────────────────────────
    base_job_id = job_info.get("job_id") if job_info else None
    base_job_token = job_info.get("job_token") if job_info else None

    if not base_job_id:
        print_info("💡 No Base.vn job was automatically linked to this brand.")
        manual_id = input(f"  {Colors.BOLD}Enter Base.vn Job ID / URL to update brand link (or Enter to skip): {Colors.END}").strip()
        if manual_id:
            m_id = re.search(r'workflow\.base\.vn/job/(\d+)', manual_id)
            base_job_id = m_id.group(1) if m_id else manual_id

    if base_job_id:
        print_step(f"📤 [Step 13] Updating brand link to Base.vn Workflow (Job ID: {base_job_id})...")
        base_cookies, base_data = load_base_auth()
        if not base_job_token:
            f_status, f_job = fetch_base_job(base_job_id, base_cookies, base_data)
            if f_status == "OK" and f_job:
                base_job_token = f_job.get("token", "")

        next_status, next_msg = api_base_job_next(
            job_id=base_job_id,
            job_token=base_job_token or "",
            brand_url=brand_url,
            cookies=base_cookies,
            data=base_data,
        )
        if next_status == "INVALID_SESSION":
            base_cookies, base_data = prompt_update_base_auth()
            next_status, next_msg = api_base_job_next(
                job_id=base_job_id,
                job_token=base_job_token or "",
                brand_url=brand_url,
                cookies=base_cookies,
                data=base_data,
            )

        if next_status == "OK":
            print_success(f"Successfully updated brand link on Base.vn job {base_job_id} and moved to next stage! ({brand_url})")
        else:
            print_warn(f"Base.vn job {base_job_id} update notice: {next_msg}")

    tab_thread.join()

# ---------------------------------------------------------------------------
# Entry point
# ---------------------------------------------------------------------------

def main() -> int:
    env_key, base = prompt_env()
    token = prompt_token(env_key)
    
    # Validate token before proceeding
    print_step("🔐 Validating token...")
    if not validate_token(base, token):
        print_fail("Token is invalid or expired. Please provide a valid token.")
        token = prompt_token(env_key, force_new=True)
        print_step("🔐 Re-validating token...")
        if not validate_token(base, token):
            print_fail("Token is still invalid. Exiting.")
            return 1
    print_success("Token is valid!")
    
    print_header(f"🌐 Environment: {Colors.BOLD}{env_key.upper()}{Colors.END} | Base URL: {Colors.CYAN}https://{base}/{Colors.END}")

    city_data = load_json("city.txt")
    cat_data  = load_json("category.txt")
    ben_data  = load_json("benefit.txt")

    while True:
        try:
            process_brand(base, token, city_data, cat_data, ben_data)
        except requests.HTTPError as exc:
            print_fail(f"ERROR: {exc}")
            if exc.response is not None and exc.response.status_code == 401:
                print_info("Token is unauthorized or expired. Please enter a new token.")
                token = prompt_token(env_key, force_new=True)
        except KeyboardInterrupt:
            # Reset terminal: clear any dangling ANSI codes, move to a fresh line,
            # then flush so the shell prompt always appears on a clean new line.
            sys.stdout.write(f"\n{Colors.END}")
            sys.stdout.flush()
            print(f"{Colors.YELLOW}{Colors.BOLD}👋 Exiting brand creation workflow. Goodbye!{Colors.END}")
            sys.stdout.flush()
            return 0
        except Exception as exc:
            print_fail(f"ERROR: {exc}")


if __name__ == "__main__":
    try:
        sys.exit(main())
    except KeyboardInterrupt:
        # Ctrl+C during initial prompts (env / token) before the while-loop.
        sys.stdout.write(f"\n{Colors.END}")
        sys.stdout.flush()
        print(f"{Colors.YELLOW}{Colors.BOLD}👋 Exiting brand creation workflow. Goodbye!{Colors.END}")
        sys.stdout.flush()
        sys.exit(0)
