STATUS_MAP = {
    "NEW": "NEW",
    "CONTACTED": "CONTACTED",
    "SCHEDULED": "SCHEDULED",
    "READY FOR WORK": "READY FOR WORK",
    "NEW": "NEW",
    "CONTACTED": "CONTACTED",
    "SCHEDULED": "SCHEDULED",
    "READY FOR WORK": "READY FOR WORK",
}

import os, re, json, time, zipfile, sqlite3, hashlib, hmac
import html
from datetime import datetime, date, timedelta, time as dtime
from urllib.parse import quote

import streamlit as st
import streamlit.components.v1 as components
from pypdf import PdfReader


def _extract_customer_phone_from_bottom(lines):
    """Return the customer phone from the very bottom of the PDF.
    Demo PDFs include the real customer phone as a standalone line at the end:
      Demo1: +372 51231232
      Demo2: +372 5111111
    We explicitly avoid:
      - Name: ... Phone: (+372) 666 6666 (shop invoice header)
      - Telephone: +37212345678 (document author footer)
    """
    def norm(p: str) -> str:
        p = (p or "").strip()
        p = re.sub(r"[ \t]+", " ", p).strip()
        p2 = re.sub(r"[^\d\+]+", "", p)
        if p2.startswith("00"):
            p2 = "+" + p2[2:]
        if len(re.sub(r"\D", "", p2)) < 7:
            return ""
        return p2

    # Look for the last standalone phone line
    standalone = []
    for i, raw in enumerate(lines):
        s = (raw or "").strip()
        if not s or s == "__PAGE_BREAK__":
            continue
        # standalone phone (allow spaces)
        if re.fullmatch(r"\+\d[\d\s]{6,}\d", s):
            standalone.append((i, norm(s)))

    if standalone:
        # Prefer the last one in the doc
        return standalone[-1][1] or ""

    # Fallback: any phone-like string in the last ~25 lines, excluding footer labels
    phone_re = re.compile(r"(\+\d[\d\s\-\(\)]{6,}\d)")
    tail = lines[max(0, len(lines) - 25):]
    for raw in reversed(tail):
        s = (raw or "").strip()
        low = s.lower()
        if not s:
            continue
        if "telephone:" in low or "document created" in low or "e-mail" in low:
            continue
        m = phone_re.search(s)
        if m:
            ph = norm(m.group(1))
            if ph:
                return ph
    return ""



def _extract_best_phone_v2(lines):
    """Pick the customer's phone (demo-first).
    - Prefer a standalone phone-like line near the END of the document.
    - Skip invoice/header 'Name: ... Phone ...' and footer 'Telephone:' under 'Document created by'.
    """
    def norm(p: str) -> str:
        p = (p or "").strip()
        p = re.sub(r"[ \t]+", " ", p).strip()
        p2 = re.sub(r"[^\d\+]+", "", p)
        if p2.startswith("00"):
            p2 = "+" + p2[2:]
        if len(re.sub(r"\D", "", p2)) < 5:
            return ""
        return p2

    standalone = re.compile(r"^\+?\d[\d\s\-]{5,}\d$")
    any_phone = re.compile(r"(\+?\d[\d\s\-\(\)]{5,}\d)")

    for raw in reversed(lines or []):
        s = (raw or "").strip()
        if not s or s == "__PAGE_BREAK__":
            continue
        low = s.lower()
        if "document created" in low or "telephone:" in low or "e-mail" in low:
            continue
        if "name:" in low and ("telefon" in low or "phone" in low):
            continue
        if standalone.fullmatch(s):
            ph = norm(s)
            if ph:
                return ph

    for raw in reversed(lines or []):
        s = (raw or "").strip()
        if not s or s == "__PAGE_BREAK__":
            continue
        low = s.lower()
        if "document created" in low or "telephone:" in low or "e-mail" in low:
            continue
        if "name:" in low and ("telefon" in low or "phone" in low):
            continue
        m = any_phone.search(s)
        if m:
            ph = norm(m.group(1))
            if ph:
                return ph
    return ""


def _parse_detached_items_block_v2(lines):
    """Parse Demo-2 detached items block at bottom.
    Accepts header lines:
      - '2    635567'
      - '3 958612'
      - '7600674'  (means item 4, code 760067)
    """
    if not lines:
        return []

    def parse_hdr(s: str):
        s = (s or "").strip()
        m = re.match(r"^(\d+)\s+(\d{5,})$", s)
        if m:
            return m.group(1), m.group(2)
        m = re.match(r"^(\d{5,})(\d)$", s)
        if m and m.group(2) != "0":
            return m.group(2), m.group(1)
        return None

    start = None
    hdrs = []
    for i in range(len(lines)):
        p = parse_hdr(lines[i])
        if not p:
            continue
        tmp=[]
        j=i
        while j < len(lines):
            pj=parse_hdr(lines[j])
            if not pj:
                break
            tmp.append(pj)
            j+=1
        if len(tmp) >= 2:
            start=i
            hdrs=tmp
            break
    if start is None:
        return []

    n=len(hdrs)
    idx=start+n

    # descriptions
    desc=[]
    while idx < len(lines) and len(desc)<n:
        s=(lines[idx] or "").strip()
        idx+=1
        if not s or s=="__PAGE_BREAK__":
            continue
        if s.lower().startswith("document created"):
            return []
        desc.append(s)

    # qty
    qty=[]
    while idx < len(lines) and len(qty)<n:
        s=(lines[idx] or "").strip()
        idx+=1
        if not s or s=="__PAGE_BREAK__":
            continue
        if re.fullmatch(r"\d+", s):
            qty.append(s)

    # warehouse
    wh=[]
    while idx < len(lines) and len(wh)<n:
        s=(lines[idx] or "").strip()
        idx+=1
        if not s or s=="__PAGE_BREAK__":
            continue
        if re.fullmatch(r"[A-Za-z]{3,}", s):
            wh.append(s.title())

    if len(desc)!=n or len(qty)!=n or len(wh)!=n:
        return []

    items=[]
    for k in range(n):
        nr,_code=hdrs[k]
        items.append({"nr": nr, "art": desc[k].strip(), "qty": qty[k].strip(), "wh": wh[k].strip()})
    return items

def fmt_date(d):
    """Format YYYY-MM-DD -> DD.MM.YYYY (or passthrough)."""
    try:
        if hasattr(d, 'strftime'):
            return d.strftime('%d.%m.%Y')
        s = str(d)
        if re.match(r'^\d{4}-\d{2}-\d{2}$', s):
            y, m, dd = s.split('-')
            return f"{dd}.{m}.{y}"
        return s
    except Exception:
        return str(d)

APP_VERSION = "v14-maps-fix"
def _fmt_hhmm(ts: str) -> str:
    try:
        s = (ts or '').strip()
        if not s:
            return ''
        t = s.split('T')[-1]
        return t[:5]
    except Exception:
        return ''



# MUST be first Streamlit call
st.set_page_config(page_title="Logistics automation", layout="wide", page_icon="🚚")
st.markdown('''
<style>
/* Worker detail: keep things compact */
.km-worker-section h3 { margin-bottom: 0.25rem; }
</style>
''', unsafe_allow_html=True)
st.markdown('''
<style>
/* FIX: LADU font ühtlustamine, ilma NR/KOGUS/ARTIKKEL rikkumata */
.km-item-wh,
.km-item-wh span,
.km-item-wh div {
    font-family: system-ui, -apple-system, BlinkMacSystemFont, "Segoe UI", sans-serif !important;
    font-weight: 400 !important;
}
</style>
''', unsafe_allow_html=True)
st.markdown('''
<style>
/* LADU font ühtlustamine (viimane lihv) */
.km-item-wh,
.km-item-wh *,
.km-item-warehouse,
.km-item-warehouse * {
  font-size: 0.75rem !important;
  font-family: system-ui, -apple-system, BlinkMacSystemFont, "Segoe UI", sans-serif !important;
  font-weight: 400 !important;
  line-height: 1.35 !important;
}
</style>
''', unsafe_allow_html=True)

st.markdown('''
<style>
/* Neutralize red hover on buttons/links */
button:hover { filter: brightness(0.98); }
div.stButton > button:hover { border-color: rgba(0,0,0,0.15) !important; }
a:hover { color: inherit !important; }
summary:hover { background: rgba(0,0,0,0.03) !important; }
div[data-testid="stDownloadButton"] button:hover { border-color: rgba(0,0,0,0.15) !important; filter: brightness(0.98); }
div[data-testid="stExpander"] summary:hover { color: inherit !important; }
</style>
''', unsafe_allow_html=True)


APP_DIR = os.path.abspath(os.path.dirname(__file__))
DATA_DIR = os.path.join(APP_DIR, "Logistic")
DB_PATH = os.path.join(DATA_DIR, "data", "db.sqlite")
ORDERS_DIR = os.path.join(DATA_DIR, "orders")
EXPORTS_DIR = os.path.join(DATA_DIR, "exports")


def ensure_dirs():
    os.makedirs(os.path.join(DATA_DIR, "data"), exist_ok=True)
    os.makedirs(ORDERS_DIR, exist_ok=True)
    os.makedirs(EXPORTS_DIR, exist_ok=True)


def db():
    """DB connection helper (cached).

    Streamlit reruns the script often. Creating many SQLite connections (and running PRAGMAs
    like journal_mode on every call) is a common cause of 'database is locked' on Windows.

    We keep a single connection in st.session_state:
      - isolation_level=None (autocommit) to avoid accidentally holding write locks
      - busy_timeout is modest so the UI doesn't feel stuck
    """
    ensure_dirs()
    if "_db_conn" in st.session_state:
        try:
            st.session_state._db_conn.execute("SELECT 1;")
            return st.session_state._db_conn
        except Exception:
            try:
                st.session_state._db_conn.close()
            except Exception:
                pass
            st.session_state.pop("_db_conn", None)

    conn = sqlite3.connect(DB_PATH, check_same_thread=False, timeout=1.0, isolation_level=None)
    conn.row_factory = sqlite3.Row
    try:
        conn.execute("PRAGMA foreign_keys=OFF;")
        conn.execute("PRAGMA busy_timeout=1200;")
    except Exception:
        pass
    st.session_state._db_conn = conn
    return conn



# -------------------------
# UI styles
# -------------------------
def inject_styles():
    st.markdown(
        """
<style>
.km-header {
  background: #111827;
  border: 1px solid rgba(255,255,255,0.08);
  border-radius: 14px;
  padding: 14px 16px;
  display: flex;
  gap: 14px;
  align-items: center;
  margin-bottom: 14px;
}
.km-logo {
  width: 64px;
  height: 64px;
  object-fit: contain;
  border-radius: 10px;
  background: rgba(255,255,255,0.04);
  padding: 6px;
}
.km-title {
  color: #fff;
  font-size: 26px;
  font-weight: 800;
  line-height: 1.1;
  margin: 0;
}
.km-sub {
  color: rgba(255,255,255,0.75);
  margin: 2px 0 0 0;
  font-size: 14px;
}

/* Pointer cursor fix for selectbox/multiselect (BaseWeb) */
div[data-baseweb="select"] { cursor: pointer !important; }
div[data-baseweb="select"] * { cursor: pointer !important; }
div[data-baseweb="select"] input { caret-color: transparent !important; }
div[data-baseweb="select"] input::selection { background: transparent !important; }

/* pre-wrap helper */
.km-pre {
  white-space: pre-wrap;
  font-family: ui-monospace, SFMono-Regular, Menlo, Monaco, Consolas, "Liberation Mono", "Courier New", monospace;
  font-size: 0.92rem;
  line-height: 1.35;
}

@media (max-width: 700px) {
  .km-logo { width: 42px; height: 42px; border-radius: 10px; }
  .km-title { font-size: 20px; }
  .km-sub { font-size: 12px; }
}

/* Item list "boxes" (build items-boxes-v2) */
.km-items { margin-top: 8px; }
.km-items-meta { display:flex; gap:8px; align-items:center; margin: 6px 0 10px 0; flex-wrap:wrap; }
.km-badge{
  display:inline-flex; align-items:center; justify-content:center;
  padding:6px 10px; border-radius:999px;
  font-weight:800; font-size:12px;
  background: rgba(17,24,39,0.08);
}
.km-item-row{
  display:grid;
  grid-template-columns: 66px 1fr 96px 170px;
  gap:10px;
  padding:12px 12px;
  border:1px solid rgba(17,24,39,0.10);
  border-radius:14px;
  background: rgba(255,255,255,0.72);
  box-shadow: 0 1px 2px rgba(0,0,0,0.04);
  margin-bottom:10px;
}
.km-item-h{
  display:grid;
  grid-template-columns: 66px 1fr 96px 170px;
  gap:10px;
  padding:4px 12px;
  margin-bottom:6px;
  color:#6b7280;
  font-size:12px !important;
  font-weight:800;
  text-transform:uppercase;
  letter-spacing:0.05em;
}
.km-pill{
  display:inline-flex;
  align-items:center;
  justify-content:center;
  padding:6px 10px;
  border-radius:999px;
  font-weight:900;
  background: rgba(17,24,39,0.06);

  font-size:12px !important;}
.km-item-art{ font-weight:650; color:#111827; line-height:1.25; 
  font-size:12px !important;}
.km-item-qty-pill{
  display:inline-flex; align-items:center; justify-content:center;
  padding:6px 10px; border-radius:999px;
  font-weight:900;
  background: rgba(17,24,39,0.10);

  font-size:12px !important;}
.km-item-wh{ color:#111827; 
  font-size:12px !important;}
@media (max-width: 700px){
  .km-item-row, .km-item-h{
    grid-template-columns: 54px 1fr 96px;
  }
  .km-item-wh{ display:none; }
}

</style>
        """,
        unsafe_allow_html=True,
    )


def render_header():
    inject_styles()
    st.markdown(
        '''
        <div style="
            width: 100%;
            background: rgba(17,24,39,0.06);
            border: 1px solid rgba(17,24,39,0.10);
            border-radius: 16px;
            padding: 18px 16px;
            margin-bottom: 14px;
            text-align: center;
        ">
          <div style="font-size: 44px; font-weight: 900; letter-spacing: 0.2px;">
            Logistics automation
          </div>
        </div>
        ''',
        unsafe_allow_html=True,
    )


def _pbkdf2_hash_password(password: str, iterations: int = 200_000) -> str:
    password = (password or "").encode("utf-8")
    salt = os.urandom(16)
    dk = hashlib.pbkdf2_hmac("sha256", password, salt, iterations)
    return f"pbkdf2_sha256${iterations}${salt.hex()}${dk.hex()}"


def _pbkdf2_verify_password(password: str, stored: str) -> bool:
    try:
        algo, iters, salt_hex, hash_hex = stored.split("$", 3)
        if algo != "pbkdf2_sha256":
            return False
        iterations = int(iters)
        salt = bytes.fromhex(salt_hex)
        expected = bytes.fromhex(hash_hex)
        dk = hashlib.pbkdf2_hmac("sha256", (password or "").encode("utf-8"), salt, iterations)
        return hmac.compare_digest(dk, expected)
    except Exception:
        return False


def _new_token() -> str:
    return os.urandom(24).hex()


# -------------------------
# DB schema
# -------------------------
def init_db():
    """Initialize / migrate DB schema.

    Team-based schema has been removed. Route items are assigned directly to workers via
    route_item_users (many-to-many). The route_items table no longer stores team_id.

    Migration:
      - If old route_items contains team_id, we rename it to route_items_legacy and recreate
        a new route_items table without team_id, preserving ids so route_item_users stays valid.
    """
    conn = db()

    # One-time DB-level pragmas (don't run these on every connection)
    try:
        conn.execute("PRAGMA journal_mode=WAL;")
        conn.execute("PRAGMA synchronous=NORMAL;")
    except Exception:
        pass
    cur = conn.cursor()

    # --- USERS (keep legacy team_id column if it exists in an old DB; new installs don't need it) ---
    cur.execute("""
    CREATE TABLE IF NOT EXISTS users (
        id INTEGER PRIMARY KEY AUTOINCREMENT,
        name TEXT NOT NULL,
        phone TEXT DEFAULT '',
        is_active INTEGER NOT NULL DEFAULT 1,
        created_at TEXT NOT NULL,
        password_hash TEXT DEFAULT '',
        auth_token TEXT DEFAULT ''
    )""")

    # --- ORDERS ---
    cur.execute("""
    CREATE TABLE IF NOT EXISTS orders (
        id INTEGER PRIMARY KEY AUTOINCREMENT,
        original_filename TEXT NOT NULL,
        stored_path TEXT NOT NULL,
        created_at TEXT NOT NULL,
        status TEXT NOT NULL DEFAULT 'NEW',

        client_name TEXT DEFAULT '',
        phone TEXT DEFAULT '',
        address TEXT DEFAULT '',
        delivery_date TEXT DEFAULT '',
        delivery_window TEXT DEFAULT '',
        notes TEXT DEFAULT '',

        order_ref TEXT DEFAULT '',
        recipient_name TEXT DEFAULT '',
        ship_address TEXT DEFAULT '',
        service_tag TEXT DEFAULT '',
        doc_author TEXT DEFAULT '',
        doc_email TEXT DEFAULT '',
        doc_phone TEXT DEFAULT '',
        items_compact TEXT DEFAULT ''
    )""")

    # --- ROUTES ---
    cur.execute("""
    CREATE TABLE IF NOT EXISTS routes (
        id INTEGER PRIMARY KEY AUTOINCREMENT,
        route_date TEXT NOT NULL
    )""")

    # --- ROUTE ITEMS (new schema, no team_id) ---
    cur.execute("""
    CREATE TABLE IF NOT EXISTS route_items (
        id INTEGER PRIMARY KEY AUTOINCREMENT,
        route_id INTEGER NOT NULL,
        order_id INTEGER NOT NULL,
        seq INTEGER NOT NULL,
        ring_no INTEGER NOT NULL DEFAULT 1,

        worker_status TEXT NOT NULL DEFAULT 'OPEN',
        worker_status_reason TEXT DEFAULT '',
        worker_status_note TEXT DEFAULT '',
        worker_status_updated_at TEXT DEFAULT '',
        worker_status_updated_by INTEGER,
        worker_started_at TEXT DEFAULT '',
        worker_finished_at TEXT DEFAULT '',

        FOREIGN KEY(route_id) REFERENCES routes(id),
        FOREIGN KEY(order_id) REFERENCES orders(id),
        FOREIGN KEY(worker_status_updated_by) REFERENCES users(id),

        UNIQUE(route_id, order_id),
        UNIQUE(route_id, seq)
    )""")

    # Worker assignment for route items (many-to-many)
    cur.execute("""CREATE TABLE IF NOT EXISTS route_item_users (
        ri_id INTEGER NOT NULL,
        user_id INTEGER NOT NULL,
        created_at TEXT,
        FOREIGN KEY(ri_id) REFERENCES route_items(id) ON DELETE CASCADE,
        FOREIGN KEY(user_id) REFERENCES users(id) ON DELETE CASCADE,
        UNIQUE(ri_id, user_id)
    )""")
    cur.execute("""CREATE INDEX IF NOT EXISTS idx_route_item_users_user ON route_item_users(user_id)""")
    cur.execute("""CREATE INDEX IF NOT EXISTS idx_route_item_users_ri ON route_item_users(ri_id)""")


    # Backward-compat: older DBs may miss created_at on route_item_users
    try:
        cur.execute("ALTER TABLE route_item_users ADD COLUMN created_at TEXT DEFAULT ''")
    except Exception:
        pass

    # simple key/value settings
    cur.execute("""
    CREATE TABLE IF NOT EXISTS settings (
        key TEXT PRIMARY KEY,
        value TEXT NOT NULL DEFAULT ''
    )""")

    def try_add_column(table, coldef):
        try:
            cur.execute(f"ALTER TABLE {table} ADD COLUMN {coldef}")
        except (sqlite3.OperationalError, sqlite3.IntegrityError):
            pass

    # Orders: tolerate legacy DBs
    for coldef in [
        "order_ref TEXT DEFAULT ''",
        "recipient_name TEXT DEFAULT ''",
        "ship_address TEXT DEFAULT ''",
        "service_tag TEXT DEFAULT ''",
        "doc_author TEXT DEFAULT ''",
        "doc_email TEXT DEFAULT ''",
        "doc_phone TEXT DEFAULT ''",
        "items_compact TEXT DEFAULT ''",
        "delivery_date TEXT DEFAULT ''",
        "delivery_window TEXT DEFAULT ''",
    ]:
        try_add_column("orders", coldef)

    # Users: tolerate legacy DBs
    for coldef in ["password_hash TEXT DEFAULT ''", "auth_token TEXT DEFAULT ''"]:
        try_add_column("users", coldef)

    # --- Migration: old route_items with team_id -> new route_items without team_id ---
    try:
        cur.execute("PRAGMA table_info(route_items)")
        cols = [r[1] for r in cur.fetchall()]
        if 'team_id' in cols:
            # rename old and recreate new
            cur.execute("ALTER TABLE route_items RENAME TO route_items_legacy")
            # recreate new route_items (same as above)
            cur.execute("""
            CREATE TABLE IF NOT EXISTS route_items (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                route_id INTEGER NOT NULL,
                order_id INTEGER NOT NULL,
                seq INTEGER NOT NULL,
                ring_no INTEGER NOT NULL DEFAULT 1,

                worker_status TEXT NOT NULL DEFAULT 'OPEN',
                worker_status_reason TEXT DEFAULT '',
                worker_status_note TEXT DEFAULT '',
                worker_status_updated_at TEXT DEFAULT '',
                worker_status_updated_by INTEGER,
                worker_started_at TEXT DEFAULT '',
                worker_finished_at TEXT DEFAULT '',

                FOREIGN KEY(route_id) REFERENCES routes(id),
                FOREIGN KEY(order_id) REFERENCES orders(id),
                FOREIGN KEY(worker_status_updated_by) REFERENCES users(id),

                UNIQUE(route_id, order_id),
                UNIQUE(route_id, seq)
            )""")
            # copy common columns (preserve ids)
            cur.execute("""
            INSERT INTO route_items (
                id, route_id, order_id, seq, ring_no,
                worker_status, worker_status_reason, worker_status_note,
                worker_status_updated_at, worker_status_updated_by,
                worker_started_at, worker_finished_at
            )
            SELECT
                id, route_id, order_id, seq,
                COALESCE(NULLIF(ring_no,0),1),
                COALESCE(NULLIF(worker_status,''),'OPEN'),
                COALESCE(worker_status_reason,''),
                COALESCE(worker_status_note,''),
                COALESCE(worker_status_updated_at,''),
                worker_status_updated_by,
                COALESCE(worker_started_at,''),
                COALESCE(worker_finished_at,'')
            FROM route_items_legacy
            """)
            # indexes
            cur.execute("CREATE UNIQUE INDEX IF NOT EXISTS idx_route_items_route_order ON route_items(route_id, order_id)")
    except Exception:
        # migration is best-effort; do not block app start
        pass

    conn.commit()



# -------------------------
# Helpers
# -------------------------

def get_setting(key: str, default: str = "") -> str:
    try:
        conn = db()
        cur = conn.cursor()
        cur.execute("SELECT value FROM settings WHERE key=?", (key,))
        row = cur.fetchone()
        return (row["value"] if row else default) or default
    except Exception:
        return default


def set_setting(key: str, value: str):
    try:
        conn = db()
        cur = conn.cursor()
        cur.execute(
            "INSERT INTO settings (key, value) VALUES (?, ?) "
            "ON CONFLICT(key) DO UPDATE SET value=excluded.value",
            ((key or "").strip(), (value or "").strip()),
        )
        conn.commit()
    except Exception:
        pass

def safe_filename(name: str) -> str:
    name = (name or "").strip()
    name = re.sub(r"[^\w\-. ]+", "_", name, flags=re.UNICODE)
    name = re.sub(r"\s+", " ", name)
    return name[:160] if name else f"file_{int(time.time())}"


def extract_pdf_text(path: str) -> str:
    reader = PdfReader(path)
    parts = []
    for page in reader.pages:
        parts.append(page.extract_text() or "")
        parts.append("\n__PAGE_BREAK__\n")
    return "\n".join(parts)


def _clean(s: str) -> str:
    return re.sub(r"[ \t]+", " ", (s or "")).strip()


def _compact_upper(s: str) -> str:
    return re.sub(r"\s+", "", (s or "")).upper()


def _is_table_header(line: str) -> bool:
    u = _compact_upper(line)
    if not u:
        return False
    need = ["NR", "NO", "KOOD", "CODE", "ARTIKKEL", "DESCRIPTION", "KOGUS", "QUANTITY", "LADU", "LOCATION"]
    return sum(1 for x in need if x in u) >= 4


def _looks_like_address_line(s: str) -> bool:
    s = (s or '').strip()
    if not s:
        return False
    u = s.upper()
    if any(x in u for x in [" TN", " TEE", " MNT", " PST", " PUIEST", " TÄNAV", " MAANTEE", " PST."]):
        return True
    if re.search(r"\d", s) and len(s) <= 64:
        return True
    if u in ["TALLINN", "TARTU", "PÄRNU", "VIIMSI", "NARVA", "RAKVERE", "HAAPSALU", "KURESSAARE"]:
        return True
    return False


def _looks_like_note_start(s: str) -> bool:
    s = (s or '').strip()
    if not s:
        return False
    u = s.upper()
    if re.match(r"^[a-zõäöü]", s):
        return True
    if any(k in u for k in ["SOOVIB", "PALUN", "VÕTTA", "VOTTA", "SOBIB", "TÄNA", "HOMME", "JÄRGM", "JÄRGMI", "RAINIST"]):
        return True
    if "." in s and len(s.split()) >= 2:
        return True
    return False


def _extract_ship_address_lines(lines):
    """Extract ship/address block robustly (ET + EN).

    Preference:
      1) Lähetusaadress: (ET ship-to)
      2) Address/Address closest to Receiver/Recipient (ship-to)
      3) Any Address/Address with plausible street+number
    """
    ship = []

    def _stop_line(x: str) -> bool:
        x = (x or "").strip()
        if not x:
            return False
        ux = x.upper()
        if _is_table_header(x):
            return True
        if ux.startswith("NR ") or ux.startswith("NO ") or ux.startswith("CODE ") or ux.startswith("DESCRIPTION "):
            return True
        if x.startswith("Dokumendi koostas:") or re.match(r"^Document\s+created\s+by\s*:", x, flags=re.I):
            return True
        if re.match(r"^(Recipient|Receiver)\s*:", x, flags=re.I):
            return True
        if re.match(r"^(Phone|Phone|Telephone|E-mail|Email)\s*:?", x, flags=re.I):
            return True
        if re.match(r"^Order\s+nr\.", x, flags=re.I):
            return True
        if ux.startswith("SIGNATURE") or ux.startswith("BALANCE") or ux.startswith("DEMO TERMS") or ux.startswith("GOODS RECEIVED"):
            return True
        return False

    # 1) Preferred ET label
    start = None
    label = None
    for i, l in enumerate(lines):
        if "Lähetusaadress:" in (l or ""):
            start = i
            label = "Lähetusaadress:"
            break

    # Find Receiver/Recipient anchor (ship-to section)
    anchor = None
    for i, l in enumerate(lines):
        s = (l or "").strip()
        if re.match(r"^(Receiver|Recipient)\s*:", s, flags=re.I):
            anchor = i
            break

    # 2) Address/Address candidates scored by closeness to anchor and plausibility
    if start is None:
        cands = []
        for i, l in enumerate(lines):
            s = (l or "").strip()
            if not s:
                continue
            if re.match(r"^(Address|Address)\s*:?", s, flags=re.I):
                after = s.split(":", 1)[-1].strip() if ":" in s else re.sub(r"^(Address|Address)\b", "", s, flags=re.I).lstrip(":").strip()
                score = 0.0
                if after and _looks_like_address_line(after):
                    score += 6.0
                # peek next non-empty line for street/city
                j = i + 1
                nxt = ""
                while j < len(lines):
                    t = (lines[j] or "").strip()
                    if t and t != "__PAGE_BREAK__":
                        nxt = t
                        break
                    j += 1
                if nxt and _looks_like_address_line(nxt):
                    score += 3.0
                if anchor is not None:
                    score -= min(abs(i - anchor), 200) / 10.0
                    if 0 <= i - anchor <= 6:
                        score += 5.0  # very likely ship-to
                cands.append((score, i))
        if cands:
            cands.sort(key=lambda x: x[0], reverse=True)
            start = cands[0][1]
            label = "Address:"

    if start is None:
        return ""

    first = (lines[start] or "")
    if ":" in first:
        after = first.split(":", 1)[-1].strip()
    else:
        after = re.sub(r"^(Address|Address|Lähetusaadress)\b", "", first, flags=re.I).lstrip(":").strip()

    if after:
        ship.append(_clean(after))

    j = start + 1
    while j < len(lines):
        l = (lines[j] or "").strip()
        if not l:
            j += 1
            continue
        if l == "__PAGE_BREAK__":
            j += 1
            continue
        if _stop_line(l):
            break
        # keep only address-like lines (prevents swallowing other sections)
        if ship and not _looks_like_address_line(l):
            break
        ship.append(_clean(l))
        if len(ship) >= 3:
            break
        j += 1

    ship = [x for x in ship if x]
    return "\n".join(ship).strip()




def _extract_notes_after_ship(lines):
    """Notes under ship address until table header; supports notes in CAPS without blank line."""
    start = None
    for i, l in enumerate(lines):
        if "Lähetusaadress:" in (l or ""):
            start = i
            break
    if start is None:
        return ""

    j = start + 1
    while j < len(lines):
        l = (lines[j] or "").strip()
        if not l:
            j += 1
            continue
        if _is_table_header(l) or l.startswith("Dokumendi koostas:"):
            return ""
        if l.startswith("Recipient:") or l.startswith("Order nr.") or l.startswith("Phone:") or l.startswith("E-mail:"):
            return ""
        if _looks_like_note_start(l):
            break
        if _looks_like_address_line(l):
            j += 1
            continue
        break

    notes = []
    while j < len(lines):
        l = (lines[j] or "").strip()
        if not l:
            j += 1
            continue
        if _is_table_header(l) or l.startswith("Dokumendi koostas:"):
            break
        if l.startswith("Recipient:") or l.startswith("Order nr."):
            j += 1
            continue
        notes.append(_clean(l))
        j += 1

    out = "\n".join(notes).strip()
    if len(out) > 900:
        out = out[:900].rstrip() + "…"
    return out


def _normalize_phone(p: str) -> str:
    p = (p or "").strip()
    p = re.sub(r"[ \t]+", " ", p).strip()
    p2 = re.sub(r"[^\d\+]+", "", p)
    if p2.startswith("00"):
        p2 = "+" + p2[2:]
    if len(re.sub(r"\D", "", p2)) < 5:
        return ""
    return p2


def _extract_client_phone(lines):
    """
    Demo-first phone extractor.

    Priority:
      1) Label lines starting with Phone/Phone/Telephone.
      2) Standalone phone number lines (e.g. "+372 5111111"), except store-hours footer.
      3) Phone embedded on Name line as fallback.

    Avoid:
      - Document created by / author block
      - Store-hours footer phone (right after "Open M-F ...")
    """
    phone_re = re.compile(
        r"(?:^|\b)(?:Phone|Phone|Telephone|Tel\.?|Mobiil)\b\s*:?s*([\(+\d][\d\s\-\(\)\+]{4,})",
        re.IGNORECASE,
    )
    standalone_re = re.compile(r"^\s*[\+]?\d[\d\s\-\(\)]{6,}\s*$")

    def is_doc_author_line(s: str) -> bool:
        u = (s or "").strip().lower()
        return (
            u.startswith("dokumendi koostas:")
            or ("document" in u and "created" in u)
            or u.startswith("document created")
            or u.startswith("e-mail:")
            or u.startswith("signature")
        )

    candidates = []
    n = len(lines)

    for i, l in enumerate(lines):
        s = (l or "").strip()
        if not s or s == "__PAGE_BREAK__":
            continue

        prev = (lines[i-1] or "").strip() if i > 0 else ""
        prev2 = (lines[i-2] or "").strip() if i > 1 else ""
        prev_u = (prev + " " + prev2).lower()

        if is_doc_author_line(s):
            continue

        score = 0.0
        ph = ""

        m = phone_re.search(s)
        if m:
            ph = _normalize_phone(m.group(1))
            if ph:
                if re.match(r"^(?:Phone|Phone|Telephone|Tel\.?|Mobiil)\b", s, flags=re.I):
                    score += 10.0
                if re.search(r"\bName\s*:\s*", s, flags=re.I):
                    score -= 2.0
        else:
            if standalone_re.match(s):
                ph = _normalize_phone(s)
                if ph:
                    score += 8.0

        if not ph:
            continue

        if ("open m-f" in prev_u) or ("open" in prev_u and "m-f" in prev_u):
            score -= 6.0

        score += (i / max(n, 1)) * 2.0
        candidates.append((score, ph))

    if not candidates:
        return ""
    candidates.sort(key=lambda x: x[0], reverse=True)
    return candidates[0][1]


def _parse_time_window_start(window: str):
    w = (window or "").strip().replace("–", "-")
    if not w:
        return None
    m = re.match(r"^(\d{1,2}):(\d{2})", w)
    if not m:
        return None
    hh, mm = int(m.group(1)), int(m.group(2))
    if 0 <= hh <= 23 and 0 <= mm <= 59:
        return dtime(hh, mm)
    return None


def _map_link(address: str) -> str:
    return f"https://www.google.com/maps/search/?api=1&query={quote((address or '').strip())}"



def _service_icons(service_tag: str) -> str:
    """Return emoji string for service tag like 'Transport', 'Transport + Paigaldus', etc."""
    s = (service_tag or '').lower()
    icons = []
    if (not s) or ('transport' in s):
        icons.append('🚚')
    if 'paigaldus' in s or 'montaa' in s or 'monteer' in s:
        icons.append('🛠️')
    if 'utiil' in s or 'utiliseer' in s:
        icons.append('♻️')
    seen=set(); out=[]
    for ic in icons:
        if ic not in seen:
            out.append(ic); seen.add(ic)
    return ' '.join(out)

def _call_link(phone: str) -> str:
    p = re.sub(r"[^\d\+]+", "", (phone or "").strip())
    return f"tel:{p}" if p else ""


def service_icons_for(row) -> str:
    """Compatibility helper (Jobs tab)."""
    try:
        svc = row['service']
    except Exception:
        try:
            svc = row.get('service')
        except Exception:
            svc = ''
    return _service_icons(svc)


def _maps_dir_link(stops: list[str], start_point: str, return_to_start: bool = False) -> str:
    """Google Maps Directions URL in the same order, showing the route line immediately.
    Uses the 'api=1' directions endpoint and adds dir_action=navigate.
    """
    sp = (start_point or "").strip() or "Liivalao 11, Tallinn"
    pts = [s.strip() for s in (stops or []) if (s or "").strip() and (s or "").strip() != "—"]

    if not pts:
        return ""

    origin = sp

    if return_to_start:
        # route: start -> stop1 -> stop2 -> ... -> stopN -> start
        destination = sp
        waypoints = pts
    else:
        # route: start -> stop1 -> ... -> stopN
        destination = pts[-1]
        waypoints = pts[:-1]

    # waypoint cap to keep URL usable
    if len(waypoints) > 20:
        waypoints = waypoints[:20]

    url = (
        f"https://www.google.com/maps/dir/?api=1"
        f"&origin={quote(origin)}"
        f"&destination={quote(destination)}"
        f"&travelmode=driving"
        f"&dir_action=navigate"
    )
    if waypoints:
        wp = "|".join([quote(x) for x in waypoints])
        url += f"&waypoints={wp}"
    return url




def _parse_items_compact(items_compact: str):
    """Parse items_compact (one item per line) into structured rows.

    Supported line formats (examples):
      "1 - KLAUS KASTIGA VOODI ... - 1 tk - Pealadu"
      "12 - TOODE ... - 2 tk"
    Parsing is done from the right, because article may contain " - ".
    Returns list of dicts: {nr:int, article:str, qty:str, warehouse:str}
    """
    out = []
    if not items_compact:
        return out

    for raw in (items_compact or "").splitlines():
        s = (raw or "").strip()
        if not s:
            continue

        # split by " - " but parse from right
        parts = [p.strip() for p in s.split(" - ") if p.strip()]
        if not parts:
            continue

        # nr is first token if numeric
        nr = None
        try:
            nr = int(re.sub(r"\D", "", parts[0]))
        except Exception:
            nr = None

        # defaults
        warehouse = ""
        qty = ""
        article = ""

        # Candidates from right
        if len(parts) >= 3:
            # likely: nr, article..., qty, warehouse?
            # decide if last looks like warehouse (non-qty)
            last = parts[-1]
            second_last = parts[-2]

            # qty heuristic: contains digit and (tk|pcs|pc) or is just digit
            def _looks_qty(x: str) -> bool:
                x = (x or "").lower().strip()
                return bool(re.search(r"\b\d+\b", x)) and ("tk" in x or "pcs" in x or "pc" in x or re.fullmatch(r"\d+", x))

            if _looks_qty(last):
                qty = last
                article_parts = parts[1:-1] if nr is not None else parts[:-1]
            else:
                warehouse = last
                qty = second_last if _looks_qty(second_last) else second_last
                article_parts = parts[1:-2] if nr is not None else parts[:-2]

            article = " - ".join(article_parts).strip()

        elif len(parts) == 2:
            # nr + article OR article + qty
            if nr is not None:
                article = parts[1]
            else:
                article = parts[0]
                qty = parts[1]
        else:
            article = parts[0] if nr is None else ""

        # Normalize
        article = re.sub(r"\s+", " ", (article or "")).strip()
        qty = re.sub(r"\s+", " ", (qty or "")).strip()
        warehouse = re.sub(r"\s+", " ", (warehouse or "")).strip()

        if nr is None:
            # fallback numbering
            nr = len(out) + 1

        out.append({"nr": nr, "article": article, "qty": qty, "warehouse": warehouse})

    return out


def parse_items_compact(items_compact: str):
    """Alias for backward compatibility."""
    return _parse_items_compact(items_compact)


def _render_items_boxes(items_compact: str, title: str = "📦 Items", show_title: bool = True):
    # Accept either compact string or already-parsed list of dicts
    if isinstance(items_compact, list):
        rows = items_compact
    else:
        rows = _parse_items_compact(items_compact if isinstance(items_compact, str) else str(items_compact or ''))
    if not rows:
        st.warning("No items detected.")
        return

    if show_title:
        st.markdown(f"### {title}")
    st.markdown(
        f"""
<div class="km-items-meta">
  <span class="km-badge">Items: {len(rows)}</span>
</div>
<div class="km-items">
  <div class="km-item-h">
    <div>Nr</div><div>Item</div><div>Quantity</div><div>Warehouse</div>
  </div>
</div>
        """,
        unsafe_allow_html=True,
    )

    for r in rows:
        nr = str(r.get("nr") or "").strip() or "—"
        art = (r.get("article") or "").strip()
        qty = str(r.get("qty") or "").strip() or "—"
        wh = str(r.get("warehouse") or "").strip() or "—"

        st.markdown(
            f"""
<div class="km-item-row">
  <div><span class="km-pill">{html.escape(nr)}</span></div>
  <div class="km-item-art">{html.escape(art)}</div>
  <div><span class="km-item-qty-pill">{html.escape(qty)}</span></div>
  <div class="km-item-wh">{html.escape(wh)}</div>
</div>
            """,
            unsafe_allow_html=True,
        )

def _copy_button(text: str, label: str = "📋 Kopeeri"):
    html = f"""
    <div style="display:flex; gap:8px; align-items:center;">
      <input id="copyInput" style="flex:1; padding:8px; border:1px solid #ddd; border-radius:6px;" value="{text}" readonly />
      <button id="copyBtn" style="padding:8px 12px; border-radius:8px; border:1px solid #ddd; cursor:pointer;">{label}</button>
    </div>
    <script>
      const btn = document.getElementById("copyBtn");
      const inp = document.getElementById("copyInput");
      btn.addEventListener("click", async () => {{
        try {{ await navigator.clipboard.writeText(inp.value); btn.innerText="✅ Kopeeritud"; }}
        catch(e) {{ inp.select(); document.execCommand("copy"); btn.innerText="✅ Kopeeritud"; }}
        setTimeout(()=>btn.innerText="{label}", 1200);
      }});
    </script>
    """
    components.html(html, height=60)


def _render_items_pre(items_text: str):
    items_text = (items_text or "").strip()
    if not items_text:
        st.warning("No items detected.")
        return
    safe = (items_text.replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;"))
    st.markdown(f'<div class="km-pre">{safe}</div>', unsafe_allow_html=True)


# -------------------------
# Parser: Aatrium PDF
# Output line: "nr. description | qty | warehouse"
# - DO NOT show code
# - DO NOT show location
# -------------------------
def parse_aatrium_pdf_text(text: str) -> dict:
    # order ref
    m = re.search(r"Order nr\.\s*([0-9]+\/\d{2}\.\d{2}\.\d{4})", text)
    order_ref = m.group(1).strip() if m else ""

    lines = [l.rstrip() for l in (text or "").splitlines()]

    # recipient / client name (supports ET + EN + slight layout variations)
    recipient_name = ""
    for l in lines:
        s = (l or "").strip()
        if not s:
            continue

        # Common labels (exact starts)
        for lbl in ("Recipient:", "Receiver:", "Vastuvõtja:", "Recipient:", "Kaubasaaja:", "Customer:"):
            if s.lower().startswith(lbl.lower()):
                recipient_name = _clean(s.split(":", 1)[-1])
                break
        if recipient_name:
            break

        # Sometimes receiver is glued: "Receiver:John Demo"
        m = re.match(r"^(Receiver|Recipient)\s*:\s*(.+)$", s, flags=re.I)
        if m:
            recipient_name = _clean(m.group(2))
            break

        # Sometimes name line is like: "Name: John Demo Phone: (+372) ..."
        m = re.search(r"\bName\s*:\s*(.+)$", s, flags=re.I)
        if m:
            candidate = m.group(1)
            candidate = re.split(r"\b(?:Phone|Phone|Telephone|Tel\.?|Mobiil)\b\s*:?", candidate, flags=re.I)[0]
            candidate = _clean(candidate)
            if candidate and len(candidate) >= 2:
                recipient_name = candidate
                break

    # Clean recipient/client name: strip any trailing phone label/number
    if recipient_name:
        recipient_name = re.sub(r"\s*(?:Phone|Phone|Telephone|Tel\.?|Mobiil)\s*:?.*$", "", recipient_name, flags=re.I).strip()
        recipient_name = re.sub(r"\s*[\(\+]?\d[\d\s\-\(\)\+]{5,}\s*$", "", recipient_name).strip()

    ship_address = _extract_ship_address_lines(lines)
    pdf_notes = _extract_notes_after_ship(lines)

    # -------------------------
    # SERVICE TAG
    # -------------------------
    # NOTE: Service is decided later (after items are parsed) using only:
    #   - pdf_notes
    #   - items_compact
    # This avoids false positives from generic PDF disclaimer/footer text.
    service_tag = "Transport"

    # doc author/email/phone
    doc_author = ""
    doc_email = ""
    doc_phone = ""
    m = re.search(r"Dokumendi koostas:\s*(.+)", text)
    if m:
        doc_author = _clean(m.group(1))
    if not doc_author:
        m = re.search(r"Document\s+created\s+by\s*:\s*(.+)", text, flags=re.I)
        if m:
            doc_author = _clean(m.group(1))
    m = re.search(r"E-mail:\s*([^\s]+)", text)
    if m:
        doc_email = _clean(m.group(1))
    m = re.search(r"Dokumendi koostas:.*?\n.*?(?:Phone|Tel|Mobiil)\s*:?\s*([+\(\)\d][\d\s\(\)\+\-]+)", text, flags=re.S | re.I)
    if m:
        doc_phone = _clean(m.group(1))
    if not doc_phone:
        m = re.search(r"Document\s+created\s+by.*?\n.*?Telephone\s*:?\s*([+\(\)\d][\d\s\(\)\+\-]+)", text, flags=re.S | re.I)
        if m:
            doc_phone = _clean(m.group(1))

    # Prefer phone from the Shoporder customer line: 'Name: X Phone/Phone: (+372) ...'
    client_phone = _extract_customer_phone_from_bottom(lines)
    for _l in lines:
        _s = (_l or '').strip()
        if not _s:
            continue
        if re.search(r"\bName\s*:\s*", _s, flags=re.I):
            mph = re.search(r"\b(?:Phone|Phone|Telephone|Tel\.?|Mobiil)\b\s*:?\s*([\(+\d][\d\s\-\(\)\+]{4,})", _s, flags=re.I)
            if mph:
                client_phone = _normalize_phone(mph.group(1))
            break
    if not client_phone:
            client_phone = _extract_best_phone_v2(lines)

    # -------------------------
    # ITEMS
    # -------------------------
    def is_footer(s: str) -> bool:
        s = (s or "").strip()
        if not s:
            return False
        return (
            # ET footers
            s.startswith("Dokumendi koostas:")
            or s.startswith("Allkiri")
            or s.startswith("Jääb tasuda")
            or s.startswith("Kaup kuulub")
            or s.startswith("NB!")
            or s.startswith("Vastuvõtja")
            or s.startswith("KAUP KÄTTE SAADUD")
            or s.startswith("Kliendi nimi ja allkiri")
            or s.startswith("Pealadu:")
            or s.startswith("Kaupluse ladu:")

            # EN / mixed invoice footers
            or re.match(r"^Document\s+created\s+by\s*:", s, flags=re.I)
            or re.match(r"^Document\s+createdby\s*:", s, flags=re.I)
            or re.match(r"^E-?mail\s*:", s, flags=re.I)
            or re.match(r"^Telephone\s*:", s, flags=re.I)
            or re.match(r"^Signature\b", s, flags=re.I)
            or re.match(r"^Balance\s*:", s, flags=re.I)
            or re.match(r"^Demo\s+Terms", s, flags=re.I)
            or re.match(r"^The\s+goods\s+remain", s, flags=re.I)
            or re.match(r"^GOODS\s+RECEIVED", s, flags=re.I)
            or re.match(r"^Customer\s+Name\s+and\s+Signature", s, flags=re.I)
            or re.match(r"^(Main\s+store|Warehouse\s+store)\s*:", s, flags=re.I)
        )

    def is_noise_code_line(s: str) -> bool:
        # Aatrium "Koht laos" koodid jms – ära lase neil tooteid nihutada
        return bool(re.fullmatch(r"\d{6,}", (s or "").strip()))

    def is_location_only(s: str) -> bool:
        s = (s or "").strip()
        return bool(re.fullmatch(r"[A-Z0-9][A-Z0-9\-\._/]{2,}", s))

    def cleanup_text(s: str) -> str:
        s = _clean(s)
        s = re.sub(r"\b\d{8,}\b", " ", s)
        s = re.sub(r"\s+", " ", s).strip()
        return s

    wh_re = re.compile(r"\b(WARE|SHOP|PEALADU|KAUPLUSE\s+LADU|[A-ZÕÄÖÜa-zõäöü]+\s+LADU)\b", re.I)
    qty_re = re.compile(r"\b(\d+)\s*TK\b", re.I)

    def extract_qty_wh_from_line(line: str):
        """
        Tagastab (qty, wh, cut_text).

        Põhireegel:
        - qty võetakse AINULT veerust "Quantity", st vahetult enne veeru "Warehouse" tokenit
          VÕI eraldi jätkurealt stiilis: "1 Pealadu O-3-3".
        - Mitte kunagi ei tohi võtta '4TK' vms artikli kirjelduse seest koguseks.
        """
        s = (line or "").strip()
        if not s:
            return None, None, None

        # Fix: liimitud tokenid nagu '4TK1' -> '4TK 1'
        s = re.sub(r"(TK)(\d)", r"\1 \2", s, flags=re.I)

        mwh = wh_re.search(s)
        if not mwh:
            return None, None, None

        wh = _clean(mwh.group(1))
        if wh.upper() == "PEALADU":
            wh = "Pealadu"
        elif wh.upper() == "KAUPLUSE LADU":
            wh = "Kaupluse ladu"
        else:
            wh = wh[0].upper() + wh[1:] if wh else ""

        before = s[:mwh.start()].strip()

        # Võta qty ainult 'before' lõpust (st vahetult enne ladu).
        qty = None
        cut_before = before

        m_end = re.search(r"(\d+(?:[.,]\d+)?)\s*(?:TK|KPL|PCS|PC)?\s*$", before, flags=re.I)
        if m_end:
            qty = m_end.group(1)
            cut_before = before[:m_end.start()].strip()

        # Kui cut_before on tühi, siis see rida on sisuliselt 'qty + ladu (+ asukoht)'
        # ja ei tohi kirjeldust juurde lisada.
        if not cut_before:
            return qty, wh, None

        return qty, wh, cut_before

    def parse_start(line: str, expected_next: int | None):
        s = (line or "").strip()
        toks = s.split()
        if not toks:
            return None
        t0 = toks[0]

        # Handle merged "nr+code" like "16ERMA" where PDF lost the space.
        m_merged = re.match(r"^(\d{1,3})([A-ZÕÄÖÜ]{2,}[A-Z0-9ÕÄÖÜ]*)$", t0)
        if m_merged:
            nr = m_merged.group(1)
            # code belongs to the 'Kood' column; DO NOT inject into the article text.
            rest = toks[1:]
            qty, wh, cut = extract_qty_wh_from_line(" ".join(rest))
            art = cut if cut is not None else " ".join(rest)
            return {"nr": nr, "art": art, "qty": qty, "wh": wh}


        # merged nr+code like "1638600 ..." (expected_next helps)
        if t0.isdigit() and len(t0) >= 5 and expected_next is not None:
            en = str(expected_next)
            if t0.startswith(en) and len(t0) > len(en):
                nr = en
                rest = toks[1:]
                qty, wh, cut = extract_qty_wh_from_line(" ".join(rest))
                art = cut if cut is not None else " ".join(rest)
                return {"nr": nr, "art": art, "qty": qty, "wh": wh}

        if not t0.isdigit():
            return None

        # Välista jätkuread stiilis "05 ASPEN 09" (need EI ole päris tootenr).
        if len(t0) > 1 and t0.startswith("0") and expected_next is not None and t0 != str(expected_next):
            return None

        nr = t0
        if len(toks) < 2:
            return None
        t1 = toks[1]

        # prevent "1 Pealadu ..." being treated as item start
        if t1.lower() in ("pealadu", "ladu", "kaupluse") or t1.lower().endswith("ladu"):
            return None

        # skip code token if it looks like code (digits/uppercase)
        if re.fullmatch(r"[A-Z0-9]{3,}", t1):
            rest = toks[2:]
        else:
            rest = toks[1:]

        if not rest:
            return None

        qty, wh, cut = extract_qty_wh_from_line(" ".join(rest))
        art = cut if cut is not None else " ".join(rest)
        return {"nr": nr, "art": art, "qty": qty, "wh": wh}

    items = []
    in_table = False
    cur = None
    expected_next = None

    def flush():
        nonlocal cur
        if not cur:
            return
        art = " ".join([cleanup_text(x) for x in cur["art_lines"] if cleanup_text(x)]).strip()
        art = re.sub(r"\s+", " ", art).strip()
        # Kui "Koht laos" veeru number satub rea lõppu (nt ") 2"), ära näita seda artikli kirjelduse sees.
        art = re.sub(r"\)\s+\d{1,2}\s*$", ")", art)
        if art:
            items.append({
                "nr": cur["nr"],
                "art": art,
                "qty": cur.get("qty") or "?",
                "wh": cur.get("wh") or "",
            })
        cur = None

    i = 0
    while i < len(lines):
        s = (lines[i] or "").strip()
        if not s:
            i += 1
            continue
        if s == "__PAGE_BREAK__":
            i += 1
            continue

        if _is_table_header(s):
            # Tabeli header kordub igal lehel, aga numeratsioon jätkub.
            in_table = True
            flush()
            if expected_next is None:
                expected_next = 1
            i += 1
            continue
        if in_table and s.lower() == "laos":
            i += 1
            continue

        if in_table and is_footer(s):
            # Footer lõpetab selle lehe tabeli, aga järgmise lehe tabel jätkub sama numeratsiooniga.
            flush()
            in_table = False
            i += 1
            continue

        if not in_table:
            i += 1
            continue

        if s.upper() in ("ADDUCO", "UTIIL", "PAIGALDUS", "TRANSPORT") or s.upper().startswith("KOJUVEDU"):
            i += 1
            continue

        start = parse_start(s, expected_next)
        if start:
            flush()
            cur = {"nr": start["nr"], "art_lines": [start["art"]], "qty": start.get("qty") or "", "wh": start.get("wh") or ""}
            try:
                expected_next = int(cur["nr"]) + 1
            except Exception:
                expected_next = None
            i += 1
            continue

        if not cur:
            i += 1
            continue

        if is_noise_code_line(s) or is_location_only(s):
            i += 1
            continue

        if (not cur.get("wh")) or (not cur.get("qty")):
            qty, wh, cut = extract_qty_wh_from_line(s)
            if wh:
                if qty:
                    cur["qty"] = qty
                cur["wh"] = wh
                if cut:
                    cur["art_lines"].append(cut)
                i += 1
                continue

        cur["art_lines"].append(s)
        i += 1

    flush()


    def _parse_shoporder_detached_items(_lines, start_nr: int):
        """Parse continuation items block that sometimes appears after Terms/footer without table header.
        Expected structure (as seen in DEMO PDFs):
          - N lines of 'nr code' (or merged like '7600674' meaning '4 760067')
          - N description lines
          - N quantity lines (digits)
          - N warehouse/location lines (Ware/Shop/Warehouse/etc)
        Returns list of dicts like items list: {nr, art, qty, wh}
        """
        if not _lines:
            return []
        start_nr = int(start_nr or 1)

        # Find candidate start: a line that begins with the expected nr or contains it with a code.
        start_i = None
        for i, l in enumerate(_lines):
            s = (l or '').strip()
            if not s:
                continue
            # exact "2    635567"
            if re.match(rf"^{start_nr}\s+\d{{3,}}$", s):
                start_i = i
                break
            # merged "7600674" (code+nr) where expected nr at end
            if re.match(rf"^\d{{5,}}{start_nr}$", s):
                start_i = i
                break
        if start_i is None:
            return []

        # Collect nr+code lines
        pairs = []
        i = start_i
        expected = start_nr
        while i < len(_lines):
            s = (_lines[i] or '').strip()
            if not s:
                i += 1
                continue
            # Stop if we hit letters (descriptions start)
            if re.search(r"[A-Za-zÕÄÖÜõäöü]", s):
                break

            m = re.match(r"^(\d+)\s+(\d{3,})$", s)
            if m:
                nr = int(m.group(1))
                code = m.group(2)
                # keep only sequential-ish rows; but be tolerant
                pairs.append((nr, code))
                expected = nr + 1
                i += 1
                continue

            # merged like "7600674" => code 760067, nr 4 (expected)
            if re.match(r"^\d{6,}\d$", s) and s.endswith(str(expected)):
                nr = expected
                code = s[:-len(str(expected))]
                pairs.append((nr, code))
                expected = nr + 1
                i += 1
                continue

            # sometimes spacing lost: "7600674" without expected tracking; try split last digit if it makes sense
            if re.match(r"^\d{6,}\d$", s):
                nr_guess = int(s[-1])
                if nr_guess >= start_nr:
                    pairs.append((nr_guess, s[:-1]))
                    expected = nr_guess + 1
                    i += 1
                    continue

            # Unknown numeric-only line; skip it
            i += 1

        n = len(pairs)
        if n < 2:
            # If we didn't get enough structure, don't risk false positives
            return []

        # Collect N description lines
        desc = []
        while i < len(_lines) and len(desc) < n:
            s = (_lines[i] or '').strip()
            if not s:
                i += 1
                continue
            if re.fullmatch(r"\d+", s):
                break
            if re.search(r"[A-Za-zÕÄÖÜõäöü]", s):
                desc.append(_clean(s))
            i += 1

        if len(desc) < n:
            return []

        # Collect N qty lines (digits)
        qty = []
        while i < len(_lines) and len(qty) < n:
            s = (_lines[i] or '').strip()
            if not s:
                i += 1
                continue
            if re.fullmatch(r"\d+", s):
                qty.append(s)
            else:
                break
            i += 1

        if len(qty) < n:
            return []

        # Collect N warehouse/location lines
        wh = []
        while i < len(_lines) and len(wh) < n:
            s = (_lines[i] or '').strip()
            if not s:
                i += 1
                continue
            u = s.strip().lower()
            if u in ("ware", "warehouse", "shop", "store", "warehousestore", "shopstore") or u.endswith("ware") or u.endswith("shop"):
                # normalize: keep 'Ware'/'Shop'
                if "shop" in u:
                    wh.append("Shop")
                else:
                    wh.append("Ware")
            else:
                # If it's some other location token, still accept but keep cleaned
                if re.search(r"[A-Za-z]", s):
                    wh.append(_clean(s))
                else:
                    break
            i += 1

        if len(wh) < n:
            # still accept, but pad empties
            wh += [""] * (n - len(wh))

        out = []
        for k in range(n):
            nr, _code = pairs[k]
            out.append({
                "nr": str(nr),
                "art": desc[k],
                "qty": qty[k],
                "wh": wh[k] if k < len(wh) else "",
            })
        return out

    def nr_key(it):
        try:
            return int(re.sub(r"\D", "", it.get("nr") or ""))
        except Exception:
            return 999999
    items = sorted(items, key=nr_key)

    # Demo-2 detached items block (bottom of PDF)
    try:
        extra = _parse_detached_items_block_v2(lines)
        if extra:
            existing_nrs = set(str(it.get("nr")) for it in items)
            for it in extra:
                if str(it.get("nr")) not in existing_nrs:
                    items.append(it)
            items = sorted(items, key=nr_key)
    except Exception:
        pass


    # DEMO EN PDF: items may continue in a detached block (no table header) on next page.
    try:
        _max_nr = max(int(re.sub(r"\D", "", it.get("nr") or "0") or 0) for it in items) if items else 0
    except Exception:
        _max_nr = 0
    _extra = _parse_shoporder_detached_items(lines, start_nr=_max_nr + 1)
    if _extra:
        items.extend(_extra)
        items = sorted(items, key=nr_key)

    formatted = []
    for it in items:
        nr = it["nr"]
        art = it["art"]
        qty = (it.get("qty") or "?").strip()
        qty_disp = f"{qty} tk" if qty != "?" else "?"
        wh = (it.get("wh") or "").strip()
        if wh:
            formatted.append(f"{nr} - {art} - {qty_disp} - {wh}")
        else:
            formatted.append(f"{nr} - {art} - {qty_disp}")

    items_compact = "\n".join(formatted).strip()

    # Recompute service tag using only notes + items (avoid generic disclaimers)
    service_hint_text = (text.split("Dokumendi koostas:")[0] if "Dokumendi koostas:" in text else text)
    detect_text = ((pdf_notes or "") + "\n" + (items_compact or "") + "\n" + (service_hint_text or "")).upper()

    has_utiil = bool(re.search(r"\bUTIIL\b|\bUTILISEER", detect_text))
    has_paig = bool(
        re.search(r"\bPAIGALDUS\b|\bPAIGALDAMIN", detect_text)
        or re.search(r"\bMONTA[A-ZÕÄÖÜ]*\b", detect_text)
        or re.search(r"\bMONTEER[A-ZÕÄÖÜ]*\b", detect_text)
    )

    svc = ["Transport"]
    if has_paig:
        svc.append("Paigaldus")
    if has_utiil:
        svc.append("Utiil")
    service_tag = " + ".join(svc)


    return {
        "order_ref": order_ref,
        "recipient_name": recipient_name,
        "ship_address": ship_address,
        "service_tag": service_tag,
        "doc_author": doc_author,
        "doc_email": doc_email,
        "doc_phone": doc_phone,
        "items_compact": items_compact,
        "pdf_notes": pdf_notes,
        "client_phone": client_phone,
    }


# Orders CRUD
# -------------------------
def save_uploaded_pdf(uploaded_file) -> str:
    now = datetime.now()
    subdir = os.path.join(ORDERS_DIR, f"{now.year}", f"{now.month:02d}")
    os.makedirs(subdir, exist_ok=True)
    safe = safe_filename(uploaded_file.name)
    stored = os.path.join(subdir, f"order_{int(time.time()*1000)}_{safe}")
    if not stored.lower().endswith(".pdf"):
        stored += ".pdf"
    with open(stored, "wb") as f:
        f.write(uploaded_file.getbuffer())
    return stored


def insert_order(original_filename: str, stored_path: str) -> int:
    conn = db()
    cur = conn.cursor()
    cur.execute(
        "INSERT INTO orders (original_filename, stored_path, created_at) VALUES (?, ?, ?)",
        (original_filename, stored_path, datetime.now().isoformat(timespec="seconds")),
    )
    conn.commit()
    return cur.lastrowid


def list_orders(status_filter=None):
    conn = db()
    cur = conn.cursor()
    cur.execute("SELECT * FROM orders ORDER BY id DESC")
    rows = cur.fetchall()
    if status_filter and status_filter != "ALL":
        rows = [r for r in rows if r["status"] == status_filter]
    return rows


def get_order(order_id: int) -> dict:
    conn = db()
    cur = conn.cursor()
    cur.execute("SELECT * FROM orders WHERE id=?", (order_id,))
    row = cur.fetchone()
    return dict(row) if row else {}


def update_order(order_id: int, **fields):
    allowed = {
        "status","client_name","phone","address","delivery_date","delivery_window","notes",
        "order_ref","recipient_name","ship_address","service_tag",
        "doc_author","doc_email","doc_phone","items_compact",
    }
    cols, vals = [], []
    for k, v in fields.items():
        if k in allowed:
            cols.append(f"{k}=?")
            vals.append(v)
    if not cols:
        return
    vals.append(order_id)
    conn = db()
    cur = conn.cursor()
    cur.execute(f"UPDATE orders SET {', '.join(cols)} WHERE id=?", vals)
    conn.commit()


def delete_order(order_id: int):
    o = get_order(order_id)
    if o:
        try:
            os.remove(o["stored_path"])
        except Exception:
            pass
    conn = db()
    cur = conn.cursor()
    cur.execute("DELETE FROM route_items WHERE order_id=?", (order_id,))
    cur.execute("DELETE FROM orders WHERE id=?", (order_id,))
    conn.commit()


# -------------------------
# Users
# -------------------------
def list_users(active_only: bool = True):
    conn = db()
    cur = conn.cursor()
    if active_only:
        cur.execute("""SELECT u.*
                       FROM users u
                       WHERE u.is_active=1 ORDER BY u.name ASC""")
    else:
        cur.execute("""SELECT u.*
                       FROM users u
                       ORDER BY u.name ASC""")
    return [dict(r) for r in cur.fetchall()]



def upsert_user(user_id, name: str, phone: str = "", is_active: int = 1):
    name = (name or "").strip()
    phone = (phone or "").strip()
    conn = db()
    cur = conn.cursor()
    if user_id:
        cur.execute("""UPDATE users SET name=?, phone=?, is_active=? WHERE id=?""",
                    (name, phone, int(is_active), int(user_id)))
    else:
        cur.execute("""INSERT INTO users (name, phone, is_active, created_at)
                       VALUES (?, ?, ?, ?)""",
                    (name, phone, int(is_active), datetime.now().isoformat(timespec="seconds")))
    conn.commit()


def delete_user(user_id: int):
    conn = db()
    cur = conn.cursor()
    cur.execute("DELETE FROM users WHERE id=?", (int(user_id),))
    conn.commit()


def set_user_password(user_id: int, password: str):
    ph = _pbkdf2_hash_password(password)
    conn = db()
    cur = conn.cursor()
    cur.execute("UPDATE users SET password_hash=? WHERE id=?", (ph, int(user_id)))
    conn.commit()


def verify_user_password(user_id: int, password: str) -> bool:
    conn = db()
    cur = conn.cursor()
    cur.execute("SELECT password_hash FROM users WHERE id=?", (int(user_id),))
    row = cur.fetchone()
    stored = (row["password_hash"] or "").strip() if row else ""
    return bool(stored) and _pbkdf2_verify_password(password, stored)


def ensure_user_token(user_id: int) -> str:
    conn = db()
    cur = conn.cursor()
    cur.execute("SELECT auth_token FROM users WHERE id=?", (int(user_id),))
    row = cur.fetchone()
    tok = (row["auth_token"] or "").strip() if row else ""
    if tok:
        return tok
    tok = _new_token()
    cur.execute("UPDATE users SET auth_token=? WHERE id=?", (tok, int(user_id)))
    conn.commit()
    return tok


def reset_user_token(user_id: int) -> str:
    tok = _new_token()
    conn = db()
    cur = conn.cursor()
    cur.execute("UPDATE users SET auth_token=? WHERE id=?", (tok, int(user_id)))
    conn.commit()
    return tok


def get_user_by_token(token: str) -> dict:
    conn = db()
    cur = conn.cursor()
    cur.execute("""SELECT u.*
                   FROM users u
                   WHERE u.auth_token=? AND u.is_active=1""", ((token or "").strip(),))
    row = cur.fetchone()
    return dict(row) if row else {}


# -------------------------
# Routes + items
# -------------------------
def get_or_create_route(route_date: str) -> int:
    conn = db()
    cur = conn.cursor()
    cur.execute("SELECT id FROM routes WHERE route_date=?", (route_date,))
    row = cur.fetchone()
    if row:
        return row["id"]
    cur.execute("INSERT INTO routes (route_date) VALUES (?)", (route_date,))
    conn.commit()
    return cur.lastrowid


def get_route_id_if_exists(route_date: str):
    conn = db()
    cur = conn.cursor()
    cur.execute("SELECT id FROM routes WHERE route_date=?", (route_date,))
    row = cur.fetchone()
    return row["id"] if row else None


def list_route_items(route_id: int):
    conn = db()
    cur = conn.cursor()
    cur.execute("""
        SELECT
            ri.id as ri_id, ri.seq, ri.ring_no,
            ri.worker_status, ri.worker_status_reason, ri.worker_status_note,
            ri.worker_status_updated_at, ri.worker_status_updated_by,
            o.*,
            COALESCE(GROUP_CONCAT(u.name, ', '), '') AS worker_names
        FROM route_items ri
        JOIN orders o ON o.id=ri.order_id
        LEFT JOIN route_item_users riu ON riu.ri_id = ri.id
        LEFT JOIN users u ON u.id = riu.user_id
        WHERE ri.route_id=? AND UPPER(COALESCE(ri.worker_status,'OPEN'))='OPEN'
        GROUP BY ri.id
        ORDER BY ri.seq ASC
    """, (route_id,))
    return [dict(r) for r in cur.fetchall()]

def list_worker_route_items(route_id: int, user_id: int):
    """Items for a specific worker (via route_item_users)."""
    conn = db()
    cur = conn.cursor()
    cur.execute("""
        SELECT
            ri.id as ri_id, ri.seq, ri.ring_no,
            ri.worker_status, ri.worker_status_reason, ri.worker_status_note,
            ri.worker_status_updated_at, ri.worker_status_updated_by,
            o.*,
            COALESCE(GROUP_CONCAT(u2.name, ', '), '') AS worker_names
        FROM route_item_users riu
        JOIN route_items ri ON ri.id = riu.ri_id
        JOIN orders o ON o.id = ri.order_id
        LEFT JOIN route_item_users riu2 ON riu2.ri_id = ri.id
        LEFT JOIN users u2 ON u2.id = riu2.user_id
        WHERE ri.route_id=? AND riu.user_id=?
        GROUP BY ri.id
        ORDER BY ri.seq ASC
    """, (int(route_id), int(user_id)))
    return [dict(r) for r in cur.fetchall()]

def list_user_route_items(user_id: int, status: str | None = None):
    """Route items assigned to a user via route_item_users."""
    status = (status or "").strip().upper()
    params = [int(user_id)]
    where = "WHERE riu.user_id=?"
    if status:
        where += " AND UPPER(COALESCE(ri.worker_status,'OPEN'))=?"
        params.append(status)

    conn = db()
    cur = conn.cursor()
    cur.execute(f"""
        SELECT
            ri.id as ri_id,
            ri.route_id,
            r.route_date,
            ri.order_id,
            ri.seq,
            ri.ring_no,
            ri.worker_status,
            ri.worker_status_reason,
            ri.worker_status_note,
            ri.worker_status_updated_at,
            ri.worker_status_updated_by,
            o.*,
            COALESCE(GROUP_CONCAT(u2.name, ', '), '') AS worker_names
        FROM route_item_users riu
        JOIN route_items ri ON ri.id = riu.ri_id
        JOIN routes r ON r.id = ri.route_id
        JOIN orders o ON o.id = ri.order_id
        LEFT JOIN route_item_users riu2 ON riu2.ri_id = ri.id
        LEFT JOIN users u2 ON u2.id = riu2.user_id
        {where}
        GROUP BY ri.id
        ORDER BY r.route_date DESC, ri.ring_no ASC, ri.seq ASC
    """, params)
    return [dict(r) for r in cur.fetchall()]


def update_route_item_status(ri_id: int, status: str, user_id: int, reason: str = "", note: str = ""):
    status = (status or "OPEN").strip().upper()
    if status not in ("OPEN", "DONE", "CANCELLED"):
        status = "OPEN"
    now = datetime.now().isoformat(timespec="seconds")
    conn = db()
    cur = conn.cursor()

    finished_at = ""
    if status in ("DONE", "CANCELLED"):
        finished_at = now

    cur.execute(
        """
        UPDATE route_items
        SET worker_status=?, worker_status_reason=?, worker_status_note=?,
            worker_status_updated_at=?, worker_status_updated_by=?,
            worker_finished_at=CASE WHEN ?!='' THEN ? ELSE COALESCE(worker_finished_at,'') END
        WHERE id=?
        """,
        (
            status, (reason or '').strip(), (note or '').strip(),
            now, int(user_id),
            finished_at, finished_at,
            int(ri_id),
        ),
    )
    conn.commit()






def add_order_to_route(route_id: int, order_id: int, user_ids, ring_no: int = 1):
    """Add / move an order into a route ring and assign selected workers.

    Teamless model:
      - route_items: (route_id, order_id, seq, ring_no, statuses...)
      - route_item_users: links route_item -> users (many-to-many)

    Lock handling:
      - Use a dedicated short-lived write connection (autocommit off via explicit BEGIN).
      - Retry quickly for ~2 seconds total to get past transient locks.
    """
    ring_no = int(ring_no or 1)
    user_ids = [int(x) for x in (user_ids or []) if str(x).strip().isdigit()]
    user_ids = sorted(set(user_ids))
    if not user_ids:
        return False, "Vali vähemalt 1 töötaja."

    ensure_dirs()

    max_attempts = 15
    sleep_s = 0.06  # ~2s total worst case

    for attempt in range(max_attempts):
        conn = None
        try:
            conn = sqlite3.connect(DB_PATH, timeout=1.0, check_same_thread=False)
            conn.row_factory = sqlite3.Row
            cur = conn.cursor()
            try:
                cur.execute("PRAGMA foreign_keys=OFF;")
                cur.execute("PRAGMA busy_timeout=1200;")
            except Exception:
                pass

            # Reserve write lock (retry if busy)
            cur.execute("BEGIN;")

            # If already on this route, keep its seq; otherwise allocate next seq for the route
            cur.execute(
                "SELECT id, seq FROM route_items WHERE route_id=? AND order_id=?",
                (int(route_id), int(order_id)),
            )
            existing = cur.fetchone()

            if existing:
                ri_id = int(existing["id"])
                seq = int(existing["seq"] or 1)
                cur.execute(
                    "UPDATE route_items SET ring_no=? WHERE id=?",
                    (int(ring_no), ri_id),
                )
            else:
                cur.execute(
                    "SELECT COALESCE(MAX(seq),0)+1 AS next_seq FROM route_items WHERE route_id=?",
                    (int(route_id),),
                )
                seq = int(cur.fetchone()["next_seq"] or 1)

                cur.execute(
                    "INSERT INTO route_items (route_id, order_id, seq, ring_no) VALUES (?, ?, ?, ?)",
                    (int(route_id), int(order_id), int(seq), int(ring_no)),
                )
                ri_id = int(cur.lastrowid)

            # Replace worker links
            cur.execute("DELETE FROM route_item_users WHERE ri_id=?", (ri_id,))

            # Backward-compat: route_item_users may not have created_at in older DBs
            try:
                cur.execute("PRAGMA table_info(route_item_users)")
                _cols = [r["name"] for r in cur.fetchall()]
            except Exception:
                _cols = []

            now = datetime.now().isoformat(timespec="seconds")
            has_created_at = ("created_at" in _cols)

            for uid in user_ids:
                if has_created_at:
                    cur.execute(
                        "INSERT OR IGNORE INTO route_item_users (ri_id, user_id, created_at) VALUES (?, ?, ?)",
                        (ri_id, int(uid), now),
                    )
                else:
                    cur.execute(
                        "INSERT OR IGNORE INTO route_item_users (ri_id, user_id) VALUES (?, ?)",
                        (ri_id, int(uid)),
                    )

            conn.commit()
            return True, "Added to route."

        except sqlite3.OperationalError as e:
            msg = str(e).lower()
            try:
                if conn:
                    conn.rollback()
            except Exception:
                pass
            # Retry on locking/busy
            if ("locked" in msg) or ("busy" in msg) or ("database is locked" in msg):
                time.sleep(sleep_s)
                continue
            return False, f"Andmebaasi viga: {e}"
        except Exception as e:
            try:
                if conn:
                    conn.rollback()
            except Exception:
                pass
            return False, f"Viga: {e}"
        finally:
            try:
                if conn:
                    conn.close()
            except Exception:
                pass

    return False, "Andmebaas on hetkeks hõivatud. Proovi uuesti."


def remove_route_item(ri_id: int):
    """Remove a route item. Also deletes any accidental duplicates for the same (route_id, order_id)."""
    conn = db()
    cur = conn.cursor()
    try:
        cur.execute("BEGIN;")
        cur.execute("SELECT route_id, order_id FROM route_items WHERE id=?", (ri_id,))
        row = cur.fetchone()
        if row:
            cur.execute("DELETE FROM route_items WHERE route_id=? AND order_id=?", (row["route_id"], row["order_id"]))
        else:
            cur.execute("DELETE FROM route_items WHERE id=?", (ri_id,))
        conn.commit()
    except (sqlite3.OperationalError, sqlite3.IntegrityError):
        conn.rollback()


def move_route_item(ri_id: int, direction: int):
    """Swap seq with the previous/next item inside the same route (teamless)."""
    conn = db()
    cur = conn.cursor()
    cur.execute("SELECT id, route_id, seq FROM route_items WHERE id=?", (int(ri_id),))
    item = cur.fetchone()
    if not item:
        return
    route_id, seq = int(item["route_id"]), int(item["seq"] or 0)
    target_seq = seq + int(direction)
    if target_seq < 1:
        return

    cur.execute("SELECT id FROM route_items WHERE route_id=? AND seq=?", (route_id, target_seq))
    other = cur.fetchone()
    if not other:
        return
    other_id = int(other["id"])

    tmp_seq = 999999999
    try:
        cur.execute("BEGIN;")
        cur.execute("UPDATE route_items SET seq=? WHERE id=?", (tmp_seq, int(ri_id)))
        cur.execute("UPDATE route_items SET seq=? WHERE id=?", (seq, other_id))
        cur.execute("UPDATE route_items SET seq=? WHERE id=?", (target_seq, int(ri_id)))
        conn.commit()
    except Exception:
        try:
            conn.rollback()
        except Exception:
            pass

    except Exception:
        conn.rollback()


# -------------------------
# Export
# -------------------------
def build_team_manifest(route_date: str, team_name: str, items):
    manifest = {"date": route_date, "team": team_name, "count": len(items), "orders": []}
    for it in items:
        it = dict(it)
        manifest["orders"].append({
            "seq": it["seq"],
            "order_id": it["id"],
            "delivery_date": it.get("delivery_date",""),
            "delivery_window": it.get("delivery_window",""),
            "address": it.get("address",""),
            "phone": it.get("phone",""),
            "client_name": it.get("client_name",""),
            "notes": it.get("notes",""),
            "worker_status": it.get("worker_status","OPEN"),
        })
    return manifest


def build_ring_sheet_html(route_date: str, team_name: str, items):
    rows = []
    for it in items:
        it = dict(it)
        rows.append(f"""
        <tr>
          <td>{it['seq']}</td>
          <td>{(it.get('delivery_window') or '')}</td>
          <td>{(it.get('address') or '').replace('<','&lt;')}</td>
          <td>{(it.get('phone') or '').replace('<','&lt;')}</td>
          <td>{(it.get('client_name') or '').replace('<','&lt;')}</td>
          <td style="white-space:pre-wrap">{(it.get('notes') or '').replace('<','&lt;')}</td>
        </tr>
        """)
    return f"""
<!doctype html>
<html><head><meta charset="utf-8"/>
<title>Routeileht {team_name} {route_date}</title>
<style>
body {{ font-family: Arial, sans-serif; padding: 16px; }}
h1 {{ margin: 0 0 6px 0; }}
.sub {{ color: #555; margin-bottom: 14px; }}
table {{ border-collapse: collapse; width: 100%; }}
th, td {{ border: 1px solid #ddd; padding: 8px; vertical-align: top; }}
th {{ background: #f3f3f3; text-align: left; }}
</style></head>
<body>
<h1>Routeileht: {team_name}</h1>
<div class="sub">Date: {route_date} • Orders: {len(items)}</div>
<table>
<thead><tr><th>#</th><th>Aeg</th><th>Address</th><th>Phone</th><th>Client</th><th>Notes</th></tr></thead>
<tbody>{''.join(rows)}</tbody>
</table>
</body></html>
"""


def worker_view():
    # tagame, et töölise vaates on sama CSS/komponendid nagu logistiku vaates
    inject_styles()
    st.markdown("""<div style='height:6px'></div>""", unsafe_allow_html=True)
    st.title("📱 Worker view")
    st.caption("Tööread: Kellaaeg • Address • Phone • Client. Ava töö → tooted + märkmed.")

    try:
        token = (st.query_params.get("token", "") or "").strip()
    except Exception:
        token = ""

    if "worker_token" not in st.session_state:
        st.session_state.worker_token = ""
    if token:
        st.session_state.worker_token = token

    user = get_user_by_token(st.session_state.worker_token) if st.session_state.worker_token else {}

    top = st.columns([3, 1], vertical_alignment="bottom")
    with top[1]:
        if st.button("Log out", use_container_width=True):
            st.session_state.worker_token = ""
            try:
                st.query_params.clear()
                st.query_params["view"] = "worker"
            except Exception:
                pass
            st.rerun()

    if not user:
        st.subheader("🔐 Login")
        active_users = list_users(active_only=True)
        if not active_users:
            st.error("Töötajaid pole lisatud.")
            return
        pick = st.selectbox("Select user", [f"{u['name']} (ID {u['id']})" for u in active_users])
        uid = int(pick.split("ID")[1].strip().rstrip(")"))
        pwd = st.text_input("Password", type="password")
        if st.button("Log in", type="primary"):
            if not verify_user_password(uid, pwd):
                st.error("Vale salasõna.")
                return
            tok = ensure_user_token(uid)
            st.session_state.worker_token = tok
            try:
                st.query_params["view"] = "worker"
                st.query_params["token"] = tok
            except Exception:
                pass
            st.success("Sisse logitud.")
            st.rerun()

        st.markdown("""
**📲 Lisa telefoni nagu äpp**
- iPhone: Safari → Share → **Add to Home Screen**
- Android: Chrome → menüü → **Add to Home screen / Install**
""")
        return

    try:
        st.query_params["view"] = "worker"
        st.query_params["token"] = st.session_state.worker_token
    except Exception:
        pass

    hdr = st.columns([3, 1])
    hdr[0].markdown(f"### 👷 {user.get('name','')}")
    hdr[1].markdown("**Määratud tööd:**")  # detailid all

    st.divider()

    status_tab = st.radio("Vaade", ["Open", "Done", "Cancelled"], index=0, horizontal=True)
    status_map = {"Open": "OPEN", "Done": "DONE", "Cancelled": "CANCELLED"}
    want_status = status_map[status_tab]

    cancel_reasons = [
        "Client ei vastanud", "Client tühistas", "Ligipääs puudus / ei saanud ligi",
        "Ese puudus / vale kaup", "Ajapuudus", "Tehniline probleem", "Muu"
    ]

    today = date.today()
    # Kuva tööd kuupäevade kaupa (kasutame eelkõige tellimuse delivery_date; kui see puudub, siis route_date).
    # OPEN: alates tänasest edasi; DONE/CANCELLED: näita ka viimased 7 päeva.
    start_date = (today - timedelta(days=7)) if want_status != 'OPEN' else today
    start_date_s = start_date.isoformat()

    conn = db()
    cur = conn.cursor()
    cur.execute(
        """
        SELECT
            ri.id as ri_id,
            ri.route_id as route_id,
            ri.order_id as order_id,
            ri.seq as seq,
            ri.ring_no as ring_no,
            ri.worker_status as worker_status,
            ri.worker_status_reason as worker_status_reason,
            ri.worker_status_note as worker_status_note,
            o.delivery_date as delivery_date,
            o.delivery_window as delivery_window,
            o.address as address,
            o.ship_address as ship_address,
            o.phone as phone,
            o.client_name as client_name,
            o.recipient_name as recipient_name,
            o.notes as notes,
            o.items_compact as items_compact,
            o.stored_path as stored_path,
            o.service_tag as service_tag,
            r.route_date as route_date
        FROM route_item_users riu
        JOIN route_items ri ON ri.id = riu.ri_id
        JOIN orders o ON o.id = ri.order_id
        JOIN routes r ON r.id = ri.route_id
        WHERE riu.user_id = ?
          AND UPPER(ri.worker_status) = ?
          AND COALESCE(NULLIF(o.delivery_date,''), r.route_date) >= ?
        ORDER BY COALESCE(NULLIF(o.delivery_date,''), r.route_date),
                 CASE WHEN o.delivery_window IS NULL OR o.delivery_window='' THEN 1 ELSE 0 END,
                 o.delivery_window,
                 ri.seq
        """,
        (int(user['id']), want_status.upper(), start_date_s)
    )
    rows_all = [dict(r) for r in cur.fetchall()]

    shown_any = False
    by_day = {}
    for it in rows_all:
        day = (it.get('delivery_date') or '').strip() or (it.get('route_date') or '').strip()
        if not day:
            continue
        by_day.setdefault(day, []).append(it)

    for day, rows in sorted(by_day.items(), key=lambda x: x[0]):
        try:
            d = date.fromisoformat(day)
            day_label = d.strftime('%d.%m.%Y')
        except Exception:
            day_label = day

        st.markdown(f"## 📅 {day_label} ({len(rows)} tööd)")
        shown_any = True

        def sort_key(it):
            w = _parse_time_window_start(it.get('delivery_window',''))
            seq = int(it.get('seq') or 999999)
            return (w or dtime(23, 59), seq)

        
        rows = sorted(rows, key=sort_key)

        # Grupeeri ringide kaupa (töölised näevad ringe samamoodi nagu logistik)
        rings = {}
        for it in rows:
            rn = int(it.get('ring_no') or 1)
            rings.setdefault(rn, []).append(it)

        for rn in sorted(rings.keys()):
            rrows = rings[rn]
            st.markdown(f"### {rn} ring ({len(rrows)})")

            for it in rrows:
                ri_id = int(it.get('ri_id'))
                window = (it.get('delivery_window') or '').strip() or '—'
                addr = (it.get('address') or '').strip() or (it.get('ship_address') or '').strip() or '—'
                phone = (it.get('phone') or '').strip()
                client = (it.get('client_name') or '').strip() or (it.get('recipient_name') or '').strip() or '—'

                svc_icons = _service_icons(it.get('service_tag') or '')
                summary = f"{svc_icons} {client} • ⏱️ {window} • 📍 {addr} • 📞 {phone or '—'}"

                # Üks töö korraga avatud (mobiilis scrolli jaoks)
                open_key = "worker_open_ri"
                if open_key not in st.session_state:
                    st.session_state[open_key] = None

                clicked = st.button(summary, key=f"wrow_{ri_id}", use_container_width=True)
                if clicked:
                    st.session_state[open_key] = None if st.session_state[open_key] == ri_id else ri_id

                if st.session_state[open_key] == ri_id:
                    actions = st.columns([1.2, 1.2, 1.6])
                    if addr and addr != '—':
                        try:
                            actions[0].link_button('🗺️ Kaart', _map_link(addr), use_container_width=True)
                        except Exception:
                            actions[0].markdown(f'<a href="{_map_link(addr)}" target="_blank">🗺️ Kaart</a>', unsafe_allow_html=True)
                    else:
                        actions[0].button('🗺️ Kaart', disabled=True, use_container_width=True)

                    if phone:
                        try:
                            actions[1].link_button('📞 Helista', f"tel:{phone}", use_container_width=True)
                        except Exception:
                            actions[1].markdown(f'<a href="tel:{phone}" style="text-decoration:none;">📞 Helista</a>', unsafe_allow_html=True)
                    else:
                        actions[1].button('📞 Helista', disabled=True, use_container_width=True)

                    # märkus + tooted nagu logistiku vaates
                    tab_notes, tab_items = st.tabs(["📝 Notes", "📦 Items"])
                    with tab_notes:
                        note_txt = (it.get('notes') or '').strip()
                        if note_txt:
                            st.info(note_txt)
                        else:
                            st.caption("—")
                    with tab_items:
                        items = parse_items_compact(it.get('items_compact') or '')
                        _render_items_boxes(items, title="📦 Items", show_title=True)

                    # Status actions (kui OPEN)
                    want_status = ((it.get('worker_status') or 'OPEN').strip()).upper()
                    if want_status not in ('DONE','CANCELLED'):
                        c1, c2 = st.columns([1.0, 1.0])
                        if c1.button('✅ Done', key=f"done_{ri_id}"):
                            update_route_item_status(ri_id, 'DONE', user_id=user['id'])
                            st.rerun()

                        cancel_key = f"cancel_open_{ri_id}"
                        if cancel_key not in st.session_state:
                            st.session_state[cancel_key] = False
                        if c2.button('⛔ Katkesta', key=f"cancel_btn_{ri_id}"):
                            st.session_state[cancel_key] = not st.session_state[cancel_key]
                        if st.session_state.get(cancel_key, False):
                            reason = st.selectbox('Põhjus', cancel_reasons, key=f"rsn_{ri_id}")
                            note = st.text_area('Märkus (valikuline)', key=f"nt_{ri_id}", height=70)
                            if st.button('Save katkestus', key=f"save_cancel_{ri_id}"):
                                update_route_item_status(ri_id, 'CANCELLED', user_id=user['id'], reason=reason, note=note)
                                st.rerun()
                    else:
                        # DONE/CANCELLED: ainult info (mitte muuta)
                        if want_status == 'CANCELLED':
                            st.write(f"**Põhjus:** {it.get('worker_status_reason') or '—'}")
                            st.write(f"**Märkus:** {it.get('worker_status_note') or '—'}")

                    st.markdown("---")
    if not shown_any:
        st.info("Selles vaates pole järgmise 7 päeva jooksul töid.")


# -------------------------
# APP ENTRY
# -------------------------
init_db()

try:
    view = st.query_params.get("view", "")
except Exception:
    view = ""

if (view or "").lower() == "worker":
    worker_view()
    st.stop()

# PDF preview in new tab (from Route Planner)
# Open: /?view=pdf&order_id=<id>
if (view or "").lower() == "pdf":
    try:
        oid = int(st.query_params.get("order_id", "0") or 0)
    except Exception:
        oid = 0
    o = get_order(oid) if oid else {}
    c_pdf_btn, c_pdf_title = st.columns([1, 8], vertical_alignment='center')
    with c_pdf_title:
        st.markdown("## PDF")
    if (not o) or (not os.path.exists(o.get("stored_path", ""))):
        st.error("PDF faili ei leitud.")
        st.stop()

    st.caption(os.path.basename(o["stored_path"]))
    import base64 as _b64
    with open(o["stored_path"], "rb") as f:
        b64 = _b64.b64encode(f.read()).decode("utf-8")

    components.html(
        f'<iframe src="data:application/pdf;base64,{b64}" width="100%" height="900px" style="border:0;"></iframe>',
        height=920
    )
    st.stop()


# =========================
# ADMIN UI
# =========================
render_header()
tabs = st.tabs(["📥 Orders", "👷 Workers", "🗓️ Route Planner", "🧾 Jobs", "⚙️ Settings"])


# ---- TAB 1: Orders ----
with tabs[0]:
    st.subheader("Orders")
    uploads = st.file_uploader("Drag & drop or select PDFs", type=["pdf"], accept_multiple_files=True)

    if st.button("Import uploaded PDFs", type="primary", disabled=not uploads):
        errors = []
        for up in uploads:
            stored = save_uploaded_pdf(up)
            order_id = insert_order(up.name, stored)
            try:
                text = extract_pdf_text(stored)
                parsed = parse_aatrium_pdf_text(text)

                update_order(
                    order_id,
                    order_ref=parsed.get("order_ref",""),
                    recipient_name=parsed.get("recipient_name",""),
                    ship_address=parsed.get("ship_address",""),
                    service_tag=parsed.get("service_tag",""),
                    doc_author=parsed.get("doc_author",""),
                    doc_email=parsed.get("doc_email",""),
                    doc_phone=parsed.get("doc_phone",""),
                    items_compact=parsed.get("items_compact",""),

                    client_name=parsed.get("recipient_name","") or "",
                    address=parsed.get("ship_address","") or "",
                    phone=parsed.get("client_phone","") or "",
                    notes=parsed.get("pdf_notes","") or "",
                    delivery_date=date.today().isoformat(),
                    delivery_window="",
                )
            except Exception as e:
                errors.append(f"{up.name}: {e}")

        if errors:
            st.error("Mõni fail ei parsitud korrektselt:")
            for e in errors:
                st.write("• " + e)
        st.success(f"Imporditud: {len(uploads)} faili")
        st.rerun()

    st.divider()
    status_filter = st.selectbox("Filter by status", ["ALL", "NEW", "CONTACTED", "SCHEDULED", "READY FOR WORK"])
    orders = list_orders(status_filter=status_filter)
    st.caption(f"Orders: {len(orders)}")

    left_sel, mid_view, right_edit = st.columns([0.85, 2.6, 1.15], vertical_alignment="top")

    with left_sel:
        order_options = {f"#{o['id']} • {o['original_filename']} • {o['status']}": o["id"] for o in orders}
        selected_label = st.selectbox("Select an order", ["—"] + list(order_options.keys()))
        selected_id = order_options.get(selected_label)

        if selected_id and st.button("🗑️ Delete order", use_container_width=True):
            delete_order(selected_id)
            st.success("Kustutatud.")
            st.rerun()

    if not selected_id:
        with mid_view:
            st.info("Select an order on the left to view the information and items read from the PDF.")
        with right_edit:
            st.info("Manual fields will appear here.")
    else:
        o = get_order(selected_id)

        with mid_view:
            c_pdf_btn, c_pdf_title = st.columns([1, 8], vertical_alignment='center')
            with c_pdf_title:
                st.markdown("## PDF")
            pdf_path = (o.get('stored_path') or '').strip()
            if pdf_path and os.path.exists(pdf_path):
                with open(pdf_path, 'rb') as _f:
                    _pdf_bytes = _f.read()
                c_pdf_btn.download_button('📄', data=_pdf_bytes, file_name=os.path.basename(pdf_path), mime='application/pdf', key=f"dl_home_{o.get('id','0')}")

            st.write(f"Fail: **{os.path.basename(o['stored_path'])}**")
            if o.get("order_ref"):
                st.markdown(f"**Order:** `{o['order_ref']}`")
            if o.get("recipient_name"):
                st.markdown(f"**Recipient:** {o['recipient_name']}")
            if o.get("phone"):
                st.markdown(f"**Phone:** {o.get('phone')}")
            _render_items_boxes(o.get("items_compact") or "", title="📦 Items")
            if o.get("service_tag"):
                st.markdown(f"### 🚚 Service: **{o['service_tag']}**")

            if o.get("doc_author") or o.get("doc_phone") or o.get("doc_email"):
                st.markdown("### ☎️ Document author")
                if o.get("doc_author"): st.write(o["doc_author"])
                if o.get("doc_phone"): st.write(o["doc_phone"])
                if o.get("doc_email"): st.write(o["doc_email"])

        with right_edit:
            st.markdown("## ✍️ Customer details")

            new_status = st.selectbox(
                "Status",
                ["NEW", "CONTACTED", "SCHEDULED", "READY FOR WORK"],
                index=["NEW","CONTACTED","SCHEDULED","READY FOR WORK"].index(STATUS_MAP.get((o.get("status") or "NEW").upper(),"NEW")),
            )

            client = st.text_input("Client", value=o.get("client_name", "") or "")
            phone = st.text_input("Phone", value=o.get("phone", "") or "")
            address = st.text_area("Address", value=o.get("address", "") or "", height=90)

            dval = (o.get("delivery_date") or "").strip()
            try:
                d_pick = date.fromisoformat(dval) if dval else date.today()
            except Exception:
                d_pick = date.today()
            d_pick = st.date_input("Delivery date", value=d_pick)

            
            # Delivery time window (algus + lõpp eraldi)
            current_window = (o.get("delivery_window") or "").strip().replace("–", "-")

            def _build_time_opts():
                opts = [""]
                start = datetime.combine(date.today(), dtime(6, 0))
                end = datetime.combine(date.today(), dtime(21, 0))
                t = start
                while t <= end:
                    opts.append(t.strftime("%H:%M"))
                    t += timedelta(minutes=30)
                return opts

            time_opts = _build_time_opts()

            # Prefill if current_window like "10:30-11:30"
            cur_a, cur_b = "", ""
            mm = re.match(r"^(\d{1,2}:\d{2})\s*-\s*(\d{1,2}:\d{2})$", current_window)
            if mm:
                cur_a, cur_b = mm.group(1), mm.group(2)

            st.markdown("**Delivery time window**")
            tw1, tw2 = st.columns(2)
            with tw1:
                start_t = st.selectbox("Start", time_opts, index=time_opts.index(cur_a) if cur_a in time_opts else 0)
            with tw2:
                end_t = st.selectbox("End", time_opts, index=time_opts.index(cur_b) if cur_b in time_opts else 0)

            if start_t and end_t:
                delivery_window = f"{start_t}-{end_t}"
            else:
                delivery_window = ""

            notes = st.text_area("Notes", value=o.get("notes", "") or "", height=220)

            if st.button("💾 Save changes", type="primary", use_container_width=True):
                update_order(
                    selected_id,
                    status=new_status,
                    client_name=client,
                    phone=phone,
                    address=address,
                    delivery_date=d_pick.isoformat(),
                    delivery_window=delivery_window,
                    notes=notes,
                )
                st.success("Savetud.")
                st.rerun()


# ---- TAB 2: Settings ----
with tabs[4]:
    st.subheader("Workers (password + token link)")
    st.caption("Worker logs in once → token link → Add to Home Screen.")


    left, right = st.columns([1, 1], vertical_alignment="top")

    with left:
        st.markdown("### ➕ Add / update worker")
        users = list_users(active_only=False)
        user_map = {"(new worker)": None}
        for u in users:
            user_map[f"{u['name']} • {'' or '—'}"] = u["id"]
        pick_label = st.selectbox("Select worker", list(user_map.keys()))
        pick_id = user_map[pick_label]
        existing = next((x for x in users if x["id"] == pick_id), {}) if pick_id else {}

        name = st.text_input("Name", value=existing.get("name", "") or "")
        phone = st.text_input("Phone (optional)", value=existing.get("phone", "") or "")
        is_active = st.checkbox("Active", value=bool(existing.get("is_active", 1)))

        if st.button("💾 Save töötaja", type="primary", use_container_width=True, disabled=not name.strip()):
            upsert_user(pick_id, name=name, phone=phone, is_active=1 if is_active else 0)
            st.success("Savetud.")
            st.rerun()

        st.divider()
        st.markdown("### 🔑 Set / change password")
        if not pick_id:
            st.info("Select an existing worker.")
        else:
            pwd1 = st.text_input("New password", type="password", key="pwd1")
            pwd2 = st.text_input("Repeat password", type="password", key="pwd2")
            if st.button("Save password", disabled=not pwd1):
                if pwd1 != pwd2:
                    st.error("Passwordd ei kattu.")
                elif len(pwd1) < 6:
                    st.error("Soovitus: vähemalt 6 märki.")
                else:
                    set_user_password(pick_id, pwd1)
                    st.success("Password salvestatud.")
                    st.rerun()

        if pick_id:
            st.divider()
            if st.button("🔄 Reset token (if the link leaked)", use_container_width=True):
                reset_user_token(pick_id)
                st.success("Token reset tehtud.")
                st.rerun()

        if pick_id and st.button("🗑️ Delete worker", use_container_width=True):
            delete_user(pick_id)
            st.success("Kustutatud.")
            st.rerun()

    with right:
        st.markdown("### 🔗 Worker link + copy")
        base_url = st.text_input("Base URL", value="http://localhost:8501")
        users = list_users(active_only=True)
        if not users:
            st.info("Lisa vähemalt 1 aktiivne töötaja.")
        else:
            pick = st.selectbox("Select worker lingi jaoks", [f"{u['name']} (ID {u['id']})" for u in users])
            uid = int(pick.split("ID")[1].strip().rstrip(")"))
            tok = ensure_user_token(uid)
            link = f"{base_url}/?view=worker&token={tok}"
            st.code(link, language=None)
            _copy_button(link, "📋 Copy link")


# ---- TAB 3: Route Planner ----
with tabs[2]:
    st.subheader("Route Planner (by date)")
    # ---- Google Maps ring seaded (salvestub DB-sse) ----
    # Presetid: Warehouse / Kontor / Muu
    preset = get_setting("maps_preset", "Warehouse")
    addr_ladu = get_setting("maps_ladu_addr", "Liivalao 11, Tallinn")
    addr_kontor = get_setting("maps_kontor_addr", "")
    addr_muu = get_setting("maps_custom_addr", "")
    return_to_start = get_setting("maps_return_to_start", "0") == "1"

    with st.expander("🧭 Map settings", expanded=False):
        # Presets
        preset = get_setting("maps_start_preset", "Warehouse")
        presets = {
            "Warehouse": get_setting("maps_start_ladu", "Liivalao 11, Tallinn"),
            "Kontor": get_setting("maps_start_kontor", "Liivalao 11, Tallinn"),
            "Muu…": get_setting("maps_start_custom", ""),
        }

        cA, cB = st.columns([1.2, 1.8])
        with cA:
            start_choice = st.selectbox("Start", list(presets.keys()), index=list(presets.keys()).index(preset) if preset in presets else 0)
            return_to_start = st.checkbox("Back to start (route)", value=(get_setting("maps_return","0") == "1"))
        with cB:
            if start_choice == "Muu…":
                start_value = st.text_input("Start aadress", value=presets["Muu…"], placeholder="nt Liivalao 11, Tallinn")
            else:
                start_value = st.text_input("Start aadress", value=presets[start_choice])

        s1, s2 = st.columns([1,1])
        if s1.button("💾 Save", use_container_width=True):
            # store preset values too (so user can edit Warehouse/Kontor)
            if start_choice == "Warehouse":
                set_setting("maps_start_ladu", start_value)
                set_setting("maps_start", start_value)
            elif start_choice == "Kontor":
                set_setting("maps_start_kontor", start_value)
                set_setting("maps_start", start_value)
            else:
                set_setting("maps_start_custom", start_value)
                set_setting("maps_start", start_value)

            set_setting("maps_start_preset", start_choice)
            set_setting("maps_return", "1" if return_to_start else "0")
            st.success("Savetud.")
            st.rerun()

        if s2.button("↩️ Reset (Liivalao 11)", use_container_width=True):
            set_setting("maps_start", "Liivalao 11, Tallinn")
            set_setting("maps_start_ladu", "Liivalao 11, Tallinn")
            set_setting("maps_start_kontor", "Liivalao 11, Tallinn")
            set_setting("maps_start_custom", "")
            set_setting("maps_start_preset", "Warehouse")
            set_setting("maps_return", "0")
            st.success("Reset tehtud.")
            st.rerun()


    teams = [1]  # legacy placeholder (tiimide UI eemaldatud)
    if not teams:
        st.warning("Lisa enne tiimid (vaheleht ⚙️ Settings).")
    else:
        route_date = date.today().isoformat()  # UI-st kuupäeva valikut ei küsi
        route_id = get_or_create_route(route_date)

        left, right = st.columns([1, 1], vertical_alignment="top")

        with left:
            st.markdown("### Add orders to route")
            # Kiirvalikud: Ready jobs / Scheduled (et ei peaks PDF nime järgi otsima)
            conn = db()
            cur = conn.cursor()
            cur.execute("SELECT order_id FROM route_items WHERE route_id=?", (route_id,))
            in_route = {r[0] for r in cur.fetchall()}

            def _available_by_status(wanted_status: str):
                all_o = list_orders(status_filter=wanted_status)
                return [o for o in all_o if o['id'] not in in_route]

            c_team, c_ring = st.columns([3, 1], vertical_alignment='center')
            user_rows = list_users(active_only=True)
            user_opts = {u['name']: int(u['id']) for u in (user_rows or [])}
            picked_user_names = c_team.multiselect('Workers (quick add)', list(user_opts.keys()), default=[], key='users_pick_quick')
            picked_ids = [user_opts[n] for n in picked_user_names]
            ring_pick_quick = c_ring.selectbox('Route', [1, 2, 3, 4], index=0, key='ring_pick_quick')

            if 'open_quick_orders' not in st.session_state:
                st.session_state.open_quick_orders = set()

            for label, st_key in [("✅ Ready jobs", "READY FOR WORK"), ("🗓️ Scheduled", "SCHEDULED")]:
                lst = _available_by_status(st_key)
                with st.expander(f"{label} ({len(lst)})", expanded=False):
                    if not lst:
                        st.caption("None.")
                    for o in lst:
                        o = dict(o)  # sqlite3.Row -> dict for .get()
                        # Ühe töö rida: vasakul toggel (detailid), paremal väike ➕ lisa
                        with st.container(border=True):
                            c_main, c_add = st.columns([9, 1], vertical_alignment='center')
                            client = (o.get('client_name') or o.get('recipient_name') or '—').strip()
                            window = (o.get('delivery_window') or '—').strip()
                            addr = (o.get('address') or o.get('ship_address') or '—').strip()
                            phone = (o.get('phone') or '—').strip()
                            svc_icons = _service_icons(o.get('service_tag') or '')
                            label_row = f"{svc_icons} {client} • ⏱️ {window} • 📍 {addr} • 📞 {phone}"
                            if o['id'] in in_route:
                                label_row = label_row + ""
                            is_open = (o['id'] in st.session_state.open_quick_orders)
                            btn_txt = (('▸ ' if not is_open else '▾ ') + label_row)
                            if c_main.button(btn_txt, key=f"qtoggle_{st_key}_{o['id']}", use_container_width=True):
                                if is_open:
                                    st.session_state.open_quick_orders.remove(o['id'])
                                else:
                                    st.session_state.open_quick_orders.add(o['id'])
                                st.rerun()
                            if c_add.button("➕", key=f"quick_add_{st_key}_{o['id']}", use_container_width=True):
                                ok, msg = add_order_to_route(route_id, int(o['id']), picked_ids, ring_no=ring_pick_quick)
                                if ok:
                                    st.success(msg or 'Lisatud.')
                                else:
                                    st.error(msg)
                        
                            if (o['id'] in st.session_state.open_quick_orders):
                                if (o.get('notes') or '').strip():
                                    st.markdown('**📝 Notes**')
                                    st.write(o.get('notes') or '')
                        
                                items = (o.get('items_compact') or '').strip()
                                if items:
                                    st.markdown('**📦 Items**')
                                    pdf_path = (o.get('stored_path') or '').strip()
                                    if pdf_path and os.path.exists(pdf_path):
                                        with open(pdf_path, 'rb') as _f:
                                            _pdf_bytes = _f.read()
                                        st.download_button('📄 PDF', data=_pdf_bytes, file_name=os.path.basename(pdf_path), mime='application/pdf', use_container_width=False, key=f"dl_quick_{st_key}_{o['id']}")
                                    else:
                                        st.button('📄 PDF', disabled=True)
                                    _render_items_boxes(items, title='', show_title=False)

        with right:
            st.markdown("### Route Planner")

            items = list_route_items(route_id)
            if not items:
                st.info("Route is empty on this date.")
            else:
                # Grupp tarne kuupäeva järgi (order.delivery_date). See võimaldab ühes ringis mitut kuupäeva.
                by_date = {}
                for it in items:
                    d = (it.get("delivery_date") or "").strip() or route_date
                    by_date.setdefault(d, []).append(it)

                status_emoji = {"OPEN": "🟦", "DONE": "✅", "CANCELLED": "⛔"}
                sections = [("OPEN", "Lisatud tööd"), ("DONE", "Done tööd"), ("CANCELLED", "Cancelled tööd")]

                # Datea plokkide avamine/sulgemine (vältimaks expanders-in-expanders viga)
                if "open_date_blocks" not in st.session_state:
                    st.session_state.open_date_blocks = set()

                for d, date_items in sorted(by_date.items(), key=lambda x: x[0]):
                    # Datea rida + Google Maps ring (ainult selle kuupäeva tööd)
                    c1 = st.container()  # kuupäeva nupp täislaiuses
                    with c1:
                        try:
                            d_label = datetime.fromisoformat(d).strftime("%d.%m.%Y")
                        except Exception:
                            d_label = d

                        btn_label = f"📅 {d_label} ({len(date_items)} tööd)"
                        if st.button(btn_label, key=f"date_toggle_{d}", use_container_width=True):
                            if d in st.session_state.open_date_blocks:
                                st.session_state.open_date_blocks.remove(d)
                            else:
                                st.session_state.open_date_blocks.add(d)
                            st.rerun()

                    if d not in st.session_state.open_date_blocks:
                        continue

                    # Jobs selle kuupäeva sees (tiimi kaupa, staatuse kaupa)
                    grouped = {}
                    for it in date_items:
                        grouped.setdefault((it.get("worker_names") or "—"), []).append(it)

                    for team_name, its in grouped.items():
                        st.markdown(f"#### {team_name} ({len(its)})")

                        by_status = {"OPEN": [], "DONE": [], "CANCELLED": []}
                        for it in its:
                            s = (it.get("worker_status") or "OPEN").upper()
                            if s not in by_status:
                                s = "OPEN"
                            by_status[s].append(it)

                        for st_key, title in sections:
                            block = by_status.get(st_key, [])
                            if not block:
                                continue

                            if st_key != "OPEN":
                                st.markdown(f"**{title}** ({len(block)})")

                            # Mitme ringi tugi (ring_no). Kui on ainult 1 ring, siis ei kuva eraldi pealkirja.
                            # Gruppimine ringide kaupa (näitame alati 1 ring + kaardi nupp iga ringi taga)
                            block_sorted = sorted(block, key=lambda x: (int(x.get('ring_no') or 1), int(x.get('seq') or 0)))
                            rings = {}
                            for _it in block_sorted:
                                rn = int(_it.get('ring_no') or 1)
                                rings.setdefault(rn, []).append(_it)
                            
                            _global_start = get_setting('maps_start', 'Liivalao 11, Tallinn')
                            _global_return = (get_setting('maps_return', '') or get_setting('maps_return_to_start', '0')) == '1'
                            
                            for rn in sorted(rings.keys()):
                                ring_rows = rings[rn]
                                addr_list = []
                                # kasuta sama aadressi loogikat nagu tööreal; ei filtreeri staatuse järgi
                                for _x in ring_rows:
                                    _addr = ((_x.get('address') or '').strip() or (_x.get('ship_address') or '').strip() or (_x.get('delivery_address') or '').strip())
                                    if _addr and _addr != '—':
                                        addr_list.append(_addr)
                                settings_key = f"maps_ring_{d}_{team_name}_{rn}"
                                try:
                                    _ring_cfg = json.loads(get_setting(settings_key, "{}") or "{}")
                                except Exception:
                                    _ring_cfg = {}
                                sp = (_ring_cfg.get('start') or _global_start).strip() or _global_start
                                ret = bool(_ring_cfg.get('return', _global_return))
                                maps_url = _maps_dir_link(addr_list, start_point=sp, return_to_start=ret) if addr_list else ''
                            
                                spc, h1, h2, h3 = st.columns([0.9, 7.3, 0.9, 0.9], vertical_alignment='center')
                                with h1:
                                    ring_uid = str((ring_rows[0].get("ri_id") or ring_rows[0].get("id") or ring_rows[0].get("order_id") or ""))
                                    open_key = f"open_ring_{d}_{team_name}_{rn}_{ring_uid}"
                                    if open_key not in st.session_state:
                                        st.session_state[open_key] = True
                                    label = f"{rn} ring"
                                    if st.button(label, key=f"tog_{d}_{team_name}_{rn}_{ring_uid}", use_container_width=True):
                                        st.session_state[open_key] = not st.session_state[open_key]
                                with h2:
                                    if maps_url:
                                        st.link_button('🗺️', maps_url, use_container_width=True)
                                    else:
                                        st.button('🗺️', disabled=True, use_container_width=True, key=f"mapd_{d}_{team_name}_{st_key}_{rn}")
                                with h3:
                                    if st.button('⚙️', key=f"mapcfg_{d}_{team_name}_{st_key}_{rn}", use_container_width=True):
                                        st.session_state[f"open_mapcfg_{d}_{team_name}_{rn}"] = not st.session_state.get(f"open_mapcfg_{d}_{team_name}_{rn}", False)
                            
                                if st.session_state.get(f"open_mapcfg_{d}_{team_name}_{rn}", False):
                                    csp1, csp2 = st.columns([3, 2], vertical_alignment='center')
                                    with csp1:
                                        new_sp = st.text_input('Startpunkt', value=sp, key=f"sp_{d}_{team_name}_{rn}")
                                    with csp2:
                                        new_ret = st.checkbox('Tagasi algusesse', value=ret, key=f"ret_{d}_{team_name}_{rn}")
                                    if st.button('Save', key=f"savecfg_{d}_{team_name}_{rn}", use_container_width=False):
                                        set_setting(settings_key, json.dumps({'start': new_sp.strip(), 'return': bool(new_ret)}))
                                        st.toast('Kaardi seaded salvestatud', icon='✅')
                            
                                if st.session_state.get(open_key, True):
                                    for it in ring_rows:
                                        window = (it.get('delivery_window') or '').strip() or '—'
                                        addr = (it.get('address') or '').strip() or (it.get('ship_address') or '').strip() or '—'
                                        phone = (it.get('phone') or '').strip() or '—'
                                        client = ((it.get('client_name') or '').strip() or (it.get('recipient_name') or '').strip() or '—')
                                        svc_icons = _service_icons(it.get('service_tag') or '')
                                        col_ctrl, row_exp, row_rm = st.columns([0.9, 8.2, 0.9], vertical_alignment='center')
                                        with col_ctrl:
                                            if st.button('⬆', key=f"up_{st_key}_{it['ri_id']}"):
                                                move_route_item(int(it['ri_id']), -1); st.rerun()
                                        if row_rm.button('✖', key=f"rm_{st_key}_{it['ri_id']}"):
                                            remove_route_item(int(it['ri_id'])); st.rerun()
                                        header = f"{svc_icons} {client} • ⏱️ {window} • 📍 {addr} • 📞 {phone}"
                                        with row_exp:
                                            with st.expander(header, expanded=False):
                                                if (it.get('notes') or '').strip():
                                                    st.markdown('**📝 Notes**')
                                                    st.write(it.get('notes') or '')
                                                items = (it.get('items_compact') or '').strip()
                                                if items:
                                                    st.markdown('**📦 Items**')
                                                    pdf_path = (it.get('stored_path') or '').strip()
                                                    if pdf_path and os.path.exists(pdf_path):
                                                        with open(pdf_path, 'rb') as _f:
                                                            _pdf_bytes = _f.read()
                                                        st.download_button('📄 PDF', data=_pdf_bytes, file_name=os.path.basename(pdf_path), mime='application/pdf', use_container_width=False, key=f"dl_ring_{st_key}_{it['ri_id']}")
                                                    else:
                                                        st.button('📄 PDF', disabled=True)
                                                    _render_items_boxes(items, title='', show_title=False)
                                                if st_key == 'CANCELLED':
                                                    st.write(f"**Põhjus:** {it.get('worker_status_reason') or '—'}")
                                                    st.write(f"**Märkus:** {it.get('worker_status_note') or '—'}")
                        st.divider()

                    st.divider()



# ---- TAB 4: Workers (vaade) ----
with tabs[1]:
    st.subheader("Workers")
    st.caption("This view shows jobs assigned to workers (from Route Planner). Change settings in the ⚙️ Settings tab.")

    users = list_users(active_only=True)
    if not users:
        st.info("Töötajaid ei leitud. Lisa töötajad vahelehel ⚙️ Settings.")
    else:
        # kiire filter
        names = [u["name"] for u in users]
        pick = st.selectbox("Select worker", ["(all)"] + names)

        def _render_user(u):
            uid = int(u["id"])
            open_items = list_user_route_items(uid, status="OPEN")
            done_items = list_user_route_items(uid, status="DONE")
            canc_items = list_user_route_items(uid, status="CANCELLED")

            # Header row: emoji only
            header = f"👷 {u['name']}  •  🟦 {len(open_items)}  •  ✅ {len(done_items)}  •  ⛔ {len(canc_items)}"

            # Per-user UI state (no expanders nesting!)
            if "worker_tab_open" not in st.session_state:
                st.session_state.worker_tab_open = {}   # uid -> bool
            if "worker_tab_mode" not in st.session_state:
                st.session_state.worker_tab_mode = {}   # uid -> 'OPEN'|'DONE'|'CANCELLED'
            if "worker_tab_day" not in st.session_state:
                st.session_state.worker_tab_day = {}    # (uid, mode) -> 'YYYY-MM-DD'

            # Clickable worker row (button) – opens/closes the section
            if st.button(header, key=f"wk_open_{uid}", use_container_width=True):
                st.session_state.worker_tab_open[uid] = not st.session_state.worker_tab_open.get(uid, False)

            if not st.session_state.worker_tab_open.get(uid, False):
                return

            # --- Mode chooser (3 options)
            mode = st.session_state.worker_tab_mode.get(uid) or "OPEN"
            c1, c2, c3 = st.columns(3)
            with c1:
                if st.button(f"🟦 Open ({len(open_items)})", key=f"wk_mode_open_{uid}", use_container_width=True):
                    mode = "OPEN"
                    st.session_state.worker_tab_mode[uid] = mode
            with c2:
                if st.button(f"✅ Done ({len(done_items)})", key=f"wk_mode_done_{uid}", use_container_width=True):
                    mode = "DONE"
                    st.session_state.worker_tab_mode[uid] = mode
            with c3:
                if st.button(f"⛔ Cancelled ({len(canc_items)})", key=f"wk_mode_canc_{uid}", use_container_width=True):
                    mode = "CANCELLED"
                    st.session_state.worker_tab_mode[uid] = mode

            items = open_items if mode == "OPEN" else (done_items if mode == "DONE" else canc_items)
            if not items:
                st.info("No jobs in this view.")
                st.divider()
                return

            # --- Dates list (buttons, not expanders)
            by_day = {}
            for it in items:
                d = (it.get("route_date") or "").strip() or "—"
                by_day.setdefault(d, []).append(it)

            days_sorted = sorted([d for d in by_day.keys() if d != "—"], reverse=True)
            if "—" in by_day:
                days_sorted.append("—")

            sel_key = (uid, mode)
            sel_day = st.session_state.worker_tab_day.get(sel_key)
            if sel_day not in by_day:
                sel_day = days_sorted[0]
                st.session_state.worker_tab_day[sel_key] = sel_day

            # render day buttons in a single column (keeps layout similar to other tabs)
            for d in days_sorted:
                n = len(by_day[d])
                label = f"📅 {fmt_date(d)} ({n})" if d != "—" else f"📅 (kuupäev puudub) ({n})"
                if st.button(label, key=f"wk_day_{uid}_{mode}_{d}", use_container_width=True):
                    st.session_state.worker_tab_day[sel_key] = d
                    sel_day = d

            st.divider()

            # --- Job list (expanders at ONE level only)
            for it in by_day.get(sel_day, []):
                window = (it.get("delivery_window") or "").strip() or "—"
                addr = (it.get("address") or "").strip() or (it.get("ship_address") or "").strip() or "—"
                phone = (it.get("phone") or "").strip() or "—"
                client = ((it.get("client_name") or "").strip() or (it.get("recipient_name") or "").strip() or "—")
                svc_icons = _service_icons(it.get("service_tag") or "")

                summary = f"{svc_icons} {client} • ⏱️ {window} • 📍 {addr} • 📞 {phone}"

                with st.expander(summary, expanded=False):
                    if (it.get("notes") or "").strip():
                        st.markdown("**📝 Notes**")
                        st.write(it.get("notes") or "")

                    items_txt = (it.get("items_compact") or "").strip()
                    if items_txt:
                        st.markdown("**📦 Items**")
                        pdf_path = (it.get("stored_path") or "").strip()
                        if pdf_path and os.path.exists(pdf_path):
                            with open(pdf_path, "rb") as _f:
                                _pdf_bytes = _f.read()
                            st.download_button(
                                "📄 PDF",
                                data=_pdf_bytes,
                                file_name=os.path.basename(pdf_path),
                                mime="application/pdf",
                                use_container_width=False,
                                key=f"dl_wk_{uid}_{mode}_{it['ri_id']}",
                            )
                        else:
                            st.button("📄 PDF", disabled=True)
                        _render_items_boxes(items_txt, title="", show_title=False)

                    if mode == "CANCELLED":
                        st.write(f"**Põhjus:** {it.get('worker_status_reason') or '—'}")
                        st.write(f"**Märkus:** {it.get('worker_status_note') or '—'}")

            st.divider()

        if pick != "(all)":
            u = next((x for x in users if x["name"] == pick), None)
            if u:
                _render_user(u)
        else:
            for u in users:
                _render_user(u)

# ---- TAB 5: Jobs ----
with tabs[3]:
    st.subheader("Jobs (done & cancelled)")

    conn = db()
    cur = conn.cursor()
    cur.execute(
        """
        SELECT r.route_date AS d, COUNT(*) AS n
        FROM route_items ri
        JOIN routes r ON r.id = ri.route_id
        WHERE COALESCE(ri.worker_status,'OPEN') IN ('DONE','CANCELLED')
        GROUP BY r.route_date AND ri.worker_status IN ('DONE','CANCELLED')
        ORDER BY r.route_date DESC
        """
    )
    days = cur.fetchall() or []

    if not days:
        st.info("No done or cancelled jobs found.")
    else:
        if "open_work_days" not in st.session_state:
            st.session_state.open_work_days = {}

        for row in days:
            d = row["d"]
            n = int(row["n"] or 0)
            # täislaiuses kuupäeva nupp
            if st.button(f"📅 {fmt_date(d)} ({n})", key=f"workday_{d}", use_container_width=True):
                st.session_state.open_work_days[d] = not st.session_state.open_work_days.get(d, False)

            if not st.session_state.open_work_days.get(d, False):
                continue

            # Päeva tööd: grupi tiimi kaupa
            cur.execute(
                """
                SELECT
                    ri.id AS ri_id,
                    ri.worker_status AS ri_status,
                    COALESCE(GROUP_CONCAT(u.name, ', '), '') AS worker_names,
                    o.*
                FROM route_items ri
                JOIN orders o ON o.id = ri.order_id
                JOIN routes r ON r.id = ri.route_id
                LEFT JOIN route_item_users riu ON riu.ri_id = ri.id
                LEFT JOIN users u ON u.id = riu.user_id
                WHERE r.route_date = ?
                  AND COALESCE(ri.worker_status,'OPEN') IN ('DONE','CANCELLED')
                GROUP BY ri.id
                ORDER BY worker_names, o.delivery_window, o.id
                """,
                (d,),
            )
            rows = cur.fetchall() or []
            # sqlite row -> dict
            items = [dict(x) for x in rows]

            teams_map = {}
            for it in items:
                teams_map.setdefault(it.get("worker_names") or "—", []).append(it)

            for team_name, its in teams_map.items():
                st.markdown(f"#### {team_name} ({len(its)})")

                done = [x for x in its if (x.get("ri_status") or "OPEN") == "DONE"]
                canc = [x for x in its if (x.get("ri_status") or "OPEN") == "CANCELLED"]

                def _render_done_list(title, lst, icon):
                    if not lst:
                        return
                    st.markdown(f"**{icon} {title} ({len(lst)})**")
                    for it in lst:
                        client = ((it.get("client_name") or it.get("recipient_name") or "—") or "—").strip()
                        window = (it.get("time_window") or it.get("delivery_window") or "").strip() or "—"
                        addr = ((it.get("address") or it.get("ship_address") or it.get("delivery_address") or "—") or "—").strip()
                        phone = ((it.get("phone") or it.get("recipient_phone") or "") or "").strip() or "—"
                        svc_icons = _service_icons(it.get('service') or it.get('service_tag') or it.get('service_tag') or '')

                        label = f"{svc_icons} {client} • ⏱️ {window} • 📍 {addr} • 📞 {phone}"

                        open_key = "jobs_open_id"
                        cur_id = int(it.get("ri_id") or it.get("id") or 0)
                        if open_key not in st.session_state:
                            st.session_state[open_key] = None
                        if st.button(label, key=f"jobrow_{title}_{cur_id}", use_container_width=True):
                            st.session_state[open_key] = None if st.session_state[open_key] == cur_id else cur_id
                        if st.session_state[open_key] == cur_id:

                            notes = (it.get("notes") or "").strip()
                            if notes:
                                st.markdown("**📝 Notes**")
                                st.write(notes)
                            items_txt = (it.get("items_compact") or "").strip()
                            if items_txt:
                                _render_items_boxes(items_txt, title="📦 Items")
                            # PDF download, kui olemas
                            pdf_path = (it.get("stored_path") or "").strip()
                            if pdf_path and os.path.exists(pdf_path):
                                with open(pdf_path, "rb") as f:
                                    pdf_bytes = f.read()
                                st.download_button(
                                    "📄 PDF",
                                    data=pdf_bytes,
                                    file_name=os.path.basename(pdf_path),
                                    mime="application/pdf",
                                    key=f"workpdf_{d}_{it.get('id')}_{it.get('ri_id')}",
                                )

                _render_done_list("Done", done, "✅")
                _render_done_list("Cancelled", canc, "⛔")
                st.markdown("---")