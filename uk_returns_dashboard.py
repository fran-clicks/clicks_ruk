#!/usr/bin/env python3
"""
Clicks UK Returns Dashboard
Connects to Gorgias API and displays tickets tagged 'uk return'.
Search by tracking number, ticket ID, customer name, or email.

Usage:
  1. Set your credentials below (or use environment variables)
  2. Run: python uk_returns_dashboard.py
  3. Open: http://localhost:5050
"""

import os
import json
import re
import http.server
import socketserver
import urllib.request
import urllib.parse
import urllib.error
import base64
import ssl
import time
import threading
import tempfile
import io
import secrets
import hashlib
import http.cookies
from datetime import datetime

# Optional image processing support
try:
    from PIL import Image, ImageEnhance, ImageOps, ImageFilter
    import pytesseract
    OCR_AVAILABLE = True
    print("[OCR] pytesseract + Pillow loaded")
except ImportError:
    OCR_AVAILABLE = False
    print("[OCR] pytesseract/Pillow not available")

# Barcode reading — disabled due to stability issues on some systems
BARCODE_AVAILABLE = False

# ─── CONFIGURATION ───────────────────────────────────────────────────────────
GORGIAS_SUBDOMAIN = os.environ.get("GORGIAS_SUBDOMAIN", "clicks")  # e.g. "clickstech"
GORGIAS_API_KEY = os.environ.get("GORGIAS_API_KEY", "267775d052d96ac4583e41f3bc46370cdd4518958f90d236af068410d1361e38")
GORGIAS_EMAIL = os.environ.get("GORGIAS_EMAIL", "kp@clicks.tech")  # email associated with the API key
PORT = int(os.environ.get("PORT", os.environ.get("DASHBOARD_PORT", "5050")))
TAG_FILTER = "uk return"

# 17track — primary tracking provider (100 registrations/month, unlimited queries)
# Sign up free at: https://api.17track.net → get API key from Settings
TRACK17_API_KEY = os.environ.get("TRACK17_API_KEY", "E8F71A5DE9760A22746CC1324F2A24A3")

# ParcelsApp tracking — fallback (10 shipments/month)
# Get your API key at: https://parcelsapp.com/dashboard
PARCELSAPP_API_KEY = os.environ.get("PARCELSAPP_API_KEY", "")

# Dashboard authentication — shared team password
DASHBOARD_PASSWORD = os.environ.get("DASHBOARD_PASSWORD", "clicks2024")
# ─────────────────────────────────────────────────────────────────────────────

# Session store: {token: expiry_timestamp}
_sessions = {}
SESSION_TTL = 86400 * 7  # 7 days


def _create_session():
    token = secrets.token_hex(32)
    _sessions[token] = time.time() + SESSION_TTL
    return token


def _validate_session(token):
    if not token or token not in _sessions:
        return False
    if time.time() > _sessions[token]:
        del _sessions[token]
        return False
    return True


def _cleanup_sessions():
    now = time.time()
    expired = [t for t, exp in _sessions.items() if now > exp]
    for t in expired:
        del _sessions[t]

BASE_URL = f"https://{GORGIAS_SUBDOMAIN}.gorgias.com/api"


def gorgias_request(endpoint, params=None):
    """Make an authenticated GET request to the Gorgias API."""
    url = f"{BASE_URL}/{endpoint}"
    if params:
        url += "?" + urllib.parse.urlencode(params)

    credentials = base64.b64encode(f"{GORGIAS_EMAIL}:{GORGIAS_API_KEY}".encode()).decode()
    req = urllib.request.Request(url)
    req.add_header("Authorization", f"Basic {credentials}")
    req.add_header("Content-Type", "application/json")
    req.add_header("User-Agent", "ClicksDashboard/1.0")
    req.add_header("Accept", "application/json")

    ctx = ssl.create_default_context()
    try:
        with urllib.request.urlopen(req, context=ctx, timeout=30) as resp:
            raw = resp.read().decode()
            data = json.loads(raw)
            if isinstance(data, str):
                return {"error": f"Unexpected string response: {data[:200]}"}
            return data
    except urllib.error.HTTPError as e:
        body = e.read().decode() if e.fp else ""
        try:
            err_data = json.loads(body)
            msg = err_data.get("error", {})
            if isinstance(msg, dict):
                msg = msg.get("msg", body[:200])
            return {"error": f"HTTP {e.code}: {msg}"}
        except Exception:
            return {"error": f"HTTP {e.code}: {body[:200]}"}
    except Exception as e:
        return {"error": str(e)}


def gorgias_post(endpoint, payload):
    """Make an authenticated POST request to the Gorgias API."""
    url = f"{BASE_URL}/{endpoint}"
    body = json.dumps(payload).encode()

    credentials = base64.b64encode(f"{GORGIAS_EMAIL}:{GORGIAS_API_KEY}".encode()).decode()
    req = urllib.request.Request(url, data=body, method="POST")
    req.add_header("Authorization", f"Basic {credentials}")
    req.add_header("Content-Type", "application/json")
    req.add_header("User-Agent", "ClicksDashboard/1.0")
    req.add_header("Accept", "application/json")

    ctx = ssl.create_default_context()
    try:
        with urllib.request.urlopen(req, context=ctx, timeout=30) as resp:
            return json.loads(resp.read().decode())
    except urllib.error.HTTPError as e:
        body_text = e.read().decode() if e.fp else ""
        return {"error": f"HTTP {e.code}: {body_text[:200]}"}
    except Exception as e:
        return {"error": str(e)}


# ─── MULTI-PROVIDER TRACKING ─────────────────────────────────────────────────
# Priority: 17track (100 reg/month, unlimited queries) → ParcelsApp fallback
_tracking_cache = {}  # {tracking_number: {data, timestamp}}
TRACKING_CACHE_TTL = 600  # 10 minutes
_registered_17track = set()  # tracking numbers already registered with 17track


# Carrier code hints for 17track (speeds up detection)
CARRIER_HINTS_17TRACK = [
    (r'^[A-Z]{2}\d{9}[A-Z]{2}$', 3011),            # Royal Mail (intl format)
    (r'^[A-Z]{2}\s*\d{4}\s*\d{4}\s*\d\s*[A-Z]{2}$', 3011),  # Royal Mail spaced
    (r'^H[A-Z0-9]{10,20}$', 190143),                # Evri (Hermes UK)
    (r'^\d{14}$', 100003),                           # DPD UK
    (r'^1Z[A-Z0-9]{16}$', 100002),                   # UPS
    (r'^\d{12,15}$', 100001),                        # FedEx
    (r'^\d{10}$', 7021),                             # DHL Express
    (r'^JD\d{18}$', 7021),                           # DHL eCommerce
    (r'^TBA\d{10,}$', 190238),                       # Amazon Logistics
    (r'^GLS\d{9,}$', 3049),                          # GLS
]


def _detect_carrier_17track(tracking_number):
    """Try to detect 17track carrier code from tracking number format."""
    clean = tracking_number.replace(" ", "").upper()
    for pattern, code in CARRIER_HINTS_17TRACK:
        if re.match(pattern, clean):
            return code
    return None  # let 17track auto-detect


def track_shipment(tracking_number):
    """Look up tracking status. Tries 17track first, falls back to ParcelsApp."""
    # Check cache
    now = time.time()
    cached = _tracking_cache.get(tracking_number)
    if cached and (now - cached["timestamp"]) < TRACKING_CACHE_TTL:
        return cached["data"]

    result = None

    # Try 17track first
    if TRACK17_API_KEY:
        result = _track_via_17track(tracking_number)
        if result and not result.get("error"):
            _tracking_cache[tracking_number] = {"data": result, "timestamp": now}
            result["provider"] = "17track"
            return result

    # Fallback to ParcelsApp
    if PARCELSAPP_API_KEY:
        result = _track_via_parcelsapp(tracking_number)
        if result and not result.get("error"):
            _tracking_cache[tracking_number] = {"data": result, "timestamp": now}
            result["provider"] = "ParcelsApp"
            return result

    # Both failed or unconfigured
    if result and result.get("error"):
        return result
    return {"error": "No tracking API configured. Set TRACK17_API_KEY (recommended) or PARCELSAPP_API_KEY."}


# ─── 17TRACK PROVIDER ───────────────────────────────────────────────────────

def _track_via_17track(tracking_number):
    """Track via 17track API v2.2. Register once, then query unlimited."""
    ctx = ssl.create_default_context()

    try:
        # Step 1: Register if not already registered
        if tracking_number not in _registered_17track:
            reg_payload = [{"number": tracking_number}]
            carrier = _detect_carrier_17track(tracking_number)
            if carrier:
                reg_payload[0]["carrier"] = carrier

            req = urllib.request.Request(
                "https://api.17track.net/track/v2.2/register",
                data=json.dumps(reg_payload).encode(),
                method="POST",
            )
            req.add_header("Content-Type", "application/json")
            req.add_header("17token", TRACK17_API_KEY)
            req.add_header("Accept", "application/json")

            with urllib.request.urlopen(req, context=ctx, timeout=15) as resp:
                reg_result = json.loads(resp.read().decode())

            if reg_result.get("code") == 0:
                accepted = (reg_result.get("data") or {}).get("accepted") or []
                rejected = (reg_result.get("data") or {}).get("rejected") or []
                if accepted:
                    _registered_17track.add(tracking_number)
                elif rejected:
                    err = rejected[0].get("error", {})
                    err_code = err.get("code", 0)
                    # -18010012 = already registered (treat as success)
                    if err_code == -18010012 or "existed" in str(err.get("message", "")).lower():
                        _registered_17track.add(tracking_number)
                    else:
                        return {"error": f"17track rejected: {err.get('message', 'unknown error')}"}

            # Wait for 17track to fetch data
            time.sleep(3)

        # Step 2: Get tracking info (free, unlimited)
        query_payload = [{"number": tracking_number}]
        carrier = _detect_carrier_17track(tracking_number)
        if carrier:
            query_payload[0]["carrier"] = carrier

        req2 = urllib.request.Request(
            "https://api.17track.net/track/v2.2/gettrackinfo",
            data=json.dumps(query_payload).encode(),
            method="POST",
        )
        req2.add_header("Content-Type", "application/json")
        req2.add_header("17token", TRACK17_API_KEY)
        req2.add_header("Accept", "application/json")

        with urllib.request.urlopen(req2, context=ctx, timeout=15) as resp2:
            info_result = json.loads(resp2.read().decode())

        return _parse_17track_result(info_result)

    except urllib.error.HTTPError as e:
        body = e.read().decode() if e.fp else ""
        return {"error": f"17track HTTP {e.code}: {body[:200]}"}
    except Exception as e:
        return {"error": f"17track: {e}"}


def _parse_17track_result(data):
    """Parse 17track API response into our standard format."""
    if data.get("code") != 0:
        return {"error": f"17track error code {data.get('code')}: {data.get('message', '')}"}

    accepted = (data.get("data") or {}).get("accepted") or []
    if not accepted:
        return {"status": "unknown", "carrier": "", "checkpoints": [], "error": None}

    item = accepted[0]
    track_info = item.get("track_info") or {}

    # Status
    latest_status = track_info.get("latest_status") or {}
    status = latest_status.get("status", "unknown")

    # Carrier name
    carrier = ""
    tracking = track_info.get("tracking") or {}
    providers = tracking.get("providers") or []
    if providers:
        prov = providers[0] if isinstance(providers[0], dict) else {}
        provider_info = prov.get("provider") or {}
        carrier = provider_info.get("name", "")

    # Get events from the first provider
    checkpoints = []
    for prov in providers:
        if not isinstance(prov, dict):
            continue
        events = prov.get("events") or []
        for ev in events:
            if isinstance(ev, dict):
                checkpoints.append({
                    "date": ev.get("time_iso", ev.get("time", "")),
                    "status": ev.get("stage", ""),
                    "location": ev.get("location", ""),
                    "message": ev.get("description", ""),
                    "carrier": (prov.get("provider") or {}).get("name", carrier),
                })

    # Sort by date descending, take last 2
    checkpoints.sort(key=lambda c: c["date"], reverse=True)
    last_two = checkpoints[:2]

    return {
        "status": status,
        "carrier": carrier,
        "checkpoints": last_two,
        "total_checkpoints": len(checkpoints),
        "error": None,
    }


# ─── PARCELSAPP FALLBACK ────────────────────────────────────────────────────

def _track_via_parcelsapp(tracking_number):
    """Fallback: look up via ParcelsApp API."""
    ctx = ssl.create_default_context()
    try:
        submit_url = "https://parcelsapp.com/api/v3/shipments/tracking"
        payload = json.dumps({
            "shipments": [{"trackingId": tracking_number, "language": "en", "country": "GB"}],
            "apiKey": PARCELSAPP_API_KEY,
        }).encode()

        req = urllib.request.Request(submit_url, data=payload, method="POST")
        req.add_header("Content-Type", "application/json")
        req.add_header("Accept", "application/json")

        with urllib.request.urlopen(req, context=ctx, timeout=15) as resp:
            submit_result = json.loads(resp.read().decode())

        uuid = submit_result.get("uuid")
        if not uuid:
            if submit_result.get("shipments"):
                return _parse_parcelsapp_result(submit_result)
            return {"error": "ParcelsApp: no UUID returned"}

        poll_url = f"https://parcelsapp.com/api/v3/shipments/tracking?apiKey={PARCELSAPP_API_KEY}&uuid={uuid}"
        for _ in range(5):
            time.sleep(2)
            req2 = urllib.request.Request(poll_url)
            req2.add_header("Accept", "application/json")
            with urllib.request.urlopen(req2, context=ctx, timeout=15) as resp2:
                poll_result = json.loads(resp2.read().decode())
            if poll_result.get("done", False) or poll_result.get("shipments"):
                return _parse_parcelsapp_result(poll_result)

        return {"error": "ParcelsApp: tracking lookup timed out"}

    except urllib.error.HTTPError as e:
        body = e.read().decode() if e.fp else ""
        return {"error": f"ParcelsApp HTTP {e.code}: {body[:200]}"}
    except Exception as e:
        return {"error": f"ParcelsApp: {e}"}


def _parse_parcelsapp_result(data):
    """Parse ParcelsApp response into our standard format."""
    shipments = data.get("shipments") or []
    if not shipments:
        return {"status": "unknown", "carrier": "", "checkpoints": [], "error": None}

    ship = shipments[0] if isinstance(shipments[0], dict) else {}
    status = ship.get("status", "unknown")
    carrier = ""
    attributes = ship.get("attributes") or {}
    if isinstance(attributes, dict):
        carrier = attributes.get("carrier", "")

    states = ship.get("states") or []
    checkpoints = []
    for s in states:
        if isinstance(s, dict):
            checkpoints.append({
                "date": s.get("date", ""),
                "status": s.get("status", ""),
                "location": s.get("location", ""),
                "message": s.get("message", s.get("description", "")),
                "carrier": s.get("carrier", carrier),
            })

    checkpoints.sort(key=lambda c: c["date"], reverse=True)
    last_two = checkpoints[:2]

    return {
        "status": status,
        "carrier": carrier,
        "checkpoints": last_two,
        "total_checkpoints": len(checkpoints),
        "error": None,
    }


# ─── CACHE ───────────────────────────────────────────────────────────────────
_cache = {"tickets": [], "enriched": [], "timestamp": 0, "loading": False, "error": None}
CACHE_TTL = 300  # 5 minutes
API_DELAY = 0.8  # seconds between API calls to avoid rate limits
MAX_PAGES = 50   # max pages to scan
PAGE_SIZE = 100  # max per Gorgias API page


def fetch_all_tagged_tickets():
    """Fetch tickets with the 'UK Return' tag using Gorgias tag search."""
    # First, try the Gorgias ticket search endpoint which supports tag filtering
    all_tickets = []

    # Method: use /api/tickets endpoint and filter by tag name via query param
    # Gorgias supports: GET /api/tickets?tag=UK+Return
    cursor = None
    page = 0

    while page < MAX_PAGES:
        params = {"limit": PAGE_SIZE, "order_by": "updated_datetime:desc"}
        if cursor:
            params["cursor"] = cursor

        data = gorgias_request("tickets", params)
        if "error" in data:
            if all_tickets:
                print(f"  Warning: API error on page {page+1}, returning {len(all_tickets)} tickets found so far")
                break
            return {"error": data["error"], "tickets": []}

        tickets = data.get("data", [])
        if not isinstance(tickets, list) or not tickets:
            break

        for t in tickets:
            if not isinstance(t, dict):
                continue
            raw_tags = t.get("tags") or []
            tag_names = []
            for tag in raw_tags:
                if isinstance(tag, dict):
                    tag_names.append(tag.get("name", "").strip().lower())
            # Match any variation: "uk return", "UK Return", "UK Returns", etc.
            if any(TAG_FILTER.lower() in tn for tn in tag_names):
                all_tickets.append(t)

        cursor = data.get("meta", {}).get("next_cursor")
        page += 1
        if not cursor:
            break

        # Throttle to avoid rate limits
        time.sleep(API_DELAY)

    print(f"  Found {len(all_tickets)} tagged tickets across {page} page(s)")
    return {"tickets": all_tickets, "error": None}


def get_cached_tickets(force_refresh=False):
    """Return cached enriched tickets, refreshing if stale."""
    now = time.time()
    if not force_refresh and _cache["enriched"] and (now - _cache["timestamp"]) < CACHE_TTL:
        return {"tickets": _cache["enriched"], "error": None, "cached": True}

    if _cache["loading"]:
        # Another request is already loading — return whatever we have
        return {"tickets": _cache["enriched"], "error": None, "cached": True, "loading": True}

    _cache["loading"] = True
    try:
        result = fetch_all_tagged_tickets()
        if result.get("error") and not result.get("tickets"):
            _cache["loading"] = False
            return result

        enriched = []
        total = len(result["tickets"])
        for i, ticket in enumerate(result["tickets"]):
            print(f"  Enriching ticket {i+1}/{total}...")
            summary = extract_ticket_details(ticket)
            summary = enrich_with_messages(summary)
            enriched.append(summary)
            if i < total - 1:
                time.sleep(0.5)  # light throttle for message fetches

        _cache["enriched"] = enriched
        _cache["timestamp"] = time.time()
        _cache["error"] = None
        return {"tickets": enriched, "error": None, "cached": False}
    except Exception as e:
        return {"error": str(e), "tickets": _cache["enriched"]}
    finally:
        _cache["loading"] = False


# Order number pattern: CT followed by alphanumeric characters
ORDER_PATTERN = r'\b(CT[A-Za-z0-9]{2,20})\b'


def extract_ticket_details(ticket):
    """Extract relevant return details from a ticket."""
    if not isinstance(ticket, dict):
        return {"id": "?", "subject": "Invalid ticket data", "status": "unknown",
                "created": "", "updated": "", "channel": "", "assignee": "",
                "customer_name": "Unknown", "customer_email": "", "tags": [],
                "custom_fields": {}, "tracking_numbers": [], "device_info": [],
                "order_numbers": [], "latest_internal_note": "", "messages_count": 0,
                "full_text": "", "gorgias_url": ""}

    # Basic info
    ticket_id = ticket.get("id", "")
    subject = ticket.get("subject", "No subject")
    status = ticket.get("status", "unknown")
    created = ticket.get("created_datetime", "")
    updated = ticket.get("updated_datetime", "")
    channel = ticket.get("channel", "unknown")
    assignee = ticket.get("assignee_user") or {}
    assignee_name = ""
    if isinstance(assignee, dict):
        assignee_name = f"{assignee.get('firstname', '')} {assignee.get('lastname', '')}".strip()

    # Customer info
    customer = ticket.get("customer") or {}
    if isinstance(customer, dict):
        customer_name = customer.get("name", "Unknown")
        customer_email = customer.get("email", "N/A")
    else:
        customer_name = "Unknown"
        customer_email = "N/A"

    # Tags
    raw_tags = ticket.get("tags") or []
    tags = [tag.get("name", "") for tag in raw_tags if isinstance(tag, dict)]

    # Custom fields
    custom_fields = {}
    for field in (ticket.get("custom_fields") or []):
        if isinstance(field, dict):
            custom_fields[field.get("name", "")] = field.get("value", "")

    # Extract order numbers from subject, custom fields, and integrations
    order_numbers = set()
    # Check subject line
    order_numbers.update(re.findall(ORDER_PATTERN, subject, re.IGNORECASE))
    # Check custom fields
    for v in custom_fields.values():
        if isinstance(v, str):
            order_numbers.update(re.findall(ORDER_PATTERN, v, re.IGNORECASE))
    # Check Shopify integration data (Gorgias stores this in integrations/meta)
    for key in ("meta", "integrations", "external_id", "order_id"):
        val = ticket.get(key)
        if isinstance(val, str):
            order_numbers.update(re.findall(ORDER_PATTERN, val, re.IGNORECASE))
        elif isinstance(val, dict):
            for v in val.values():
                if isinstance(v, str):
                    order_numbers.update(re.findall(ORDER_PATTERN, v, re.IGNORECASE))

    return {
        "id": ticket_id,
        "subject": subject,
        "status": status,
        "created": created,
        "updated": updated,
        "channel": channel,
        "assignee": assignee_name,
        "customer_name": customer_name,
        "customer_email": customer_email,
        "tags": tags,
        "custom_fields": custom_fields,
        "order_numbers": list(order_numbers),
        "tracking_numbers": [],
        "device_info": [],
        "messages_count": 0,
        "full_text": "",
        "gorgias_url": f"https://{GORGIAS_SUBDOMAIN}.gorgias.com/app/ticket/{ticket_id}",
    }


def download_image(url):
    """Download image from URL, returns PIL Image or None."""
    try:
        req = urllib.request.Request(url)
        req.add_header("User-Agent", "ClicksDashboard/1.0")
        if "gorgias" in url.lower():
            credentials = base64.b64encode(f"{GORGIAS_EMAIL}:{GORGIAS_API_KEY}".encode()).decode()
            req.add_header("Authorization", f"Basic {credentials}")
        ctx = ssl.create_default_context()
        with urllib.request.urlopen(req, context=ctx, timeout=20) as resp:
            img_data = resp.read()
            print(f"  [IMG] Downloaded ({len(img_data)} bytes)")
        return Image.open(io.BytesIO(img_data))
    except Exception as e:
        print(f"  [IMG] Download failed: {e}")
        return None


def scan_barcodes_from_image(img):
    """Scan all barcodes/QR codes from an image. Returns list of decoded strings."""
    if not BARCODE_AVAILABLE:
        return []
    results = []
    try:
        # Try original image
        decoded = decode_barcodes(img)
        for d in decoded:
            text = d.data.decode('utf-8', errors='ignore').strip()
            if text:
                results.append(text)
                print(f"  [Barcode] Found {d.type}: {text}")

        if not results:
            # Try with preprocessing for angled/blurry photos
            for label, processed in _preprocess_for_barcode(img):
                decoded = decode_barcodes(processed)
                for d in decoded:
                    text = d.data.decode('utf-8', errors='ignore').strip()
                    if text and text not in results:
                        results.append(text)
                        print(f"  [Barcode:{label}] Found {d.type}: {text}")
                if results:
                    break
    except Exception as e:
        print(f"  [Barcode] Error: {e}")
    return results


def _preprocess_for_barcode(img):
    """Generate preprocessed versions of image for barcode scanning."""
    variants = []

    # Grayscale + high contrast
    g = img.convert("L")
    g = ImageEnhance.Contrast(g).enhance(2.5)
    g = ImageEnhance.Sharpness(g).enhance(2.0)
    variants.append(("contrast", g))

    # Upscaled
    w, h = g.size
    big = g.resize((w * 2, h * 2), Image.LANCZOS)
    variants.append(("upscale", big))

    # Binarized
    bw = g.point(lambda x: 255 if x > 128 else 0, '1')
    variants.append(("binary", bw))

    # Binarized upscaled
    bw_big = big.point(lambda x: 255 if x > 128 else 0, '1')
    variants.append(("binary+upscale", bw_big))

    return variants


def extract_text_from_image(url):
    """Extract tracking info from image: barcode scan first, OCR fallback."""
    img = download_image(url)
    if img is None:
        return {"barcodes": [], "ocr_text": ""}

    # 1. Try barcode scanning (fast and reliable)
    barcodes = scan_barcodes_from_image(img)
    if barcodes:
        return {"barcodes": barcodes, "ocr_text": ""}

    # 2. Fall back to OCR (slower, less reliable on photos)
    if not OCR_AVAILABLE:
        return {"barcodes": [], "ocr_text": ""}

    best_text = ""
    try:
        configs = [
            ("default", img.convert("L"), '--psm 6'),
            ("contrast", ImageEnhance.Contrast(img.convert("L")).enhance(2.5), '--psm 6'),
        ]
        # Also try upscaled
        g = ImageEnhance.Contrast(img.convert("L")).enhance(2.5)
        w, h = g.size
        big = g.resize((w * 3, h * 3), Image.LANCZOS)
        configs.append(("upscale", big, '--psm 6'))

        for name, proc, cfg in configs:
            text = pytesseract.image_to_string(proc, config=cfg).strip()
            has_tracking = bool(re.search(
                r'[A-Z]{2}\s*\d{4}\s*\d{4}\s*\d\s*[A-Z]{2}|\b[A-Z]{2}\d{9}[A-Z]{2}\b|\b1Z[A-Z0-9]{16}\b|\bJD\d{10,}\b',
                text
            ))
            print(f"  [OCR:{name}] {len(text)} chars, tracking={has_tracking}")
            if has_tracking:
                best_text = text
                break
            if len(text) > len(best_text):
                best_text = text
    except Exception as e:
        print(f"  [OCR] Error: {e}")

    return {"barcodes": [], "ocr_text": best_text}


def extract_images_from_message(msg):
    """Extract image URLs from message attachments and inline HTML images."""
    images = []

    # Check attachments
    for att in (msg.get("attachments") or []):
        if isinstance(att, dict):
            url = att.get("url", "")
            name = att.get("name", att.get("filename", ""))
            content_type = att.get("content_type", "")
            if url and (content_type.startswith("image/") or
                        re.search(r'\.(jpg|jpeg|png|gif|webp|heic)(\?|$)', url, re.IGNORECASE) or
                        re.search(r'\.(jpg|jpeg|png|gif|webp|heic)$', name, re.IGNORECASE)):
                images.append({"url": url, "name": name, "type": content_type})

    # Check inline images in HTML body
    html = msg.get("body_html", "") or ""
    for match in re.findall(r'<img[^>]+src=["\']([^"\']+)["\']', html):
        if match.startswith("http") and match not in [i["url"] for i in images]:
            images.append({"url": match, "name": os.path.basename(match.split("?")[0]), "type": "image"})

    return images


# Clicks product patterns — accessories for iPhones and Androids
PRODUCT_PATTERNS = [
    # "clicks X keyboard" or "clicks keyboard" — allows words between clicks and product type
    r'(clicks\s+(?:\w+\s+)*?(?:keyboard|case|cover|stand|mount|charger|cable|adapter|dock|holder|protector|grip))',
    # Specific Clicks product lines
    r'(clicks\s+(?:creator\s*edition|gen\s*\d|g\d|power|pro|mini|plus|max|classic)(?:\s+\w+)*)',
    # "clicks for iPhone/Android"
    r'(clicks\s+for\s+(?:iphone|android|samsung|pixel|google)[^\n,\.]{0,30})',
    # iPhone models
    r'(iphone\s*(?:1[0-6]|se|\d)\s*(?:pro\s*max|pro|plus|mini)?)',
    # Samsung models
    r'((?:samsung\s*)?galaxy\s*(?:s\d{2}|z\s*(?:fold|flip)\s*\d|a\d{2})[^\n,\.]{0,20})',
    # Google Pixel
    r'(pixel\s*\d[a-z]?\s*(?:pro|xl)?)',
    # "using a clicks ..." — captures product name after "using a/my clicks"
    r'(?:using|have|got|bought|ordered|received)\s+(?:a|my|the)\s+(clicks\s+\w[\w\s]{2,30}?)(?:\.|,|\n|$)',
]

TRACKING_PATTERNS = [
    # ── UK Carriers ──
    # Royal Mail / Parcelforce (with or without spaces): SE 3156 4320 3GB / SE315643203GB
    r'\b([A-Z]{2}\s*\d{4}\s*\d{4}\s*\d\s*[A-Z]{2})\b',
    r'\b([A-Z]{2}\d{9}[A-Z]{2})\b',
    # Evri / Hermes: JD followed by digits
    r'\b(JD\d{10,18})\b',
    # DPD UK: 15-digit numeric or alphanumeric
    r'\b(\d{15,16})\b',
    # Yodel: JJD followed by digits
    r'\b(JJD\d{16,18})\b',

    # ── European Carriers ──
    # GLS: numeric 8-12 digits or GLS prefix
    r'\b(GLS[\w-]{8,})\b',
    # DHL (international): 10-digit or 3S+digits or JD+digits
    r'\b(\d{10})\b(?=.*(?:dhl|parcel))',  # 10-digit near DHL mention
    r'\b(3S[A-Z0-9]{10,20})\b',           # DHL Parcel 3S prefix
    r'\b(JJD\d{16,20})\b',                # DHL Express
    # Deutsche Post / DHL Germany: 12-20 digits
    r'\b(00\d{12,20})\b',
    # PostNL (Netherlands): 3S prefix or 13-char alphanumeric
    r'\b(3S[A-Z0-9]{11,})\b',
    # Correos (Spain): 13-char alphanumeric starting with letters
    r'\b([A-Z]{2}\d{9}[A-Z]{2})\b',
    # Colissimo (France): 13-15 alphanumeric
    r'\b(\d[A-Z]\d{11,13})\b',
    # Poste Italiane: 2 letters + 9 digits + 2 letters (same as UPU)
    # (covered by Royal Mail pattern above)
    # La Poste / Swiss Post / other UPU: 2 letters + 9 digits + 2 letters
    # (covered above)

    # ── International / Global ──
    # UPS: 1Z followed by alphanumeric
    r'\b(1Z[A-Z0-9]{16,18})\b',
    # FedEx: 12, 15, or 20 digit
    r'\b(\d{12})\b(?=.*(?:fedex|fed\s*ex))',
    r'\b(\d{20})\b',
    # USPS: 20-22 digit or starts with 94
    r'\b(94\d{18,22})\b',
    # TNT/FedEx: GE/TT prefix + digits
    r'\b([GT][EN]\d{9,})\b',
    # Amazon Logistics: TBA followed by digits
    r'\b(TBA\d{10,15})\b',

    # ── Generic fallback ──
    # "tracking: XXXXX" or "tracking number: XXXXX" — explicit label
    r'(?:tracking\s*(?:number|code|no|#)?|track(?:ing)?)[:\s#]+([A-Za-z0-9]{8,30})',
]

ISSUE_PATTERNS = [
    r'(?:issue|problem|fault|defect|broken|damaged|not\s*working|stopped\s*working|cracked|scratched|malfunction)[:\s]+([^\n\.]{5,100})',
    r'((?:screen|button|battery|charging|bluetooth|connectivity|keys?|typing|hinge|speaker|microphone|camera)[^\n\.]{0,40}(?:issue|problem|broken|not\s*work|fault|defect|stuck|loose|cracked))',
    r'((?:won\'?t|doesn\'?t|can\'?t|cannot|will\s*not|does\s*not)\s+(?:charge|connect|pair|turn\s*on|work|type|respond)[^\n\.]{0,60})',
]


def enrich_with_messages(ticket_summary):
    """Fetch full messages for a ticket to extract more details."""
    tid = ticket_summary["id"]
    data = gorgias_request(f"tickets/{tid}/messages", {"limit": 100})
    if "error" not in data:
        messages = data.get("data", [])
        if not isinstance(messages, list):
            return ticket_summary
        ticket_summary_copy = dict(ticket_summary)

        tracking_numbers = set()
        device_info = set()
        issues_found = set()
        order_numbers = set(ticket_summary_copy.get("order_numbers", []))
        latest_internal_note = ""
        all_text = []
        all_images = []
        ocr_text_combined = ""

        for msg in messages:
            if not isinstance(msg, dict):
                continue
            body = msg.get("body_text", "") or ""
            html = msg.get("body_html", "") or ""
            body_clean = body if body else re.sub(r'<[^>]+>', ' ', html)
            all_text.append(body_clean)

            if msg.get("channel", "") == "internal-note":
                latest_internal_note = body_clean.strip()[:500]

            # Extract images from this message
            msg_images = extract_images_from_message(msg)
            all_images.extend(msg_images)

            # Find tracking numbers in text
            for p in TRACKING_PATTERNS:
                tracking_numbers.update(re.findall(p, body_clean, re.IGNORECASE))

            # Find product/device references
            for p in PRODUCT_PATTERNS:
                matches = re.findall(p, body_clean, re.IGNORECASE)
                device_info.update(m.strip() for m in matches if len(m.strip()) > 2)

            # Find issue descriptions
            for p in ISSUE_PATTERNS:
                matches = re.findall(p, body_clean, re.IGNORECASE)
                issues_found.update(m.strip() for m in matches if len(m.strip()) > 4)

            # Find order numbers (CT prefix)
            order_numbers.update(re.findall(ORDER_PATTERN, body_clean, re.IGNORECASE))

        # Scan images for barcodes and OCR text
        if (BARCODE_AVAILABLE or OCR_AVAILABLE) and all_images:
            for img_info in all_images[:5]:
                result = extract_text_from_image(img_info["url"])

                # Barcodes — direct tracking numbers
                for bc in result["barcodes"]:
                    # Clean barcode: remove spaces for uniform format
                    cleaned = bc.strip()
                    if len(cleaned) >= 6:
                        tracking_numbers.add(cleaned)
                        print(f"  [+] Tracking from barcode: {cleaned}")

                # OCR text — try to extract tracking patterns
                ocr_text = result["ocr_text"]
                if ocr_text:
                    ocr_text_combined += " " + ocr_text
                    for p in TRACKING_PATTERNS:
                        ocr_matches = re.findall(p, ocr_text, re.IGNORECASE)
                        for m in ocr_matches:
                            tracking_numbers.add(m)

        # Clean up tracking numbers: normalize spaces, deduplicate, remove false positives
        TRACKING_BLACKLIST = {
            'information', 'confirmed', 'delivered', 'available', 'received',
            'processed', 'generated', 'provided', 'attached', 'included',
            'following', 'reference', 'regarding', 'mentioned', 'customers',
            'something', 'returning', 'wednesday', 'thursday', 'saturday',
        }
        clean_tracking = set()
        for tn in tracking_numbers:
            cleaned = re.sub(r'\s+', ' ', tn).strip()
            # Skip common English words caught by generic pattern
            if cleaned.lower().rstrip(' (from image)') in TRACKING_BLACKLIST:
                continue
            # Skip if it's all letters (not a real tracking number)
            core = cleaned.replace(' (from image)', '').replace(' ', '')
            if core.isalpha():
                continue
            if len(cleaned) >= 8:
                clean_tracking.add(cleaned)
        ticket_summary_copy["tracking_numbers"] = list(clean_tracking)
        # Uppercase order numbers for consistency
        ticket_summary_copy["order_numbers"] = sorted(set(o.upper() for o in order_numbers))
        # Clean up product names: capitalize nicely
        clean_devices = set()
        for d in device_info:
            d = re.sub(r'\s+', ' ', d).strip().rstrip('.,;:')
            if len(d) > 3:
                clean_devices.add(d.title() if d.islower() else d)
        ticket_summary_copy["device_info"] = list(clean_devices)
        ticket_summary_copy["issues"] = list(issues_found)
        ticket_summary_copy["images"] = all_images[:20]  # cap at 20 images
        ticket_summary_copy["ocr_text"] = ocr_text_combined.strip()[:2000]
        ticket_summary_copy["latest_internal_note"] = latest_internal_note
        ticket_summary_copy["messages_count"] = len(messages)
        ticket_summary_copy["full_text"] = " ".join(all_text)[:5000]
        return ticket_summary_copy
    return ticket_summary


LOGIN_HTML = r"""<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="UTF-8">
<meta name="viewport" content="width=device-width, initial-scale=1.0">
<title>Login — Clicks UK Returns</title>
<style>
  :root {
    --bg: #0f1117;
    --card: #1a1d27;
    --border: #2a2d3a;
    --accent: #6c5ce7;
    --accent-light: #a29bfe;
    --text: #e2e4e9;
    --text-dim: #7f8694;
    --red: #ff6b6b;
  }
  * { margin: 0; padding: 0; box-sizing: border-box; }
  body {
    font-family: -apple-system, BlinkMacSystemFont, 'Segoe UI', Roboto, sans-serif;
    background: var(--bg);
    color: var(--text);
    min-height: 100vh;
    display: flex;
    align-items: center;
    justify-content: center;
  }
  .login-box {
    background: var(--card);
    border: 1px solid var(--border);
    border-radius: 16px;
    padding: 40px;
    width: 360px;
    text-align: center;
  }
  .login-box h1 {
    font-size: 20px;
    margin-bottom: 6px;
    color: var(--accent-light);
  }
  .login-box p {
    font-size: 13px;
    color: var(--text-dim);
    margin-bottom: 28px;
  }
  .login-box input {
    width: 100%;
    padding: 12px 16px;
    background: var(--bg);
    border: 1px solid var(--border);
    border-radius: 8px;
    color: var(--text);
    font-size: 14px;
    margin-bottom: 16px;
    outline: none;
  }
  .login-box input:focus { border-color: var(--accent); }
  .login-box button {
    width: 100%;
    padding: 12px;
    background: var(--accent);
    color: white;
    border: none;
    border-radius: 8px;
    font-size: 14px;
    font-weight: 600;
    cursor: pointer;
    transition: opacity 0.2s;
  }
  .login-box button:hover { opacity: 0.9; }
  .login-box button:disabled { opacity: 0.5; cursor: not-allowed; }
  .error {
    color: var(--red);
    font-size: 13px;
    margin-bottom: 12px;
    display: none;
  }
</style>
</head>
<body>
<div class="login-box">
  <h1>Clicks UK Returns</h1>
  <p>Enter the team password to access the dashboard</p>
  <div class="error" id="errorMsg">Incorrect password</div>
  <form onsubmit="doLogin(event)">
    <input type="password" id="pwd" placeholder="Password" autofocus autocomplete="current-password">
    <button type="submit" id="loginBtn">Sign in</button>
  </form>
</div>
<script>
async function doLogin(e) {
  e.preventDefault();
  const btn = document.getElementById('loginBtn');
  const err = document.getElementById('errorMsg');
  btn.disabled = true;
  err.style.display = 'none';
  try {
    const resp = await fetch('/auth/login', {
      method: 'POST',
      headers: {'Content-Type': 'application/json'},
      body: JSON.stringify({password: document.getElementById('pwd').value}),
    });
    const data = await resp.json();
    if (data.ok) {
      window.location.href = '/';
    } else {
      err.textContent = data.error || 'Incorrect password';
      err.style.display = 'block';
    }
  } catch(ex) {
    err.textContent = 'Connection error';
    err.style.display = 'block';
  }
  btn.disabled = false;
}
</script>
</body>
</html>"""


DASHBOARD_HTML = r"""<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="UTF-8">
<meta name="viewport" content="width=device-width, initial-scale=1.0">
<title>Clicks UK Returns Dashboard</title>
<style>
  :root {
    --bg: #0f1117;
    --card: #1a1d27;
    --card-hover: #22263a;
    --border: #2a2e3d;
    --text: #e4e6eb;
    --text-dim: #8b8fa3;
    --accent: #6c5ce7;
    --accent-light: #a29bfe;
    --green: #00b894;
    --yellow: #fdcb6e;
    --red: #e17055;
    --blue: #74b9ff;
    --orange: #f39c12;
  }
  * { box-sizing: border-box; margin: 0; padding: 0; }
  body {
    font-family: -apple-system, BlinkMacSystemFont, 'Segoe UI', Roboto, sans-serif;
    background: var(--bg);
    color: var(--text);
    min-height: 100vh;
  }
  .header {
    background: linear-gradient(135deg, #1a1d27 0%, #2d1f4e 100%);
    border-bottom: 1px solid var(--border);
    padding: 20px 32px;
    display: flex;
    align-items: center;
    justify-content: space-between;
    flex-wrap: wrap;
    gap: 16px;
  }
  .header h1 {
    font-size: 22px;
    font-weight: 700;
    display: flex;
    align-items: center;
    gap: 10px;
  }
  .header h1 span { font-size: 26px; }
  .header-right {
    display: flex;
    align-items: center;
    gap: 12px;
  }
  .btn {
    background: var(--accent);
    color: white;
    border: none;
    padding: 8px 18px;
    border-radius: 8px;
    font-size: 14px;
    cursor: pointer;
    font-weight: 500;
    transition: all 0.2s;
  }
  .btn:hover { background: var(--accent-light); }
  .btn:disabled { opacity: 0.5; cursor: not-allowed; }
  .btn-logout {
    background: transparent;
    border: 1px solid var(--border);
    color: var(--text-dim);
    font-size: 12px;
    padding: 6px 12px;
    text-decoration: none;
  }
  .btn-logout:hover { border-color: var(--red); color: var(--red); background: rgba(255,107,107,0.1); }
  .btn-outline {
    background: transparent;
    border: 1px solid var(--border);
    color: var(--text-dim);
  }
  .btn-outline:hover { border-color: var(--accent); color: var(--text); }
  .stats-bar {
    display: flex;
    gap: 16px;
    padding: 16px 32px;
    overflow-x: auto;
  }
  .stat-card {
    background: var(--card);
    border: 1px solid var(--border);
    border-radius: 12px;
    padding: 16px 24px;
    min-width: 140px;
    flex: 1;
  }
  .stat-card .label { font-size: 12px; color: var(--text-dim); text-transform: uppercase; letter-spacing: 0.5px; }
  .stat-card .value { font-size: 28px; font-weight: 700; margin-top: 4px; }
  .stat-card.open .value { color: var(--blue); }
  .stat-card.closed .value { color: var(--green); }
  .stat-card.pending .value { color: var(--yellow); }
  .stat-card.total .value { color: var(--accent-light); }

  .search-section {
    padding: 16px 32px;
  }
  .search-box {
    background: var(--card);
    border: 1px solid var(--border);
    border-radius: 12px;
    padding: 12px 20px;
    display: flex;
    align-items: center;
    gap: 12px;
    transition: border-color 0.2s;
  }
  .search-box:focus-within { border-color: var(--accent); }
  .search-box input {
    flex: 1;
    background: none;
    border: none;
    color: var(--text);
    font-size: 15px;
    outline: none;
  }
  .search-box input::placeholder { color: var(--text-dim); }
  .search-icon { color: var(--text-dim); font-size: 18px; }

  .filters {
    display: flex;
    gap: 8px;
    padding: 8px 32px 16px;
    flex-wrap: wrap;
  }
  .filter-chip {
    padding: 6px 14px;
    border-radius: 20px;
    font-size: 13px;
    border: 1px solid var(--border);
    background: var(--card);
    color: var(--text-dim);
    cursor: pointer;
    transition: all 0.2s;
  }
  .filter-chip:hover { border-color: var(--accent); color: var(--text); }
  .filter-chip.active { background: var(--accent); border-color: var(--accent); color: white; }

  .content { padding: 0 32px 32px; }

  .ticket-list {
    display: flex;
    flex-direction: column;
    gap: 8px;
  }
  .ticket-row {
    background: var(--card);
    border: 1px solid var(--border);
    border-radius: 10px;
    padding: 16px 20px;
    cursor: pointer;
    transition: all 0.15s;
    display: grid;
    grid-template-columns: 80px 1fr 120px 160px 160px 120px 120px 100px;
    align-items: center;
    gap: 16px;
  }
  .ticket-row:hover { background: var(--card-hover); border-color: var(--accent); transform: translateY(-1px); }
  .col-headers {
    background: transparent;
    border: none;
    padding: 8px 20px;
    font-size: 11px;
    font-weight: 600;
    color: var(--text-dim);
    text-transform: uppercase;
    letter-spacing: 0.5px;
    cursor: default;
  }
  .col-headers:hover { background: transparent; border-color: transparent; transform: none; }
  .ticket-id { font-weight: 600; color: var(--accent-light); font-size: 14px; }
  .ticket-subject {
    font-size: 14px;
    white-space: nowrap;
    overflow: hidden;
    text-overflow: ellipsis;
  }
  .ticket-product { font-size: 12px; color: var(--accent-light); white-space: nowrap; overflow: hidden; text-overflow: ellipsis; }
  .ticket-customer { font-size: 13px; color: var(--text-dim); }
  .ticket-date { font-size: 13px; color: var(--text-dim); }
  .ticket-assignee { font-size: 13px; color: var(--text-dim); }

  .status-badge {
    display: inline-block;
    padding: 4px 12px;
    border-radius: 20px;
    font-size: 12px;
    font-weight: 600;
    text-transform: uppercase;
    letter-spacing: 0.3px;
  }
  .status-open { background: rgba(116,185,255,0.15); color: var(--blue); }
  .status-closed { background: rgba(0,184,148,0.15); color: var(--green); }
  .status-snoozed { background: rgba(253,203,110,0.15); color: var(--yellow); }
  .order-num { font-family: monospace; font-weight: 600; color: var(--accent-light); }
  .add-tracking-row {
    display: flex;
    gap: 8px;
    margin-top: 10px;
    align-items: center;
  }
  .add-tracking-row input {
    flex: 1;
    background: var(--bg);
    border: 1px solid var(--border);
    color: var(--text);
    padding: 7px 12px;
    border-radius: 6px;
    font-size: 13px;
    outline: none;
  }
  .add-tracking-row input:focus { border-color: var(--accent); }
  .add-tracking-row input::placeholder { color: var(--text-dim); }
  .btn-sm {
    padding: 6px 14px;
    font-size: 12px;
    border-radius: 6px;
    border: none;
    cursor: pointer;
    font-weight: 600;
    transition: all 0.15s;
  }
  .btn-add {
    background: var(--accent);
    color: white;
  }
  .btn-add:hover { background: var(--accent-light); }
  .btn-add:disabled { opacity: 0.5; cursor: not-allowed; }
  .btn-plus {
    background: transparent;
    border: 1px dashed var(--border);
    color: var(--text-dim);
    padding: 4px 10px;
    border-radius: 6px;
    cursor: pointer;
    font-size: 14px;
    transition: all 0.15s;
  }
  .btn-plus:hover { border-color: var(--accent); color: var(--accent-light); }
  .tracking-success {
    color: var(--green);
    font-size: 12px;
    margin-top: 6px;
  }
  .tracking-error {
    color: var(--red);
    font-size: 12px;
    margin-top: 6px;
  }

  /* Detail panel */
  .detail-overlay {
    display: none;
    position: fixed;
    top: 0; left: 0; right: 0; bottom: 0;
    background: rgba(0,0,0,0.6);
    z-index: 100;
    justify-content: flex-end;
  }
  .detail-overlay.open { display: flex; }
  .detail-panel {
    width: 620px;
    max-width: 100%;
    background: var(--bg);
    border-left: 1px solid var(--border);
    overflow-y: auto;
    padding: 24px;
    animation: slideIn 0.2s ease;
  }
  @keyframes slideIn { from { transform: translateX(100%); } to { transform: translateX(0); } }
  .detail-close {
    float: right;
    background: none;
    border: none;
    color: var(--text-dim);
    font-size: 24px;
    cursor: pointer;
    padding: 4px 8px;
  }
  .detail-close:hover { color: var(--text); }
  .detail-header { margin-bottom: 24px; }
  .detail-header h2 { font-size: 18px; margin-bottom: 8px; padding-right: 40px; }
  .detail-section {
    background: var(--card);
    border: 1px solid var(--border);
    border-radius: 10px;
    padding: 16px;
    margin-bottom: 12px;
  }
  .detail-section h3 {
    font-size: 13px;
    color: var(--accent-light);
    text-transform: uppercase;
    letter-spacing: 0.5px;
    margin-bottom: 12px;
  }
  .detail-row {
    display: flex;
    justify-content: space-between;
    padding: 6px 0;
    border-bottom: 1px solid var(--border);
    font-size: 14px;
  }
  .detail-row:last-child { border-bottom: none; }
  .detail-row .label { color: var(--text-dim); }
  .detail-row .value { font-weight: 500; text-align: right; max-width: 60%; word-break: break-word; }
  .tag-list { display: flex; flex-wrap: wrap; gap: 6px; margin-top: 8px; }
  .tag {
    background: rgba(108,92,231,0.15);
    color: var(--accent-light);
    padding: 3px 10px;
    border-radius: 12px;
    font-size: 12px;
  }
  .note-box {
    background: rgba(253,203,110,0.08);
    border-left: 3px solid var(--yellow);
    padding: 12px;
    border-radius: 0 8px 8px 0;
    font-size: 13px;
    color: var(--text-dim);
    line-height: 1.5;
    margin-top: 8px;
    white-space: pre-wrap;
  }
  .open-gorgias {
    display: inline-block;
    margin-top: 16px;
    color: var(--accent-light);
    text-decoration: none;
    font-size: 14px;
  }
  .open-gorgias:hover { text-decoration: underline; }
  .image-grid {
    display: grid;
    grid-template-columns: repeat(auto-fill, minmax(120px, 1fr));
    gap: 8px;
    margin-top: 8px;
  }
  .image-grid img {
    width: 100%;
    height: 100px;
    object-fit: cover;
    border-radius: 6px;
    border: 1px solid var(--border);
    cursor: pointer;
    transition: transform 0.15s;
  }
  .image-grid img:hover { transform: scale(1.05); border-color: var(--accent); }
  .issue-tag {
    background: rgba(225,112,85,0.15);
    color: var(--red);
    padding: 4px 10px;
    border-radius: 12px;
    font-size: 12px;
    display: inline-block;
    margin: 3px;
  }
  .ocr-badge {
    font-size: 11px;
    color: var(--yellow);
    opacity: 0.7;
  }
  /* Tracking analysis */
  .tracking-item {
    background: rgba(255,255,255,0.03);
    border: 1px solid var(--border);
    border-radius: 8px;
    padding: 10px 12px;
    margin-bottom: 8px;
  }
  .tracking-header {
    display: flex;
    align-items: center;
    gap: 8px;
    flex-wrap: wrap;
    margin-bottom: 6px;
  }
  .tracking-code {
    font-family: monospace;
    font-size: 13px;
    color: var(--accent-light);
    font-weight: 600;
  }
  .tracking-status {
    font-size: 11px;
    padding: 2px 8px;
    border-radius: 10px;
    font-weight: 600;
    text-transform: capitalize;
  }
  .ts-delivered { background: rgba(76,175,80,0.2); color: #81c784; }
  .ts-transit { background: rgba(33,150,243,0.2); color: #64b5f6; }
  .ts-other { background: rgba(255,255,255,0.1); color: var(--text-dim); }
  .tracking-carrier {
    font-size: 11px;
    color: var(--text-dim);
    background: rgba(255,255,255,0.06);
    padding: 2px 6px;
    border-radius: 4px;
  }
  .tracking-provider {
    font-size: 10px;
    color: var(--text-dim);
    opacity: 0.6;
    font-style: italic;
  }
  .tracking-error {
    color: var(--red);
    font-size: 12px;
    margin-top: 4px;
  }
  .checkpoints { margin-top: 4px; }
  .checkpoint {
    display: flex;
    gap: 10px;
    align-items: baseline;
    padding: 4px 0;
    border-bottom: 1px solid rgba(255,255,255,0.04);
    font-size: 12px;
  }
  .checkpoint:last-child { border-bottom: none; }
  .cp-date { color: var(--text-dim); min-width: 130px; flex-shrink: 0; }
  .cp-msg { color: var(--text-light); }
  .cp-loc { color: var(--text-dim); font-style: italic; margin-left: auto; }
  .loader-sm {
    display: inline-block;
    width: 12px;
    height: 12px;
    border: 2px solid var(--border);
    border-top-color: var(--accent);
    border-radius: 50%;
    animation: spin 0.8s linear infinite;
    vertical-align: middle;
    margin-right: 6px;
  }
  /* Image lightbox */
  .lightbox {
    display: none;
    position: fixed;
    top: 0; left: 0; right: 0; bottom: 0;
    background: rgba(0,0,0,0.9);
    z-index: 200;
    justify-content: center;
    align-items: center;
    cursor: pointer;
  }
  .lightbox.open { display: flex; }
  .lightbox img { max-width: 90%; max-height: 90%; border-radius: 8px; }

  .loading {
    text-align: center;
    padding: 60px;
    color: var(--text-dim);
  }
  .loading .spinner {
    width: 36px; height: 36px;
    border: 3px solid var(--border);
    border-top-color: var(--accent);
    border-radius: 50%;
    animation: spin 0.8s linear infinite;
    margin: 0 auto 16px;
  }
  @keyframes spin { to { transform: rotate(360deg); } }

  .empty-state {
    text-align: center;
    padding: 60px;
    color: var(--text-dim);
  }
  .empty-state .icon { font-size: 48px; margin-bottom: 12px; }
  .error-banner {
    background: rgba(225,112,85,0.15);
    border: 1px solid var(--red);
    color: var(--red);
    padding: 12px 20px;
    border-radius: 8px;
    margin: 16px 32px;
    font-size: 14px;
  }

  @media (max-width: 900px) {
    .ticket-row {
      grid-template-columns: 70px 1fr 100px;
    }
    .ticket-customer, .ticket-date, .ticket-assignee, .ticket-product { display: none; }
    .col-headers div:nth-child(n+4):nth-child(-n+7) { display: none; }
    .detail-panel { width: 100%; }
  }
</style>
</head>
<body>

<div class="header">
  <h1><span>&#x1F4E6;</span> Clicks UK Returns</h1>
  <div class="header-right">
    <span id="lastUpdated" style="font-size:13px;color:var(--text-dim)"></span>
    <button class="btn" id="refreshBtn" onclick="loadTickets()">Refresh</button>
    <a href="/auth/logout" class="btn btn-logout" title="Sign out">Logout</a>
  </div>
</div>

<div class="stats-bar" id="statsBar">
  <div class="stat-card total"><div class="label">Total Returns</div><div class="value" id="statTotal">-</div></div>
  <div class="stat-card open"><div class="label">Open</div><div class="value" id="statOpen">-</div></div>
  <div class="stat-card pending"><div class="label">Snoozed</div><div class="value" id="statSnoozed">-</div></div>
  <div class="stat-card closed"><div class="label">Closed</div><div class="value" id="statClosed">-</div></div>
</div>

<div class="search-section">
  <div class="search-box">
    <span class="search-icon">&#128269;</span>
    <input type="text" id="searchInput" placeholder="Search by ticket #, tracking number, customer name or email..." oninput="filterTickets()">
  </div>
</div>

<div class="filters" id="filterBar">
  <button class="filter-chip active" data-filter="all" onclick="setFilter('all',this)">All</button>
  <button class="filter-chip" data-filter="open" onclick="setFilter('open',this)">Open</button>
  <button class="filter-chip" data-filter="snoozed" onclick="setFilter('snoozed',this)">Snoozed</button>
  <button class="filter-chip" data-filter="closed" onclick="setFilter('closed',this)">Closed</button>
</div>

<div id="errorBanner" class="error-banner" style="display:none"></div>

<div class="content">
  <div id="loadingState" class="loading">
    <div class="spinner"></div>
    <div>Loading UK return tickets from Gorgias...</div>
  </div>
  <div id="colHeaders" class="ticket-row col-headers" style="display:none">
    <div>ID</div><div>Subject</div><div>Order</div><div>Product</div><div>Customer</div><div>Updated</div><div>Assignee</div><div>Status</div>
  </div>
  <div id="ticketList" class="ticket-list" style="display:none"></div>
  <div id="emptyState" class="empty-state" style="display:none">
    <div class="icon">&#128270;</div>
    <div>No matching tickets found</div>
  </div>
</div>

<!-- Detail Panel -->
<div class="detail-overlay" id="detailOverlay" onclick="if(event.target===this)closeDetail()">
  <div class="detail-panel" id="detailPanel"></div>
</div>

<!-- Lightbox for full-size images -->
<div class="lightbox" id="lightbox" onclick="this.classList.remove('open')">
  <img id="lightboxImg" src="" alt="Full size">
</div>

<script>
let allTickets = [];
let currentFilter = 'all';

async function loadTickets() {
  const btn = document.getElementById('refreshBtn');
  const loading = document.getElementById('loadingState');
  const list = document.getElementById('ticketList');
  const empty = document.getElementById('emptyState');
  const errBanner = document.getElementById('errorBanner');

  const colHeaders = document.getElementById('colHeaders');
  btn.disabled = true;
  btn.textContent = 'Loading...';
  loading.style.display = 'block';
  list.style.display = 'none';
  colHeaders.style.display = 'none';
  empty.style.display = 'none';
  errBanner.style.display = 'none';

  try {
    const isRefresh = allTickets.length > 0;
    const resp = await fetch('/api/tickets' + (isRefresh ? '?refresh=1' : ''));
    if (resp.status === 401) { window.location.href = '/login'; return; }
    const data = await resp.json();

    if (data.error) {
      errBanner.textContent = 'API Error: ' + data.error;
      errBanner.style.display = 'block';
      loading.style.display = 'none';
      btn.disabled = false;
      btn.textContent = 'Refresh';
      return;
    }

    allTickets = data.tickets || [];
    updateStats();
    filterTickets();
    document.getElementById('lastUpdated').textContent = 'Updated ' + new Date().toLocaleTimeString();
  } catch (e) {
    errBanner.textContent = 'Connection error: ' + e.message;
    errBanner.style.display = 'block';
  }

  loading.style.display = 'none';
  btn.disabled = false;
  btn.textContent = 'Refresh';
}

function updateStats() {
  document.getElementById('statTotal').textContent = allTickets.length;
  document.getElementById('statOpen').textContent = allTickets.filter(t => t.status === 'open').length;
  document.getElementById('statSnoozed').textContent = allTickets.filter(t => t.status === 'snoozed').length;
  document.getElementById('statClosed').textContent = allTickets.filter(t => t.status === 'closed').length;
}

function setFilter(filter, chip) {
  currentFilter = filter;
  document.querySelectorAll('.filter-chip').forEach(c => c.classList.remove('active'));
  chip.classList.add('active');
  filterTickets();
}

function filterTickets() {
  const query = document.getElementById('searchInput').value.toLowerCase().trim();
  const list = document.getElementById('ticketList');
  const empty = document.getElementById('emptyState');
  const colHeaders = document.getElementById('colHeaders');

  let filtered = allTickets;

  // Status filter
  if (currentFilter !== 'all') {
    filtered = filtered.filter(t => t.status === currentFilter);
  }

  // Search filter
  if (query) {
    filtered = filtered.filter(t => {
      const searchable = [
        String(t.id),
        t.subject,
        t.customer_name,
        t.customer_email,
        ...(t.tracking_numbers || []),
        ...(t.device_info || []),
        ...(t.issues || []),
        ...(t.order_numbers || []),
        t.ocr_text || '',
        t.full_text || '',
        ...Object.values(t.custom_fields || {}),
      ].join(' ').toLowerCase();
      return searchable.includes(query);
    });
  }

  if (filtered.length === 0) {
    list.style.display = 'none';
    colHeaders.style.display = 'none';
    empty.style.display = 'block';
    return;
  }

  empty.style.display = 'none';
  colHeaders.style.display = 'grid';
  list.style.display = 'flex';
  list.innerHTML = filtered.map(t => `
    <div class="ticket-row" onclick="openDetail(${t.id})">
      <div class="ticket-id">#${t.id}</div>
      <div class="ticket-subject">${esc(t.subject)}</div>
      <div class="ticket-id" style="font-size:12px">${(t.order_numbers||[]).join(', ') || '-'}</div>
      <div class="ticket-product">${(t.device_info||[]).map(d => esc(d)).join(', ') || '-'}</div>
      <div class="ticket-customer">${esc(t.customer_name)}</div>
      <div class="ticket-date">${formatDate(t.updated)}</div>
      <div class="ticket-assignee">${esc(t.assignee || 'Unassigned')}</div>
      <div><span class="status-badge status-${t.status}">${t.status}</span></div>
    </div>
  `).join('');
}

function openDetail(id) {
  const t = allTickets.find(x => x.id === id);
  if (!t) return;

  const panel = document.getElementById('detailPanel');
  const trackingHtml = (t.tracking_numbers || []).length
    ? t.tracking_numbers.map(n => `<span class="tag">${esc(n)}</span>`).join('')
    : '<span style="color:var(--text-dim)">None detected</span>';

  const deviceHtml = (t.device_info || []).length
    ? t.device_info.map(d => `<span class="tag">${esc(d)}</span>`).join('')
    : '<span style="color:var(--text-dim)">None detected</span>';

  const customFieldsHtml = Object.entries(t.custom_fields || {}).map(([k, v]) =>
    `<div class="detail-row"><span class="label">${esc(k)}</span><span class="value">${esc(String(v))}</span></div>`
  ).join('') || '<div style="color:var(--text-dim);font-size:13px">No custom fields</div>';

  const tagsHtml = (t.tags || []).map(tag => `<span class="tag">${esc(tag)}</span>`).join('');

  const issuesHtml = (t.issues || []).length
    ? t.issues.map(i => `<span class="issue-tag">${esc(i)}</span>`).join('')
    : '<span style="color:var(--text-dim)">None detected</span>';

  const ordersHtml = (t.order_numbers || []).length
    ? t.order_numbers.map(o => `<span class="tag order-num">${esc(o)}</span>`).join('')
    : '<span style="color:var(--text-dim)">None found</span>';

  const imagesHtml = (t.images || []).length
    ? `<div class="image-grid">${t.images.map(img =>
        `<img src="${esc(img.url)}" alt="${esc(img.name)}" title="${esc(img.name)}" onclick="event.stopPropagation();openLightbox('${img.url.replace(/'/g, "\\'")}')" loading="lazy">`
      ).join('')}</div>`
    : '<span style="color:var(--text-dim)">No images attached</span>';

  panel.innerHTML = `
    <button class="detail-close" onclick="closeDetail()">&times;</button>
    <div class="detail-header">
      <h2>${esc(t.subject)}</h2>
      <span class="status-badge status-${t.status}">${t.status}</span>
    </div>

    <div class="detail-section">
      <h3>Customer</h3>
      <div class="detail-row"><span class="label">Name</span><span class="value">${esc(t.customer_name)}</span></div>
      <div class="detail-row"><span class="label">Email</span><span class="value">${esc(t.customer_email)}</span></div>
    </div>

    <div class="detail-section">
      <h3>Order Number</h3>
      <div class="tag-list">${ordersHtml}</div>
    </div>

    <div class="detail-section">
      <h3>Return Details</h3>
      <div class="detail-row"><span class="label">Ticket ID</span><span class="value">#${t.id}</span></div>
      <div class="detail-row"><span class="label">Channel</span><span class="value">${esc(t.channel)}</span></div>
      <div class="detail-row"><span class="label">Assignee</span><span class="value">${esc(t.assignee || 'Unassigned')}</span></div>
      <div class="detail-row"><span class="label">Created</span><span class="value">${formatDate(t.created)}</span></div>
      <div class="detail-row"><span class="label">Last Updated</span><span class="value">${formatDate(t.updated)}</span></div>
      <div class="detail-row"><span class="label">Messages</span><span class="value">${t.messages_count}</span></div>
    </div>

    <div class="detail-section">
      <h3>Product / Device Returned</h3>
      <div class="tag-list">${deviceHtml}</div>
    </div>

    <div class="detail-section">
      <h3>Reported Issue</h3>
      <div class="tag-list">${issuesHtml}</div>
    </div>

    <div class="detail-section">
      <h3>Tracking Numbers <button class="btn-plus" onclick="toggleAddTracking(${t.id})" title="Add tracking manually">+</button></h3>
      <div class="tag-list">${trackingHtml}</div>
      ${t.ocr_text ? '<div class="ocr-badge" style="margin-top:6px">* includes codes extracted from images via OCR</div>' : ''}
      <div id="addTrackingForm-${t.id}" style="display:none">
        <div class="add-tracking-row">
          <input type="text" id="trackingInput-${t.id}" placeholder="Enter tracking number..." onkeydown="if(event.key==='Enter')submitTracking(${t.id})">
          <button class="btn-sm btn-add" id="trackingSubmit-${t.id}" onclick="submitTracking(${t.id})">Add & Post Note</button>
        </div>
        <div id="trackingMsg-${t.id}"></div>
      </div>
    </div>

    <div class="detail-section">
      <h3>Tracking Analysis</h3>
      <div id="trackingAnalysis-${t.id}">
        ${(t.tracking_numbers || []).length
          ? '<div style="color:var(--text-dim);font-size:13px"><span class="loader-sm"></span> Loading tracking status...</div>'
          : '<div style="color:var(--text-dim);font-size:13px">No tracking numbers to analyse</div>'}
      </div>
    </div>

    <div class="detail-section">
      <h3>Attached Images (${(t.images||[]).length})</h3>
      ${imagesHtml}
    </div>

    <div class="detail-section">
      <h3>Tags</h3>
      <div class="tag-list">${tagsHtml}</div>
    </div>

    <div class="detail-section">
      <h3>Custom Fields</h3>
      ${customFieldsHtml}
    </div>

    ${t.latest_internal_note ? `
    <div class="detail-section">
      <h3>Latest Internal Note</h3>
      <div class="note-box">${esc(t.latest_internal_note)}</div>
    </div>` : ''}

    <a class="open-gorgias" href="${t.gorgias_url}" target="_blank">Open in Gorgias &#x2197;</a>
  `;

  document.getElementById('detailOverlay').classList.add('open');

  // Auto-fetch tracking analysis
  if ((t.tracking_numbers || []).length) {
    fetchTrackingAnalysis(t.id, t.tracking_numbers);
  }
}

async function fetchTrackingAnalysis(ticketId, trackingNumbers) {
  const container = document.getElementById('trackingAnalysis-' + ticketId);
  if (!container) return;

  let html = '';
  for (const tn of trackingNumbers) {
    try {
      const resp = await fetch('/api/track-status', {
        method: 'POST',
        headers: {'Content-Type': 'application/json'},
        body: JSON.stringify({tracking: tn}),
      });
      const data = await resp.json();

      if (data.error) {
        html += `<div class="tracking-item"><div class="tracking-code">${esc(tn)}</div><div class="tracking-error">${esc(data.error)}</div></div>`;
        continue;
      }

      const statusClass = (data.status || '').toLowerCase().includes('deliver') ? 'delivered'
        : (data.status || '').toLowerCase().includes('transit') ? 'transit' : 'other';

      let cpHtml = '';
      if (data.checkpoints && data.checkpoints.length) {
        cpHtml = data.checkpoints.map(cp => {
          const d = cp.date ? new Date(cp.date).toLocaleString('en-GB', {day:'2-digit',month:'short',year:'numeric',hour:'2-digit',minute:'2-digit'}) : '';
          return `<div class="checkpoint"><span class="cp-date">${esc(d)}</span><span class="cp-msg">${esc(cp.message || cp.status || '')}</span>${cp.location ? `<span class="cp-loc">${esc(cp.location)}</span>` : ''}</div>`;
        }).join('');
      } else {
        cpHtml = '<div style="color:var(--text-dim);font-size:12px">No checkpoints available yet</div>';
      }

      html += `<div class="tracking-item">
        <div class="tracking-header">
          <span class="tracking-code">${esc(tn)}</span>
          <span class="tracking-status ts-${statusClass}">${esc(data.status || 'unknown')}</span>
          ${data.carrier ? `<span class="tracking-carrier">${esc(data.carrier)}</span>` : ''}
          ${data.provider ? `<span class="tracking-provider">via ${esc(data.provider)}</span>` : ''}
        </div>
        <div class="checkpoints">${cpHtml}</div>
      </div>`;
    } catch (e) {
      html += `<div class="tracking-item"><div class="tracking-code">${esc(tn)}</div><div class="tracking-error">Failed to fetch: ${esc(e.message)}</div></div>`;
    }
  }

  container.innerHTML = html || '<div style="color:var(--text-dim);font-size:13px">No results</div>';
}

function closeDetail() {
  document.getElementById('detailOverlay').classList.remove('open');
}

function openLightbox(url) {
  document.getElementById('lightboxImg').src = url;
  document.getElementById('lightbox').classList.add('open');
}

function toggleAddTracking(ticketId) {
  const form = document.getElementById('addTrackingForm-' + ticketId);
  if (form.style.display === 'none') {
    form.style.display = 'block';
    document.getElementById('trackingInput-' + ticketId).focus();
  } else {
    form.style.display = 'none';
  }
}

async function submitTracking(ticketId) {
  const input = document.getElementById('trackingInput-' + ticketId);
  const btn = document.getElementById('trackingSubmit-' + ticketId);
  const msgDiv = document.getElementById('trackingMsg-' + ticketId);
  const tracking = input.value.trim();

  if (!tracking) {
    input.focus();
    return;
  }

  btn.disabled = true;
  btn.textContent = 'Posting...';
  msgDiv.innerHTML = '';

  try {
    const resp = await fetch('/api/add-tracking', {
      method: 'POST',
      headers: {'Content-Type': 'application/json'},
      body: JSON.stringify({ticket_id: ticketId, tracking: tracking})
    });
    const data = await resp.json();

    if (data.ok) {
      msgDiv.innerHTML = '<div class="tracking-success">Posted as internal note on ticket</div>';
      input.value = '';

      // Add to local display immediately
      const t = allTickets.find(x => x.id === ticketId);
      if (t) {
        if (!t.tracking_numbers) t.tracking_numbers = [];
        t.tracking_numbers.push(tracking);
      }
      // Update the tag list in the current detail view
      const tagList = document.getElementById('addTrackingForm-' + ticketId).previousElementSibling?.previousElementSibling;
      if (tagList && tagList.classList.contains('tag-list')) {
        const noneSpan = tagList.querySelector('span[style]');
        if (noneSpan && noneSpan.textContent === 'None detected') noneSpan.remove();
        const newTag = document.createElement('span');
        newTag.className = 'tag';
        newTag.textContent = tracking;
        tagList.appendChild(newTag);
      }

      setTimeout(() => { msgDiv.innerHTML = ''; }, 3000);
    } else {
      msgDiv.innerHTML = '<div class="tracking-error">Error: ' + esc(data.error || 'Unknown') + '</div>';
    }
  } catch (e) {
    msgDiv.innerHTML = '<div class="tracking-error">Connection error: ' + esc(e.message) + '</div>';
  }

  btn.disabled = false;
  btn.textContent = 'Add & Post Note';
}

function formatDate(iso) {
  if (!iso) return '-';
  const d = new Date(iso);
  return d.toLocaleDateString('en-GB', { day: '2-digit', month: 'short', year: 'numeric' }) +
    ' ' + d.toLocaleTimeString('en-GB', { hour: '2-digit', minute: '2-digit' });
}

function esc(s) {
  const d = document.createElement('div');
  d.textContent = s || '';
  return d.innerHTML;
}

document.addEventListener('keydown', e => {
  if (e.key === 'Escape') closeDetail();
  if (e.key === '/' && !['INPUT','TEXTAREA'].includes(document.activeElement.tagName)) {
    e.preventDefault();
    document.getElementById('searchInput').focus();
  }
});

// Load on start
loadTickets();
</script>
</body>
</html>"""


class DashboardHandler(http.server.BaseHTTPRequestHandler):
    def log_message(self, format, *args):
        print(f"[{datetime.now().strftime('%H:%M:%S')}] {args[0]}")

    def _get_session_token(self):
        cookie_header = self.headers.get("Cookie", "")
        cookies = http.cookies.SimpleCookie()
        try:
            cookies.load(cookie_header)
        except Exception:
            return None
        morsel = cookies.get("session")
        return morsel.value if morsel else None

    def _is_authenticated(self):
        token = self._get_session_token()
        return _validate_session(token)

    def _require_auth(self):
        """Returns True if request is authenticated, False if redirected to login."""
        if self._is_authenticated():
            return True
        # For API calls return 401, for pages redirect to login
        if self.path.startswith('/api/'):
            self.send_response(401)
            self.send_header('Content-Type', 'application/json')
            self.end_headers()
            self.wfile.write(json.dumps({"error": "Not authenticated"}).encode())
        else:
            self.send_response(302)
            self.send_header('Location', '/login')
            self.end_headers()
        return False

    def do_GET(self):
        # Public routes
        if self.path == '/login':
            self.send_response(200)
            self.send_header('Content-Type', 'text/html')
            self.end_headers()
            self.wfile.write(LOGIN_HTML.encode())
            return

        if self.path == '/auth/logout':
            token = self._get_session_token()
            if token and token in _sessions:
                del _sessions[token]
            self.send_response(302)
            self.send_header('Location', '/login')
            self.send_header('Set-Cookie', 'session=; Path=/; Max-Age=0; HttpOnly; SameSite=Strict')
            self.end_headers()
            return

        # All other routes require auth
        if not self._require_auth():
            return

        if self.path == '/':
            self.send_response(200)
            self.send_header('Content-Type', 'text/html')
            self.end_headers()
            self.wfile.write(DASHBOARD_HTML.encode())

        elif self.path in ('/api/tickets', '/api/tickets?refresh=1'):
            force = 'refresh=1' in self.path
            self.send_response(200)
            self.send_header('Content-Type', 'application/json')
            self.send_header('Cache-Control', 'no-cache')
            self.end_headers()

            result = get_cached_tickets(force_refresh=force)
            self.wfile.write(json.dumps(result).encode())

        elif self.path.startswith('/api/ticket/'):
            ticket_id = self.path.split('/')[-1]
            self.send_response(200)
            self.send_header('Content-Type', 'application/json')
            self.end_headers()
            data = gorgias_request(f"tickets/{ticket_id}")
            if "error" not in data:
                summary = extract_ticket_details(data)
                summary = enrich_with_messages(summary)
                self.wfile.write(json.dumps(summary).encode())
            else:
                self.wfile.write(json.dumps(data).encode())

        else:
            self.send_response(404)
            self.end_headers()

    def do_POST(self):
        # Login endpoint — public
        if self.path == '/auth/login':
            content_length = int(self.headers.get('Content-Length', 0))
            body = self.rfile.read(content_length)
            try:
                data = json.loads(body)
            except Exception:
                data = {}

            password = data.get("password", "")
            if password == DASHBOARD_PASSWORD:
                _cleanup_sessions()
                token = _create_session()
                self.send_response(200)
                self.send_header('Content-Type', 'application/json')
                secure_flag = "; Secure" if os.environ.get("RENDER") else ""
                self.send_header('Set-Cookie', f'session={token}; Path=/; Max-Age={SESSION_TTL}; HttpOnly; SameSite=Strict{secure_flag}')
                self.end_headers()
                self.wfile.write(json.dumps({"ok": True}).encode())
            else:
                self.send_response(200)
                self.send_header('Content-Type', 'application/json')
                self.end_headers()
                self.wfile.write(json.dumps({"ok": False, "error": "Incorrect password"}).encode())
            return

        # All other POST routes require auth
        if not self._require_auth():
            return

        if self.path == '/api/add-tracking':
            content_length = int(self.headers.get('Content-Length', 0))
            body = self.rfile.read(content_length)
            try:
                data = json.loads(body)
            except Exception:
                self.send_response(400)
                self.send_header('Content-Type', 'application/json')
                self.end_headers()
                self.wfile.write(json.dumps({"error": "Invalid JSON"}).encode())
                return

            ticket_id = data.get("ticket_id")
            tracking = data.get("tracking", "").strip()

            if not ticket_id or not tracking:
                self.send_response(400)
                self.send_header('Content-Type', 'application/json')
                self.end_headers()
                self.wfile.write(json.dumps({"error": "ticket_id and tracking required"}).encode())
                return

            # Post as internal note on the Gorgias ticket
            note_body = f"<b>Return tracking added via Dashboard:</b><br><code>{tracking}</code>"
            result = gorgias_post(f"tickets/{ticket_id}/messages", {
                "channel": "internal-note",
                "via": "api",
                "source": {"type": "internal-note", "from": {"name": "UK Returns Dashboard"}},
                "body_html": note_body,
            })

            self.send_response(200)
            self.send_header('Content-Type', 'application/json')
            self.end_headers()

            if "error" in result:
                self.wfile.write(json.dumps({"ok": False, "error": result["error"]}).encode())
            else:
                # Invalidate cache so next load picks up the new note
                _cache["timestamp"] = 0
                self.wfile.write(json.dumps({"ok": True, "message_id": result.get("id")}).encode())
        elif self.path == '/api/track-status':
            content_length = int(self.headers.get('Content-Length', 0))
            body = self.rfile.read(content_length)
            try:
                data = json.loads(body)
            except Exception:
                self.send_response(400)
                self.send_header('Content-Type', 'application/json')
                self.end_headers()
                self.wfile.write(json.dumps({"error": "Invalid JSON"}).encode())
                return

            tracking_number = data.get("tracking", "").strip()
            if not tracking_number:
                self.send_response(400)
                self.send_header('Content-Type', 'application/json')
                self.end_headers()
                self.wfile.write(json.dumps({"error": "tracking required"}).encode())
                return

            result = track_shipment(tracking_number)

            self.send_response(200)
            self.send_header('Content-Type', 'application/json')
            self.end_headers()
            self.wfile.write(json.dumps(result).encode())
        else:
            self.send_response(404)
            self.end_headers()


def ensure_ocr_deps():
    """Auto-install OCR + barcode dependencies into a local venv if not available."""
    global OCR_AVAILABLE
    if OCR_AVAILABLE:
        return  # already loaded

    import subprocess
    import sys

    script_dir = os.path.dirname(os.path.abspath(__file__))
    venv_dir = os.path.join(script_dir, ".dashboard_venv")
    venv_python = os.path.join(venv_dir, "bin", "python3")

    # If we're not already running inside the venv, set it up and re-exec
    if not sys.prefix.startswith(venv_dir):
        print("\n[Setup] OCR libraries missing. Setting up virtual environment...")

        # Create venv if needed
        if not os.path.exists(venv_python):
            print("[Setup] Creating venv at .dashboard_venv/ ...")
            subprocess.run([sys.executable, "-m", "venv", venv_dir], check=True)

        # Install deps
        pip = os.path.join(venv_dir, "bin", "pip")
        print("[Setup] Installing pytesseract and Pillow...")
        subprocess.run([pip, "install", "-q", "pytesseract", "Pillow"], check=True)

        # Re-exec this script under the venv python
        print("[Setup] Restarting with OCR support...\n")
        os.execv(venv_python, [venv_python] + sys.argv)


def main():
    if GORGIAS_SUBDOMAIN == "YOUR_SUBDOMAIN" or GORGIAS_API_KEY == "YOUR_API_KEY":
        print("\n" + "=" * 60)
        print("  SETUP REQUIRED")
        print("=" * 60)
        print("\n  Edit this file and set your Gorgias credentials:")
        print(f"    GORGIAS_SUBDOMAIN = 'your-store'")
        print(f"    GORGIAS_EMAIL     = 'your@email.com'")
        print(f"    GORGIAS_API_KEY   = 'your-api-key'")
        print("\n  Or use environment variables:")
        print("    export GORGIAS_SUBDOMAIN=your-store")
        print("    export GORGIAS_EMAIL=your@email.com")
        print("    export GORGIAS_API_KEY=your-api-key")
        print("\n  To get your API key:")
        print("    Gorgias > Settings > REST API > Create API Key")
        print("=" * 60 + "\n")
        return

    # Auto-install OCR if missing (skip on Render — no tesseract binary)
    if not os.environ.get("RENDER"):
        ensure_ocr_deps()

    HOST = os.environ.get("HOST", "0.0.0.0")
    socketserver.TCPServer.allow_reuse_address = True
    with socketserver.TCPServer((HOST, PORT), DashboardHandler) as httpd:
        print(f"\n{'=' * 60}")
        print(f"  Clicks UK Returns Dashboard")
        print(f"  Running at: http://localhost:{PORT}")
        print(f"  Connected to: {GORGIAS_SUBDOMAIN}.gorgias.com")
        print(f"  Filtering by tag: '{TAG_FILTER}'")
        print(f"  OCR: {'Enabled' if OCR_AVAILABLE else 'Disabled'}")
        print(f"  Press Ctrl+C to stop")
        print(f"{'=' * 60}\n")
        try:
            httpd.serve_forever()
        except KeyboardInterrupt:
            print("\nDashboard stopped.")


if __name__ == "__main__":
    main()
