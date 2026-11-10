#!/usr/bin/env python3
"""
ecoDMS -> Paperless-ngx Import (abgespeckte Version).

Importiert nur die Felder, die in deinem ecoDMS-Export tatsaechlich vorkommen.
Die benoetigten Custom Fields werden beim Start automatisch per API angelegt,
falls sie in Paperless noch nicht existieren.

Konfiguration ueber Umgebungsvariablen (kein Token mehr im Code):
  PAPERLESS_URL     (Default: http://localhost:8000)
  PAPERLESS_TOKEN   (Pflicht)
  ECODMS_ARCHIVE    (Default: ./archive/ - Ordner mit export.xml und den Dokumenten)

Beispiele:
  python ecodmstopaperless.py --dry-run
  python ecodmstopaperless.py --start 0 --end 100
"""
import argparse
import hashlib
import logging
import mimetypes
import os
import pathlib
import sqlite3
import sys
import time
from xml.dom import minidom

import requests

PAPERLESS_URL = os.environ.get("PAPERLESS_URL", "http://localhost:8000").rstrip("/")
PAPERLESS_TOKEN = os.environ.get("PAPERLESS_TOKEN", "")
ARCHIVE_FOLDER = os.environ.get("ECODMS_ARCHIVE", "./archive/")
VERIFY_TLS = False  # True oder Pfad zum Zertifikat, falls HTTPS mit echtem Zertifikat

# Dateitypen, bei denen das Original statt der PDF-Repraesentation genommen wird
SUPPORTED_SUFFIXES = {".pdf", ".jpg", ".tif", ".odt", ".odp", ".ods",
                      ".docx", ".doc", ".txt", ".ppt", ".pptx", ".xls", ".xlsx"}

ADD_NOTE_WITH_RAW_XML = True      # Roh-XML als Notiz am Dokument ablegen
SET_OWNER_FROM_ECODMS = True      # Besitzer = ecoDMS-User (muss in Paperless existieren)
SKIP_TRASHED = True               # Dokumente im ecoDMS-Papierkorb ueberspringen
TASK_POLL_INTERVAL = 0.5
TASK_TIMEOUT = int(os.environ.get("TASK_TIMEOUT", "180"))

# Custom Fields, die angelegt/benutzt werden (Name -> Datentyp).
# "Status" wird als Auswahlfeld angelegt; die Optionen werden aus den Daten ermittelt.
CUSTOM_FIELDS = {
    "ecoDMS ID": "integer",
    "Revision": "string",
    "Status": "select",
    "Ordner": "string",
    "Hauptordner": "string",
    "Letzte Änderung": "date",
    "Zurückgestellt bis": "date",
    "Bearbeitet von": "string",
    "Ordnerpfad": "string",
}

log = logging.getLogger("ecodms2paperless")
session = requests.Session()


# --------------------------------------------------------------------------- XML

def text(node, tag):
    """Text eines Kindelements; leere Platzhalter ('null', '---') werden zu ''."""
    els = node.getElementsByTagName(tag)
    if els and els[0].firstChild is not None:
        value = (els[0].firstChild.nodeValue or "").strip()
        return "" if value in ("null", "---") else value
    return ""


def to_date(value):
    """'2025-11-30 21:37:09.595381' oder '2025-11-30' -> '2025-11-30'."""
    value = (value or "").strip()
    return value[:10] if len(value) >= 10 else ""


def newest_version(document):
    versions = document.getElementsByTagName("Version")
    best = versions[0]
    for v in versions:
        if float(text(v, "revision") or 0) > float(text(best, "revision") or 0):
            best = v
    return best


def parse_metadata(version):
    status = text(version, "status")
    ordner = text(version, "ordner")
    hauptordner = text(version, "hauptordner")

    tags = []
    for t in (status, hauptordner, ordner):
        if t and t not in tags:
            tags.append(t[:127])
    for key in text(version, "ordner-extkey").split(","):
        key = key.strip()
        if key and key not in tags:
            tags.append(key[:127])

    parent = version.parentNode
    trashed = parent is not None and parent.getAttribute("trashed") == "true"

    return {
        "title": text(version, "bemerkung")[:127],
        "created": to_date(text(version, "datum")),
        "document_type": text(version, "dokumentenart"),
        "tags": tags,
        "trashed": trashed,
        "cf": {
            "Revision": text(version, "revision"),
            "Status": status,
            "Ordner": ordner,
            "Hauptordner": hauptordner,
            "Letzte Änderung": to_date(text(version, "letzte-änderung")),
            "Zurückgestellt bis": to_date(text(version, "zurückgestellt-bis")),
            "Bearbeitet von": text(version, "bearbeitet-von"),
        },
    }


def parse_file_info(document):
    files_el = document.getElementsByTagName("files")[0]
    doc_id = files_el.getAttribute("id")
    filename = ARCHIVE_FOLDER + files_el.getAttribute("filePath")
    orig = files_el.getAttribute("origname")
    owner = None

    versions = files_el.getElementsByTagName("fileVersion")
    if versions:
        owner = text(versions[0], "user") or None
        best = max(versions, key=lambda fv: int(fv.getAttribute("version") or 0))
        if pathlib.Path(best.getAttribute("origname")).suffix.lower() in SUPPORTED_SUFFIXES:
            orig = best.getAttribute("origname")
            filename = ARCHIVE_FOLDER + best.getAttribute("filePath")

    pdf_filename = pdf_orig = None
    for pf in files_el.getElementsByTagName("pdfFile"):
        path_attr = pf.getAttribute("filePath")
        if path_attr:
            pdf_filename = ARCHIVE_FOLDER + path_attr
            pdf_orig = pf.getAttribute("origName") or pf.getAttribute("origname") or path_attr
    return {
        "id": doc_id,
        "filename": filename,
        "origname": orig,
        "pdf_filename": pdf_filename,
        "pdf_origname": pdf_orig,
        "owner": owner,
        "mime": mimetypes.guess_type(filename)[0],
        "raw_xml": document.toxml(),
    }


def load_folder_paths(db_path):
    """Liest den Ordnerbaum aus der ecoDMS-Datenbank (export.data, SQLite).

    Rueckgabe: {ecoDMS-Dokument-ID (str): 'Hauptordner\\Unterordner\\Ordner'}
    """
    con = sqlite3.connect(f"file:{db_path}?mode=ro", uri=True)
    try:
        nodes = {oid: (name, parent) for oid, name, parent in
                 con.execute("select oid, name, parentid from systemordner")}

        def full_path(oid):
            parts, seen = [], set()
            while oid in nodes and oid not in seen:
                seen.add(oid)
                name, parent = nodes[oid]
                parts.append(name)
                oid = parent
            return "\\".join(reversed(parts))

        best = {}  # docid -> (revision, pfad)
        for docid, folder, revision in con.execute(
                "select docid, folder, revision from klassifizierung"):
            if folder not in nodes:   # z.B. '0' = nicht zugeordnet
                continue
            try:
                rev = float(revision)
            except (TypeError, ValueError):
                rev = 0.0
            if str(docid) not in best or rev >= best[str(docid)][0]:
                best[str(docid)] = (rev, full_path(folder))
        return {k: v[1] for k, v in best.items()}
    finally:
        con.close()


# ------------------------------------------------------------------- Paperless

def api(method, path, **kwargs):
    url = path if path.startswith("http") else f"{PAPERLESS_URL}{path}"
    r = session.request(method, url, verify=VERIFY_TLS, **kwargs)
    return r


def get_all(path):
    results, url = [], path
    while url:
        r = api("GET", url)
        r.raise_for_status()
        data = r.json()
        results += data["results"]
        url = data.get("next")
    return results


def ensure_named(endpoint, names):
    """Tags / Dokumenttypen anlegen. Automatisches Matching wird deaktiviert."""
    existing = {x["name"]: x["id"] for x in get_all(f"/api/{endpoint}/")}
    for name in sorted(set(n for n in names if n)):
        if name in existing:
            continue
        r = api("POST", f"/api/{endpoint}/",
                json={"name": name, "matching_algorithm": 0})
        if r.status_code in (200, 201):
            existing[name] = r.json()["id"]
        else:
            log.error("%s '%s' konnte nicht angelegt werden: %s", endpoint, name, r.text)
    return existing


def ensure_tag_tree(paths):
    """Legt verschachtelte Tags an (Hauptordner > Unterordner > Ordner).

    paths: Menge von Tupeln, die alle Praefixe enthaelt, z.B. ('Hauptordner',),
           ('Hauptordner', 'Unterordner'), ('Hauptordner', 'Unterordner', 'Ordner').
    Rueckgabe: {Tupel: Tag-ID} oder None, wenn der Server keine Eltern-Tags kennt.
    """
    existing = get_all("/api/tags/")
    if existing and "parent" not in existing[0]:
        return None
    index = {(t["name"], t.get("parent")): t["id"] for t in existing}
    result = {}

    # Paperless erlaubt jeden Tag-Namen nur einmal. Kommt ein Ordnername an mehreren
    # Stellen im Baum vor, wird er als "Name (Eltern-Tag)" angelegt.
    counts = {}
    for p in paths:
        counts[p[-1]] = counts.get(p[-1], 0) + 1

    def display_name(p):
        if counts[p[-1]] > 1 and len(p) > 1:
            return f"{p[-1]} ({p[-2]})"
        return p[-1]

    for path in sorted(paths, key=lambda p: (len(p), p)):
        parent = result[path[:-1]] if len(path) > 1 else None
        name = display_name(path)
        key = (name, parent)
        if key not in index:
            payload = {"name": name, "matching_algorithm": 0}
            if parent is not None:
                payload["parent"] = parent
            r = api("POST", "/api/tags/", json=payload)
            if r.status_code not in (200, 201) and parent is not None:
                # Evtl. Namenskollision (gleicher Name unter anderem Eltern-Tag)
                log.warning("Tag %s konnte nicht unter dem Eltern-Tag angelegt werden (%s) - "
                            "versuche eindeutigen Namen", " > ".join(path), r.text[:200])
                payload["name"] = " / ".join(path[-2:])
                r = api("POST", "/api/tags/", json=payload)
            if r.status_code not in (200, 201):
                log.error("Tag %s konnte nicht angelegt werden: %s", " > ".join(path), r.text)
                return None
            data = r.json()
            if parent is not None and data.get("parent") != parent:
                log.warning("Server hat den Eltern-Tag ignoriert - Fallback auf flache Tags")
                return None
            index[key] = data["id"]
        result[path] = index[key]
    return result


def ensure_custom_fields(status_values):
    """Legt fehlende Custom Fields an und liefert Name -> {id, type, options}."""
    existing = {f["name"]: f for f in get_all("/api/custom_fields/")}
    result = {}
    for name, dtype in CUSTOM_FIELDS.items():
        field = existing.get(name)
        if field is None:
            payload = {"name": name, "data_type": dtype}
            if dtype == "select":
                payload["extra_data"] = {
                    "select_options": [{"label": s} for s in sorted(status_values)]
                }
            r = api("POST", "/api/custom_fields/", json=payload)
            if r.status_code not in (200, 201):
                log.error("Custom Field '%s' konnte nicht angelegt werden: %s", name, r.text)
                continue
            field = r.json()
            log.info("Custom Field angelegt: %s (%s)", name, dtype)

        if dtype == "select" and field.get("id") and name in existing:
            have = {(o.get("label") if isinstance(o, dict) else o)
                    for o in (field.get("extra_data") or {}).get("select_options") or []}
            missing = sorted(v for v in status_values if v not in have)
            if missing:
                opts = list((field.get("extra_data") or {}).get("select_options") or [])
                opts += [{"label": m} for m in missing]
                r = api("PATCH", f"/api/custom_fields/{field['id']}/",
                        json={"extra_data": {"select_options": opts}})
                if r.ok:
                    field = r.json()
                    log.info("Status-Optionen ergaenzt: %s", ", ".join(missing))
                else:
                    log.error("Optionen konnten nicht ergaenzt werden: %s", r.text[:300])

        options = {}
        if dtype == "select":
            opts = (field.get("extra_data") or {}).get("select_options") or []
            for i, o in enumerate(opts):
                if isinstance(o, dict):
                    options[o.get("label")] = o.get("id")
                else:  # aeltere Paperless-Versionen: Liste von Strings, Wert = Index
                    options[o] = i
        result[name] = {"id": field["id"], "type": dtype, "options": options}
    return result


_user_cache = {}


def get_user_id(username):
    if not _user_cache:
        for u in get_all("/api/users/"):
            _user_cache[u["username"]] = u["id"]
    return _user_cache.get(username)


def build_custom_field_values(doc, fields):
    values = []
    cf = dict(doc["cf"])
    cf["ecoDMS ID"] = doc["id"]
    for name, value in cf.items():
        if value in ("", None) or name not in fields:
            continue
        f = fields[name]
        if f["type"] == "integer":
            value = int(value)
        elif f["type"] == "select":
            if f["options"].get(value) is None:
                log.warning("Option '%s' fuer Feld '%s' nicht vorhanden bzw. ohne ID (bekannt: %s) "
                            "- Wert wird uebersprungen", value, name, f["options"])
                continue
            value = f["options"][value]
        values.append({"field": f["id"], "value": value})
    return values


def wait_for_task(task_id):
    deadline = time.time() + TASK_TIMEOUT
    last = None
    while time.time() < deadline:
        r = api("GET", "/api/tasks/", params={"task_id": task_id})
        last = r
        if r.ok:
            data = r.json()
            # Aeltere Versionen liefern eine Liste, neuere ein Objekt mit "results".
            if isinstance(data, dict):
                data = data.get("results", [data] if "status" in data else [])
            # Sicherstellen, dass es wirklich unser Task ist (Filter koennte ignoriert werden).
            data = [t for t in data if str(t.get("task_id")) == str(task_id)] or data
            if data:
                task = data[0]
                if str(task.get("status")).upper() in ("SUCCESS", "FAILURE", "REVOKED"):
                    return task
        time.sleep(TASK_POLL_INTERVAL)
    # Diagnose: letzte Antwort der Task-API ausgeben
    if last is not None:
        log.error("Task-ID: %r | letzte Antwort der Task-API: HTTP %s | %s",
                  task_id, last.status_code, last.text[:800])
    return None


def task_document_id(task):
    """Dokument-ID aus der Task-Antwort (alte und neue Paperless-Versionen)."""
    ids = task.get("related_document_ids")
    if ids:
        return ids[0]
    rd = task.get("result_data")
    if isinstance(rd, dict) and rd.get("document_id"):
        return rd["document_id"]
    rel = task.get("related_document")
    return int(rel) if rel else None


def find_by_checksum(path):
    """ID eines bereits importierten Dokuments anhand der MD5 der Originaldatei."""
    md5 = hashlib.md5(pathlib.Path(path).read_bytes()).hexdigest()
    r = api("GET", "/api/documents/", params={"checksum__iexact": md5})
    if r.ok and r.json().get("results"):
        return r.json()["results"][0]["id"]
    return None


def find_unprocessed(doc, fields):
    """Sucht ein bereits hochgeladenes Dokument, das noch kein Feld 'ecoDMS ID' hat.

    Wird fuer Dokumente gebraucht, deren Upload zwar ankam, die Nachbearbeitung
    (Custom Fields, Notiz) aber nicht lief, z.B. wegen eines Timeouts.
    """
    id_field = fields["ecoDMS ID"]["id"]
    candidates = []
    if doc["title"]:
        r = api("GET", "/api/documents/", params={"title__iexact": doc["title"], "page_size": 100})
        if r.ok:
            candidates = r.json().get("results", [])
    cid = find_by_checksum(doc["filename"]) if os.path.exists(doc["filename"]) else None
    if cid and cid not in [c["id"] for c in candidates]:
        rr = api("GET", f"/api/documents/{cid}/")
        if rr.ok:
            candidates.append(rr.json())
    # 1. Schon vollstaendig importiert (Feld 'ecoDMS ID' passt)? Dann nur Felder nochmals setzen.
    for c in candidates:
        for cf in c.get("custom_fields") or []:
            if cf.get("field") == id_field and str(cf.get("value")) == str(doc["id"]):
                return c["id"]
    # 2. Hochgeladen, aber ohne Nachbearbeitung (Feld 'ecoDMS ID' fehlt)
    free = [c for c in candidates
            if not any(cf.get("field") == id_field for cf in c.get("custom_fields") or [])]
    # Gleiches Erstellungsdatum bevorzugen
    free.sort(key=lambda c: (str(c.get("created", ""))[:10] != doc["created"], c["id"]))
    if len(free) > 1:
        log.warning("%s: %d passende unbearbeitete Dokumente gefunden (IDs %s) - nehme das erste",
                    doc["id"], len(free), [c["id"] for c in free])
    return free[0]["id"] if free else None


def build_upload_data(doc, tag_ids, type_ids, tag_tree):
    tag_list = [tag_ids[t] for t in doc["flat_tags"] if t in tag_ids]
    parts = doc["folder_parts"]
    if tag_tree and parts:
        # Blatt-Tag und alle Eltern-Tags explizit zuweisen
        tag_list += [tag_tree[parts[:i]] for i in range(1, len(parts) + 1)]
    data = {"tags": [str(t) for t in dict.fromkeys(tag_list)]}
    if doc["title"]:
        data["title"] = doc["title"]
    if doc["created"]:
        data["created"] = doc["created"]
    if doc["document_type"] in type_ids:
        data["document_type"] = str(type_ids[doc["document_type"]])
    return data


def upload(doc, data):
    """Laedt hoch; bei nicht unterstuetztem Dateityp wird die PDF-Darstellung probiert."""
    attempts = [(doc["filename"], doc["origname"])]
    if doc.get("pdf_filename"):
        attempts.append((doc["pdf_filename"], doc["pdf_origname"]))
    r = None
    for i, (path, name) in enumerate(attempts):
        with open(path, "rb") as fh:
            r = api("POST", "/api/documents/post_document/", data=data,
                    files={"document": (name, fh)})
        if r.status_code == 200:
            if i > 0:
                log.info("%s: PDF-Darstellung statt Original hochgeladen (%s)", doc["id"], name)
            return r.json()
        if "not supported" not in r.text or i == len(attempts) - 1:
            break
        log.warning("%s: Dateityp von '%s' wird nicht unterstuetzt - versuche PDF-Darstellung",
                    doc["id"], name)
    log.error("Upload von %s fehlgeschlagen: %s %s", doc["id"], r.status_code, r.text[:300])
    return None


def finalize(doc, paperless_id, data, fields):
    """Tags/Typ erzwingen, Custom Fields und Besitzer setzen, XML-Notiz anhaengen."""
    patch = {"tags": [int(t) for t in data["tags"]],
             "custom_fields": build_custom_field_values(doc, fields)}
    if "document_type" in data:
        patch["document_type"] = int(data["document_type"])
    if SET_OWNER_FROM_ECODMS and doc["owner"]:
        uid = get_user_id(doc["owner"])
        if uid:
            patch["owner"] = uid
        else:
            log.warning("Paperless-User '%s' nicht gefunden", doc["owner"])
    pr = api("PATCH", f"/api/documents/{paperless_id}/", json=patch)
    if not pr.ok:
        log.error("PATCH fuer Dokument %s fehlgeschlagen: HTTP %s | gesendet: %s | Antwort: %s",
                  paperless_id, pr.status_code, patch, pr.text[:500])
        return False
    res = pr.json()
    got_cf = len(res.get("custom_fields") or [])
    log.info("Paperless-Dokument %s: %d Tags, %d/%d Custom Fields gesetzt",
             paperless_id, len(res.get("tags") or []), got_cf, len(patch["custom_fields"]))
    if got_cf != len(patch["custom_fields"]):
        log.warning("Nicht alle Custom Fields uebernommen. Gesendet: %s | Antwort: %s",
                    patch["custom_fields"], res.get("custom_fields"))
    if ADD_NOTE_WITH_RAW_XML:
        nr = api("GET", f"/api/documents/{paperless_id}/notes/")
        already = nr.ok and any(n.get("note") == doc["raw_xml"] for n in nr.json())
        if not already:
            nr = api("POST", f"/api/documents/{paperless_id}/notes/", json={"note": doc["raw_xml"]})
            if not nr.ok:
                log.warning("Notiz fuer Dokument %s fehlgeschlagen: %s", paperless_id, nr.text)
    return True


def import_document(doc, tag_ids, type_ids, fields, tag_tree=None, repair=False, deferred=None):
    """Importiert ein Dokument. Rueckgabe: True bei Erfolg, sonst Fehlertext."""
    data = build_upload_data(doc, tag_ids, type_ids, tag_tree)

    if repair:
        existing = find_unprocessed(doc, fields)
        if existing:
            log.info("%s: bereits in Paperless als Dokument %s - hole Nachbearbeitung nach",
                     doc["id"], existing)
            return True if finalize(doc, existing, data, fields) else "PATCH fehlgeschlagen"

    task_id = upload(doc, data)
    if task_id is None:
        return "Upload fehlgeschlagen"

    task = wait_for_task(task_id)
    if not task:
        log.error("Timeout beim Warten auf Task fuer %s - wird am Ende nochmals geprueft", doc["id"])
        if deferred is not None:
            deferred.append((doc, task_id, data))
        return "Timeout"
    return finish_task(doc, task, data, fields)


def finish_task(doc, task, data, fields):
    paperless_id = task_document_id(task)
    if str(task.get("status")).upper() != "SUCCESS":
        log.warning("Task fuer %s nicht erfolgreich. Komplette Task-Antwort: %s",
                    doc["id"], str(task)[:1000])
        if not paperless_id:
            paperless_id = find_by_checksum(doc["filename"])
        if not paperless_id:
            return "Task fehlgeschlagen"
        log.info("Vorhandenes Dokument %s wird aktualisiert (Felder, Notiz)", paperless_id)
    return True if finalize(doc, paperless_id, data, fields) else "PATCH fehlgeschlagen"


# ------------------------------------------------------------------------ main

def main():
    ap = argparse.ArgumentParser(description="ecoDMS-Export nach Paperless-ngx importieren")
    ap.add_argument("--start", type=int, default=0)
    ap.add_argument("--end", type=int, default=-1)
    ap.add_argument("--xml", default=ARCHIVE_FOLDER + "export.xml")
    ap.add_argument("--dry-run", action="store_true",
                    help="Nur parsen und anzeigen, nichts an Paperless senden")
    ap.add_argument("--include-trashed", action="store_true")
    ap.add_argument("--flat-tags", action="store_true",
                    help="Keine verschachtelten Tags, nur flache Tags fuer Hauptordner/Ordner")
    ap.add_argument("--ids", default=None,
                    help="Nur diese ecoDMS-IDs verarbeiten (kommagetrennt), z.B. 465,749,750. "
                         "Aktiviert automatisch --repair")
    ap.add_argument("--repair", action="store_true",
                    help="Vor dem Upload pruefen, ob das Dokument schon in Paperless liegt, aber "
                         "noch keine ecoDMS-Felder hat; dann nur Nachbearbeitung statt Upload")
    ap.add_argument("--db", default=None,
                    help="ecoDMS-Datenbank (export.data) fuer den vollstaendigen Ordnerpfad; "
                         "Default: ../export.data relativ zur XML, falls vorhanden")
    args = ap.parse_args()

    logging.basicConfig(level=logging.INFO, format="%(levelname)s %(message)s")

    db_path = args.db or os.path.join(os.path.dirname(os.path.abspath(args.xml)), "../export.data")
    folder_paths = {}
    if os.path.exists(db_path):
        folder_paths = load_folder_paths(db_path)
        log.info("Ordnerbaum aus %s geladen (%d Dokumente)", db_path, len(folder_paths))
    else:
        log.warning("Keine Datenbank unter %s - 'Ordnerpfad' bleibt leer (siehe --db)", db_path)

    if not args.dry_run:
        if not PAPERLESS_TOKEN:
            sys.exit("PAPERLESS_TOKEN ist nicht gesetzt.")
        session.headers["Authorization"] = f"Token {PAPERLESS_TOKEN}"

    xml = minidom.parse(args.xml)
    documents = xml.getElementsByTagName("document")
    end = len(documents) if args.end in (-1,) or args.end > len(documents) else args.end

    wanted = {x.strip() for x in args.ids.split(",") if x.strip()} if args.ids else None
    repair = args.repair or bool(wanted)
    if wanted:
        args.start, end = 0, len(documents)

    docs = []
    all_parts = set()   # Ordner ALLER Dokumente, damit Tag-Namen immer gleich gebildet werden
    for d in documents[args.start:end]:
        info = parse_file_info(d)
        meta = parse_metadata(newest_version(d))
        meta["cf"]["Ordnerpfad"] = folder_paths.get(info["id"], "")
        meta["folder_parts"] = tuple(p for p in meta["cf"]["Ordnerpfad"].split("\\") if p)
        meta["flat_tags"] = list(meta["tags"])
        if meta["trashed"] and SKIP_TRASHED and not args.include_trashed:
            if not wanted:
                log.info("Ueberspringe %s (Papierkorb)", info["id"])
            continue
        all_parts.update(meta["folder_parts"][:i] for i in range(1, len(meta["folder_parts"]) + 1))
        if wanted and info["id"] not in wanted:
            continue
        if not os.path.exists(info["filename"]) and not args.dry_run:
            log.error("Datei fehlt fuer %s: %s", info["id"], info["filename"])
            continue
        docs.append(info | meta)

    if args.dry_run:
        for d in docs:
            print(d["id"], "|", d["title"], "|", d["created"], "|", d["document_type"],
                  "|", d["tags"], "|", d["cf"])
        print(f"{len(docs)} Dokumente wuerden importiert.")
        return

    status_values = {d["cf"]["Status"] for d in docs if d["cf"]["Status"]}
    fields = ensure_custom_fields(status_values)
    tag_tree = None
    if folder_paths and not args.flat_tags:
        tag_tree = ensure_tag_tree(all_parts)
        if tag_tree is None:
            log.warning("Verschachtelte Tags nicht moeglich - verwende flache Tags")
        else:
            # Hauptordner-/Ordner-Namen brauchen dann keine eigenen flachen Tags mehr
            for d in docs:
                if d["folder_parts"]:
                    skip = {d["cf"]["Hauptordner"], d["cf"]["Ordner"]}
                    d["flat_tags"] = [t for t in d["tags"] if t not in skip]

    tag_ids = ensure_named("tags", [t for d in docs for t in d["flat_tags"]])
    type_ids = ensure_named("document_types", [d["document_type"] for d in docs])

    if wanted:
        missing = wanted - {d["id"] for d in docs}
        if missing:
            log.warning("Nicht gefundene/uebersprungene IDs: %s", ", ".join(sorted(missing)))

    failed = []      # (ecoDMS-ID, Titel, Grund)
    deferred = []    # Dokumente, deren Task beim ersten Warten nicht fertig wurde
    for i, d in enumerate(docs, 1):
        log.info("[%d/%d] ecoDMS-ID %s: %s", i, len(docs), d["id"], d["title"])
        result = import_document(d, tag_ids, type_ids, fields, tag_tree,
                                 repair=repair, deferred=deferred)
        if result is not True and result != "Timeout":
            failed.append((d["id"], d["title"], result))

    # Zweite Runde fuer Timeouts: Paperless war evtl. nur langsam und ist jetzt fertig.
    for d, task_id, data in deferred:
        log.info("Pruefe erneut: ecoDMS-ID %s (%s)", d["id"], d["title"])
        task = wait_for_task(task_id)
        if not task:
            failed.append((d["id"], d["title"], "Timeout (Task laeuft noch)"))
            continue
        result = finish_task(d, task, data, fields)
        if result is not True:
            failed.append((d["id"], d["title"], result))

    if failed:
        log.error("%d Dokument(e) nicht vollstaendig importiert:", len(failed))
        for did, title, why in failed:
            log.error("  ecoDMS-ID %s | %s | %s", did, title, why)
        log.error("Nachbearbeitung: python %s --ids %s", os.path.basename(sys.argv[0]),
                  ",".join(f[0] for f in failed))
    else:
        log.info("Fertig: alle %d Dokumente importiert.", len(docs))


if __name__ == "__main__":
    main()
