#!/usr/bin/env python3
"""Mechanical evidence checker for litsweep artifacts.

For every quoted claim in a litsweep artifact (recent_progress[] and
solved_evidence), fetch the cited source_url and check the quote actually
appears there. No model judgment — pure fetch + string matching.

Matching: HTML is stripped, whitespace/unicode normalized. A quote counts as
FOUND if its normalized text appears as a substring, or if >= 80% of its
word 5-grams appear (tolerates ellipses and minor cleanup in quoting).

Verdicts per claim: found | not_found | fetch_failed
Artifact grade: PASS (all found), PARTIAL (>=1 not fetchable, none missing),
FAIL (>=1 quote definitively absent from its cited page).

Usage: verify_quotes.py <artifact.json | dir-of-artifacts> [--out report.json]
"""

import html
import json
import re
import subprocess
import sys
import time
import unicodedata
from pathlib import Path

UA = "Mozilla/5.0 (X11; Linux x86_64) AllMath-evidence-checker/1.0"


_BLOCK_MARKERS = ("Just a moment...", "Performing security verification",
                  "Attention Required! | Cloudflare", "Access denied")


def _curl(url: str) -> str | None:
    for attempt in range(3):
        r = subprocess.run(
            ["curl", "-sL", "--max-time", "90", "-A", UA, url],
            capture_output=True, text=True, errors="replace",
        )
        if r.returncode == 0 and len(r.stdout) > 500:
            head = r.stdout[:6000]
            if any(m in head for m in _BLOCK_MARKERS):
                return None  # bot-blocked; caller falls back to wayback
            if "web.archive.org" in url and ("Wayback Machine has not archived" in r.stdout
                                             or "This page is not available" in head):
                return None  # snapshot missing
            return r.stdout
        time.sleep(5 * (attempt + 1))
    return None


def _pdf_text(url: str) -> str | None:
    r = subprocess.run(["curl", "-sL", "--max-time", "120", "-A", UA, "-o", "/tmp/vq_doc.pdf", url])
    if r.returncode != 0:
        return None
    t = subprocess.run(["pdftotext", "/tmp/vq_doc.pdf", "-"], capture_output=True, text=True,
                       errors="replace")
    return t.stdout if t.returncode == 0 and len(t.stdout) > 500 else None


def fetch(url: str) -> str | None:
    """Fetch the cited page PLUS the obvious full-text behind it, concatenated.

    Quotes often come from a paper body while the artifact cites the landing
    page (arXiv abs, Zenodo record). Checking landing page + full text keeps
    the mechanical check strict about fabrication without flagging honest
    one-level-deep quoting.
    """
    if "www.erdosproblems.com" in url and "web.archive.org" not in url:
        url = "https://web.archive.org/web/2026id_/" + url
    # GitHub blob pages are JS-rendered; the quoted content is in the raw file
    m = re.match(r"https://github\.com/([^/]+/[^/]+)/blob/([^?#]+)", url)
    if m:
        url = f"https://raw.githubusercontent.com/{m.group(1)}/{m.group(2)}"
    parts = []
    page = _curl(url)
    if page is None and "web.archive.org" not in url:
        page = _curl("https://web.archive.org/web/2026id_/" + url)
    if page:
        parts.append(page)
    m = re.search(r"arxiv\.org/(?:abs|html)/([0-9]+\.[0-9]+)", url)
    if m:
        arxiv_id = m.group(1)
        for full in (f"https://arxiv.org/html/{arxiv_id}", f"https://ar5iv.org/abs/{arxiv_id}"):
            body = _curl(full)
            if body and len(body) > 20000:
                parts.append(body)
                break
        else:
            pdf = _pdf_text(f"https://arxiv.org/pdf/{arxiv_id}")
            if pdf:
                parts.append(pdf)
    m = re.search(r"zenodo\.org/records?/([0-9]+)", url)
    if m:
        api = _curl(f"https://zenodo.org/api/records/{m.group(1)}")
        if api:
            try:
                for f in json.loads(api).get("files", []):
                    link = (f.get("links") or {}).get("self", "")
                    if f.get("key", "").lower().endswith(".pdf") and link:
                        if "/api/" in link and not link.endswith("/content"):
                            link += "/content"
                        pdf = _pdf_text(link)
                        if pdf:
                            parts.append(pdf)
            except (json.JSONDecodeError, AttributeError):
                pass
    return "\n".join(parts) if parts else None


def normalize(text: str) -> str:
    text = re.sub(r"<(script|style)[^>]*>.*?</\1>", " ", text, flags=re.S | re.I)
    text = re.sub(r"<[^>]+>", " ", text)
    text = html.unescape(text)
    text = unicodedata.normalize("NFKD", text)
    text = "".join(c for c in text if not unicodedata.combining(c))
    text = re.sub(r"[^a-z0-9 ]+", " ", text.lower())
    return re.sub(r"\s+", " ", text).strip()


def _dewordify(norm: str) -> str:
    """Drop tokens of <= 2 chars. Inline math renders as short-token noise
    ('$T$' -> 't t bf t' on ar5iv); dropping short tokens from BOTH quote and
    page makes the comparison math-agnostic while long words still anchor it."""
    return " ".join(w for w in norm.split() if len(w) > 2)


def _gram_ratio(words: list[str], page_norm: str) -> float:
    if len(words) < 5:
        return 1.0 if " ".join(words) in page_norm else 0.0
    grams = [" ".join(words[i:i + 5]) for i in range(len(words) - 4)]
    return sum(1 for g in grams if g in page_norm) / len(grams)


def _longest_run(words: list[str], page_norm: str) -> int:
    """Longest run of consecutive matching 5-grams; run k means k+4
    consecutive quote words appear verbatim on the page."""
    best = cur = 0
    for i in range(max(0, len(words) - 4)):
        if " ".join(words[i:i + 5]) in page_norm:
            cur += 1
            best = max(best, cur)
        else:
            cur = 0
    return best


def _fragment_found(q: str, page_norm: str) -> bool:
    if q in page_norm:
        return True
    words = q.split()
    if _gram_ratio(words, page_norm) >= 0.8:
        return True
    # 8+ consecutive verbatim words anchor the quote even when rendered math
    # mangles the rest (fabricated quotes do not share runs this long)
    if _longest_run(words, page_norm) >= 4:
        return True
    qd = _dewordify(q)
    if len(qd.split()) >= 4:
        pd = _dewordify(page_norm)
        return _gram_ratio(qd.split(), pd) >= 0.8 or _longest_run(qd.split(), pd) >= 4
    return False


def quote_found(quote: str, page_norm: str) -> bool:
    # Quotes may legitimately stitch page fragments with "..." — check each
    # fragment on its own so the gap doesn't poison the n-gram window.
    fragments = [f for f in re.split(r"\.{3}|…", quote) if normalize(f)]
    if not fragments:
        return False
    return all(_fragment_found(normalize(f), page_norm) for f in fragments)


def check_artifact(path: Path, page_cache: dict) -> dict:
    art = json.loads(path.read_text())
    claims = []
    for item in art.get("recent_progress") or []:
        claims.append(("recent_progress", item.get("source_url", ""), item.get("quote", "")))
    ev = art.get("solved_evidence")
    if ev:
        claims.append(("solved_evidence", ev.get("url", ""), ev.get("quote", "")))
    results = []
    for kind, url, quote in claims:
        if not url or not quote:
            results.append({"kind": kind, "url": url, "verdict": "not_found",
                            "note": "missing url or quote"})
            continue
        if url not in page_cache:
            page = fetch(url)
            page_cache[url] = normalize(page) if page else None
        page_norm = page_cache[url]
        if page_norm is None:
            verdict = "fetch_failed"
        else:
            verdict = "found" if quote_found(quote, page_norm) else "not_found"
        results.append({"kind": kind, "url": url, "verdict": verdict,
                        "quote_head": quote[:80]})
    n_missing = sum(1 for r in results if r["verdict"] == "not_found")
    n_failed = sum(1 for r in results if r["verdict"] == "fetch_failed")
    grade = "FAIL" if n_missing else ("PARTIAL" if n_failed else "PASS")
    if not results:
        grade = "PASS"  # honest empty artifact
    return {"artifact": path.name, "grade": grade, "claims": results,
            "status_claim": art.get("status_claim")}


def main() -> int:
    target = Path(sys.argv[1])
    out = None
    if "--out" in sys.argv:
        out = Path(sys.argv[sys.argv.index("--out") + 1])
    files = sorted(target.glob("*.json")) if target.is_dir() else [target]
    page_cache: dict = {}
    reports = []
    for f in files:
        rep = check_artifact(f, page_cache)
        reports.append(rep)
        bad = [c for c in rep["claims"] if c["verdict"] != "found"]
        print(f"{rep['artifact']}: {rep['grade']} ({len(rep['claims'])} claims, "
              f"{len(bad)} not confirmed)")
        for c in bad:
            print(f"    {c['verdict']}: [{c['kind']}] {c['url']}")
    summary = {
        "pass": sum(1 for r in reports if r["grade"] == "PASS"),
        "partial": sum(1 for r in reports if r["grade"] == "PARTIAL"),
        "fail": sum(1 for r in reports if r["grade"] == "FAIL"),
    }
    print(f"SUMMARY: {summary}")
    if out:
        out.write_text(json.dumps({"summary": summary, "reports": reports}, indent=1))
        print(f"report -> {out}")
    return 0 if summary["fail"] == 0 else 1


if __name__ == "__main__":
    raise SystemExit(main())
