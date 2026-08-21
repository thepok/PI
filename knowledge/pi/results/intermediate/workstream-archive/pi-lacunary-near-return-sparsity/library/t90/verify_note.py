#!/usr/bin/env python3
"""Self-contained structural and source-pin checks for the T90 survey."""

from __future__ import annotations

import hashlib
from pathlib import Path


ROOT = Path(__file__).resolve().parent

EXPECTED = {
    "canonical_statement.txt": "cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8",
    "becher-carton-1805.03713v1.pdf": "3197ae6ff0aecb4cfc80bb89688bdc3250d09f9c11b168c9f401fdb835602448",
    "scheerer-1511.03582v2.pdf": "6f746011ab585043d042394e776a381a680a5ffeee6504246cdc1507570d8394",
    "larcher-stockinger-1803.05236v2.pdf": "a9ea7099fb191b68cd7a322bf6b50a1d009820c69c5fa16fc3d2746a1c4baeae",
    "stoneham-1973.pdf": "62d1718944b11b61543a20eebc2df9adbe94b94f825befa1774063897d2586d3",
    "becher-graus-2407.13114v1.pdf": "675874240f96a98340683d0c0bece975efb658530956d591ce5bd0bbb4c30dd7",
    "becher-carton-1805.03713v1.txt": "1350d0d9e1044d21455308fb1885db6f255f43652faad68caf53031bac40440a",
    "scheerer-1511.03582v2.txt": "1603d5c3a7b77c7ba2bf523d27c51e89808bdf1fe7a3f8aee9923ac42d0f833a",
    "larcher-stockinger-1803.05236v2.txt": "82d585a371bc8a5c88ff0a4b79f3fe5448356835fa74a1464ac4f1aba2301639",
    "stoneham-1973.txt": "cb7c7f5a50363e843bf55318c122a7f82614928eb2580384dc6aca3a963ef1cd",
    "becher-graus-2407.13114v1.txt": "8e5082e8e541bd17f2cc9254ffc5095472c737e76102c2d9fdb1c6c7f0f0fcb5",
}


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1 << 20), b""):
            digest.update(chunk)
    return digest.hexdigest()


def require(text: str, needle: str, label: str) -> None:
    if needle not in text:
        raise AssertionError(f"missing {label}: {needle!r}")


for name, expected in EXPECTED.items():
    actual = sha256(ROOT / name)
    if actual != expected:
        raise AssertionError(f"hash mismatch for {name}: {actual}")

report = (ROOT / "REPORT.md").read_text(encoding="utf-8")
sources = (ROOT / "SOURCE_PINS.md").read_text(encoding="utf-8")
search = (ROOT / "SEARCH_LOG.md").read_text(encoding="utf-8")
becher = (ROOT / "becher-carton-1805.03713v1.txt").read_text(encoding="utf-8")
scheerer = (ROOT / "scheerer-1511.03582v2.txt").read_text(encoding="utf-8")
larcher = (ROOT / "larcher-stockinger-1803.05236v2.txt").read_text(encoding="utf-8")
graus = (ROOT / "becher-graus-2407.13114v1.txt").read_text(encoding="utf-8")

# Source theorem locators in derivatives.
require(becher, "Theorem 1. For each base b", "Becher--Carton Theorem 1")
require(becher, "is O((log N )2 /N )", "Becher--Carton discrepancy rate")
require(scheerer, "Theorem 2.4. The discrepancy of Schmidt", "Scheerer Theorem 2.4")
require(scheerer, "A′m (x)", "Scheerer minimizing functional")
require(larcher, "Theorem 3 The sequence ({2n α2,3 })", "Stoneham non-PPC theorem")
require(larcher, "N = 2w", "Stoneham proof scale")
require(graus, "none of these has been proved normal in", "current pi-normality status")

# Literal canonical normalization and candidate/source caps.
for needle in (
    "pairs are ordered",
    "the diagonal is included",
    "for every integer A >= 1",
    "there exists an integer n_0 >= 1",
    "for every integer n >= n_0",
    "there exists an integer N >= 1",
):
    require((ROOT / "canonical_statement.txt").read_text(encoding="utf-8"), needle, "canonical statement")

require(report, "Exactly three fixed candidates and five primary sources", "caps declaration")
source_headings = [line for line in sources.splitlines() if line.startswith("## S") and line[4:5].isdigit()]
if len(source_headings) != 5:
    raise AssertionError("SOURCE_PINS.md must contain exactly five primary source sections")

corpus_table = report.split("## 2. Retained corpus and candidates", 1)[1].split("## 3.", 1)[0]
candidate_rows = [line for line in corpus_table.splitlines() if line.startswith("|")][2:]
if len(candidate_rows) != 3 or {line.split("|")[1].strip() for line in candidate_rows} != {"L", "S", "T"}:
    raise AssertionError("retained-candidate table must contain exactly L, S, and T")

# Every required local comparison and the precise unknown pi property.
for item in ("T2", "T3", "T7", "T10", "T60", "T67", "T72", "semantic obstruction memory"):
    require(report, f"| {item} |", f"local comparison {item}")
require(report, "lim_(N->infinity) D_N(({10^j*pi})", "precise unknown pi property")
require(report, "equivalently base-10 normality of `pi`", "pi discriminator")

# Exactly one permitted terminal classification per retained candidate.
final = report.split("## 11. Final classifications", 1)[1]
expected_verdicts = {
    "L: Levin--Becher--Carton nested-necklace point": "hold as model",
    "S: Scheerer computable absolutely normal point": "close",
    "T: Stoneham `alpha_(2,3)`": "hold as model",
}
for candidate, verdict in expected_verdicts.items():
    row = f"| {candidate} | {verdict} |"
    if final.count(row) != 1:
        raise AssertionError(f"missing or duplicate final classification: {row}")
if final.count("develop") != 0 or final.count("close") != 1 or final.count("hold as model") != 2:
    raise AssertionError("unexpected terminal verdict count")
final_rows = [line for line in final.splitlines() if line.startswith("|")][2:]
if len(final_rows) != 3:
    raise AssertionError("final table must contain exactly three candidate rows")
allowed = {"develop", "hold as model", "close"}
for row in final_rows:
    fields = [field.strip() for field in row.strip("|").split("|")]
    if len(fields) != 2 or fields[1] not in allowed:
        raise AssertionError(f"invalid final classification row: {row}")

# Dated bounded-search declarations.
require(search, "Search date: 2026-08-09 UTC", "search date")
require(search, "three candidates and five primary sources", "search caps")
require(search, "not exhaustive", "bounded-search limitation")
require(sources, "the required `tesseract` executable", "scan tooling disclosure")

manifest = ROOT / "SHA256SUMS"
if not manifest.is_file():
    raise AssertionError("missing SHA256SUMS")
for line in manifest.read_text(encoding="ascii").splitlines():
    expected, name = line.split("  ", 1)
    if sha256(ROOT / name) != expected:
        raise AssertionError(f"SHA256SUMS mismatch for {name}")

print("T90 verification passed")
print("canonical hash: verified")
print("primary PDF hashes: 5 verified; text derivatives: 5 verified")
print("candidate cap: 3; primary-source cap: 5")
print("terminal verdicts: L=hold as model, S=close, T=hold as model")
