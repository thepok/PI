#!/usr/bin/env python3
"""Self-contained structural verifier for the bounded T193 survey."""
from hashlib import sha256
from pathlib import Path
import csv

ROOT = Path(__file__).resolve().parent
CANONICAL = "cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8"
EXPECTED = {
    "han-wu-1406.1594v1.pdf": "6763f0624e0613e18269c127b17ca6e57c0b94d5e0d3de6f453e824d435b0b1c",
    "guo-han-wu-2001.10246v5.pdf": "b3885e2dc069a7b6836ccc50b1a77d2584fface6e9fa3e56e8934f39ea1cee19",
    "rowland-yassawi-1310.8635v2.pdf": "17ff14e22d4dce2c8f0723dc9273ee888239b853d3cf0c556134da089a868c4d",
}
EXPECTED_ACCEPTED_IDS = """
T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T12 T13 T14 T17 T18 T19 T20 T21 T23 T24
T25 T26 T27 T28 T29 T31 T32 T33 T34 T35 T36 T37 T38 T39 T40 T41 T43 T44
T45 T46 T47 T49 T50 T51 T53 T54 T55 T56 T57 T58 T59 T60 T61 T62 T63 T64
T65 T67 T68 T72 T73 T78 T79 T80 T81 T82 T83 T85 T86 T87 T88 T89 T90 T91
T92 T93 T94 T95 T96 T97 T98 T99 T100 T101 T102 T103 T104 T105 T106 T107
T108 T110 T111 T112 T113 T114 T115 T116 T117 T118 T120 T121 T124 T125 T126
T127 T128 T130 T131 T132 T133 T134 T135 T136 T137 T140 T141 T143 T144 T145
T147 T148 T149 T150 T151 T152 T153 T154 T155 T157 T158 T159 T160 T161 T162
T163 T164 T165 T166 T167 T168 T169 T170 T171 T172 T173 T175 T176 T177 T178
T179 T180 T181 T183 T184 T186 T187 T190
""".split()

def digest(name):
    return sha256((ROOT / name).read_bytes()).hexdigest()

assert digest("canonical_statement.txt") == CANONICAL
for name, expected in EXPECTED.items():
    assert digest(name) == expected, name

with (ROOT / "SOURCE_LEDGER.csv").open(newline="") as handle:
    rows = list(csv.DictReader(handle))
assert len(rows) == 3 and len(rows) <= 8
assert {row["id"] for row in rows} == {"F", "H", "R"}
assert len({row["domain"] for row in rows}) == 3
assert len({row["normalized_fingerprint"] for row in rows}) == 3
assert all(row["verdict"] == "close" for row in rows)

boundaries = (ROOT / "ACCEPTED_BOUNDARIES.csv").read_text()
assert "through_T190" in boundaries
with (ROOT / "ACCEPTED_RECORDS.csv").open(newline="") as handle:
    accepted = list(csv.DictReader(handle))
assert len(accepted) == 158
assert accepted[-1]["accepted_id"] == "T190"
assert len({row["accepted_id"] for row in accepted}) == 158
assert accepted[0]["accepted_id"] == "T1"
assert [row["accepted_id"] for row in accepted] == EXPECTED_ACCEPTED_IDS
report = (ROOT / "REPORT.md").read_text()
for required in [
    "primary source/theorem tuples were inspected", "3 <= 8", "floor((1/4) log_10 N) = floor(4) = 4",
    "Verdict: close.", "no successor is selected", "ordered, diagonal-inclusive",
    "Additional unproved transfer hypothesis (conjecture)",
    "required powers `2^(-3^i)`",
]:
    assert required in report, required
for forbidden in ["T189", "T192", "A1", "C1", "C2"]:
    assert forbidden not in report and forbidden not in boundaries, forbidden
print("T193 replay passed: three tuples, three domains, three distinct fingerprints, and no successor.")
