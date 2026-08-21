#!/usr/bin/env python3
"""Self-contained integrity and finite-arithmetic replay for T120.

The checks are experiments. They do not prove source theorems or asymptotics.
"""

from __future__ import annotations

import hashlib
import math
from pathlib import Path


ROOT = Path(__file__).resolve().parent

EXPECTED = {
    "canonical_statement.txt": "cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8",
    "gouezel-math0202147.pdf": "c17395927edc5f02a5edbdf9975bd13fcd5b0d28ae339addb442b046d07b6343",
    "gouezel-math0202147.txt": "18f88fcdaf54253738526534a244bcc818f2ece21c6aeac792a7d7fa79c6b100",
    "kessebohmer-slassi-math0607681.pdf": "ec9b2b54a6e0ca0bfade2564d15a9ac66213679a00bf6072c4cf103b0a968114",
    "kessebohmer-slassi-math0607681.txt": "8404284f280f61436bd4c82e10ee08a2699ad66f51cb59f44a96b7fd55e2e0d7",
    "isola-math0308018.pdf": "24cef1306ff28a06330e4bfa3dba144dee85c733ed3c3b8bd6bee62ffa54b5f3",
    "isola-math0308018.txt": "fad73cbf17f501a2f04f44fe1e2f755452a653fbbde8d7bed2d99ef0f7e1d8a6",
    "jordan-sahlsten-1312.3619v3.pdf": "21e65b4456ea71e2113a3f2a5191b6d9a1061c6732dfa0618d0e4891ba70cb75",
    "jordan-sahlsten-1312.3619v3.txt": "2b8c086b1f45b13e463bade618ec521525a24510eb9700fc3efdb3ff4cef6483",
    "prior-t118-REPORT.md": "f7f2491e5d11a11268d7e75de452950073fba75e1682ea883b52b608a520bf4b",
}


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


for name, expected in EXPECTED.items():
    actual = digest(ROOT / name)
    assert actual == expected, (name, actual, expected)

report = (ROOT / "REPORT.md").read_text(encoding="utf-8")
pins = (ROOT / "SOURCE_PINS.md").read_text(encoding="utf-8")
search = (ROOT / "SEARCH_LOG.md").read_text(encoding="utf-8")

required_report_markers = [
    "PRIMARY_SOURCE_COUNT: 4",
    "PRIMARY_SOURCE_CAP: 12",
    "CANDIDATE_COUNT: 4",
    "CANDIDATE_CAP: 4",
    "T7_OR_T107_CALCULATION_COUNT: 4",
    "SCOPED_VERDICT_COUNT: 1",
    "SUCCESSOR_COUNT: 0",
    "R-LSV",
    "R-FAR",
    "R-ISO",
    "R-JS",
    "PI-LSV premise",
    "PI-FAR premise",
    "PI-ISO premise",
    "PI-JS premise",
    "SCOPED VERDICT (1/1): **hold as model**",
]
for marker in required_report_markers:
    assert marker in report, marker

assert report.count("SCOPED VERDICT (1/1):") == 1
assert report.count("PI-LSV premise") == 1
assert report.count("PI-FAR premise") == 1
assert report.count("PI-ISO premise") == 1
assert report.count("PI-JS premise") == 1

for prior in ("T39", "T90", "T103", "T109", "T112", "T115", "T117", "T118", "T119"):
    assert prior in report, prior

for excluded in (
    "finite-state carry",
    "Toeplitz",
    "substitution",
    "Riesz",
    "perturbative coupling",
    "cyclotomic modular",
    "collision-to-Hankel-rank",
):
    assert excluded in report or excluded in search, excluded

source_markers = {
    "gouezel-math0202147.txt": [
        "Corollary 7.1.",
        "The Liverani-Saussol-Vaienti map",
        "Markov partition",
    ],
    "kessebohmer-slassi-math0607681.txt": [
        "Theorem 4.1.",
        "Farey vs. Gauss map",
        "induced transformation S coincides with Gauss map",
    ],
    "isola-math0308018.txt": [
        "Theorem 1. Suppose P has ergodic degree",
        "necessarily not uniform in",
        "Theorem 2. Suppose that the chain P",
    ],
    "jordan-sahlsten-1312.3619v3.txt": [
        "Theorem 1.3.",
        "Proposition 4.4.",
        "Corollary 1.6.",
    ],
}
for name, markers in source_markers.items():
    text = (ROOT / name).read_text(encoding="utf-8")
    for marker in markers:
        assert marker in text, (name, marker)

# R-LSV: alpha=3/4 gives marker mass exponent -1/3 and
# m times squared mass exponent +1/3.
alpha = 3.0 / 4.0
integrated_tail_exponent = 1.0 - 1.0 / alpha
t7_scaled_exponent = 1.0 + 2.0 * integrated_tail_exponent
assert math.isclose(integrated_tail_exponent, -1.0 / 3.0)
assert math.isclose(t7_scaled_exponent, 1.0 / 3.0)

# R-FAR: the exact conditional tail has n*tail -> 1/log(2)>1.
farey_rows = []
for n in (10, 100, 1000, 10000):
    scaled = n * math.log((n + 2.0) / (n + 1.0)) / math.log(2.0)
    farey_rows.append((n, scaled))
assert farey_rows[-1][1] > 1.44
assert abs(farey_rows[-1][1] - 1.0 / math.log(2.0)) < 5e-4

# R-ISO: d=1/4 gives q_m^2 exponent -1/2 and m*q_m^2 exponent +1/2.
d = 0.25
marker_collision_exponent = -2.0 * d
isola_scaled_exponent = 1.0 - 2.0 * d
assert math.isclose(marker_collision_exponent, -0.5)
assert math.isclose(isola_scaled_exponent, 0.5)

# A finite truncation checks the combinatorial identity behind (5.9):
# sum_{k=m+1}^J sum_{j=k}^J j^(-s)
# = sum_{j=m+1}^J (j-m)j^(-s).
s = d + 2.0
for m in (1, 2, 5, 10):
    cutoff = 5000
    lhs = sum(sum(j ** (-s) for j in range(k, cutoff + 1)) for k in range(m + 1, cutoff + 1))
    rhs = sum((j - m) * j ** (-s) for j in range(m + 1, cutoff + 1))
    assert abs(lhs - rhs) < 1e-10

# R-JS: eta_s is increasing on (1/2,1] and eta_1=1/9.
def eta_s(value: float) -> float:
    return (2.0 * value * value - value) / ((4.0 - value) * (1.0 + 2.0 * value))


samples = [eta_s(0.5 + i / 2000.0) for i in range(1, 1001)]
assert all(a < b for a, b in zip(samples, samples[1:]))
assert math.isclose(eta_s(1.0), 1.0 / 9.0)
assert 3.0 * eta_s(1.0) < 0.5

assert "Exactly four primary papers" in pins
assert "PRIMARY_SOURCE_COUNT: 4 <= 12" in search

print("T120 replay: PASS")
print(f"hashes checked: {len(EXPECTED)}")
print("candidates checked: 4")
print(f"LSV scaled collision exponent: {t7_scaled_exponent:.12f}")
for n, value in farey_rows:
    print(f"Farey n={n}: n*tail={value:.12f}")
print(f"Isola d=1/4 scaled collision exponent: {isola_scaled_exponent:.12f}")
print(f"Jordan-Sahlsten eta_1={eta_s(1.0):.12f}; 3*eta_1={3*eta_s(1.0):.12f}")
print("labels: literature-checked / proof sketch / experiment / conjectural transfer")
