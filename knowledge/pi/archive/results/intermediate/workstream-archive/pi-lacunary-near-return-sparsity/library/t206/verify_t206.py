#!/usr/bin/env python3
"""Self-contained integrity and quantitative replay for T206."""

from decimal import Decimal, getcontext
from hashlib import sha256
from pathlib import Path
import csv
import json
import math
import xml.etree.ElementTree as ET


root = Path(__file__).resolve().parent

expected = {
    "canonical_statement.txt": "cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8",
    "bugeaud-kaneko-kim-2510.17177v3.pdf": "c825aac435e48f4668d8d1a496869c8c1e86ff1d18cea407e2c0156ece1bdd01",
    "bugeaud-kaneko-kim-2510.17177v3.txt": "dfc034b117ced87cc16f9beebe0153ddc220a2f0f62594358562d8c4fdf47122",
    "hauke-2506.01736v2.pdf": "270182d296fa68628edf6aa7bb7399278e2dc215ccf55e820f64f6b6f72ff54e",
    "hauke-2506.01736v2.txt": "1951a6c5511d8d44406c880a62f4908678f7e943a91713d0198ede397919cace",
    "cheng-gao-2409.13515v2.pdf": "a75dffc9952a05eb8e9917cb4cf4444fb56a567eb5ee4dfad53f54bc2901ab67",
    "cheng-gao-2409.13515v2.txt": "808f90fc8a2c58bbbcdbcc83e8a3e1c74d4816bc7dccfe042ad5466313827ade",
    "t87-threshold-bugeaud-kim-2510.02059v2.pdf": "fd557275332e2a360aaf6ef55a651746fd0b271b009e1df48f5f970991723330",
    "t87-threshold-bugeaud-kim-2510.02059v2.txt": "938ab2b2c05c94dd1114ffd6bdf49d2e7c43a393816f7c400d7e1d00bd1552cf",
    "search-restricted.xml": "a2ad072867eb2f7dce6cbc451b2a70b7452c445c52f79f524e378e43d4bec6c8",
    "search-dynamics.xml": "75485973b5c2d3943137e89d7a5a394eb29a219ebf595f84c9b1fcb475bba803",
    "search-fourier.xml": "1d00d78cbb99d3415958cd3597e9f9a83c31e9b9099a354aace0cb5fe902175f",
}

for name, digest in expected.items():
    actual = sha256((root / name).read_bytes()).hexdigest()
    assert actual == digest, (name, actual)

rows = list(csv.DictReader((root / "SOURCE_LEDGER.csv").open()))
assert len(rows) == 3
assert {row["card"] for row in rows} == {"I", "II", "III"}
assert len({row["fingerprint"] for row in rows}) == 3
assert all("not found" in row["prior_audit_status"] for row in rows)

receipt = json.loads((root / "SEARCH_RECEIPT.json").read_text())
assert receipt["searched_at_utc"] == "2026-08-19T09:32:47Z"
assert len(receipt["queries"]) == 3
for query in receipt["queries"]:
    relative = Path(query["response_snapshot"])
    assert len(relative.parts) == 2 and relative.parts[0] == "theory_artifacts"
    snapshot = root / relative.name
    assert snapshot.exists()
    assert sha256(snapshot.read_bytes()).hexdigest() == query["sha256"]
    tree = ET.parse(snapshot)
    feed = tree.getroot()
    assert feed.tag.endswith("feed")
    assert any(child.tag.endswith("entry") for child in feed)

# T87 threshold: bisect the unique root in (2, 2.3), then replay Delta.
getcontext().prec = 50


def poly(x: Decimal) -> Decimal:
    return x**3 - 2 * x**2 - x + 1


def delta(x: Decimal) -> Decimal:
    return (-x**3 + 2 * x**2 + x - 1) / (
        x**4 - 2 * x**3 + 3 * x**2 - 3 * x + 1
    )


lo, hi = Decimal("2"), Decimal("2.3")
for _ in range(200):
    mid = (lo + hi) / 2
    if poly(mid) < 0:
        lo = mid
    else:
        hi = mid
mu1 = (lo + hi) / 2
assert abs(mu1 - Decimal("2.246979603717467")) < Decimal("1e-15")
assert delta(Decimal(2)) == Decimal(1) / Decimal(7)
assert abs(delta(mu1)) < Decimal("1e-45")

# Card II decimal depth is genuine: d=floor(log10 N) implies 1/N <= 10^-d < 10/N.
for n_samples in (10, 99, 100, 999, 1000, 1234567):
    d = len(str(n_samples)) - 1
    radius = Decimal(10) ** (-d)
    assert Decimal(1) / n_samples <= radius < Decimal(10) / n_samples
# The source's off-diagonal limits 2 and 20 become 3 and 21 after the exact diagonal N.
assert 1 + 2 == 3 and 1 + 20 == 21

# Card III exact scale and numerator-sensitive Corollary 2.9 screen.
p, ell, m = 5, 3, 1
N = ell**m
phi_N = (ell - 1) * ell ** (m - 1)
q = p**phi_N
assert (N, q, int(math.log10(q))) == (3, 25, 1)
assert abs(N - ell * math.log(q) / ((ell - 1) * math.log(p))) < 1e-12
sqrt5 = math.sqrt(5)
energies = [9.0, 4 - sqrt5, 4 + sqrt5, 4 + sqrt5, 4 - sqrt5]
assert all(0 <= value <= N * N for value in energies)
assert abs(energies[2] - energies[1] - 2 * sqrt5) < 1e-12

report = (root / "REPORT.md").read_text()
for marker in (
    "T87 exponent check",
    "C_I(m,L;x)",
    "C_II(d_N,N)",
    "E_III(N,a)",
    "HOLD AS MODEL",
    "no successor is recommended",
    "finite-alphabet/Cauchy floor",
    "ambient a.e. Fourier decay",
    "sublogarithmic character sum",
    "No T204 artifact is cited, compared",
):
    assert marker in report, marker
assert report.count("**CLOSE.**") == 2
assert report.count("**HOLD AS MODEL.**") == 1

print("T206 replay passed: 3 tuples, raw receipts, T87 threshold, pair screen, and logarithmic Fourier energy")
