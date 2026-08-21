#!/usr/bin/env python3
"""Self-contained replay checks for the T93 proof-sketch note.

Finite checks here audit displayed arithmetic; REPORT.md contains the
universal argument. No finite loop is represented as a proof of PPC failure.
"""

from __future__ import annotations

import hashlib
import math
from fractions import Fraction
from pathlib import Path


ROOT = Path(__file__).resolve().parent

EXPECTED = {
    "canonical_statement.txt": "cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8",
    "larcher-stockinger-1803.05236v2.pdf": "a9ea7099fb191b68cd7a322bf6b50a1d009820c69c5fa16fc3d2746a1c4baeae",
    "larcher-stockinger-1803.05236v2.txt": "82d585a371bc8a5c88ff0a4b79f3fe5448356835fa74a1464ac4f1aba2301639",
    "stoneham-1973.pdf": "62d1718944b11b61543a20eebc2df9adbe94b94f825befa1774063897d2586d3",
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


def multiplicative_order(a: int, modulus: int) -> int:
    if math.gcd(a, modulus) != 1:
        raise ValueError("order requires a unit")
    value = 1
    for order in range(1, modulus + 1):
        value = value * a % modulus
        if value == 1:
            return order
    raise AssertionError("order not found")


def skeleton(limit: int) -> list[Fraction]:
    """Compute z_0,...,z_(limit-1) exactly from the recurrence."""
    z = Fraction(0)
    values = [z]
    powers = set()
    p = 7
    while p < limit:
        powers.add(p)
        p *= 7
    for n in range(1, limit):
        injection = Fraction(1, n) if n in powers else Fraction(0)
        z = (10 * z + injection) % 1
        values.append(z)
    return values


for name, expected in EXPECTED.items():
    actual = sha256(ROOT / name)
    if actual != expected:
        raise AssertionError(f"hash mismatch for {name}: {actual}")

source = (ROOT / "larcher-stockinger-1803.05236v2.txt").read_text(encoding="utf-8")
report = (ROOT / "REPORT.md").read_text(encoding="utf-8")
canonical = (ROOT / "canonical_statement.txt").read_text(encoding="utf-8")

require(source, "pair correlation statistics", "source PPC definition")
require(source, "Theorem 3 The sequence ({2n α2,3 })", "source Theorem 3")
require(source, "N = 2w", "source proof subsequence")
require(source, "5     Proof of Theorem 3", "source proof locator")

for needle in (
    "pairs are ordered",
    "the diagonal is included",
    "for every integer A >= 1",
    "there exists an integer n_0 >= 1",
    "for every integer n >= n_0",
    "there exists an integer N >= 1",
):
    require(canonical, needle, "canonical normalization")

for q in range(1, 9):
    expected_order = 6 * 7 ** (q - 1)
    actual_order = multiplicative_order(10, 7**q)
    if actual_order != expected_order:
        raise AssertionError((q, actual_order, expected_order))
    quotient = (pow(10, expected_order) - 1) // (7**q)
    if quotient % 7 == 0:
        raise AssertionError(f"valuation lift failed at q={q}")

if (10**6 - 1) // 7 % 7 != 1:
    raise AssertionError("v_7(10^6-1) base calculation failed")

for q in range(0, 5):
    start = 0 if q == 0 else 7**q
    stop = 7 if q == 0 else 7 ** (q + 1)
    values = skeleton(stop)[start:stop]
    counts: dict[Fraction, int] = {}
    for value in values:
        counts[value] = counts.get(value, 0) + 1
    if set(counts.values()) != {7}:
        raise AssertionError(f"level {q} multiplicities are not all seven")
    expected_classes = 1 if q == 0 else 6 * 7 ** (q - 1)
    if len(counts) != expected_classes:
        raise AssertionError(f"level {q} class count mismatch")
    if q > 0 and any(value.denominator != 7**q for value in counts):
        raise AssertionError(f"level {q} has a non-reduced denominator")

endpoint_bounds = {
    0: Fraction(42, 13),
    1: Fraction(54, 19),
    2: Fraction(54, 19),
    3: Fraction(78, 25),
    4: Fraction(114, 31),
    5: Fraction(162, 37),
    6: Fraction(222, 43),
}


def ratio(a: int, theta: Fraction) -> Fraction:
    numerator = 6 + Fraction(6, 7) * (a * (a - 1) + 2 * a * theta)
    denominator = 1 + Fraction(6, 7) * (a + theta)
    return numerator / denominator


for a, expected_bound in endpoint_bounds.items():
    actual_bound = min(ratio(a, Fraction(0)), ratio(a, Fraction(1)))
    if actual_bound != expected_bound:
        raise AssertionError((a, actual_bound, expected_bound))
    if expected_bound < Fraction(54, 19):
        raise AssertionError(f"lower bound failed at a={a}")

for needle in (
    "Result label: `proof sketch`",
    "sibling model",
    "liminf_(w->infinity) F_(10^w)(1) >= 54/19 > 2",
    "E_w := 12*ell*w + 42",
    "ord_(7^q)(10) = 6 * 7^(q-1)",
    "does not have Poissonian pair correlation",
    "makes no conclusion about",
    "`pi`, C1, or C2.",
    "This is only a transfer hypothesis, not an assertion",
):
    require(report, needle, "report scope or theorem marker")

print("T93 replay passed")
print("canonical hash: verified")
print("primary PDF hashes: 2 verified; source text derivative: verified")
print("orders ord_(7^q)(10)=6*7^(q-1): exact finite audit q=1..8")
print("skeleton multiplicity seven: exact finite audit q=0..4")
print("symbolic endpoint minimum: 54/19 > 2")
print("universal status: proof sketch in REPORT.md; finite checks are not proof")
