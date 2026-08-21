#!/usr/bin/env python3
"""Finite exact sanity checks for the T99 proof-sketch note.

The universal family argument is in REPORT.md. No finite computation here is
represented as proof of its universal quantifiers or as evidence about pi.
"""

from __future__ import annotations

import hashlib
import math
from collections import Counter
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


def multiplicative_order(base: int, modulus: int) -> int:
    if math.gcd(base, modulus) != 1:
        raise ValueError("multiplicative order requires a unit")
    value = 1
    for order in range(1, modulus + 1):
        value = value * base % modulus
        if value == 1:
            return order
    raise AssertionError("order not found")


def v3(value: int) -> int:
    valuation = 0
    while value % 3 == 0:
        value //= 3
        valuation += 1
    return valuation


def skeleton(base: int, limit: int) -> list[Fraction]:
    """Compute z_0,...,z_(limit-1) exactly from recurrence (5.4)."""
    powers: set[int] = set()
    power = 3
    while power < limit:
        powers.add(power)
        power *= 3
    z = Fraction(0)
    values = [z]
    for n in range(1, limit):
        injection = Fraction(1, n) if n in powers else Fraction(0)
        z = (base * z + injection) % 1
        values.append(z)
    return values


def prefix_parameters(n_terms: int) -> tuple[int, int, int, int, int]:
    ell = 0
    power = 1
    while power * 3 < n_terms:
        power *= 3
        ell += 1
    if not (power < n_terms < 3 * power):
        raise AssertionError((n_terms, power))
    period = 2 * power // 3
    height = n_terms - power
    quotient, remainder = divmod(height, period)
    return ell, power, period, quotient, remainder


def formula_count(n_terms: int) -> int:
    _, power, period, quotient, remainder = prefix_parameters(n_terms)
    return (
        2 * power
        + period * quotient * (quotient - 1)
        + 2 * quotient * remainder
    )


def rational_tail_collision_count(length: int, period: int) -> int:
    quotient, remainder = divmod(length, period)
    return period * quotient * (quotient - 1) + 2 * quotient * remainder


for name, expected in EXPECTED.items():
    actual = sha256(ROOT / name)
    if actual != expected:
        raise AssertionError(f"hash mismatch for {name}: {actual}")

source = (ROOT / "larcher-stockinger-1803.05236v2.txt").read_text(encoding="utf-8")
report = (ROOT / "REPORT.md").read_text(encoding="utf-8")
pins = (ROOT / "SOURCE_PINS.md").read_text(encoding="utf-8")
canonical = (ROOT / "canonical_statement.txt").read_text(encoding="utf-8")

require(source, "pair correlation statistics", "source PPC definition")
require(source, "Theorem 3 The sequence", "source Theorem 3")
require(source, "does not have Poissonian pair corre-", "source Theorem 3 conclusion")
require(source, "5     Proof of Theorem 3", "source proof locator")

for needle in (
    "pairs are ordered",
    "the diagonal is included",
    "for every integer A >= 1",
    "there exists an integer n_0 >= 1",
    "for every integer n >= n_0",
    "there exists an integer N >= 1",
    "A13: replace pi, base 10",
):
    require(canonical, needle, "canonical normalization")

# ord_9(b)=6 is exactly b=2 or 5 modulo 9.
admissible_residues = {
    residue for residue in range(9)
    if math.gcd(residue, 9) == 1 and multiplicative_order(residue, 9) == 6
}
if admissible_residues != {2, 5}:
    raise AssertionError(admissible_residues)

# Finite exact order and valuation sanity checks for several admissible bases.
for base in (2, 5, 11, 14, 20, 23):
    if multiplicative_order(base, 9) != 6:
        raise AssertionError(f"test base {base} is not admissible")
    for q in range(1, 7):
        expected_order = 2 * 3 ** (q - 1)
        actual_order = multiplicative_order(base, 3**q)
        if actual_order != expected_order:
            raise AssertionError((base, q, actual_order, expected_order))
        if v3(pow(base, expected_order) - 1) != q:
            raise AssertionError(f"valuation lift failed for b={base}, q={q}")

# Every reduced residue in each audited complete block occurs three times.
for base in (2, 5, 11, 14):
    values = skeleton(base, 3**6)
    initial = Counter(values[0:3])
    if initial != {Fraction(0): 3}:
        raise AssertionError((base, initial))
    for q in range(1, 5):
        start = 3**q
        stop = 3 ** (q + 1)
        counts = Counter(values[start:stop])
        if set(counts.values()) != {3}:
            raise AssertionError(f"triple failure b={base}, q={q}")
        if len(counts) != 2 * 3 ** (q - 1):
            raise AssertionError(f"class-count failure b={base}, q={q}")
        if any(value.denominator != 3**q for value in counts):
            raise AssertionError(f"denominator failure b={base}, q={q}")

# Direct exact collision counts agree with formula (7.5).
for base, exponents in ((2, range(2, 11)), (5, range(1, 6)), (11, range(1, 4))):
    for w in exponents:
        n_terms = base**w
        if n_terms <= 3:
            continue
        values = skeleton(base, n_terms)
        direct = sum(count * (count - 1) for count in Counter(values).values())
        exact = formula_count(n_terms)
        if direct != exact:
            raise AssertionError((base, w, direct, exact))

# Exact endpoint checks for the three affine-fractional cases in (9.2).
for a in range(3):
    ratios: list[Fraction] = []
    for t in (Fraction(0), Fraction(1)):
        numerator = 2 + Fraction(2, 3) * (a * (a - 1) + 2 * a * t)
        denominator = 1 + Fraction(2, 3) * (a + t)
        ratios.append(numerator / denominator)
    if min(ratios) < Fraction(6, 5):
        raise AssertionError((a, ratios))

# The T96-style s=1 lower-excess expression is never positive.
for a in range(3):
    for t in (Fraction(0), Fraction(1, 2), Fraction(1)):
        difference = Fraction(2, 3) * (a * (a - 3) + 2 * (a - 1) * t)
        if difference > 0:
            raise AssertionError((a, t, difference))

# Smallest admissible base and the displayed two-level kill calculation.
if [pow(2, exponent, 9) for exponent in range(1, 7)] != [2, 4, 8, 7, 5, 1]:
    raise AssertionError("ord_9(2) cycle mismatch")
if formula_count(16) != 20 or Fraction(formula_count(16), 16) != Fraction(5, 4):
    raise AssertionError("b=2, N=16 calculation failed")

# Finite tail-bound sanity checks with a rigorous geometric remainder bound.
for base in (2, 5, 11):
    for w in range(2, 6):
        n_terms = base**w
        for q in range(1, 4):
            m = 3 ** (q + 1) - w
            if m < 3**q:
                continue
            last_k = q + 3
            tail_prefix = sum(
                (
                    Fraction(1, 3**k * base ** (3**k - m))
                    for k in range(q + 1, last_k + 1)
                ),
                Fraction(0),
            )
            remainder_bound = Fraction(1, n_terms * 2 * 3**last_k)
            broad_bound = Fraction(1, n_terms * 2 * 3**q)
            if not (0 < tail_prefix < tail_prefix + remainder_bound <= broad_bound):
                raise AssertionError((base, w, q, tail_prefix, remainder_bound))
            if broad_bound > Fraction(1, 6 * n_terms):
                raise AssertionError((base, w, q, broad_bound))

# Formula (11.1) agrees with direct period-class counts.
for period in range(1, 12):
    for length in range(0, 4 * period + 1):
        direct = sum(
            count * (count - 1)
            for count in Counter(index % period for index in range(length)).values()
        )
        exact = rational_tail_collision_count(length, period)
        if direct != exact:
            raise AssertionError((period, length, direct, exact))

for needle in (
    "Result label: `proof sketch`",
    "liminf_(w->infinity) F_(b^w)(1/6) >= 6/5",
    "ord_(3^q)(b) = 2*3^(q-1)",
    "E_w=4*ell*w+6",
    "normalized excess",
    "Finite replay checks are `sanity checks` only",
    "rational approximants whose first",
    "o(1/N)",
    "not evidence for, and makes no claim about, pi, C1, or C2",
    "Disposition: `hold as model`.",
):
    require(report, needle, "report theorem, evidence, transfer, or scope marker")

for needle in (
    "Exact bounded verdict",
    "Theorem 3 states non-PPC only",
    "not an exhaustive literature",
):
    require(pins, needle, "source coverage marker")

print("T99 replay passed")
print("canonical hash: verified")
print("primary PDF hashes: 2 verified; source text derivative: verified")
print("ord_9 residues and order lifting: finite exact sanity checks passed")
print("triple skeleton and exact prefix count: finite exact sanity checks passed")
print("tail and endpoint bounds: finite exact sanity checks passed")
print("smallest base kill: b=2, N=16, C_z/N=5/4<2")
print("rational-period transfer count: finite exact sanity checks passed")
print("universal status: proof sketch in REPORT.md; finite checks are not proof")
