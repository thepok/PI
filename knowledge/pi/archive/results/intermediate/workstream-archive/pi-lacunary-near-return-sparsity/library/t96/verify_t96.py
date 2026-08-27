#!/usr/bin/env python3
"""Finite exact sanity checks for the T96 proof-sketch note.

The universal proof is in REPORT.md. No finite computation in this file is
represented as a proof of the family theorem or as evidence about pi.
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


def first_primitive_root(p: int) -> int:
    target = p * (p - 1)
    for base in range(2, p * p):
        if multiplicative_order(base, p * p) == target:
            return base
    raise AssertionError(f"no primitive root found modulo {p*p}")


def skeleton(p: int, base: int, limit: int) -> list[Fraction]:
    """Compute z_0,...,z_(limit-1) exactly from recurrence (5.4)."""
    powers: set[int] = set()
    power = p
    while power < limit:
        powers.add(power)
        power *= p
    z = Fraction(0)
    values = [z]
    for n in range(1, limit):
        injection = Fraction(1, n) if n in powers else Fraction(0)
        z = (base * z + injection) % 1
        values.append(z)
    return values


def prefix_parameters(p: int, n_terms: int) -> tuple[int, int, int, int, int]:
    ell = 0
    power = 1
    while power * p < n_terms:
        power *= p
        ell += 1
    if not (power < n_terms < power * p):
        raise AssertionError((p, n_terms, power))
    a_power = power
    period = (p - 1) * a_power // p
    height = n_terms - a_power
    quotient, remainder = divmod(height, period)
    return ell, a_power, period, quotient, remainder


def formula_count(p: int, n_terms: int) -> int:
    _, a_power, period, quotient, remainder = prefix_parameters(p, n_terms)
    return (
        (p - 1) * a_power
        + period * quotient * (quotient - 1)
        + 2 * quotient * remainder
    )


for name, expected in EXPECTED.items():
    actual = sha256(ROOT / name)
    if actual != expected:
        raise AssertionError(f"hash mismatch for {name}: {actual}")

source = (ROOT / "larcher-stockinger-1803.05236v2.txt").read_text(encoding="utf-8")
report = (ROOT / "REPORT.md").read_text(encoding="utf-8")
canonical = (ROOT / "canonical_statement.txt").read_text(encoding="utf-8")

require(source, "pair correlation statistics", "source PPC definition")
require(source, "Theorem 3 The sequence ({2n α2,3 })", "source Theorem 3")
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

# Exact finite order-lifting sanity checks for several parameter pairs.
primitive_roots: dict[int, int] = {}
for p in (3, 5, 7, 11, 13):
    base = first_primitive_root(p)
    primitive_roots[p] = base
    for q in range(1, 5):
        expected_order = (p - 1) * p ** (q - 1)
        actual_order = multiplicative_order(base, p**q)
        if actual_order != expected_order:
            raise AssertionError((p, base, q, actual_order, expected_order))
        quotient = (pow(base, expected_order) - 1) // (p**q)
        if quotient % p == 0:
            raise AssertionError(f"valuation lift failed for p={p}, q={q}")

# Every reduced residue in a complete level occurs exactly p times.
for p, max_q in ((3, 4), (5, 3), (7, 3), (11, 2)):
    base = primitive_roots[p]
    values = skeleton(p, base, p ** (max_q + 1))
    for q in range(0, max_q + 1):
        start = 0 if q == 0 else p**q
        stop = p if q == 0 else p ** (q + 1)
        counts = Counter(values[start:stop])
        if set(counts.values()) != {p}:
            raise AssertionError(f"multiplicity failure p={p}, q={q}")
        expected_classes = 1 if q == 0 else (p - 1) * p ** (q - 1)
        if len(counts) != expected_classes:
            raise AssertionError(f"class-count failure p={p}, q={q}")
        if q and any(value.denominator != p**q for value in counts):
            raise AssertionError(f"reduced-denominator failure p={p}, q={q}")

# Compare the complete direct repeated-pair count with formula (7.6).
for p, exponents in ((5, range(3, 10)), (7, range(2, 6)), (11, range(4, 10))):
    base = primitive_roots[p]
    for w in exponents:
        n_terms = base**w
        if n_terms <= p:
            continue
        values = skeleton(p, base, n_terms)
        direct = sum(count * (count - 1) for count in Counter(values).values())
        exact = formula_count(p, n_terms)
        if direct != exact:
            raise AssertionError((p, base, w, direct, exact))

# Exact endpoint checks suffice because (9.2) is affine in t.
for p in (5, 7, 11, 13, 17, 19, 23, 29, 31):
    c = Fraction(p - 1, p)
    delta = Fraction(p * p - 5 * p + 2, p * p)
    if delta <= 0:
        raise AssertionError(f"nonpositive Delta for p={p}")
    for a in range(p):
        for t in (Fraction(0), Fraction(1)):
            numerator = p - 1 + c * (a * (a - 1) + 2 * a * t)
            denominator = 1 + c * (a + t)
            if numerator / denominator <= 2 + delta:
                raise AssertionError((p, a, t, numerator / denominator, delta))

# The displayed p=3 route obstruction is exact.
p3_endpoint = Fraction(2, 1) / (1 + Fraction(2, 3))
if p3_endpoint != Fraction(6, 5) or not p3_endpoint < 2:
    raise AssertionError(p3_endpoint)

# Finite exact checks of actual tail prefixes plus a rigorous remainder bound.
for p in (5, 7):
    base = primitive_roots[p]
    for w in range(2, 6):
        n_terms = base**w
        for q in range(1, 3):
            m = p ** (q + 1) - w
            if m < p**q:
                continue
            last_k = q + 2
            tail_prefix = sum(
                (
                    Fraction(1, p**k * base ** (p**k - m))
                    for k in range(q + 1, last_k + 1)
                ),
                Fraction(0),
            )
            remainder_bound = Fraction(
                1,
                n_terms * (p - 1) * p**last_k,
            )
            broad_bound = Fraction(1, n_terms * (p - 1) * p**q)
            if not (0 < tail_prefix < tail_prefix + remainder_bound <= broad_bound):
                raise AssertionError((p, base, w, q, tail_prefix, remainder_bound))
            if not broad_bound < Fraction(1, n_terms):
                raise AssertionError((p, base, w, q, broad_bound))

for needle in (
    "Result label: `proof sketch`",
    "liminf_(w->infinity) F_(b^w)(1) >= 2+Delta_p > 2",
    "ord_(p^q)(b) = (p-1)*p^(q-1)",
    "E_w=2*(p-1)*ell*w+p*(p-1)",
    "Equation (7.6), including `a=0`, is the complete repeated-spacing count.",
    "finite exact checks",
    "explicitly `sanity checks`",
    "no implication for fixed `pi`",
    "C1, or C2",
):
    require(report, needle, "report theorem, evidence, or scope marker")

print("T96 replay passed")
print("canonical hash: verified")
print("primary PDF hashes: 2 verified; source text derivative: verified")
print("order lifting: exact finite sanity checks for p=3,5,7,11,13 and q=1..4")
print("complete level multiplicities: exact finite sanity checks through selected levels")
print("prefix formula (7.6): exact direct-count sanity checks on selected b^w prefixes")
print("tail bound (8.3): exact tail-prefix and rigorous remainder sanity checks")
print("family excess inequality: exact endpoint sanity checks for primes 5..31")
print("p=3 obstruction: exact endpoint 6/5 < 2")
print("universal status: proof sketch in REPORT.md; finite checks are not proof")
