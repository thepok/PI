#!/usr/bin/env python3
"""Exact finite sanity checks for the T102 proof-sketch note.

The universal proof is in REPORT.md. Finite checks here are experiments, not
proof of universal quantifiers and not evidence about pi, A1, C1, or C2.
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
    "stoneham-1973.pdf": "62d1718944b11b61543a20eebc2df9adbe94b94f825befa1774063897d2586d3",
    "larcher-stockinger-1803.05236v2.pdf": "a9ea7099fb191b68cd7a322bf6b50a1d009820c69c5fa16fc3d2746a1c4baeae",
    "larcher-stockinger-1803.05236v2.txt": "82d585a371bc8a5c88ff0a4b79f3fe5448356835fa74a1464ac4f1aba2301639",
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


def valuation(value: int, prime: int) -> int:
    if value == 0:
        raise ValueError("valuation of zero is not used")
    result = 0
    while value % prime == 0:
        value //= prime
        result += 1
    return result


def profile(prime: int, base: int) -> tuple[int, int, int, int]:
    d = multiplicative_order(base, prime)
    lam = valuation(pow(base, d) - 1, prime)
    h = (prime - 1) // d
    stable = h * prime**lam
    return d, lam, h, stable


def predicted_order(prime: int, d: int, lam: int, q: int) -> int:
    return d * prime ** max(0, q - lam)


def predicted_multiplicity(prime: int, d: int, lam: int, q: int) -> int:
    block_length = (prime - 1) * prime**q
    return block_length // predicted_order(prime, d, lam, q)


def skeleton(prime: int, base: int, limit: int) -> list[Fraction]:
    powers: set[int] = set()
    power = prime
    while power < limit:
        powers.add(power)
        power *= prime
    z = Fraction(0)
    values = [z]
    for n in range(1, limit):
        injection = Fraction(1, n) if n in powers else Fraction(0)
        z = (base * z + injection) % 1
        values.append(z)
    return values


def completed_formula(prime: int, base: int, ell: int) -> int:
    d, lam, _, _ = profile(prime, base)
    total = prime * (prime - 1)
    for q in range(1, ell):
        length = (prime - 1) * prime**q
        multiplicity = predicted_multiplicity(prime, d, lam, q)
        total += length * (multiplicity - 1)
    return total


def constant_k(prime: int, base: int) -> int:
    d, lam, h, stable = profile(prime, base)
    del d
    early = prime * (prime - 1)
    early += (prime - 1) * sum(
        prime**q * (h * prime**q - 1) for q in range(1, lam)
    )
    return early - (stable - 1) * prime**lam


def prefix_parameters(prime: int, base: int, terms: int) -> tuple[int, int, int, int, int]:
    d, lam, _, _ = profile(prime, base)
    power = 1
    ell = 0
    while power * prime < terms:
        power *= prime
        ell += 1
    if not (power < terms < prime * power):
        raise AssertionError((prime, base, terms, power))
    if ell < lam:
        raise ValueError("stable prefix requested before lambda")
    period = d * prime ** (ell - lam)
    quotient, remainder = divmod(terms - power, period)
    return ell, power, period, quotient, remainder


def full_prefix_formula(prime: int, base: int, terms: int) -> int:
    _, power, period, quotient, remainder = prefix_parameters(prime, base, terms)
    _, _, _, stable = profile(prime, base)
    return (
        (stable - 1) * power
        + constant_k(prime, base)
        + period * quotient * (quotient - 1)
        + 2 * quotient * remainder
    )


def endpoint_count(prime: int, q: int, w: int, terms: int) -> int:
    return max(
        0,
        min(prime ** (q + 1), terms)
        - max(prime**q, prime ** (q + 1) - w + 1),
    )


def rational_tail_collision_count(length: int, period: int) -> int:
    quotient, remainder = divmod(length, period)
    return period * quotient * (quotient - 1) + 2 * quotient * remainder


for name, expected in EXPECTED.items():
    actual = sha256(ROOT / name)
    if actual != expected:
        raise AssertionError(f"hash mismatch for {name}: {actual}")

source = (ROOT / "larcher-stockinger-1803.05236v2.txt").read_text(encoding="utf-8")
canonical = (ROOT / "canonical_statement.txt").read_text(encoding="utf-8")
report = (ROOT / "REPORT.md").read_text(encoding="utf-8")
pins = (ROOT / "SOURCE_PINS.md").read_text(encoding="utf-8")

require(source, "pair correlation statistics", "source PPC definition")
require(source, "Theorem 3 The sequence", "source Theorem 3")
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

# Order and LTE-profile checks over maximal, defective, and high-valuation cases.
cases = (
    (3, 2),
    (3, 4),
    (3, 8),
    (3, 10),
    (3, 26),
    (5, 2),
    (5, 4),
    (5, 7),
    (7, 8),
    (7, 10),
    (11, 3),
)
for prime, base in cases:
    d, lam, h, stable = profile(prime, base)
    if (prime - 1) % d or stable != h * prime**lam or stable < prime:
        raise AssertionError((prime, base, d, lam, h, stable))
    for q in range(1, 6):
        expected_order = predicted_order(prime, d, lam, q)
        actual_order = multiplicative_order(base, prime**q)
        if actual_order != expected_order:
            raise AssertionError((prime, base, q, actual_order, expected_order))
        if valuation(pow(base, expected_order) - 1, prime) < q:
            raise AssertionError("predicted order does not work")
    for multiplier in range(1, 20):
        actual_v = valuation(pow(base, d * multiplier) - 1, prime)
        expected_v = lam + valuation(multiplier, prime)
        if actual_v != expected_v:
            raise AssertionError((prime, base, multiplier, actual_v, expected_v))

# Exact coset size, denominator, and multiplicity in every audited block.
for prime, base in cases:
    d, lam, _, stable = profile(prime, base)
    max_q = 4 if prime == 3 else 3
    values = skeleton(prime, base, prime ** (max_q + 1))
    if Counter(values[:prime]) != {Fraction(0): prime}:
        raise AssertionError((prime, base, "initial block"))
    for q in range(1, max_q + 1):
        start = prime**q
        stop = prime ** (q + 1)
        counts = Counter(values[start:stop])
        expected_order = predicted_order(prime, d, lam, q)
        expected_mult = predicted_multiplicity(prime, d, lam, q)
        if len(counts) != expected_order or set(counts.values()) != {expected_mult}:
            raise AssertionError((prime, base, q, len(counts), set(counts.values())))
        if any(value.denominator != prime**q for value in counts):
            raise AssertionError((prime, base, q, "non-reduced denominator"))
        if q >= lam and expected_mult != stable:
            raise AssertionError((prime, base, q, expected_mult, stable))

# Completed prefixes and the fixed K identity agree with direct exact counts.
for prime, base in cases:
    _, lam, _, stable = profile(prime, base)
    for ell in range(max(1, lam), max(1, lam) + 3):
        terms = prime**ell
        values = skeleton(prime, base, terms)
        direct = sum(count * (count - 1) for count in Counter(values).values())
        formula = completed_formula(prime, base, ell)
        stable_formula = (stable - 1) * terms + constant_k(prime, base)
        if direct != formula or formula != stable_formula:
            raise AssertionError((prime, base, ell, direct, formula, stable_formula))

# Stable partial-block formulas agree with direct exact skeleton counts.
prefix_cases = (
    (3, 2, range(3, 10)),
    (3, 4, range(2, 7)),
    (3, 8, range(2, 6)),
    (3, 10, range(2, 5)),
    (5, 2, range(2, 7)),
    (7, 10, range(1, 5)),
)
for prime, base, exponents in prefix_cases:
    for w in exponents:
        terms = base**w
        power = 1
        ell = 0
        while power * prime < terms:
            power *= prime
            ell += 1
        _, lam, _, stable = profile(prime, base)
        if ell < lam or terms in (power, prime * power):
            continue
        values = skeleton(prime, base, terms)
        direct = sum(count * (count - 1) for count in Counter(values).values())
        formula = full_prefix_formula(prime, base, terms)
        if direct != formula:
            raise AssertionError((prime, base, w, direct, formula, stable))

# Endpoint cardinality formula is exact by direct set enumeration and obeys w-1.
for prime in (3, 5, 7):
    for q in range(1, 4):
        block = range(prime**q, prime ** (q + 1))
        for w in range(1, 8):
            for terms in (prime**q + 1, prime ** (q + 1) - 1, prime ** (q + 1) + 2):
                direct = sum(
                    1
                    for index in block
                    if index < terms and index > prime ** (q + 1) - w
                )
                exact = endpoint_count(prime, q, w, terms)
                if direct != exact or exact > w - 1:
                    raise AssertionError((prime, q, w, terms, direct, exact))

# Exact tail prefixes plus a rigorous geometric remainder obey (8.3).
for prime, base in ((3, 4), (3, 8), (5, 2), (7, 10)):
    for w in range(2, 6):
        terms = base**w
        for q in range(1, 4):
            later = prime ** (q + 1) - w
            if later < prime**q:
                continue
            last_k = q + 3
            tail_prefix = sum(
                (
                    Fraction(1, prime**k * base ** (prime**k - later))
                    for k in range(q + 1, last_k + 1)
                ),
                Fraction(0),
            )
            remainder_bound = Fraction(
                1,
                terms * (prime - 1) * prime**last_k,
            )
            broad_bound = Fraction(1, terms * (prime - 1) * prime**q)
            if not (0 < tail_prefix < tail_prefix + remainder_bound <= broad_bound):
                raise AssertionError((prime, base, w, q, tail_prefix, remainder_bound))
            if broad_bound > Fraction(1, terms * prime * (prime - 1)):
                raise AssertionError((prime, base, w, q, broad_bound))

# Direct finite no-wrap checks with an upper bound for the uncomputed tail.
for prime, base in ((3, 4), (3, 8), (3, 26), (5, 2), (7, 10)):
    for q in range(1, 4):
        for n in (prime**q, prime ** (q + 1) - 1):
            active = sum(
                (Fraction(base ** (n - prime**k), prime**k) for k in range(1, q + 1)),
                Fraction(0),
            )
            z = active % 1
            last_k = q + 3
            tail_prefix = sum(
                (
                    Fraction(1, prime**k * base ** (prime**k - n))
                    for k in range(q + 1, last_k + 1)
                ),
                Fraction(0),
            )
            remainder_bound = Fraction(1, base * (prime - 1) * prime**last_k)
            if not z.denominator == prime**q:
                raise AssertionError((prime, base, q, n, z.denominator))
            if not z + tail_prefix + remainder_bound < 1:
                raise AssertionError((prime, base, q, n, z, tail_prefix, remainder_bound))

# Symbolic-profile endpoint and universal excess sanity checks.
for prime in (3, 5, 7, 11, 13, 17, 19):
    for d in range(1, prime):
        if (prime - 1) % d:
            continue
        for lam in range(1, 4):
            stable = (prime - 1) * prime**lam // d
            rho = Fraction(d, prime**lam)
            lower = Fraction(stable - 1, prime)
            poisson = Fraction(2, prime * (prime - 1))
            if stable < prime or lower <= poisson:
                raise AssertionError((prime, d, lam, stable, lower, poisson))
            endpoints = [
                Fraction(stable - 1, 1) + rho * k * (k - 1)
                for k in range(stable + 1)
            ]
            endpoints = [
                numerator / (1 + rho * k)
                for k, numerator in enumerate(endpoints)
            ]
            if min(endpoints) < lower:
                raise AssertionError((prime, d, lam, min(endpoints), lower))

# Required exact defective-order and higher-valuation cases.
expected_profiles = {
    (3, 4): (1, 1, 6, -9, [1, 3, 9, 27]),
    (3, 8): (2, 2, 9, -54, [2, 2, 6, 18]),
    (3, 10): (1, 2, 18, -117, [1, 1, 3, 9]),
}
for (prime, base), (d0, lam0, stable0, k0, orders0) in expected_profiles.items():
    d, lam, _, stable = profile(prime, base)
    orders = [multiplicative_order(base, prime**q) for q in range(1, 5)]
    if (d, lam, stable, constant_k(prime, base), orders) != (
        d0,
        lam0,
        stable0,
        k0,
        orders0,
    ):
        raise AssertionError((prime, base, d, lam, stable, constant_k(prime, base), orders))

# Formula (11.1) agrees with direct period-class collision counts.
for period in range(1, 16):
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
    "ord_(p^q)(b) = d*p^max(0,q-lambda)",
    "The visited numerators form the single coset",
    "M_q = h*p^q",
    "C_z(N)=(M-1)*A+K+P*a*(a-1)+2*a*r",
    "e_(q,w,N)",
    "liminf_(w->infinity) F_(b^w)(s_p)",
    "Smallest defective order: (p,b)=(3,4)",
    "Smallest higher valuation: (p,b)=(3,8)",
    "exclusively an A13 sibling",
    "no claim about pi, canonical A1, C1, C2",
    "Disposition: `develop`",
):
    require(report, needle, "report theorem, calculation, or scope marker")

for needle in (
    "not an exhaustive literature search",
    "primitive root `g modulo p^2`",
    "Theorem 3 states non-PPC only",
    "Arbitrary coprime cases in T102 are called generalized Stoneham-type series",
):
    require(pins, needle, "source scope marker")

print("T102 replay passed")
print("canonical hash: verified")
print("primary PDF hashes: 2 verified; source text derivative: verified")
print("order lifting: exact checks across maximal, defective, and high-valuation profiles")
print("coset multiplicities: pre-stable and stable regimes checked exactly")
print("completed and partial prefix formulas: direct rational checks passed")
print("tail and endpoint bounds: exact finite checks passed")
print("no-wrap: direct lambda<=3 rational checks passed")
print("defective cases: (3,4), (3,8), and (3,10) checked")
print("rational-period kill count: exact checks passed")
print("universal status: proof sketch in REPORT.md; finite replay is experiment only")
