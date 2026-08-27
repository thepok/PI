#!/usr/bin/env python3
"""Independent exact replay for the Machin--Chebotarev obstruction.

This script does not import the primary checker.  It reconstructs the full
Machin rational at the displayed witness depth, checks the finite-field
splitting data in two independent ways, and verifies the exact T48 source
interface.  Chebotarev density itself is an infinite theorem and is not
claimed to be proved by this finite computation.
"""

from __future__ import annotations

from fractions import Fraction
import hashlib
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
TARGET = ROOT / "problems/local/pi-digits.txt"
T48 = ROOT / (
    "TheoryLib/PiQuantitativeBlockHitting/"
    "T48T48MachinSeedUpperHalfPrimeSurvival.lean"
)

TARGET_SHA = "2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825"
T48_SHA = "cbe303cf13da7c60e2c4d602ba97b009a59c3cf49659b2e37d41165a02ab8f3a"


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def prime_by_trial_division(n: int) -> bool:
    if n < 2:
        return False
    if n % 2 == 0:
        return n == 2
    divisor = 3
    while divisor * divisor <= n:
        if n % divisor == 0:
            return False
        divisor += 2
    return True


def valuation(n: int, p: int) -> int:
    assert n != 0 and p > 1
    n = abs(n)
    exponent = 0
    while n % p == 0:
        n //= p
        exponent += 1
    return exponent


def order_mod(a: int, p: int) -> int:
    assert 0 < a % p and prime_by_trial_division(p)
    value = 1
    for exponent in range(1, p):
        value = value * a % p
        if value == 1:
            return exponent
    raise AssertionError("Fermat bound failed")


def roots_of_power(a: int, exponent: int, p: int) -> list[int]:
    return [x for x in range(1, p) if pow(x, exponent, p) == a % p]


def arctan_partial(q: int, terms: int) -> Fraction:
    """Literal reconstruction of T36's arctanPartialRat."""
    total = Fraction(0)
    q_power = q
    q_square = q * q
    sign = 1
    for index in range(terms):
        total += Fraction(sign, (2 * index + 1) * q_power)
        sign = -sign
        q_power *= q_square
    return total


def machin_lower(depth: int) -> Fraction:
    """Literal reconstruction of T36's machinLowerRat."""
    common_terms = 2 * (depth + 1)
    return (
        16 * arctan_partial(5, common_terms)
        - 4 * arctan_partial(239, common_terms + 1)
    )


def sieve(limit: int) -> list[int]:
    flags = bytearray(b"\x01") * limit
    if limit > 0:
        flags[0] = 0
    if limit > 1:
        flags[1] = 0
    divisor = 2
    while divisor * divisor < limit:
        if flags[divisor]:
            start = divisor * divisor
            flags[start:limit:divisor] = b"\x00" * (
                (limit - 1 - start) // divisor + 1
            )
        divisor += 1
    return [n for n, flag in enumerate(flags) if flag]


def finite_field_bad_class(p: int) -> bool:
    return (
        p % 16 == 1
        and pow(10, (p - 1) // 16, p) == 1
        and pow(2, (p - 1) // 4, p) != 1
    )


def check_t48_interface() -> None:
    source = T48.read_text(encoding="utf-8")
    required_fragments = (
        "def sampledMachinValueRat (N : ℕ) : ℚ :=",
        "(10 : ℚ) ^ N * machinLowerRat (3 * N)",
    )
    t46 = (
        ROOT
        / "TheoryLib/PiQuantitativeBlockHitting/"
        "T46T46MachinFixedModulusTelescoping.lean"
    ).read_text(encoding="utf-8")
    assert all(fragment in t46 for fragment in required_fragments)

    theorem_start = source.index(
        "theorem padicValNat_sampledMachinValueRat_den_upperHalfPrime"
    )
    theorem_text = source[theorem_start : theorem_start + 850]
    for fragment in (
        "(N p : ℕ)",
        "(hp : p.Prime)",
        "(hpgt : 5 < p)",
        "(hp239 : p ≠ 239)",
        "(hp317 : p ≠ 317)",
        "(hpLower : 12 * N + 15 < 2 * p)",
        "(hpUpper : p ≤ 12 * N + 15)",
        "padicValNat p (sampledMachinValueRat (N + 1)).den = 1",
    ):
        assert fragment in theorem_text


def main() -> None:
    assert digest(TARGET) == TARGET_SHA
    assert digest(T48) == T48_SHA
    check_t48_interface()

    p = 5521
    assert prime_by_trial_division(p)
    assert p - 1 == 16 * 345

    # Cyclic-group power tests and an exhaustive root replay agree.
    assert pow(10, 345, p) == 1
    assert pow(2, 1380, p) == p - 1
    roots_10_16 = roots_of_power(10, 16, p)
    roots_2_4 = roots_of_power(2, 4, p)
    assert len(roots_10_16) == 16
    assert roots_2_4 == []
    assert order_mod(10, p) == 345
    assert all(pow(10, m, p) != 16 for m in range(345))

    # Exact indexing and full rational reconstruction of the T48 witness.
    N = 459
    j = N + 1
    depth = 3 * j
    d = 12 * N + 15
    assert (j, depth, d) == (460, 1380, 5523)
    assert d < 2 * p and p <= d
    assert p > 5 and p not in (239, 317)
    assert 2 * (depth + 1) == 2762
    assert 2 * (depth + 1) + 1 == 2763
    assert 2 * (2762 - 1) + 1 == 5523
    assert 2 * (2763 - 1) + 1 == 5525 < 2 * p
    assert (p - 1) // 2 == 2760

    m_value = machin_lower(depth)
    r_value = 10**j * m_value
    assert valuation(m_value.numerator, p) == 0
    assert valuation(m_value.denominator, p) == 1
    assert valuation(r_value.numerator, p) == 0
    assert valuation(r_value.denominator, p) == 1

    # Since the reduced denominator contains p exactly once, p*R is
    # p-integral.  Its full-Fraction residue agrees with the localized pair.
    p_times_r_residue = (
        r_value.numerator * pow(r_value.denominator // p, -1, p)
    ) % p
    localized_residue = (
        pow(10, j, p)
        * (16 * pow(5, -1, p) - 4 * pow(239, -1, p))
    ) % p
    assert p_times_r_residue == localized_residue == 551

    # Independent bounded experiment for the sufficient splitting class.
    bad_primes = [
        q for q in sieve(100_000) if finite_field_bad_class(q)
    ]
    assert bad_primes[0] == p
    assert len(bad_primes) == 41
    for q in bad_primes:
        order = order_mod(10, q)
        assert all(pow(10, m, q) != 16 for m in range(order))

    print(
        "PASS: independent splitting certificate, exact T48 interface, "
        "and full-Fraction Machin witness; "
        f"p={p}, ord_p(10)=345, pR residue={p_times_r_residue}, "
        f"bad primes below 100000={len(bad_primes)}"
    )
    print(
        "BOUNDARY: finite computation does not prove Chebotarev density, "
        "a fixed return, or V1"
    )


if __name__ == "__main__":
    main()
