#!/usr/bin/env python3
"""Exact replay for the Chebotarev/Machin anchor obstruction.

The finite checks here do not prove Chebotarev density.  They certify the
finite splitting witness, the exact first displayed Machin localization, and
the repository/source pins used by the accompanying proof sketch.
"""

from __future__ import annotations

import hashlib
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
TARGET = ROOT / "problems/local/pi-digits.txt"
T48 = (
    ROOT
    / "TheoryLib/PiQuantitativeBlockHitting/"
    "T48T48MachinSeedUpperHalfPrimeSurvival.lean"
)

TARGET_SHA = "2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825"
T48_SHA = "cbe303cf13da7c60e2c4d602ba97b009a59c3cf49659b2e37d41165a02ab8f3a"


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def is_prime_trial(n: int) -> bool:
    if n < 2:
        return False
    if n % 2 == 0:
        return n == 2
    q = 3
    while q * q <= n:
        if n % q == 0:
            return False
        q += 2
    return True


def sieve(limit: int) -> list[int]:
    flag = bytearray(b"\x01") * limit
    if limit:
        flag[0] = 0
    if limit > 1:
        flag[1] = 0
    for q in range(2, int(limit**0.5) + 1):
        if flag[q]:
            flag[q * q : limit : q] = b"\x00" * (
                (limit - 1 - q * q) // q + 1
            )
    return [q for q in range(limit) if flag[q]]


def sufficient_bad_prime(p: int) -> bool:
    """Finite-field version of the sufficient Chebotarev conditions."""
    return (
        is_prime_trial(p)
        and p % 16 == 1
        and pow(10, (p - 1) // 16, p) == 1
        and pow(2, (p - 1) // 4, p) != 1
    )


def multiplicative_orbit(a: int, p: int) -> list[int]:
    out = []
    x = 1
    while True:
        x = x * a % p
        out.append(x)
        if x == 1:
            return out
        assert len(out) < p


def main() -> None:
    assert sha256(TARGET) == TARGET_SHA
    assert sha256(T48) == T48_SHA
    t48_source = T48.read_text(encoding="utf-8")
    assert "theorem padicValNat_sampledMachinValueRat_den_upperHalfPrime" in t48_source
    assert "padicValNat p (sampledMachinValueRat (N + 1)).den = 1" in t48_source

    # Exact finite splitting witness K < KE.
    p = 5521
    assert is_prime_trial(p)
    assert p == 16 * 345 + 1
    assert pow(10, 345, p) == 1
    assert pow(2, 1380, p) == p - 1
    assert sufficient_bad_prime(p)

    orbit = multiplicative_orbit(10, p)
    assert len(orbit) == 345
    assert 16 not in orbit

    # The witness lies in the actual T48 upper-half window at N=459.
    N = 459
    d = 12 * N + 15
    j = N + 1
    K = 3 * j
    assert d == 5523
    assert d < 2 * p and p <= d
    assert p not in (239, 317)

    five_terms = 2 * (K + 1)
    two39_terms = 2 * (K + 1) + 1
    max_five_den = 2 * (five_terms - 1) + 1
    max_two39_den = 2 * (two39_terms - 1) + 1
    singular_index = (p - 1) // 2
    assert (K, five_terms, two39_terms) == (1380, 2762, 2763)
    assert (max_five_den, max_two39_den) == (5523, 5525)
    assert singular_index == 2760 and singular_index % 2 == 0
    assert max_two39_den < 2 * p

    # Mod-p residue of p * sampledMachinValueRat(460).  Every regular
    # summand vanishes after multiplication by p; the two p-denominator
    # summands give 16/5 - 4/239 because their Taylor sign is positive.
    localized = (
        pow(10, j, p)
        * (16 * pow(5, -1, p) - 4 * pow(239, -1, p))
    ) % p
    localized_closed = (
        pow(10, j, p) * 3804 * pow(1195, -1, p)
    ) % p
    assert localized == localized_closed == 551

    # Bounded enumeration is an experiment only.  It confirms that the
    # witness is the first prime in this sufficient class and that the class
    # has many further members; density comes solely from Chebotarev.
    bound = 100_000
    bad = [q for q in sieve(bound) if sufficient_bad_prime(q)]
    assert bad[0] == 5521
    assert len(bad) == 41
    assert all(16 not in multiplicative_orbit(10, q) for q in bad)

    print(
        {
            "target_sha256": TARGET_SHA,
            "t48_sha256": T48_SHA,
            "splitting_witness": p,
            "order_10_mod_witness": len(orbit),
            "machin_window_N": N,
            "localized_residue": localized,
            "sufficient_bad_primes_below_100000": len(bad),
            "asserts_exact_anchor_obstruction_asymptotic": False,
            "asserts_fixed_return": False,
            "asserts_v1": False,
        }
    )


if __name__ == "__main__":
    main()
