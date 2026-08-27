#!/usr/bin/env python3
"""Exact replay for the 2/3 arctangent-shadow audit.

All identities and congruences are checked with Python integers and
``fractions.Fraction``.  Floating point is used only for the compact scale
table printed at the end; it is not used by an assertion.
"""

from __future__ import annotations

from fractions import Fraction
from hashlib import sha256
from math import gcd, isqrt, log10
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
SOURCE = ROOT / "problems/local/pi-digits.txt"
SOURCE_SHA256 = "2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825"


def sign4(odd: int) -> int:
    assert odd > 0 and odd % 2 == 1
    return 1 if odd % 4 == 1 else -1


def vp_int(n: int, p: int) -> int:
    assert p >= 2 and n != 0
    n = abs(n)
    value = 0
    while n % p == 0:
        value += 1
        n //= p
    return value


def vp_rat(x: Fraction, p: int) -> int:
    assert x != 0
    return vp_int(x.numerator, p) - vp_int(x.denominator, p)


def floor_log_p(n: int, p: int) -> int:
    assert n >= 1 and p >= 2
    value = 0
    power = 1
    while power * p <= n:
        power *= p
        value += 1
    return value


def lcm(a: int, b: int) -> int:
    return a // gcd(a, b) * b


def primes_up_to(limit: int) -> list[int]:
    sieve = bytearray(b"\x01") * (limit + 1)
    if limit >= 0:
        sieve[0] = 0
    if limit >= 1:
        sieve[1] = 0
    for p in range(2, isqrt(limit) + 1):
        if sieve[p]:
            sieve[p * p : limit + 1 : p] = b"\x00" * (
                (limit - p * p) // p + 1
            )
    return [p for p in range(2, limit + 1) if sieve[p]]


def rational_mod(x: Fraction, p: int) -> int:
    assert x.denominator % p != 0
    return (x.numerator % p) * pow(x.denominator % p, -1, p) % p


def euler_lower(K: int) -> Fraction:
    R = 4 * K + 3
    return 4 * sum(
        (
            sign4(r)
            * (Fraction(1, r * 2**r) + Fraction(1, r * 3**r))
            for r in range(1, R + 1, 2)
        ),
        Fraction(0),
    )


def euler_width(K: int) -> Fraction:
    R = 4 * K + 3
    return Fraction(4, (R + 2) * 2 ** (R + 2)) + Fraction(
        4, (R + 2) * 3 ** (R + 2)
    )


def euler_upper(K: int) -> Fraction:
    return euler_lower(K) + euler_width(K)


def local_constant(M: int) -> Fraction:
    """C_M for odd M: four times the two Gregory partial sums."""
    assert M >= 1 and M % 2 == 1
    return 4 * sum(
        (
            sign4(m)
            * (Fraction(1, m * 2**m) + Fraction(1, m * 3**m))
            for m in range(1, M + 1, 2)
        ),
        Fraction(0),
    )


def largest_odd_at_most(n: int) -> int:
    assert n >= 1
    return n if n % 2 else n - 1


def three_primary_certificate(R: int) -> tuple[int, int, int, Fraction]:
    """Return M_R, U_R, N_R, and the certified rational N/(U*2^R*3^M)."""
    assert R >= 1 and R % 2 == 1
    rows = [(r, vp_int(r, 3)) for r in range(1, R + 1, 2)]
    M = max(r + v for r, v in rows)
    U = 1
    for r, v in rows:
        U = lcm(U, r // 3**v)
    N = sum(
        4
        * sign4(r)
        * (3**r + 2**r)
        * (U // (r // 3**v))
        * 2 ** (R - r)
        * 3 ** (M - r - v)
        for r, v in rows
    )
    certified = Fraction(N, U * 2**R * 3**M)
    return M, U, N, certified


def transfer_horizon(width: Fraction, ell: int) -> int:
    """Largest j >= 0 with 10^j width < 10^-ell/2, or -1."""
    threshold = Fraction(1, 2 * 10**ell)
    scaled = width
    j = -1
    while scaled < threshold:
        j += 1
        scaled *= 10
    return j


def nonbase_radical_of_denominator(x: Fraction, R: int) -> int:
    result = 1
    for p in primes_up_to(R):
        if p not in (2, 3) and x.denominator % p == 0:
            result *= p
    return result


def main() -> None:
    actual_sha = sha256(SOURCE.read_bytes()).hexdigest()
    assert actual_sha == SOURCE_SHA256

    # Exact tangent-addition input for arctan(1/2) + arctan(1/3) = pi/4.
    # The quadrant check is the elementary positivity argument in the note.
    x = Fraction(1, 2)
    y = Fraction(1, 3)
    assert (x + y) / (1 - x * y) == 1

    bracket_rows = 0
    primary_rows = 0
    for K in range(0, 121):
        R = 4 * K + 3
        lower = euler_lower(K)
        width = euler_width(K)
        upper = euler_upper(K)

        # The adjacent upper sum adds precisely the two positive terms at R+2.
        direct_upper = lower + Fraction(4, (R + 2) * 2 ** (R + 2)) + Fraction(
            4, (R + 2) * 3 ** (R + 2)
        )
        assert upper == direct_upper
        assert upper - lower == width > 0
        assert width == Fraction(
            1 + Fraction(2, 3) ** (R + 2), (R + 2) * 2**R
        )
        bracket_rows += 1

        # Exact 2-primary denominator and exact decimal preperiod.
        assert vp_rat(lower, 2) == 2 - R
        assert vp_int(lower.denominator, 2) == R - 2
        assert vp_int(lower.denominator, 5) <= floor_log_p(R, 5)
        assert max(
            vp_int(lower.denominator, 2), vp_int(lower.denominator, 5)
        ) == R - 2

        # Exact general 3-primary integer certificate.
        M, U, N, certified = three_primary_certificate(R)
        assert certified == lower
        assert gcd(U * 2**R, 3) == 1
        assert vp_rat(lower, 3) == vp_int(N, 3) - M

        # No nonempty-word transfer reaches the first post-transient state.
        assert 5**R > 10 * (R + 2)
        for ell in (1, 2, 3, 6):
            horizon = transfer_horizon(width, ell)
            threshold = Fraction(1, 2 * 10**ell)
            assert horizon < R - 2
            assert 10 ** (R - 2) * width > Fraction(1, 10**ell)
            if horizon == -1:
                assert width >= threshold
            else:
                assert 10**horizon * width < threshold
                assert 10 ** (horizon + 1) * width >= threshold
        primary_rows += 1

    # On R=3^e with e odd, the final term is the unique 3-adic minimum.
    power_rows: list[tuple[int, int, int]] = []
    for exponent in (1, 3, 5):
        R = 3**exponent
        K = (R - 3) // 4
        lower = euler_lower(K)
        assert 4 * K + 3 == R
        assert vp_rat(lower, 3) == -(R + exponent)
        assert vp_int(lower.denominator, 3) == R + exponent
        power_rows.append((R, exponent, R + exponent))

    local_checks = 0
    good_local_checks = 0
    upper_band_checks = 0
    global_crt_checks = 0
    for K in range(1, 161):
        R = 4 * K + 3
        lower = euler_lower(K)
        selected: list[tuple[int, int]] = []
        for p in primes_up_to(R):
            if p <= 3 or p * p <= R:
                continue
            M = largest_odd_at_most(R // p)
            C = local_constant(M)
            lhs = rational_mod(p * lower, p)
            rhs = sign4(p) * rational_mod(C, p) % p
            assert lhs == rhs
            local_checks += 1
            if rhs != 0:
                assert vp_rat(lower, p) == -1
                assert vp_int(lower.denominator, p) == 1
                selected.append((p, M))
                good_local_checks += 1
            else:
                assert vp_rat(lower, p) >= 0
            if 3 * p > R:
                assert M == 1 and C == Fraction(10, 3)
                assert rhs == sign4(p) * 10 * pow(3, -1, p) % p
                upper_band_checks += 1

        # Recombine every checked local coordinate into the actual reduced
        # numerator's additive-CRT projection.
        G = 1
        for p, _ in selected:
            G *= p
        if G > 1:
            assert lower.denominator % G == 0
            C = lower.denominator // G
            assert gcd(G, C) == 1
            projected = lower.numerator * pow(C, -1, G) % G
            for p, M in selected:
                local = sign4(p) * rational_mod(local_constant(M), p) % p
                assert projected % p == local * (G // p) % p
                global_crt_checks += 1
            for j in range(6):
                x = lower.numerator * 10**j
                alpha = x * pow(C, -1, G) % G
                beta = x * pow(G, -1, C) % C if C > 1 else 0
                assert (C * alpha + G * beta - x) % (G * C) == 0

    scale_rows: list[tuple[int, int, int, float, float, float, float]] = []
    for K in (10, 20, 40, 80, 120, 160):
        R = 4 * K + 3
        lower = euler_lower(K)
        horizon = transfer_horizon(euler_width(K), 1)
        radical = nonbase_radical_of_denominator(lower, R)
        good_product = 1
        for p in primes_up_to(R):
            if p <= 3 or p * p <= R:
                continue
            M = largest_odd_at_most(R // p)
            if local_constant(M).numerator % p:
                good_product *= p
                assert lower.denominator % p == 0
        assert radical % good_product == 0
        scale_rows.append(
            (
                K,
                R,
                horizon,
                horizon / R,
                log10(radical) / R,
                log10(good_product) / R,
                horizon - log10(lower.denominator),
            )
        )

    print(f"source sha256: {actual_sha}")
    print(f"exact bracket rows: {bracket_rows}")
    print(f"exact 2/3-primary and transient rows: {primary_rows}")
    print(f"local congruence rows: {local_checks}")
    print(f"nonzero local valuation rows: {good_local_checks}")
    print(f"upper-band C_1=10/3 rows: {upper_band_checks}")
    print(f"global selected-prime CRT rows: {global_crt_checks}")
    print("exact 3-primary power subsequence (R, exponent, denominator exponent):")
    for row in power_rows:
        print(" ", *row)
    print(
        "scale rows "
        "(K, R, ell=1 horizon, horizon/R, log10(radical)/R, "
        "log10(checked-good-product)/R, log10(10^horizon/Q)):"
    )
    for K, R, horizon, hratio, rratio, gratio, alignment in scale_rows:
        print(
            f"  {K:3d} {R:4d} {horizon:4d} {hratio:.6f} "
            f"{rratio:.6f} {gratio:.6f} {alignment:.3e}"
        )
    print("all exact checks passed")


if __name__ == "__main__":
    main()
