#!/usr/bin/env python3
"""Exact replay for the Gauss prefix-gcd circularity report."""

from __future__ import annotations

import hashlib
import math
import re
from pathlib import Path

try:
    import gmpy2
except ImportError as exc:  # pragma: no cover - environment diagnostic
    raise SystemExit(
        "gmpy2 is required for the n=50000 exact replay; run this checker "
        "with the repository virtual environment"
    ) from exc


ROOT = Path(__file__).resolve().parents[2]
REPORT = ROOT / "work/ultrapi-resume/gauss_prefix_gcd_exact_circularity_20260813.md"
TARGET = ROOT / "problems/local/pi-digits.txt"
TARGET_SHA256 = "2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825"
LIMIT = 50_000
SUPPORT_LIMIT = 3_000
LARGE_EXPECTED = {
    25_000: 8_649_551,
    30_000: 137_309,
    40_000: 177_241,
    50_000: 51_811,
}


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def odd_part(value: gmpy2.mpz) -> gmpy2.mpz:
    return value >> gmpy2.bit_scan1(value)


def primes_through(limit: int) -> list[int]:
    sieve = bytearray(b"\x01") * (limit + 1)
    sieve[:2] = b"\x00\x00"
    for p in range(2, math.isqrt(limit) + 1):
        if sieve[p]:
            start = p * p
            sieve[start : limit + 1 : p] = b"\x00" * (
                (limit - start) // p + 1
            )
    return [p for p in range(3, limit + 1, 2) if sieve[p]]


def build_sequence(limit: int) -> list[gmpy2.mpz]:
    values = [gmpy2.mpz(1), gmpy2.mpz(2)]
    for n in range(1, limit):
        numerator = 2 * (2 * n + 1) * values[n] + 4 * n * values[n - 1]
        assert numerator % (n + 1) == 0
        values.append(numerator // (n + 1))
    return values


def coefficient_value(n: int, quadratic: int = 2) -> int:
    # [x^n](1 + 2x + quadratic*x^2)^n.
    total = 0
    for k in range(n // 2 + 1):
        middle = n - 2 * k
        total += (
            math.comb(n, k)
            * math.comb(n - k, middle)
            * (2**middle)
            * (quadratic**k)
        )
    return total


def digit_product_mod(n: int, p: int, values: list[gmpy2.mpz]) -> int:
    product = 1
    while n:
        product = product * int(values[n % p] % p) % p
        n //= p
    return product


def prefix_gcd(n: int, odds: list[gmpy2.mpz]) -> gmpy2.mpz:
    remaining = odds[n]
    original = remaining
    for r in range(1, (n - 1) // 3 + 1):
        if remaining == 1:
            break
        remaining //= gmpy2.gcd(remaining, odds[r])
    return original // remaining


def check_hygiene(paths: list[Path]) -> None:
    for path in paths:
        raw = path.read_bytes()
        raw.decode("utf-8")
        assert raw.endswith(b"\n"), f"missing final newline: {path}"
        assert b"\t" not in raw, f"tab byte: {path}"
        assert not any(byte < 32 and byte != 10 for byte in raw), (
            f"C0 byte: {path}"
        )
        assert 127 not in raw, f"DEL byte: {path}"
        for line_number, line in enumerate(raw.splitlines(), 1):
            assert line == line.rstrip(b" "), (
                f"trailing whitespace: {path}:{line_number}"
            )


def check_local_links() -> None:
    text = REPORT.read_text(encoding="utf-8")
    for target in re.findall(r"\[[^\]]+\]\(([^)]+)\)", text):
        if "://" in target or target.startswith("#"):
            continue
        path = (REPORT.parent / target).resolve()
        assert path.exists(), f"missing local link: {target}"


def main() -> None:
    assert sha256(TARGET) == TARGET_SHA256
    assert REPORT.exists()

    values = build_sequence(LIMIT)
    odds = [odd_part(value) for value in values]

    for n in range(31):
        assert int(values[n]) == coefficient_value(n, 2)
    assert coefficient_value(2, 2) == 8
    assert coefficient_value(2, 4) == 12

    small_primes = primes_through(211)
    for p in small_primes:
        for n in range(0, 6 * p + 1):
            assert int(values[n] % p) == digit_product_mod(n, p, values)
        half = (p - 1) // 2
        for d in range(p):
            reflected = p - 1 - d
            left_zero = values[d] % p == 0
            right_zero = values[reflected] % p == 0
            assert left_zero == right_zero
            if d <= half:
                scalar = pow(-4, half - d, p)
                assert int(values[reflected] % p) == scalar * int(
                    values[d] % p
                ) % p

    support_primes = primes_through(SUPPORT_LIMIT)
    max_ratio = (0.0, 0, 0.0)
    for n in range(2, SUPPORT_LIMIT + 1):
        common = prefix_gcd(n, odds)
        ratio = float(gmpy2.log(common)) / n if common > 1 else 0.0
        if ratio > max_ratio[0]:
            max_ratio = (ratio, n, float(gmpy2.log(common)))

        for p in support_primes:
            if p >= n:
                break
            assert (common % p == 0) == (values[n] % p == 0), (n, p)

    assert prefix_gcd(226, odds) == 131 * 263 * 577 * 24_071
    assert prefix_gcd(76, odds) == 17**2 * 23 * 97
    witness_bound = (226 - 1) // 3
    assert [r for r in range(1, witness_bound + 1) if values[r] % 263 == 0] == [30, 36]
    assert [r for r in range(1, witness_bound + 1) if values[r] % 577 == 0] == [41]
    assert [r for r in range(1, witness_bound + 1) if values[r] % 24_071 == 0] == [42]

    large_rows = []
    for n, expected in LARGE_EXPECTED.items():
        common = prefix_gcd(n, odds)
        assert common == expected, (n, common, expected)
        large_rows.append((n, expected, float(gmpy2.log(common)) / n))

    check_hygiene([REPORT, Path(__file__)])
    check_local_links()

    print(
        "PASS: coefficient normalization, recurrence, Lucas product, and "
        "reflection through prime 211"
    )
    print(
        "PASS: exact below-n prime support of the prefix gcd for every "
        f"2 <= n <= {SUPPORT_LIMIT}"
    )
    print(
        "PASS: strict full-gcd witnesses G_226=131*263*577*24071 and "
        "G_76=17^2*23*97"
    )
    print(
        "EXPERIMENT: all prefix gcds through n=3000 have maximum "
        f"log(G_n)/n={max_ratio[0]:.12f} at n={max_ratio[1]}; "
        f"large sampled rows={large_rows}"
    )
    print(
        "BOUNDARY: finite gcd data prove no little-o bound; the square-free "
        "below-n statement is exactly the prior medium-prime target"
    )


if __name__ == "__main__":
    main()
