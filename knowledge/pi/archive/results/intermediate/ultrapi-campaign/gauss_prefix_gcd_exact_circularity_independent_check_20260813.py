#!/usr/bin/env python3
"""Independent replay for the Gauss prefix-gcd support audit.

This implementation intentionally does not import or execute the primary checker.
Finite checks are experiments; the accompanying note contains the proofs.
"""

from __future__ import annotations

import hashlib
import math
import re
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
PRIMARY_REPORT = (
    ROOT / "work/ultrapi-resume/gauss_prefix_gcd_exact_circularity_20260813.md"
)
PRIMARY_CHECKER = (
    ROOT
    / "work/ultrapi-resume/gauss_prefix_gcd_exact_circularity_20260813_check.py"
)
AUDIT = (
    ROOT
    / "work/ultrapi-resume/"
    "gauss_prefix_gcd_exact_circularity_independent_audit_20260813.md"
)
TARGET = ROOT / "problems/local/pi-digits.txt"

PRIMARY_REPORT_SHA256 = (
    "e7faee8c575b526e79bc7488ae61d3b7fb88012a2257ec60c6a442eabe6a083e"
)
PRIMARY_CHECKER_SHA256 = (
    "7d2f857c8c35c4d5a8783dd885ba2e20c8a100624ad197ffc2130eee2d72b8de"
)
TARGET_SHA256 = "2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825"
NOE_SHA256 = "971d271f35eb4400ac223f7e3536cdc7ac28e14393caa03c1204bc16d30a094c"
ROWLAND_YASSAWI_V2_SHA256 = (
    "17ff14e22d4dce2c8f0723dc9273ee888239b853d3cf0c556134da089a868c4d"
)
XIAO_V2_SHA256 = "e631a86a1e94f172a113ed648d0841075a210527f3fba0c200adbca450f0f6ab"
LIMIT = 1_200


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def central_coefficient(n: int, quadratic_coefficient: int = 2) -> int:
    """Return [x^n](1 + 2*x + q*x^2)^n by direct multinomials."""
    answer = 0
    for quadratic_terms in range(n // 2 + 1):
        linear_terms = n - 2 * quadratic_terms
        answer += (
            math.comb(n, quadratic_terms)
            * math.comb(n - quadratic_terms, linear_terms)
            * quadratic_coefficient**quadratic_terms
            * 2**linear_terms
        )
    return answer


def build_values(limit: int) -> list[int]:
    """Use the recurrence obtained from Q(z)F'(z)=(2+4z)F(z)."""
    values = [1, 2]
    for n in range(1, limit):
        numerator = (4 * n + 2) * values[n] + 4 * n * values[n - 1]
        quotient, remainder = divmod(numerator, n + 1)
        assert remainder == 0
        values.append(quotient)
    return values


def primes_below(limit: int) -> list[int]:
    sieve = bytearray(b"\x01") * limit
    if limit:
        sieve[0] = 0
    if limit > 1:
        sieve[1] = 0
    for candidate in range(2, math.isqrt(limit - 1) + 1):
        if sieve[candidate]:
            for multiple in range(candidate * candidate, limit, candidate):
                sieve[multiple] = 0
    return [number for number, flag in enumerate(sieve) if flag]


def base_p_digits(number: int, prime: int) -> list[int]:
    if number == 0:
        return [0]
    digits = []
    while number:
        number, digit = divmod(number, prime)
        digits.append(digit)
    return digits


def lucas_product(number: int, prime: int, values: list[int]) -> int:
    product = 1
    for digit in base_p_digits(number, prime):
        product = product * values[digit] % prime
    return product


def odd_part(number: int) -> int:
    return number // (number & -number)


def exact_prefix_gcd(n: int, values: list[int]) -> int:
    prefix = math.prod(
        odd_part(values[r]) for r in range(1, (n - 1) // 3 + 1)
    )
    return math.gcd(odd_part(values[n]), prefix)


def valuation(number: int, prime: int) -> int:
    result = 0
    while number % prime == 0:
        number //= prime
        result += 1
    return result


def is_prime(number: int) -> bool:
    if number < 2:
        return False
    for divisor in range(2, math.isqrt(number) + 1):
        if number % divisor == 0:
            return False
    return True


def check_hygiene(paths: list[Path]) -> None:
    for path in paths:
        raw = path.read_bytes()
        raw.decode("utf-8")
        assert raw.endswith(b"\n"), f"missing final newline: {path}"
        assert b"\t" not in raw, f"tab byte: {path}"
        assert 127 not in raw, f"DEL byte: {path}"
        assert not any(byte < 32 and byte != 10 for byte in raw), (
            f"C0 byte: {path}"
        )
        for line_number, line in enumerate(raw.splitlines(), 1):
            assert line == line.rstrip(b" "), (
                f"trailing whitespace: {path}:{line_number}"
            )


def check_local_links(path: Path) -> None:
    text = path.read_text(encoding="utf-8")
    for target in re.findall(r"\[[^\]]+\]\(([^)]+)\)", text):
        if "://" in target or target.startswith("#"):
            continue
        assert (path.parent / target).resolve().exists(), (
            f"missing local link in {path.name}: {target}"
        )


def main() -> None:
    assert sha256(PRIMARY_REPORT) == PRIMARY_REPORT_SHA256
    assert sha256(PRIMARY_CHECKER) == PRIMARY_CHECKER_SHA256
    assert sha256(TARGET) == TARGET_SHA256

    target_text = TARGET.read_text(encoding="utf-8")
    assert "every FINITE digit string occurs contiguously" in target_text
    assert "leading zeros are permitted" in target_text

    values = build_values(LIMIT)
    assert values[:8] == [1, 2, 8, 32, 136, 592, 2624, 11776]
    for n in range(101):
        assert values[n] == central_coefficient(n, 2)
        assert 1 <= values[n] <= 5**n
    assert central_coefficient(2, 2) == 8
    assert central_coefficient(2, 4) == 12

    primes = primes_below(LIMIT + 1)
    odd_primes = [prime for prime in primes if prime != 2]

    lucas_checks = 0
    reflection_checks = 0
    for prime in [p for p in odd_primes if p <= 101]:
        half = (prime - 1) // 2
        for n in range(LIMIT + 1):
            assert values[n] % prime == lucas_product(n, prime, values)
            lucas_checks += 1
        for d in range(prime):
            reflected = prime - 1 - d
            assert (values[d] % prime == 0) == (
                values[reflected] % prime == 0
            )
            reflection_checks += 1
        for d in range(half + 1):
            scalar = pow(-4, half - d, prime)
            assert values[prime - 1 - d] % prime == (
                scalar * values[d]
            ) % prime

    first_zero: dict[int, int | None] = {}
    max_prefix = (LIMIT - 1) // 3
    for prime in odd_primes:
        first_zero[prime] = next(
            (r for r in range(1, max_prefix + 1) if values[r] % prime == 0),
            None,
        )

    support_checks = 0
    direct_witnesses = 0
    high_band_witnesses = 0
    for n in range(2, LIMIT + 1):
        prefix_bound = (n - 1) // 3
        below_n = []
        medium = []
        for prime in odd_primes:
            if prime >= n:
                break
            divides = values[n] % prime == 0
            common_support = divides and (
                first_zero[prime] is not None
                and first_zero[prime] <= prefix_bound
            )
            assert common_support == divides, (n, prime)
            support_checks += 1
            if not divides:
                continue

            below_n.append(prime)
            if prime * prime > n:
                medium.append(prime)

            if 3 * prime <= 2 * n:
                zero_digits = [
                    digit
                    for digit in base_p_digits(n, prime)
                    if values[digit] % prime == 0
                ]
                assert zero_digits
                digit = zero_digits[0]
                assert digit not in (0, prime - 1)
                r = min(digit, prime - 1 - digit)
                assert 1 <= r <= prefix_bound
                assert values[r] % prime == 0
                direct_witnesses += 1
            else:
                assert prime < n < 2 * prime
                s = n - prime
                assert values[n] % prime == 2 * values[s] % prime
                assert 1 <= s <= prefix_bound
                high_band_witnesses += 1

        small_difference = set(below_n) - set(medium)
        assert all(prime * prime <= n for prime in small_difference)

    # The strict endpoint p=n is harmless for odd primes: A_p == A_1 mod p.
    for prime in odd_primes:
        assert values[prime] % prime == 2 % prime

    g226 = exact_prefix_gcd(226, values)
    g76 = exact_prefix_gcd(76, values)
    assert g226 == 131 * 263 * 577 * 24_071
    assert g76 == 17**2 * 23 * 97
    assert all(is_prime(p) for p in (131, 263, 577, 24_071, 17, 23, 97))
    assert [r for r in range(1, 76) if values[r] % 263 == 0] == [30, 36]
    assert [r for r in range(1, 76) if values[r] % 577 == 0] == [41]
    assert [r for r in range(1, 76) if values[r] % 24_071 == 0] == [42]
    assert 263 >= 226 and 577 >= 226 and 24_071 >= 226
    assert valuation(g76, 17) == 2

    alpha = 2 + 2 * math.sqrt(2)
    rho = 1 / alpha
    assert math.isclose(1 - 4 * rho - 4 * rho * rho, 0.0, abs_tol=1e-15)
    other_root = -(1 + math.sqrt(2)) / 2
    assert rho > 0 and rho < abs(other_root)
    observed_log_rate = math.log(values[LIMIT]) / LIMIT
    assert abs(observed_log_rate - math.log(alpha)) < 0.01

    report_text = PRIMARY_REPORT.read_text(encoding="utf-8")
    audit_text = AUDIT.read_text(encoding="utf-8")
    for source_pin in (NOE_SHA256, XIAO_V2_SHA256):
        assert source_pin in report_text
    for source_pin in (
        NOE_SHA256,
        ROWLAND_YASSAWI_V2_SHA256,
        XIAO_V2_SHA256,
    ):
        assert source_pin in audit_text

    check_hygiene([PRIMARY_REPORT, PRIMARY_CHECKER, AUDIT, Path(__file__)])
    check_local_links(PRIMARY_REPORT)
    check_local_links(AUDIT)

    print(
        "PASS: frozen primary pins, normalization, recurrence, Lucas product, "
        f"and reflection ({lucas_checks} Lucas; {reflection_checks} reflection)"
    )
    print(
        "PASS: exact below-n odd-prime support through n="
        f"{LIMIT} ({support_checks} prime/depth checks; "
        f"witness branches {direct_witnesses}+{high_band_witnesses})"
    )
    print(
        "PASS: strict full-gcd examples G_226=131*263*577*24071 and "
        "G_76=17^2*23*97"
    )
    print(
        "EXPERIMENT: log(A_1200)/1200="
        f"{observed_log_rate:.12f}; predicted exponential rate="
        f"{math.log(alpha):.12f}"
    )
    print(
        "BOUNDARY: the replay proves no little-o estimate; canonical V1 "
        "remains a conjecture"
    )


if __name__ == "__main__":
    main()
