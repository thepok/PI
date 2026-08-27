#!/usr/bin/env python3
"""Exact finite checks for subshift_log_algebraic_bridge.md.

These checks validate identities and finite instances only. They are not a
proof of V1, of an asymptotic entropy statement, or of a literature theorem.
"""

from __future__ import annotations

import cmath
import hashlib
import itertools
import math
from decimal import Decimal, getcontext
from fractions import Fraction
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
REPORT = Path(__file__).with_name("subshift_log_algebraic_bridge.md")
TARGET = ROOT / "problems/local/pi-digits.txt"
TARGET_SHA = "2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825"

assertions = 0


def check(condition: bool, message: str) -> None:
    global assertions
    assert condition, message
    assertions += 1


def legal_count(forbidden: tuple[int, ...], length: int) -> int:
    """Count words avoiding one pattern, using prefix/KMP states."""
    m = len(forbidden)
    transition: list[list[int | None]] = []
    for state in range(m):
        row: list[int | None] = []
        for digit in range(10):
            candidate = forbidden[:state] + (digit,)
            next_state = 0
            for size in range(min(m, len(candidate)), -1, -1):
                if size == 0 or tuple(candidate[-size:]) == forbidden[:size]:
                    next_state = size
                    break
            row.append(None if next_state == m else next_state)
        transition.append(row)

    dp = [0] * m
    dp[0] = 1
    for _ in range(length):
        new = [0] * m
        for state, count in enumerate(dp):
            for next_state in transition[state]:
                if next_state is not None:
                    new[next_state] += count
        dp = new
    return sum(dp)


def de_bruijn(k: int, n: int) -> list[int]:
    """A cyclic de Bruijn word B(k,n), from the standard FKM recursion."""
    a = [0] * (k * n + 1)
    sequence: list[int] = []

    def db(t: int, p: int) -> None:
        if t > n:
            if n % p == 0:
                sequence.extend(a[1 : p + 1])
            return
        a[t] = a[t - p]
        db(t + 1, p)
        for value in range(a[t - p] + 1, k):
            a[t] = value
            db(t + 1, t)

    db(1, 1)
    return sequence


def periodic_rational(digits: tuple[int, ...], i: int, j: int) -> Fraction:
    prefix = 0
    for digit in digits[:i]:
        prefix = 10 * prefix + digit
    block = 0
    for digit in digits[i:j]:
        block = 10 * block + digit
    r = j - i
    return Fraction(prefix, 10**i) + Fraction(block, 10**i * (10**r - 1))


def finite_decimal(digits: tuple[int, ...]) -> Fraction:
    value = 0
    for digit in digits:
        value = 10 * value + digit
    return Fraction(value, 10 ** len(digits))


def thue(n: int) -> int:
    return n.bit_count() & 1


def convolve(left: list[int], right: list[int]) -> list[int]:
    out = [0] * (len(left) + len(right) - 1)
    for i, a in enumerate(left):
        for j, b in enumerate(right):
            out[i + j] += a * b
    return out


def gaussian_mul(x: tuple[int, int], y: tuple[int, int]) -> tuple[int, int]:
    return x[0] * y[0] - x[1] * y[1], x[0] * y[1] + x[1] * y[0]


def gaussian_add(x: tuple[int, int], y: tuple[int, int]) -> tuple[int, int]:
    return x[0] + y[0], x[1] + y[1]


def gaussian_scale(a: int, x: tuple[int, int]) -> tuple[int, int]:
    return a * x[0], a * x[1]


def power_i(k: int) -> tuple[int, int]:
    return ((1, 0), (0, 1), (-1, 0), (0, -1))[k % 4]


# Canonical source pin.
check(hashlib.sha256(TARGET.read_bytes()).hexdigest() == TARGET_SHA, "target SHA")

# Exact aligned-block bounds, exhaustively for every forbidden word through
# length four (including words with leading zero).
for m in range(1, 5):
    for forbidden in itertools.product(range(10), repeat=m):
        for length in range(13):
            count = legal_count(forbidden, length)
            q, r = divmod(length, m)
            check(9**length <= count, f"nine-shift lower bound: {forbidden}, {length}")
            check(
                count <= 10**r * (10**m - 1) ** q,
                f"aligned-block upper bound: {forbidden}, {length}",
            )

# Overlap lemma and rational-error bound. Exhaustive short words include
# leading zero and the all-nine alternative-expansion case.
alphabet = (0, 1, 9)
for size in range(2, 9):
    for digits in itertools.product(alphabet, repeat=size):
        value = finite_decimal(digits)
        for length in range(1, size):
            for i in range(size - length):
                for j in range(i + 1, size - length + 1):
                    if digits[i : i + length] != digits[j : j + length]:
                        continue
                    end = j + length
                    y = periodic_rational(digits, i, j)
                    check(abs(value - y) <= Fraction(1, 10**end), "overlap error")
                    q_unreduced = 10**i * (10 ** (j - i) - 1)
                    check(q_unreduced < 10**j, "unreduced denominator")

# A first repeated L-block can be delayed to 9^L on the nine-symbol subsystem.
for length in range(1, 5):
    cycle = de_bruijn(9, length)
    check(len(cycle) == 9**length, "de Bruijn length")
    linear = cycle + cycle[: length - 1]
    windows = {tuple(linear[i : i + length]) for i in range(9**length)}
    check(len(windows) == 9**length, "de Bruijn unique windows")

# Thue--Morse recurrence and the coefficient form of the Mahler identity.
for n in range(4096):
    check(thue(2 * n) == thue(n), "Thue even recurrence")
    check(thue(2 * n + 1) == 1 - thue(n), "Thue odd recurrence")
    check(thue(n) == thue(2 * n), "Mahler even coefficient")
    check(1 - thue(n) == thue(2 * n + 1), "Mahler odd coefficient")

# Explicit no-carry separator for every forbidden word through length four.
# Choosing c as the first digit tests every possible leading digit, including
# zero. Every separator digit omits c, so every occurrence of w is impossible.
tm_prefix = [thue(n) for n in range(512)]
for m in range(1, 5):
    for forbidden in itertools.product(range(10), repeat=m):
        c = forbidden[0]
        a, b = [digit for digit in range(10) if digit != c][:2]
        separator = [a + (b - a) * digit for digit in tm_prefix]
        check(all(0 <= digit <= 9 for digit in separator), "no carry")
        check(all(digit != c for digit in separator), "omitted selected digit")
        windows = zip(*(separator[k:] for k in range(m)))
        check(tuple(forbidden) not in windows, "word omitted")

# Finite witnesses against every prospective short eventual period. The
# report's elementary proof can take k of both parities in 2^k-p.
for period in range(1, 129):
    witnesses = []
    for k in range(10, 18):
        n = 2**k - period
        if thue(n) != thue(n + period):
            witnesses.append((k, n))
    check(bool(witnesses), f"nonperiodicity witness p={period}")

# Euler-tail identity and first-order normalization on safe floating scales.
# The report's derivation is symbolic; this catches a sign or scale mistake.
for n in range(7):
    q = 10**n
    p = math.floor(q * math.pi)
    x = q * math.pi - p
    lhs = cmath.exp(1j * p / q) + 1
    rhs = 1 - cmath.exp(-1j * x / q)
    check(abs(lhs - rhs) < 2e-14, "Euler identity sign")
    check(abs(lhs) <= x / q + 2e-15, "Euler upper bound")
    check(abs(q * lhs - 1j * x) <= 0.6 / q + 2e-14, "Euler normalization")

# Selected-tail factor coefficients, product degree/height, and the explicit
# log-height estimate used in the Cijsouw parameter substitution.
getcontext().prec = 100
pi_dec = Decimal(
    "3.141592653589793238462643383279502884197169399375105820974944592307816406286"
)
product = [1]
for n in range(1, 13):
    t = 10**n
    A = int(pi_dec * t)
    factor = [-A * (1 + A), t * (1 + 2 * A), -(t**2)]
    check(sum(abs(c) for c in factor) <= 30 * t**2, "factor l1 bound")
    product = convolve(product, factor)
    check(len(product) - 1 == 2 * n, "product degree")
    check(abs(product[-1]) == 10 ** (n * (n + 1)), "leading coefficient")
    check(max(abs(c) for c in product) <= 30**n * 10 ** (n * (n + 1)), "height")
    log_height_bound = n * math.log(30) + n * (n + 1) * math.log(10)
    check(log_height_bound <= 9 * n * n, "explicit log-height bound")
    check(
        (2 * n) ** 2 * (2 * n + 9 * n * n) <= 44 * n**4,
        "Cijsouw polynomial scale",
    )

# Exact Gaussian-coefficient check for Q(Y)=P(-iY)P(iY).
for degree in range(1, 9):
    for seed in range(1, 25):
        coeffs = [((seed + 3 * k) % 11) - 5 for k in range(degree + 1)]
        if coeffs[-1] == 0:
            coeffs[-1] = 1
        height = max(abs(c) for c in coeffs)
        q_coeffs: list[tuple[int, int]] = [(0, 0)] * (2 * degree + 1)
        for k, ak in enumerate(coeffs):
            for ell, al in enumerate(coeffs):
                phase = gaussian_mul(power_i(-k), power_i(ell))
                term = gaussian_scale(ak * al, phase)
                q_coeffs[k + ell] = gaussian_add(q_coeffs[k + ell], term)
        check(all(imag == 0 for _, imag in q_coeffs), "Q has real coefficients")
        real_coeffs = [real for real, _ in q_coeffs]
        check(all(real_coeffs[k] == 0 for k in range(1, 2 * degree + 1, 2)), "Q even")
        check(max(abs(c) for c in real_coeffs) <= (degree + 1) * height**2, "Q height")
        check(real_coeffs[-1] != 0, "Q nonzero and full degree")

# Keep this checker network-independent. The audit records direct downloads;
# here we ensure every re-fetched SHA-256 pin remains in the report.
expected_pins = (
    "fc31f7cf4ce0177a46966c0ef41b05c6252c0d4f3abb762d50c2e43e7f48a46a",
    "e3bd2934800e94dd27930d43d47abc44f760de7e90320d1d014b372b681be9a0",
    "735e483213db56fb0a7c07a5293d63b22d23f1f47ae5d2c83b488b8caaff42c3",
    "6d7607e8a70e8524630daa45001192113487d9af1f1588c96556283445c7460c",
    "3778e06391c3aacde0012f7145a11549ee1311353bbd4bd8d28546f4b02963e5",
    "d44bec7a6c2b016d4a65971e60e583a9d013e8389948c52393911f5b12b7e7dd",
    "c428a9a555b8d7abeb25f3e8a02c8f7880c640e7fe6a2f85c411ca1b68f1945c",
    "86669c0103d2a589c9a45970734a9ebac47c737382c015fa026b546960c0301d",
    "2cfb651d65a9960bc0385a2658005752dd899bb4a8919b08d91c8319a18a87b2",
    "5bb31a65f491bd85a72864938f610cddf04e45bac6e6f635e508ff6cf70b67bf",
    "fd557275332e2a360aaf6ef55a651746fd0b271b009e1df48f5f970991723330",
    "c825aac435e48f4668d8d1a496869c8c1e86ff1d18cea407e2c0156ece1bdd01",
)
report_text = REPORT.read_text(encoding="utf-8")
for pin in expected_pins:
    check(pin in report_text, f"source pin present: {pin[:12]}")

print(f"PASS: {assertions:,} exact finite assertions")
