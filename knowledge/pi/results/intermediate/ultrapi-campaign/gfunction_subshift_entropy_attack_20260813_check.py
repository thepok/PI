#!/usr/bin/env python3
"""Exact finite checks for the 2026-08-13 G-function/SFT audit.

Claim status: ``experiment``.  The assertions check finite combinatorics and
exact algebraic identities used by the accompanying proof sketches.  They do
not inspect digits of pi and do not prove the canonical conjecture.
"""

from __future__ import annotations

from fractions import Fraction
from hashlib import sha256
from itertools import product
from math import log, log1p
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
PINNED_FILES = {
    "problems/local/pi-digits.txt":
        "2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825",
    "work/ultrapi-resume/special_values_digit_complexity_literature.md":
        "b08859d7fa8e68402e26393a76dffb010b19a3dbb442053b6765e87f1b67ece9",
    "work/ultrapi-resume/subshift_log_algebraic_bridge.md":
        "b4e4fb05397f75e1e4af7bbd6d4d32e80d489893fead9773de51a57a28aca896",
    "work/ultrapi-resume/subexponential_candidate_avoidance.md":
        "aaec73cba088f84c9630603856385e8d1efe581a35f4ff73818dda7629b64aee",
    ".lake/packages/mathlib/Mathlib/Dynamics/SymbolicDynamics/Basic.lean":
        "c3113c110c17101ac09ac6ac332053ee09c1b02b7c78dbdedbc4f6f6afcc8eca",
}


def file_sha256(path: Path) -> str:
    return sha256(path.read_bytes()).hexdigest()


def next_kmp_state(pattern: tuple[int, ...], state: int, digit: int) -> int | None:
    """Next prefix-match state; None is the forbidden absorbing state."""
    candidate = pattern[:state] + (digit,)
    for length in range(min(len(pattern), len(candidate)), -1, -1):
        if length == 0 or tuple(candidate[-length:]) == pattern[:length]:
            return None if length == len(pattern) else length
    raise AssertionError("empty prefix must match")


def avoidance_count(pattern: tuple[int, ...], length: int, base: int = 10) -> int:
    """Count words of exactly ``length`` avoiding ``pattern``, by exact DP."""
    states = [0] * len(pattern)
    states[0] = 1
    for _ in range(length):
        following = [0] * len(pattern)
        for state, multiplicity in enumerate(states):
            for digit in range(base):
                nxt = next_kmp_state(pattern, state, digit)
                if nxt is not None:
                    following[nxt] += multiplicity
        states = following
    return sum(states)


def brute_avoidance_count(pattern: tuple[int, ...], length: int, base: int) -> int:
    return sum(
        all(word[i : i + len(pattern)] != pattern
            for i in range(length - len(pattern) + 1))
        for word in product(range(base), repeat=length)
    )


def multiply_linear_factors(factors: list[tuple[int, int]]) -> list[int]:
    """Low-to-high coefficients of product(c0 + c1 X)."""
    coefficients = [1]
    for c0, c1 in factors:
        following = [0] * (len(coefficients) + 1)
        for degree, value in enumerate(coefficients):
            following[degree] += c0 * value
            following[degree + 1] += c1 * value
        coefficients = following
    return coefficients


def thue_morse(count: int) -> list[int]:
    return [n.bit_count() & 1 for n in range(count)]


def tangent_double(x: Fraction) -> Fraction:
    return 2 * x / (1 - x * x)


def main() -> None:
    # Frozen-input audit.
    observed_pins = {}
    for relative, expected in PINNED_FILES.items():
        observed = file_sha256(ROOT / relative)
        assert observed == expected, (relative, observed, expected)
        observed_pins[relative] = observed

    # KMP counts agree with exhaustive enumeration on independent small cases.
    for base in (2, 3):
        for width in range(1, 4):
            for pattern in product(range(base), repeat=width):
                for length in range(0, 8):
                    assert avoidance_count(pattern, length, base) == brute_avoidance_count(
                        pattern, length, base
                    )
    for pattern in ((0,), (1, 2), (1, 0, 1)):
        for length in range(0, 6):
            assert avoidance_count(pattern, length, 10) == brute_avoidance_count(
                pattern, length, 10
            )

    # Every decimal forbidden word of length at most three obeys both exact
    # elementary bounds for all checked prefix lengths.  Neither inequality
    # relies on floating-point arithmetic.
    checked_patterns = 0
    checked_inequalities = 0
    samples: dict[str, dict[str, int]] = {}
    for width in range(1, 4):
        for pattern in product(range(10), repeat=width):
            checked_patterns += 1
            for length in range(0, 9):
                count = avoidance_count(pattern, length)
                blocks, remainder = divmod(length, width)
                lower = 9**length
                upper = 10**remainder * (10**width - 1) ** blocks
                assert lower <= count <= upper
                checked_inequalities += 2
            if pattern in ((0,), (1, 2), (1, 0, 1)):
                samples["".join(map(str, pattern))] = {
                    "length": 8,
                    "exact_count": avoidance_count(pattern, 8),
                }

    # The entropy upper bound is strictly below full entropy for every m; the
    # following floating-point numbers are display only.  Strictness itself is
    # the exact integer inequality 10**m - 1 < 10**m.
    entropy_rows = []
    for width in (1, 2, 3, 10, 100):
        assert 0 < 10**width - 1 < 10**width
        # log1p avoids cancellation when 10**(-width) is tiny.
        deficit = -log1p(-(10.0 ** (-width))) / width
        upper = log(10) - deficit
        assert deficit > 0
        entropy_rows.append((width, upper, deficit))

    # Exact all-prefix language polynomial ledger for w=12 and n=2:
    # B_n(X) = product_a (10^n(X-3)-a).  Its degree is the survivor count and
    # its leading coefficient is 10^(n R_n), already a height lower bound.
    pattern = (1, 2)
    prefix_length = 2
    scale = 10**prefix_length
    allowed = [
        a
        for a in range(scale)
        if tuple(map(int, f"{a:0{prefix_length}d}")) != pattern
    ]
    language_polynomial = multiply_linear_factors(
        [(-(3 * scale + a), scale) for a in allowed]
    )
    degree = len(language_polynomial) - 1
    assert degree == avoidance_count(pattern, prefix_length) == 99
    assert language_polynomial[-1] == 10 ** (prefix_length * degree)
    assert max(map(abs, language_polynomial)) >= language_polynomial[-1]

    # Exact coefficient-cost bound for selected-tail quadratic factors
    # F(10^n X-A_n), using arbitrary legal 3*10^n < A_n < 4*10^n.
    l1_product = 1
    advertised_bound = 1
    for n in range(1, 13):
        scale = 10**n
        integer_part = 3 * scale + scale // 7
        coefficients = (
            -integer_part * (1 + integer_part),
            scale * (1 + 2 * integer_part),
            -(scale**2),
        )
        l1_norm = sum(map(abs, coefficients))
        assert l1_norm <= 30 * scale**2
        l1_product *= l1_norm
        advertised_bound *= 30 * scale**2
        assert l1_product <= advertised_bound
    assert advertised_bound == 30**12 * 10 ** (12 * 13)

    # Machin identity, checked entirely in Q at the tangent level.
    tan_a = Fraction(1, 5)
    tan_2a = tangent_double(tan_a)
    tan_4a = tangent_double(tan_2a)
    assert tan_2a == Fraction(5, 12)
    assert tan_4a == Fraction(120, 119)
    tan_difference = (tan_4a - Fraction(1, 239)) / (
        1 + tan_4a * Fraction(1, 239)
    )
    assert tan_difference == 1

    # Thue--Morse recurrence, its coefficientwise Mahler equation, and an
    # explicit path inside every tested single-word survivor.
    tm = thue_morse(4096)
    for n in range(2048):
        assert tm[2 * n] == tm[n]
        assert tm[2 * n + 1] == 1 - tm[n]
    for coefficient in range(1024):
        rhs = 0
        if coefficient % 2 == 0:
            rhs += tm[coefficient // 2]
        else:
            rhs -= tm[(coefficient - 1) // 2]
            rhs += 1
        assert tm[coefficient] == rhs

    mapped_survivors = 0
    for width in range(1, 4):
        for pattern in product(range(10), repeat=width):
            omitted_digit = pattern[0]
            selected = [digit for digit in range(10) if digit != omitted_digit][:2]
            a, b = selected
            mapped = tuple(a + (b - a) * bit for bit in tm)
            assert omitted_digit not in mapped
            assert all(
                mapped[i : i + width] != pattern
                for i in range(len(mapped) - width + 1)
            )
            mapped_survivors += 1

    # The affine formula has exactly the mapped decimal digits, with no carry.
    a, b, count = 3, 8, 80
    mapped_digits = [a + (b - a) * bit for bit in tm[:count]]
    direct = sum(Fraction(digit, 10 ** (n + 1)) for n, digit in enumerate(mapped_digits))
    affine = a * sum(Fraction(1, 10 ** (n + 1)) for n in range(count))
    affine += (b - a) * sum(
        Fraction(bit, 10 ** (n + 1)) for n, bit in enumerate(tm[:count])
    )
    assert direct == affine
    assert all(0 <= digit <= 9 for digit in mapped_digits)

    print("claim_status=experiment")
    print("canonical_result=OPEN; this checker is not a proof")
    print(f"pinned_files={len(observed_pins)}")
    print(f"decimal_patterns_checked={checked_patterns}")
    print(f"exact_bound_inequalities_checked={checked_inequalities}")
    print(f"mapped_thue_morse_survivors_checked={mapped_survivors}")
    for word, data in samples.items():
        print(f"avoid[{word}]_length_{data['length']}={data['exact_count']}")
    for width, upper, deficit in entropy_rows:
        print(
            f"entropy_upper[m={width}]={upper:.17g}; "
            f"deficit_from_log10={deficit:.17g}"
        )
    print(
        "all_prefix_polynomial[w=12,n=2]: "
        f"degree={degree}; leading_coefficient=10^{prefix_length * degree}"
    )
    print("machin_tangent_identity=exact")
    print("thue_morse_mahler_coefficients_checked=1024")


if __name__ == "__main__":
    main()
