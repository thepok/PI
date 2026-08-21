#!/usr/bin/env python3
"""Independent exact replay for the restricted-denominator audit.

Finite enumeration is labelled only as an experiment.  The symbolic
cofactor arguments in the report do not depend on exhausting these ranges.
"""

from fractions import Fraction
from hashlib import sha256
from itertools import product
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
IYER_PDF = (
    ROOT
    / "work/theory/pi-positive-decimal-factor-entropy/library/t79"
    / "iyer-2312.01076.pdf"
)
IYER_PDF_SHA256 = (
    "a312fd3c401f46360939dfa7ffff92a3d3f293693a9637fad2f2574e181821d8"
)


def valuation(n: int, p: int) -> int:
    assert n != 0 and p > 1
    n = abs(n)
    value = 0
    while n % p == 0:
        value += 1
        n //= p
    return value


def block_value(block: tuple[str, ...]) -> int:
    return int("".join(block)) if block else 0


def check_cantor_denominators(depth: int = 6) -> int:
    checked = 0
    for s in range(depth + 1):
        for t in range(1, depth + 1):
            period_denominator = 10**t - 1
            for prefix in product("01", repeat=s):
                a = block_value(prefix)
                for period in product("01", repeat=t):
                    b = block_value(period)
                    x = Fraction(
                        a * period_denominator + b,
                        10**s * period_denominator,
                    )
                    if x:
                        assert valuation(x.denominator, 2) == valuation(
                            x.denominator, 5
                        )
                        checked += 1
    return checked


def zero_one_values(width: int):
    values = [0]
    place = 1
    for _ in range(width):
        values += [x + place for x in values]
        place *= 10
    return values[1:]


def first_digits_of_unit_fraction(k: int, length: int) -> tuple[int, ...]:
    remainder = 1
    digits = []
    for _ in range(length):
        remainder *= 10
        digit, remainder = divmod(remainder, k)
        digits.append(digit)
    return tuple(digits)


def check_general_cofactor_finite() -> int:
    checked = 0
    for c in range(1, 51):
        v2c, v5c = valuation(c, 2), valuation(c, 5)
        if v2c == v5c:
            continue
        support = max(v2c, v5c)
        for n in range(support + 1, 11):
            target = 10**n - c
            if target <= 0:
                continue
            for d in zero_one_values(n):
                k, remainder = divmod(target, d)
                if remainder or k <= c:
                    continue
                assert valuation(d, 2) == valuation(d, 5)
                assert valuation(k, 2) - valuation(k, 5) == v2c - v5c
                assert k >= n - support + 2
                checked += 1
    return checked


def verify_special_alignment(d: int, n: int) -> dict[str, int]:
    target = 10**n - 16
    k, remainder = divmod(target, d)
    assert remainder == 0
    assert set(str(d)) <= {"0", "1"}
    assert first_digits_of_unit_fraction(k, n) == tuple(
        int(ch) for ch in str(d).zfill(n)
    )
    assert valuation(k, 2) == 4 and valuation(k, 5) == 0
    assert k % 16 == 0
    m = k // 16
    assert m > 1 and m % 2 and m % 5
    assert m >= n - 2

    state_count = 0
    if n >= 8:
        states = [pow(10, i, k) for i in range(4, n + 1)]
        assert states[-1] == 16
        assert all(r > 0 and r % 16 == 0 and 5 * r < k for r in states)
        assert len(states) == len(set(states)) == n - 3
        scaled = [r // 16 for r in states]
        assert all(1 <= s and 5 * s < m for s in scaled)
        assert len(scaled) <= (m - 1) // 5
        assert m >= 5 * n - 14
        assert k >= 80 * n - 224
        state_count = len(states)

    return {
        "d": d,
        "n": n,
        "cofactor_digits": len(str(k)),
        "states": state_count,
    }


def check_all_small_special_alignments(max_n: int = 17) -> tuple[int, int]:
    candidates = 0
    alignments = 0
    for n in range(5, max_n + 1):
        target = 10**n - 16
        for d in zero_one_values(n):
            candidates += 1
            if target % d == 0:
                verify_special_alignment(d, n)
                alignments += 1
    return candidates, alignments


def check_piecewise_quadratic_bound() -> None:
    # Exact certificates for the three ranges in the report.  The first two
    # log comparisons are simply monotonicity of the logarithm.
    assert 2**3 < 10
    assert 32 < 10**2
    assert all(16 * (n - 2) > n**2 for n in range(5, 8))
    assert all(80 * n - 224 > n**2 for n in range(8, 26))
    assert 24**3 > 20 * 26**2
    for n in range(3, 1000):
        assert (n - 1) ** 3 * n**2 > (n - 2) ** 3 * (n + 1) ** 2


def main() -> None:
    assert sha256(IYER_PDF.read_bytes()).hexdigest() == IYER_PDF_SHA256
    check_piecewise_quadratic_bound()
    cantor_cases = check_cantor_denominators()
    general_cases = check_general_cofactor_finite()
    candidates, alignments = check_all_small_special_alignments()
    examples = [
        verify_special_alignment(1011, 208),
        verify_special_alignment(1101, 190),
    ]
    print(
        json.dumps(
            {
                "status": "PASS",
                "piecewise_quadratic_certificate": "PASS",
                "iyer_pdf_sha256": IYER_PDF_SHA256,
                "rational_01_cases_checked": cantor_cases,
                "general_cofactor_alignments_checked": general_cases,
                "specialized_experiment": {
                    "n_min": 5,
                    "n_max": 17,
                    "zero_one_candidates": candidates,
                    "alignments": alignments,
                },
                "large_modular_examples": examples,
            },
            sort_keys=True,
        )
    )


if __name__ == "__main__":
    main()
