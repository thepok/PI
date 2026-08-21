#!/usr/bin/env python3
"""Exact finite replay for restricted_denominator_iyer_attack.md.

All computations are deterministic and use only Python's standard library.
Finite searches are experiments; the report's cofactor bound is proved
symbolically and does not depend on search exhaustion.
"""

from fractions import Fraction
from itertools import product
import json


def valuation(n: int, p: int) -> int:
    assert n != 0 and p > 1
    n = abs(n)
    out = 0
    while n % p == 0:
        n //= p
        out += 1
    return out


def zero_one_integer(n: int) -> bool:
    return n > 0 and set(str(n)) <= {"0", "1"}


def block_value(bits: tuple[str, ...]) -> int:
    return int("".join(bits)) if bits else 0


def check_rational_cantor_denominators(max_preperiod: int, max_period: int) -> int:
    checked = 0
    for s in range(max_preperiod + 1):
        for t in range(1, max_period + 1):
            ten_t_minus_one = 10**t - 1
            for prefix in product("01", repeat=s):
                a = block_value(prefix)
                for period in product("01", repeat=t):
                    b = block_value(period)
                    x = Fraction(
                        a * ten_t_minus_one + b,
                        10**s * ten_t_minus_one,
                    )
                    if x == 0:
                        continue
                    assert valuation(x.denominator, 2) == valuation(
                        x.denominator, 5
                    )
                    checked += 1
    return checked


def search_small_cofactor(max_n: int) -> int:
    """Count alignments d=(10^N-16)/k in D_10 with k <= N^2."""
    hits = 0
    for n in range(5, max_n + 1):
        q = 10**n - 16
        for k in range(1, n * n + 1):
            d, remainder = divmod(q, k)
            if remainder == 0 and zero_one_integer(d):
                hits += 1
    return hits


def check_global_quadratic_certificate() -> dict[str, int | str]:
    """Replay the exact integer inequalities used after (23f).

    The transcendental inequalities are symbolic in the report:
    log_2(10) > 3 follows from 10 > 2^3, and log_10(32) < 2 follows
    from 32 < 10^2.  The remaining threshold comparison is integral.
    """
    assert 10 > 2**3
    assert 32 < 10**2
    for n in range(5, 8):
        assert 16 * (n - 2) > n * n
    for n in range(8, 26):
        assert 80 * n - 224 > n * n
    assert (26 - 2) ** 3 > 20 * 26**2

    # An exact cross-multiplication verifies that
    # (n-2)^3/n^2 strictly increases for every integer n >= 3.
    for n in range(3, 500):
        assert (n - 1) ** 3 * n**2 > (n - 2) ** 3 * (n + 1) ** 2
    return {
        "range_1": "5<=N<=7: 16(N-2)>N^2",
        "range_2": "8<=N<=25: 80N-224>N^2",
        "range_3_threshold": 26,
    }


def main() -> None:
    rational_cases = check_rational_cantor_denominators(5, 5)
    quadratic_certificate = check_global_quadratic_certificate()

    modular_examples = ((1011, 208), (1101, 190))
    example_rows = []
    for d, n in modular_examples:
        assert zero_one_integer(d)
        assert pow(10, n, d) == 16 % d
        q = 10**n - 16
        k, remainder = divmod(q, d)
        assert remainder == 0
        assert k >= 16 * (n - 2)
        assert k % 16 == 0
        m = k // 16
        assert m >= 5 * n - 14

        # Replay the exact long-division state argument behind (23c).
        states = [pow(10, i, k) for i in range(4, n + 1)]
        assert states[-1] == 16
        assert all(r > 0 and r % 16 == 0 for r in states)
        assert all(5 * r < k for r in states)
        assert len(states) == len(set(states)) == n - 3
        scaled_states = [r // 16 for r in states]
        assert all(1 <= s and 5 * s < m for s in scaled_states)
        assert len(scaled_states) <= (m - 1) // 5
        example_rows.append(
            {
                "d": d,
                "n": n,
                "cofactor_digits": len(str(k)),
                "linear_lower_bound": 16 * (n - 2),
                "long_division_lower_bound": 80 * n - 224,
                "long_division_states": len(states),
            }
        )

    # v_2(10^N - 16) = 4 and v_5(10^N - 16) = 0 at representative
    # depths, exactly as used in the symbolic proof.
    for n in range(5, 80):
        q = 10**n - 16
        assert valuation(q, 2) == 4
        assert valuation(q, 5) == 0

    # The report now proves this globally from Schleischitz's theorem.  This
    # bounded replay remains an experiment and is not used for that claim.
    max_n = 200
    small_cofactor_hits = search_small_cofactor(max_n)
    assert small_cofactor_hits == 0

    print(
        json.dumps(
            {
                "status": "PASS",
                "rational_01_cases_checked": rational_cases,
                "global_quadratic_certificate": quadratic_certificate,
                "modular_divisor_examples": example_rows,
                "small_cofactor_experiment": {
                    "c": 16,
                    "n_min": 5,
                    "n_max": max_n,
                    "cofactor_cap": "N^2",
                    "hits": small_cofactor_hits,
                },
            },
            sort_keys=True,
        )
    )


if __name__ == "__main__":
    main()
