#!/usr/bin/env python3
"""Exact-arithmetic replay for T63's abstract phase separation.

This does not test pi.  It checks the finite parameter family and the rational
upper/lower certificates stated in T63_AOC4_VAALER_CROSSWALK.md.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
from fractions import Fraction
from pathlib import Path


CANONICAL_SHA256 = "a70dd741b27595aeb3dfc902b5e201579fed6bae24e2191f58c5ac64a22939e6"
T43_SHA256 = "7b71b5f9dc7003f0d2d47861ad399db88a0ffaf920d669a97fda092df407afed"


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def ceil_sqrt(x: int) -> int:
    root = math.isqrt(x)
    return root if root * root == x else root + 1


def sum_integers(lo: int, hi: int) -> int:
    if hi < lo:
        return 0
    count = hi - lo + 1
    return count * (lo + hi) // 2


def sum_squares(hi: int) -> int:
    if hi <= 0:
        return 0
    return hi * (hi + 1) * (2 * hi + 1) // 6


def fraction_text(x: Fraction) -> str:
    return f"{x.numerator}/{x.denominator}"


def decimal_text(x: Fraction, places: int = 12) -> str:
    scale = 10**places
    rounded = (x.numerator * scale + x.denominator // 2) // x.denominator
    integer, fractional = divmod(rounded, scale)
    return f"{integer}.{fractional:0{places}d}"


def certificate(n: int) -> dict[str, object]:
    if n < 16 or n % 4 != 0:
        raise ValueError("each n must be a multiple of 4 and at least 16")

    # Exact T56/T61 scales.
    sample_length = 10 ** (n // 2)
    bandwidth = 10**n // 2

    # First canonical T43 block is [1, first_block_power + 1).
    first_block_power = 1 << ((sample_length - 1).bit_length() - 1)
    width_squared = first_block_power**2 + 2 * first_block_power

    root_n_upper = ceil_sqrt(n)
    selected_k_min = 6 * n
    selected_k_max = first_block_power // root_n_upper
    selected_k_count = max(0, selected_k_max - selected_k_min + 1)
    if selected_k_count == 0:
        raise AssertionError("selected k interval unexpectedly empty")

    # At every selected k, the T56 short labels are v=k-r, 1<=r<n.
    selected_v_count_per_k = n - 1

    def first_block_lambda(k: int, v: int) -> int:
        return (v - n + 1 if v >= n else 0) + max(k - 2 * n + 1 - v, 0)

    for k in (selected_k_min, selected_k_max):
        breakpoints = {0, n - 1, n, k - 2 * n, k - 2 * n + 1, k - 1}
        values = [first_block_lambda(k, v) for v in breakpoints if 0 <= v < k]
        assert min(values) == k - 3 * n + 2
        assert max(values) == k - n
        assert 2 * (k - 3 * n + 2) >= k

    # The phase 1/2 is in terminal shell K_n and has exact weight 2^-K_n.
    shell_count = (10**n - 1).bit_length() - 1
    terminal_shell_weight = Fraction(1, 2**shell_count)
    assert Fraction(1, 10**n) < terminal_shell_weight
    assert terminal_shell_weight <= Fraction(2, 10**n)

    k_sum = sum_integers(selected_k_min, selected_k_max)
    sqrt_k_upper = ceil_sqrt(selected_k_max)

    # For selected k, G_k <= k^2/B, mu_k-tau <= (n-1)/k,
    # Xi_k <= 4n^2/k^2, and Var_k <= (n-1)/k.  The last two
    # inequalities give G_k*sqrt(Xi_k Var_k)
    # <= 2*n*ceil(sqrt(n))*ceil(sqrt(K))/B.
    base_terminal_shell = (
        terminal_shell_weight * sample_length * (sample_length - 1) / 2
    )
    selected_mean_excess = Fraction(
        selected_v_count_per_k * k_sum, first_block_power
    )
    selected_covariance = Fraction(
        2
        * n
        * root_n_upper
        * selected_k_count
        * sqrt_k_upper,
        first_block_power,
    )
    aoc_lhs_upper = 2 * (
        base_terminal_shell + selected_mean_excess + selected_covariance
    )

    # Use the literal AOC_4 target with s=3/4.
    aoc_rhs = Fraction(sample_length, 1) + Fraction(
        sample_length**2, 10 ** (3 * n // 4)
    )
    aoc_constant_upper = aoc_lhs_upper / aoc_rhs

    # T61's complete majorant is at least one at phase zero, by T61's
    # kernel-checked pointwise majorization.  All other terms are nonnegative.
    t61_complete_lower = selected_v_count_per_k * selected_k_count
    t61_complete_ratio_lower = Fraction(t61_complete_lower, sample_length)

    # The positive-frequency signed part subtracts the zero mode 2/H for
    # every label in the full short rectangle, not just the selected labels.
    short_rectangle_card = (
        (n - 1) * sample_length - n * (n - 1) // 2
    )
    t61_signed_lower = Fraction(t61_complete_lower, 1) - Fraction(
        2 * short_rectangle_card, bandwidth
    )
    t61_signed_ratio_lower = t61_signed_lower / sample_length

    assert first_block_power < sample_length
    assert selected_k_max <= first_block_power
    assert selected_k_min >= 6 * n
    assert width_squared == first_block_power**2 + 2 * first_block_power
    assert aoc_constant_upper < 1

    return {
        "n": n,
        "sample_length": f"10^{n // 2}",
        "bandwidth": f"10^{n}/2",
        "first_block_power_over_L_decimal": decimal_text(
            Fraction(first_block_power, sample_length)
        ),
        "width_identity_checked": "W^2=B^2+2B",
        "selected_k_min": selected_k_min,
        "selected_k_max_decimal_digits": len(str(selected_k_max)),
        "selected_k_count_decimal_digits": len(str(selected_k_count)),
        "selected_v_count_per_k": selected_v_count_per_k,
        "terminal_shell_index": shell_count,
        "terminal_shell_weight": f"2^-{shell_count}",
        "aoc_constant_upper_decimal": decimal_text(aoc_constant_upper),
        "t61_complete_over_L_lower_decimal": decimal_text(
            t61_complete_ratio_lower
        ),
        "t61_signed_over_L_lower_decimal": decimal_text(t61_signed_ratio_lower),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--scales",
        nargs="+",
        type=int,
        default=[16, 64, 256, 1024],
        help="multiples of four, each at least 16",
    )
    parser.add_argument("--write", type=Path)
    args = parser.parse_args()

    root = Path(__file__).resolve().parent
    canonical = root / "pi-positive-decimal-factor-entropy.txt"
    t43 = root / "T43_AVERAGED_ORBIT_CORRELATION.md"
    if sha256(canonical) != CANONICAL_SHA256:
        raise SystemExit("canonical statement hash mismatch")
    if sha256(t43) != T43_SHA256:
        raise SystemExit("T43 source hash mismatch")

    rows = [certificate(n) for n in args.scales]
    exact_rows = [
        Fraction(
            (n - 1)
            * max(
                0,
                ((1 << (((10 ** (n // 2)) - 1).bit_length() - 1)) // ceil_sqrt(n))
                - 6 * n
                + 1,
            ),
            10 ** (n // 2),
        )
        for n in args.scales
    ]
    if any(b <= a for a, b in zip(exact_rows, exact_rows[1:])):
        raise AssertionError("displayed T61 lower ratios must increase")

    result = {
        "claim_status": "experiment",
        "scope": "abstract finite phase family, not the fixed phase pi",
        "canonical_sha256": CANONICAL_SHA256,
        "t43_source_sha256": T43_SHA256,
        "phase_assignment": {
            "selected_short_labels": "0",
            "all_other_labels": "1/2",
        },
        "checks": {
            "all_aoc_constant_upper_bounds_below_1": True,
            "lambda_breakpoints_and_width_identities": True,
            "t61_complete_ratios_strictly_increase": True,
            "arithmetic": "integers and fractions only",
        },
        "scales": rows,
    }
    rendered = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.write:
        args.write.write_text(rendered, encoding="ascii")
    else:
        print(rendered, end="")


if __name__ == "__main__":
    main()
