#!/usr/bin/env python3
"""Exact certificate replay for T64's decimal-orbit counterexample.

The seed is alpha=0 at every scale.  No digits of pi and no floating-point
arithmetic are used.  The script checks the integer inequalities underlying
the geometric-mass lower bound and the T61-majorant upper bound.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from fractions import Fraction
from pathlib import Path


CANONICAL_SHA256 = "a70dd741b27595aeb3dfc902b5e201579fed6bae24e2191f58c5ac64a22939e6"

# The optional --constants interface deliberately supports exact witnesses
# whose decimal representations exceed Python's conservative default limit.
sys.set_int_max_str_digits(0)


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def fraction_text(value: Fraction) -> str:
    return f"{value.numerator}/{value.denominator}"


def decimal_text(value: Fraction, places: int = 12) -> str:
    scale = 10**places
    rounded = (value.numerator * scale + value.denominator // 2) // value.denominator
    integer, fractional = divmod(rounded, scale)
    return f"{integer}.{fractional:0{places}d}"


def scale_certificate(n: int) -> dict[str, object]:
    if n < 16 or n % 4 != 0:
        raise ValueError("n must be a multiple of four and at least 16")

    sample_length = 10 ** (n // 2)
    bandwidth = 10**n // 2
    first_block_power = 1 << ((sample_length - 1).bit_length() - 1)
    first_selected_k = first_block_power // 2
    selected_k_count = first_block_power // 2  # B/2 <= k < B

    assert first_block_power <= sample_length - 1 < 2 * first_block_power
    assert 4 * first_block_power > sample_length
    assert first_selected_k >= 6 * n
    assert 5 * n < 31 * first_selected_k

    def first_block_lambda(k: int, v: int) -> int:
        return (v - n + 1 if v >= n else 0) + max(k - 2 * n + 1 - v, 0)

    for k in (first_selected_k, first_block_power - 1):
        breakpoints = {0, n - 1, n, k - 2 * n, k - 2 * n + 1, k - 1}
        for v in breakpoints:
            if 0 <= v < k:
                lam = first_block_lambda(k, v)
                assert lam >= k - 3 * n + 2
                assert 2 * lam >= k

    # For every selected k and v<k, Lambda(v,k) >= k/2.  Since
    # W=sqrt(B^2+2B)<2B, each G_k>B/16 and there are B/2 selected k.
    geometric_mass_lower = Fraction(first_block_power**2, 32)
    universal_geometric_lower = Fraction(sample_length**2, 512)
    assert geometric_mass_lower > universal_geometric_lower

    # The note proves 1 <= M_H(0) < 3.  The complete short rectangle has
    # cardinality < nL, hence its T61 total is <3nL.
    t61_total_upper = 3 * n * sample_length
    short_rectangle_card = (
        (n - 1) * sample_length - n * (n - 1) // 2
    )
    assert 0 < short_rectangle_card < n * sample_length
    residual_over_L_lower = Fraction(sample_length, 512) - 3 * n
    assert residual_over_L_lower > 0
    assert (
        universal_geometric_lower - t61_total_upper
        == residual_over_L_lower * sample_length
    )

    return {
        "n": n,
        "sample_length": f"10^{n // 2}",
        "bandwidth": f"10^{n}/2",
        "first_block_power_bits": first_block_power.bit_length(),
        "first_block_power_over_L_decimal": decimal_text(
            Fraction(first_block_power, sample_length)
        ),
        "selected_k_range": "B/2 <= k < B",
        "selected_k_count_decimal_digits": len(str(selected_k_count)),
        "strict_activity_checked_at_left_endpoint": True,
        "centered_aoc_quantity": "0",
        "short_rectangle_card": str(short_rectangle_card),
        "t61_total_strict_upper": f"3*{n}*10^{n // 2}",
        "geometric_mass_strict_lower": f"10^{n}/512",
        "residual_over_L_strict_lower": fraction_text(residual_over_L_lower),
        "certified_integer_comparison_constants_below":
            residual_over_L_lower.numerator // residual_over_L_lower.denominator,
    }


def constant_certificate(k: int) -> dict[str, object]:
    if k < 0:
        raise ValueError("comparison constants must be nonnegative integers")
    n = 4 * (k + 4)
    sample_length = 10 ** (n // 2)
    margin = Fraction(sample_length, 512) - 3 * n
    assert sample_length > 512 * (13 * k + 48)
    assert margin > k
    row = scale_certificate(n)
    return {
        "comparison_constant_K": k,
        "chosen_scale_n": n,
        "same_seed": "alpha=0",
        "certified_abs_residual_gt_K_times_L": True,
        "residual_over_L_strict_lower": f"10^{n // 2}/512-{3 * n}",
        "residual_over_L_lower_exceeds_K": margin > k,
        "sample_length_decimal_digits": n // 2 + 1,
        "first_block_power_bits": row["first_block_power_bits"],
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--scales",
        nargs="+",
        type=int,
        default=[16, 32, 64, 128],
        help="declared multiples of four, each at least 16",
    )
    parser.add_argument(
        "--constants",
        nargs="+",
        type=int,
        default=[0, 10, 100, 1000],
        help="integer comparison constants K; uses n=4(K+4)",
    )
    parser.add_argument("--write", type=Path)
    args = parser.parse_args()

    root = Path(__file__).resolve().parent
    canonical = root / "pi-positive-decimal-factor-entropy.txt"
    if sha256(canonical) != CANONICAL_SHA256:
        raise SystemExit("canonical statement hash mismatch")

    scales = [scale_certificate(n) for n in args.scales]
    constants = [constant_certificate(k) for k in args.constants]
    result = {
        "claim_status": "experiment",
        "argument_status": "proof sketch",
        "scope": (
            "universal finite restricted-Schur inequality on decimal-orbit "
            "phase vectors; not the fixed-pi all-scale claim"
        ),
        "canonical_sha256": CANONICAL_SHA256,
        "phase_seed": "alpha=0",
        "seed_varies_with_scale": False,
        "arithmetic": "integers and fractions only",
        "analytic_input_proved_in_note_not_recomputed": "1 <= M_H(0) < 3 for H>=2",
        "verification_scope": (
            "checks canonical hash, scale witnesses, block endpoints, Lambda "
            "case breakpoints, short cardinality, and final rational bounds"
        ),
        "candidate_inequality": (
            "abs(COV residual) <= 2*sum_k G_k*sqrt(Xi_k*Var_k) + C*L"
        ),
        "scales": scales,
        "constant_certificates": constants,
    }
    rendered = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.write:
        args.write.write_text(rendered, encoding="ascii")
    else:
        print(rendered, end="")


if __name__ == "__main__":
    main()
