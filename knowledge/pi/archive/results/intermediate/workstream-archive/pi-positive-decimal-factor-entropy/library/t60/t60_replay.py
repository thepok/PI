#!/usr/bin/env python3
"""Replay finite T60 range and exponent calculations.

Finite output is an experiment. The universal derivations are in the note.
"""

from __future__ import annotations

import argparse
import json
from decimal import Decimal, getcontext
from pathlib import Path


CANONICAL_SHA256 = "a70dd741b27595aeb3dfc902b5e201579fed6bae24e2191f58c5ac64a22939e6"
MU_NUMERATOR = 888
LOSS_NUMERATOR = 763
EXPONENT_DENOMINATOR = 125


def decimal_log10(value: Decimal) -> Decimal:
    return value.ln() / Decimal(10).ln()


def fmt(value: Decimal) -> str:
    return format(value.quantize(Decimal("0.000000000001")), "f")


def coefficient_root() -> tuple[Decimal, Decimal]:
    """Bisection for tan(v)=2v; display only, not a proof."""
    import math

    lo = math.pi / 4
    hi = math.pi / 2 - 1e-14
    for _ in range(100):
        mid = (lo + hi) / 2
        if math.tan(mid) - 2 * mid < 0:
            lo = mid
        else:
            hi = mid
    v = Decimal(str((lo + hi) / 2))
    u = Decimal(1) - v / Decimal(str(math.pi))
    return v, u


def exponent_condition(q: int, n: int) -> bool:
    """Exact form of q^(763/125) <= 10^n."""
    return q**LOSS_NUMERATOR <= 10 ** (EXPONENT_DENOMINATOR * n)


def audit(n: int) -> dict[str, object]:
    assert n >= 2
    length = 10 ** (n // 2)
    bandwidth = 10**n // 2
    assert 2 * bandwidth == 10**n
    assert length >= n

    rectangle = sum(length - r for r in range(1, n))
    rectangle_formula = (n - 1) * length - n * (n - 1) // 2
    assert rectangle == rectangle_formula

    exponent_eligible = 0
    exact_cutoffs: list[dict[str, int]] = []
    for r in range(1, n):
        count = 0
        for j in range(length - r):
            q = 10**j * (10**r - 1)
            if exponent_condition(q, n):
                count += 1
                assert LOSS_NUMERATOR * (j + r - 1) <= EXPONENT_DENOMINATOR * n
            else:
                # q grows by exactly ten when j increases.
                break
        exponent_eligible += count
        exact_cutoffs.append({"r": r, "eligible_j_count": count})

    coarse_bound = n * ((EXPONENT_DENOMINATOR * n) // LOSS_NUMERATOR + 2)
    assert exponent_eligible <= coarse_bound

    # The legal endpoint at r=1 has q=9*10^(L-2).
    log_q_endpoint = Decimal(length - 2) + decimal_log10(Decimal(9))
    loss = Decimal(LOSS_NUMERATOR) / Decimal(EXPONENT_DENOMINATOR)
    t56_log_loss = loss * log_q_endpoint - Decimal(n)

    log_h = decimal_log10(Decimal(bandwidth - 1))
    log_H = decimal_log10(Decimal(bandwidth))
    grid_log_loss = loss * (log_H + log_h + log_q_endpoint) - decimal_log10(Decimal(2))
    vaaler_zero_log_loss = loss * (
        decimal_log10(Decimal(2)) + log_H + log_q_endpoint
    ) - decimal_log10(Decimal(2))

    return {
        "n": n,
        "L_n": length,
        "H_n": bandwidth,
        "lag_range": [1, n - 1],
        "frequency_range": [1, bandwidth - 1],
        "rectangle_size": rectangle,
        "rectangle_formula": rectangle_formula,
        "exponent_eligible_positions": exponent_eligible,
        "coarse_O_n_squared_bound": coarse_bound,
        "per_lag_cutoffs": exact_cutoffs,
        "endpoint_q": f"9*10^{length - 2}",
        "T56_window_log10_loss": fmt(t56_log_loss),
        "H_grid_half_cell_log10_loss_a_1": fmt(grid_log_loss),
        "Vaaler_zero_complete_grid_half_cell_log10_loss": fmt(vaaler_zero_log_loss),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--write", type=Path)
    args = parser.parse_args()

    getcontext().prec = 80
    assert MU_NUMERATOR - EXPONENT_DENOMINATOR == LOSS_NUMERATOR
    v_root, u_root = coefficient_root()
    result = {
        "label": "experiment",
        "canonical_statement_sha256": CANONICAL_SHA256,
        "irrationality_exponent": "888/125 = 7.104",
        "near_integer_loss": "763/125 = 6.104",
        "coefficient_transition": {
            "equation": "tan(v)=2v; u=1-v/pi",
            "v_approx": fmt(v_root),
            "u_approx": fmt(u_root),
        },
        "symbolic_identities": {
            "requested_grid_bound":
                "||h*q*pi-k/H||_T > 1/(H*(H*h*q)^(763/125))",
            "two_H_grid_bound":
                "||h*q*pi-k/(2H)||_T > 1/(2H*(2H*h*q)^(763/125))",
            "actual_Vaaler_zero_bound":
                "||q*pi-k/(2H)||_T > 1/(2H*(2H*q)^(763/125)), k odd",
            "half_cell_loss": "(a*H*h*q)^(763/125)/2",
            "T56_exclusion_condition": "q^763 <= 10^(125*n)",
        },
        "audits": [audit(n) for n in range(2, 9)],
        "scope": {
            "proves_universal_formulas": False,
            "proves_fixed_pi_incidence_bound": False,
            "proves_C7": False,
            "proves_C2": False,
            "proves_C1": False,
        },
    }
    text = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.write:
        args.write.write_text(text, encoding="ascii")
    print(text, end="")


if __name__ == "__main__":
    main()
