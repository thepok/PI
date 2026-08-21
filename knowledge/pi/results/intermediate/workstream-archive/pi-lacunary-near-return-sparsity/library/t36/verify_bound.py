#!/usr/bin/env python3
"""Replay finite checks for the T36 proof sketch.

All model errors and budgets are computed with Fraction. Floating point is
used only for trigonometric displays and a sampled check of the closed-form
optimization; neither is presented as a universal proof.
"""

from __future__ import annotations

import hashlib
import json
import math
from fractions import Fraction
from pathlib import Path


EXPECTED_STATEMENT_SHA256 = (
    "cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8"
)


def denominator(j: int, s: int) -> int:
    assert j >= 0 and s >= 1
    return 10**j * (10**s - 1)


def circle_distance(x: Fraction) -> Fraction:
    floor = x.numerator // x.denominator
    low = x - floor
    return min(low, 1 - low)


def fejer_one(x: Fraction) -> float:
    return 1.0 + math.cos(2.0 * math.pi * float(x))


def m_closed(x: float, y: float) -> float:
    if x >= 0.5 and x + y >= 1.0:
        return 1.0
    if x < 0.5:
        return (x / max(0.5, 1.0 - y)) ** 2
    assert x + y < 1.0 and x < 1.0 and y < 1.0
    return max((y / (1.0 - x)) ** 2, (x / (1.0 - y)) ** 2)


def m_sampled(x: float, y: float, steps: int = 200_000) -> float:
    best = 0.0
    for n in range(steps + 1):
        lam = 0.5 + 0.5 * n / steps
        left = 1.0 if lam <= x else (x / lam) ** 2
        one_minus = 1.0 - lam
        right = 1.0 if one_minus <= y else (y / one_minus) ** 2
        best = max(best, left * right)
    return best


def check_model(
    *,
    name: str,
    u_factor: int,
    j: int,
    s: int,
    beta0: Fraction,
    a0: int,
    a1: int,
    m0: int,
    m1: int,
) -> dict[str, object]:
    q = denominator(j, s)
    beta1 = u_factor * beta0
    e0 = abs(q * beta0 - a0)
    e1 = abs(q * beta1 - a1)
    budget = q * e1 + u_factor * q * e0
    assert 1 <= s and j + s < m0 and j + s < m1
    return {
        "name": name,
        "U": u_factor,
        "j": j,
        "s": s,
        "Q": q,
        "beta0": str(beta0),
        "beta1": str(beta1),
        "a0": a0,
        "a1": a1,
        "e0": str(e0),
        "e1": str(e1),
        "mixed_budget": str(budget),
        "fejer_H1_product": round(
            fejer_one(q * beta0) * fejer_one(q * beta1), 12
        ),
    }


def main() -> None:
    root = Path(__file__).resolve().parent
    statement = root / "canonical_statement.txt"
    packaged_statement = statement.read_bytes()
    # apply_patch packages text with one terminal LF; the immutable source has
    # none. Remove exactly that transport byte before checking source bytes.
    assert packaged_statement.endswith(b"\n")
    assert not packaged_statement.endswith(b"\n\n")
    statement_hash = hashlib.sha256(packaged_statement[:-1]).hexdigest()
    assert statement_hash == EXPECTED_STATEMENT_SHA256

    # Exact denominator strata and decimal bounds.
    stratum_limit = 8
    strata = []
    all_denominators: set[int] = set()
    for ell in range(1, stratum_limit):
        values = []
        for j in range(ell):
            s = ell - j
            q = denominator(j, s)
            assert q == 10**ell - 10**j
            assert 9 * 10 ** (ell - 1) <= q < 10**ell
            assert q not in all_denominators
            all_denominators.add(q)
            values.append(q)
        assert len(values) == ell
        assert values == sorted(values, reverse=True)
        strata.append({"ell": ell, "count": len(values), "Q": values})
    assert len(all_denominators) == stratum_limit * (stratum_limit - 1) // 2

    # Injective range and the sharp equality collision.
    h0, h1, u_factor = 4, 3, 9
    frequencies: dict[int, tuple[int, int]] = {}
    for u in range(-h0, h0 + 1):
        for v in range(-h1, h1 + 1):
            w = u + u_factor * v
            assert w not in frequencies
            frequencies[w] = (u, v)
    equality_collision = {
        "H0": 4,
        "H1": 1,
        "U": 8,
        "left_pair": [-4, 1],
        "right_pair": [4, 0],
        "frequency": 4,
    }
    assert -4 + 8 * 1 == 4 + 8 * 0

    cycle = check_model(
        name="exact_cycle",
        u_factor=9,
        j=0,
        s=1,
        beta0=Fraction(1, 9),
        a0=1,
        a1=9,
        m0=3,
        m1=2,
    )
    assert cycle["e0"] == "0" and cycle["e1"] == "0"
    assert cycle["mixed_budget"] == "0"
    assert abs(float(cycle["fejer_H1_product"]) - 4.0) < 1e-12
    cycle.update(
        {
            "boundary_class": "good",
            "actual_boundary_contribution": 0.0,
            "candidate_DBL_check": True,
        }
    )

    positive_preperiod = check_model(
        name="exact_positive_preperiod",
        u_factor=99,
        j=1,
        s=1,
        beta0=Fraction(1, 2),
        a0=45,
        a1=4455,
        m0=5,
        m1=3,
    )
    assert positive_preperiod["e0"] == "0"
    assert positive_preperiod["e1"] == "0"
    assert positive_preperiod["mixed_budget"] == "0"
    assert abs(float(positive_preperiod["fejer_H1_product"]) - 4.0) < 1e-12
    positive_preperiod.update(
        {
            "boundary_class": "good",
            "actual_boundary_contribution": 0.0,
            "candidate_DBL_check": True,
        }
    )
    # Every 10^a-1 and 99(10^a-1) is odd.
    for period in range(1, 25):
        cycle_q = 10**period - 1
        assert circle_distance(Fraction(cycle_q, 2)) == Fraction(1, 2)
        assert circle_distance(Fraction(99 * cycle_q, 2)) == Fraction(1, 2)

    large_q = denominator(0, 6)
    perturbed = check_model(
        name="large_denominator_mixed_failure",
        u_factor=9,
        j=0,
        s=6,
        beta0=Fraction(11, 10 * large_q),
        a0=1,
        a1=10,
        m0=8,
        m1=7,
    )
    assert perturbed["e0"] == "1/10" and perturbed["e1"] == "1/10"
    assert perturbed["mixed_budget"] == str(large_q)
    exact_perturbed_weight = (15.0 + 5.0 * math.sqrt(5.0)) / 8.0
    assert abs(
        float(perturbed["fejer_H1_product"]) - exact_perturbed_weight
    ) < 1e-12

    # Sample the exact closed form against its defining one-variable maximum.
    optimization_cases = [
        (0.10, 0.20),
        (0.20, 0.90),
        (0.55, 0.20),
        (0.70, 0.35),
        (2.00, 3.00),
    ]
    optimization = []
    for x, y in optimization_cases:
        closed = m_closed(x, y)
        sampled = m_sampled(x, y)
        assert abs(closed - sampled) < 2e-5
        optimization.append(
            {
                "x": x,
                "y": y,
                "closed": round(closed, 12),
                "sampled": round(sampled, 12),
            }
        )

    # In the perturbed model H0=H1=1, so A0=A1=2 and m=1.
    x_q = 9 * large_q / 4
    y_q = large_q / 4
    assert m_closed(x_q, y_q) == 1.0
    assert float(perturbed["fejer_H1_product"]) <= 4.0
    perturbed.update(
        {
            "boundary_class": "mixed_budget_failure",
            "actual_boundary_contribution": perturbed["fejer_H1_product"],
            "candidate_per_pair_cap": 4.0,
            "candidate_DBL_check": True,
        }
    )

    output = {
        "label": "experiment",
        "canonical_statement_sha256": statement_hash,
        "denominator_strata": {
            "L": stratum_limit,
            "total_pairs": len(all_denominators),
            "strata": strata,
        },
        "frequency_injectivity": {
            "verified_case": {"H0": h0, "H1": h1, "U": u_factor},
            "frequency_count": len(frequencies),
            "sharp_equality_collision": equality_collision,
        },
        "models": [cycle, positive_preperiod, perturbed],
        "perturbed_exact_fejer_product": "(15 + 5*sqrt(5))/8",
        "perturbed_fraction_of_maximum": round(exact_perturbed_weight / 4.0, 12),
        "mixed_envelope_optimization_samples": optimization,
        "verdict": "OPEN WITH ONE NAMED ESTIMATE: Fixed-Stratum Fejer Spike (FSFS)",
    }
    print(json.dumps(output, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
