#!/usr/bin/env python3
"""Finite numerical audit for the exact T59 formulas; universal claims are not proved."""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path


CANONICAL_SHA256 = "a70dd741b27595aeb3dfc902b5e201579fed6bae24e2191f58c5ac64a22939e6"


def fejer(H: int, x: float) -> float:
    denominator = math.sin(math.pi * x)
    if abs(denominator) < 1e-14:
        return float(H)
    return math.sin(math.pi * H * x) ** 2 / (H * denominator**2)


def coefficient(H: int, h: int) -> float:
    t = h / H
    return (math.sin(math.pi * t) / math.pi + 2 * (1 - t) * math.cos(math.pi * t)) / H


def vaaler_weight(t: float) -> float:
    return math.pi * t * (1 - abs(t)) / math.tan(math.pi * t) + abs(t)


def sawtooth(x: float) -> float:
    nearest = round(x)
    if abs(x - nearest) < 1e-14:
        return 0.0
    return x - math.floor(x) - 0.5


def sawtooth_polynomial(H: int, x: float) -> float:
    return -sum(
        vaaler_weight(h / H) * math.sin(2 * math.pi * h * x) / (math.pi * h)
        for h in range(1, H)
    )


def majorant(H: int, x: float) -> float:
    return 2 / H + 2 * sum(
        coefficient(H, h) * math.cos(2 * math.pi * h * x)
        for h in range(1, H)
    )


def shifted_majorant(H: int, x: float) -> float:
    delta = 1 / (2 * H)
    return (
        1 / H
        + sawtooth_polynomial(H, x - delta)
        - sawtooth_polynomial(H, x + delta)
        + (fejer(H, x - delta) + fejer(H, x + delta)) / (2 * H)
    )


def fejer_zero_closed_form(H: int) -> float:
    a = math.pi / (2 * H)
    return (
        (1 / math.sin(a) ** 2 + 1 / math.sin(3 * a) ** 2) / H**2
        + (1 / math.tan(3 * a) - 1 / math.tan(a)) / (math.pi * H)
    )


def audit(n: int) -> dict[str, object]:
    L = 10 ** (n // 2)
    H = 10**n // 2
    rectangle_size = sum(L - r for r in range(1, n))
    expected_size = (n - 1) * L - n * (n - 1) // 2
    delta = 1 / (2 * H)
    points = {
        "strict_endpoint": delta,
        "fejer_zero": 1 / H,
        "vaaler_zero": 3 / (2 * H),
    }
    values = {
        name: {
            "x": x,
            "M_H": majorant(H, x),
            "K_over_H": fejer(H, x) / H,
            "strict_incidence": abs(x) < delta,
        }
        for name, x in points.items()
    }
    tolerance = 2e-9
    assert rectangle_size == expected_size
    assert abs(values["strict_endpoint"]["M_H"] - 1) < tolerance
    assert values["strict_endpoint"]["strict_incidence"] is False
    assert abs(values["fejer_zero"]["K_over_H"]) < tolerance
    assert values["fejer_zero"]["M_H"] >= 4 / (9 * math.pi**2) - tolerance
    assert abs(values["vaaler_zero"]["M_H"]) < tolerance
    assert values["vaaler_zero"]["K_over_H"] >= 4 / (9 * math.pi**2) - tolerance
    for x in points.values():
        assert abs(majorant(H, x) - shifted_majorant(H, x)) < tolerance
    assert abs(values["fejer_zero"]["M_H"] - fejer_zero_closed_form(H)) < tolerance
    # A finite mesh independently checks the source inequality and majorization.
    if H <= 500:
        for index in range(4 * H):
            x = index / (4 * H)
            error = abs(sawtooth(x) - sawtooth_polynomial(H, x))
            assert error <= fejer(H, x) / (2 * H) + tolerance
            strict_indicator = min(x, 1 - x) < delta
            assert shifted_majorant(H, x) + tolerance >= int(strict_indicator)
    assert coefficient(H, H - 1) < 0
    return {
        "n": n,
        "L_n": L,
        "H_n": H,
        "frequency_range": [1, H - 1],
        "rectangle_size": rectangle_size,
        "rectangle_formula": expected_size,
        "rectangle_over_L": rectangle_size / L,
        "last_coefficient": coefficient(H, H - 1),
        "separation_values": values,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--write", type=Path)
    args = parser.parse_args()
    result = {
        "label": "experiment",
        "canonical_statement_sha256": CANONICAL_SHA256,
        "audits": [audit(n) for n in range(2, 7)],
        "scope": {
            "proves_universal_vaaler_formula": False,
            "proves_fixed_pi_estimate": False,
            "proves_T56_predicate": False,
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
