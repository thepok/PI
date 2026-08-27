#!/usr/bin/env python3
"""Independent bounded checker for the selected BBP 3-adic shell series.

The companion report gives the all-depth argument.  This standard-library
checker only verifies finite rational/modular instances and a frozen record.
Every computed row has claim label ``experiment``; nothing here asserts
automaticity, algebraicity, exceptional-fibre escape, or canonical V1.
"""

from __future__ import annotations

import hashlib
import json
from itertools import product
from math import gcd
from pathlib import Path


SOURCE_SHA256 = "2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825"
FROZEN = {
    "problems/local/pi-digits.txt": SOURCE_SHA256,
    "work/ultrapi-resume/bbp_three_primary_decimation_20260813.md":
        "29d4f903dca429ebe2cedad248f0a726b985492bfd0f06471a668a47e652ede0",
    "work/theory/pi-quantitative-block-hitting/library/t4/bbp-1997.pdf":
        "e4e0b97fde01328ec41da5f2cd4d6ffc8bcd2b7bd7516b9d8afc320f6d1916c4",
}
RECORD_PATH = "work/ultrapi-resume/bbp_selected_limit_shell_series_20260813_record.json"
RECORD_SHA256 = "3dd091a46e5f363e5c50f289c0c47ab932ab95c376a3287445acc1f23d9f4a8f"
POLES = (
    # linear coefficient, constant coefficient, numerator, denominator
    (8, 1, 4, 1),
    (2, 1, -1, 2),
    (8, 5, -1, 1),
    (4, 3, -1, 2),
)
DIRECT_EPOCHS = (2, 4, 6, 8, 10, 12)
LIMIT_PRECISION = 24
HEIGHT_BOUND = 100_000
EXPECTED_LIMIT_ROWS = {
    2: 2,
    4: 38,
    6: 524,
    8: 4_898,
    10: 57_386,
    12: 175_484,
    14: 3_364_130,
    16: 3_364_130,
    18: 175_551_014,
    20: 2_112_653_459,
    22: 30_006_928_667,
    24: 30_006_928_667,
}
EXPECTED_BASE9 = [2, 4, 6, 6, 8, 2, 6, 0, 4, 5, 8, 0]


def root() -> Path:
    return Path(__file__).resolve().parents[2]


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def depth(epoch: int) -> int:
    return 5 * (3**epoch - 1) // 8 - 1


def split_three(value: int) -> tuple[int, int]:
    exponent = 0
    while value % 3 == 0:
        exponent += 1
        value //= 3
    return exponent, value


def endpoint_unit(epoch: int, precision: int) -> int:
    """Compute 3^epoch B_(M_epoch) modulo 3^precision from four poles."""
    modulus = 3**precision
    inverse_sixteen = pow(16, -1, modulus)
    inverse_power = 1
    total = 0
    for index in range(depth(epoch) + 1):
        for linear, constant, numerator, coefficient_denominator in POLES:
            denominator = coefficient_denominator * (linear * index + constant)
            numerator_height, numerator_unit = split_three(abs(numerator))
            if numerator < 0:
                numerator_unit = -numerator_unit
            denominator_height, denominator_unit = split_three(denominator)
            shift = epoch + numerator_height - denominator_height
            assert shift >= 0
            if shift < precision:
                total += (
                    numerator_unit
                    * 3**shift
                    * pow(denominator_unit, -1, modulus)
                    * inverse_power
                )
                total %= modulus
        inverse_power = inverse_power * inverse_sixteen % modulus
    return total


def rho_mod(precision: int) -> int:
    """The root rho^2=-2 in Z_3 with rho=1 (mod 3), to given precision."""
    value = 1
    power = 3
    for _ in range(1, precision):
        next_power = 3 * power
        candidates = (value, value + power, value + 2 * power)
        value = next(candidate for candidate in candidates
                     if (candidate * candidate + 2) % next_power == 0)
        power = next_power
    assert (value * value + 2) % (3**precision) == 0
    assert value % 3 == 1
    return value


def progression_inverse_sum(
    bound: int, residue: int, step: int, precision: int
) -> int:
    """Sum q^-1 over 1 <= q <= bound, q=residue (mod step), 3 not dividing q.

    Direct enumeration is used when the real interval is shorter.  Otherwise
    terms are grouped by their residue modulo 3^precision.  This is disjoint
    from the direct four-pole endpoint computation above.
    """
    modulus = 3**precision
    assert 1 <= residue <= step
    count = 0 if bound < residue else (bound - residue) // step + 1
    unit_residue_count = 2 * 3 ** (precision - 1)
    if count <= unit_residue_count:
        return sum(
            (pow(q, -1, modulus)
             for q in range(residue, bound + 1, step) if q % 3),
            0,
        ) % modulus

    inverse_modulus = pow(modulus, -1, step)
    period = step * modulus
    total = 0
    for unit in range(1, modulus):
        if unit % 3 == 0:
            continue
        offset = ((residue - unit) * inverse_modulus) % step
        first = unit + offset * modulus
        if first <= bound:
            multiplicity = (bound - first) // period + 1
            total += multiplicity * pow(unit, -1, modulus)
            total %= modulus
    return total


def shell_coefficient(shell: int, precision: int) -> int:
    """C_shell modulo 3^precision from the four stable unit progressions."""
    modulus = 3**precision
    power = 3**shell
    residue_eight = pow(3, shell, 8)
    h1 = progression_inverse_sum(
        5 * power - 1, residue_eight, 8, precision
    )
    h3_residue = 5 * residue_eight % 8
    h3 = progression_inverse_sum(
        5 * power - 1, h3_residue or 8, 8, precision
    )
    h2 = progression_inverse_sum(
        (5 * power - 1) // 4, 1, 2, precision
    )
    h4_residue = 3 * pow(3, shell, 4) % 4
    h4 = progression_inverse_sum(
        (5 * power - 1) // 2, h4_residue or 4, 4, precision
    )
    rho = rho_mod(precision)
    return (4 * rho * (h1 - h3) - 2 * h2 + 4 * h4) % modulus


def limit_mod(precision: int) -> int:
    modulus = 3**precision
    return sum(
        3**shell * shell_coefficient(shell, precision - shell)
        for shell in range(precision)
    ) % modulus


def digits_base_n(value: int, base: int, count: int) -> list[int]:
    digits = []
    for _ in range(count):
        digits.append(value % base)
        value //= base
    return digits


def has_small_rational(value: int, modulus: int, bound: int) -> bool:
    for denominator in range(1, bound + 1):
        if denominator % 3 == 0:
            continue
        numerator = value * denominator % modulus
        if numerator > modulus // 2:
            numerator -= modulus
        if abs(numerator) <= bound and gcd(abs(numerator), denominator) == 1:
            return True
    return False


def has_small_monic_quadratic(value: int, modulus: int, bound: int) -> bool:
    square = value * value % modulus
    for linear in range(-bound, bound + 1):
        constant = -(square + linear * value) % modulus
        if constant > modulus // 2:
            constant -= modulus
        if abs(constant) <= bound:
            return True
    return False


def affine_recurrence_count(digits: list[int], order: int) -> int:
    count = 0
    for coefficients in product(range(9), repeat=order + 1):
        weights = coefficients[:-1]
        constant = coefficients[-1]
        if all(
            digits[index] % 9
            == (sum(weights[offset] * digits[index - order + offset]
                    for offset in range(order)) + constant) % 9
            for index in range(order, len(digits))
        ):
            count += 1
    return count


def build_record() -> dict[str, object]:
    observed = {relative: sha256(root() / relative) for relative in FROZEN}
    assert observed == FROZEN

    limit = limit_mod(LIMIT_PRECISION)
    assert limit == EXPECTED_LIMIT_ROWS[LIMIT_PRECISION]
    base9 = digits_base_n(limit, 9, LIMIT_PRECISION // 2)
    assert base9 == EXPECTED_BASE9

    direct_rows = []
    for epoch in DIRECT_EPOCHS:
        direct = endpoint_unit(epoch, epoch)
        shell = limit % 3**epoch
        assert direct == shell == EXPECTED_LIMIT_ROWS[epoch]
        direct_rows.append({
            "epoch": epoch,
            "depth": depth(epoch),
            "direct_unit_mod_3e": direct,
            "shell_limit_mod_3e": shell,
        })

    limit_rows = []
    for precision, expected in EXPECTED_LIMIT_ROWS.items():
        observed_limit = limit % 3**precision
        assert observed_limit == expected
        limit_rows.append({"precision": precision, "residue": observed_limit})

    modulus = 3**LIMIT_PRECISION
    small_rational = has_small_rational(limit, modulus, HEIGHT_BOUND)
    small_quadratic = has_small_monic_quadratic(limit, modulus, HEIGHT_BOUND)
    assert not small_rational
    assert not small_quadratic
    affine_counts = {
        str(order): affine_recurrence_count(base9, order)
        for order in (1, 2, 3)
    }
    assert affine_counts == {"1": 0, "2": 0, "3": 0}

    return {
        "frozen_inputs": observed,
        "limit_precision_ternary_digits": LIMIT_PRECISION,
        "rho_mod_3pow24": rho_mod(LIMIT_PRECISION),
        "limit_mod_3pow24": limit,
        "base9_digits_least_significant_first": base9,
        "direct_rows": direct_rows,
        "limit_rows": limit_rows,
        "bounded_falsification": {
            "height_bound": HEIGHT_BOUND,
            "small_rational_found": small_rational,
            "small_monic_quadratic_found": small_quadratic,
            "affine_recurrence_counts_over_zmod9": affine_counts,
        },
        "claim_label": "experiment",
        "asserts_irrationality": False,
        "asserts_transcendence": False,
        "asserts_nonautomaticity": False,
        "asserts_exceptional_path_decay": False,
        "asserts_v1": False,
    }


def main() -> None:
    record = build_record()
    encoded = json.dumps(record, indent=2, sort_keys=True) + "\n"
    record_path = root() / RECORD_PATH
    if record_path.exists():
        assert sha256(record_path) == RECORD_SHA256
        assert json.loads(record_path.read_text(encoding="utf-8")) == record
    else:
        print(encoded, end="")
        raise SystemExit("record is not frozen yet")

    print("status=PASS")
    print("claim_label=experiment")
    print(f"limit_mod_3pow24={record['limit_mod_3pow24']}")
    print("base9_digits=" + ",".join(map(
        str, record["base9_digits_least_significant_first"]
    )))
    print("direct_shell_matches=e2,e4,e6,e8,e10,e12")
    print("small_rational_height_le_100000=false")
    print("small_monic_quadratic_height_le_100000=false")
    print("affine_recurrence_orders_1_2_3=false")
    print("asserts_nonautomaticity=false")
    print("asserts_exceptional_path_decay=false")
    print("asserts_v1=false")
    print(f"record_sha256={RECORD_SHA256}")


if __name__ == "__main__":
    main()
