#!/usr/bin/env python3
"""Exact bounded audit of the coherent three-adic BBP endpoint path.

All finite rows have claim label ``experiment``.  The script also checks the
finite rational instances used to audit the elementary all-depth identities in
the companion report.  It imports no branch checker and asserts no decay or V1.
"""

from __future__ import annotations

import hashlib
import json
import sys
from fractions import Fraction
from math import gcd
from pathlib import Path


sys.set_int_max_str_digits(5_000_000)

SOURCE_SHA256 = "2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825"
FROZEN = {
    "problems/local/pi-digits.txt": SOURCE_SHA256,
    "work/ultrapi-resume/bbp_three_primary_decimation_20260813.md":
        "29d4f903dca429ebe2cedad248f0a726b985492bfd0f06471a668a47e652ede0",
    "work/ultrapi-resume/bbp_cf36_gowers_cube_persistence_20260813.md":
        "3bd9a948945570e975defd7bd2297338da0068f9c82eb027be84364a66bb528e",
    "work/ultrapi-resume/bbp_exceptional_path_actual_complement_20260813.md":
        "95e3b5d67784adefeda89357b3c652b7dd2b9d2550a26f00dedf2a0f489e01dc",
}
POLES = (
    (8, 1, Fraction(4)),
    (2, 1, Fraction(-1, 2)),
    (8, 5, Fraction(-1)),
    (4, 3, Fraction(-1, 2)),
)
EXACT_EPOCHS = (2, 4, 6, 8)
MODULAR_EPOCHS = (2, 4, 6, 8, 10, 12, 14)
EXPECTED = {
    2: (2, 2, 3),
    4: (38, 29, 0),
    6: (524, 29, 0),
    8: (4898, 29, 4),
    10: (57386, 26273, 3),
    12: (175484, 203420, 3),
    14: (3364130, 1797743, 1),
}


def root() -> Path:
    return Path(__file__).resolve().parents[2]


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def depth(epoch: int) -> int:
    return 5 * (3**epoch - 1) // 8 - 1


def coefficient(index: int) -> Fraction:
    return Fraction(
        120 * index * index + 151 * index + 47,
        (2 * index + 1) * (4 * index + 3)
        * (8 * index + 1) * (8 * index + 5) * 16**index,
    )


def split_power_three(value: int) -> tuple[int, int]:
    exponent = 0
    while value % 3 == 0:
        exponent += 1
        value //= 3
    return exponent, value


def rational_mod(value: Fraction, modulus: int) -> int:
    denominator_height, denominator_unit = split_power_three(value.denominator)
    numerator_height, numerator_unit = split_power_three(abs(value.numerator))
    assert denominator_height == 0 and numerator_height == 0
    if value.numerator < 0:
        numerator_unit = -numerator_unit
    return numerator_unit * pow(denominator_unit, -1, modulus) % modulus


def endpoint_unit(epoch: int) -> int:
    """Return U_e=3^e B_{M_e} modulo 3^(e+2), term by term."""
    precision = epoch + 2
    modulus = 3**precision
    inverse_power = 1
    inverse_sixteen = pow(16, -1, modulus)
    total = 0
    for index in range(depth(epoch) + 1):
        numerator = 120 * index * index + 151 * index + 47
        denominator = (
            (2 * index + 1) * (4 * index + 3)
            * (8 * index + 1) * (8 * index + 5)
        )
        common = gcd(numerator, denominator)
        numerator //= common
        denominator //= common
        numerator_height, numerator_unit = split_power_three(numerator)
        denominator_height, denominator_unit = split_power_three(denominator)
        shift = epoch + numerator_height - denominator_height
        assert shift >= 0
        if shift < precision:
            total += (
                numerator_unit * 3**shift
                * pow(denominator_unit, -1, modulus) * inverse_power
            )
            total %= modulus
        inverse_power = inverse_power * inverse_sixteen % modulus
    return total


def exact_partial_sums() -> dict[int, Fraction]:
    targets = {depth(epoch): epoch for epoch in EXACT_EPOCHS}
    total = Fraction()
    answer: dict[int, Fraction] = {}
    for index in range(max(targets) + 1):
        total += coefficient(index)
        if index in targets:
            answer[targets[index]] = total
    return answer


def all_depth_symbolic_checks() -> int:
    """Check endpoint algebra and the modulo-9 pole boundary pattern."""
    checks = 0
    for epoch in range(2, 162, 2):
        old = depth(epoch)
        new = depth(epoch + 2)
        assert new == 9 * old + 13
        assert new - old == 5 * 3**epoch
        assert old % 9 == 4 and new % 9 == 4
        assert pow(10, 5 * 3**epoch, 3 ** (epoch + 2)) == 1
        # At endpoint M_e the pole quotients floor((a M_e+b)/3^e)
        # have the stable residues needed by the report's finite-shell audit.
        expected = ((4, 8), (1, 2), (4, 8), (2, 4))
        for (a, b, _), (old_q, new_q) in zip(POLES, expected):
            if epoch >= 4:
                assert (a * old + b) // 3**epoch % 9 == old_q
                assert (a * new + b) // 3**epoch % 9 == new_q
        checks += 1
    return checks


def defect_shell_table() -> list[dict[str, int]]:
    """Audit the residue table proving D_e = 1 (mod 9).

    In the decimation expansion, paired errors are 3*c_i*m_i (mod 9).
    Complete nine-blocks of nonlift height-one terms cancel, so only residues
    0,...,4 remain because M_(e+2) = 4 (mod 9).  The regular boundary has
    f_1(M_e+1)+f_2(M_e+1), with M_e+1 = 5 (mod 9).
    """
    multipliers = (1, 4, 1, 2)
    pair_counts_mod_three = (0, 0, 2, 2)
    expected = (
        (0, 6, 2, 8),
        (0, 3, 5, 8),
        (3, 6, 0, 0),
        (3, 0, 0, 3),
    )
    rows: list[dict[str, int]] = []
    for pole_index, ((a, b, coefficient_value), multiplier, pair_count) in enumerate(
        zip(POLES, multipliers, pair_counts_mod_three)
    ):
        coefficient_mod_three = (
            coefficient_value.numerator
            * pow(coefficient_value.denominator, -1, 3)
        ) % 3
        paired_each = 3 * (coefficient_mod_three * multiplier % 3) % 9
        paired_total = paired_each * pair_count % 9

        full_block = 0
        partial_nonlift = 0
        for residue in range(9):
            linear = a * residue + b
            if linear % 3 == 0 and linear % 9 != 0:
                unit = linear // 3 % 3
                value = 3 * (
                    coefficient_mod_three * pow(unit, -1, 3) % 3
                ) % 9
                full_block = (full_block + value) % 9
                if residue <= 4:
                    partial_nonlift = (partial_nonlift + value) % 9
        assert full_block == 0

        boundary = 0
        if pole_index < 2:
            boundary_index = 5
            linear = a * boundary_index + b
            coefficient_mod_nine = (
                coefficient_value.numerator
                * pow(coefficient_value.denominator, -1, 9)
            ) % 9
            boundary = (
                coefficient_mod_nine
                * pow(linear, -1, 9)
                * pow(pow(16, boundary_index, 9), -1, 9)
            ) % 9
        total = (paired_total + partial_nonlift + boundary) % 9
        observed = (paired_total, partial_nonlift, boundary, total)
        assert observed == expected[pole_index], (pole_index, observed)
        rows.append({
            "pole": pole_index + 1,
            "paired_mod_9": paired_total,
            "nonlift_mod_9": partial_nonlift,
            "boundary_mod_9": boundary,
            "total_mod_9": total,
        })
    assert sum(row["total_mod_9"] for row in rows) % 9 == 1
    return rows


def main() -> None:
    observed = {relative: sha256(root() / relative) for relative in FROZEN}
    assert observed == FROZEN
    symbolic_checks = all_depth_symbolic_checks()
    shell_table = defect_shell_table()
    exact = exact_partial_sums()

    exact_defects = []
    for epoch in EXACT_EPOCHS[:-1]:
        defect = 9 * exact[epoch + 2] - exact[epoch]
        assert rational_mod(defect, 9) == 1
        exact_defects.append({"epoch": epoch, "defect_mod_9": 1})

    rows = []
    for epoch in MODULAR_EPOCHS:
        unit_full = endpoint_unit(epoch)
        unit = unit_full % 3**epoch
        modulus = 3 ** (epoch + 2)
        phased = unit_full * pow(10, depth(epoch), modulus) % modulus
        selected = phased % 3**epoch
        hidden_carry = (phased - selected) // 3**epoch
        lift = (hidden_carry + 1) % 9
        assert (unit, selected, lift) == EXPECTED[epoch]
        rows.append({
            "epoch": epoch,
            "depth": depth(epoch),
            "unit_mod_3e": unit,
            "selected": selected,
            "hidden_carry_mod_9": hidden_carry,
            "next_lift_digit_pair": lift,
            "predicted_next_selected": selected + lift * 3**epoch,
        })
    for lower, upper in zip(rows, rows[1:]):
        assert lower["predicted_next_selected"] == upper["selected"]

    # Same visible selected residue a_e, different hidden carry, hence different
    # next lift.  This is a finite counterexample to the state choice a_e alone.
    assert rows[1]["selected"] == rows[2]["selected"] == rows[3]["selected"] == 29
    assert [rows[i]["next_lift_digit_pair"] for i in (1, 2, 3)] == [0, 0, 4]

    record = {
        "frozen_inputs": observed,
        "symbolic_endpoint_checks": symbolic_checks,
        "defect_shell_table": shell_table,
        "exact_defects": exact_defects,
        "rows": rows,
        "visible_state_collision": {"selected": 29, "next_lifts": [0, 0, 4]},
        "claim_label": "experiment",
        "asserts_finite_state_impossibility_for_all_encodings": False,
        "asserts_exceptional_path_decay": False,
        "asserts_v1": False,
    }
    digest = hashlib.sha256(
        json.dumps(record, sort_keys=True, separators=(",", ":")).encode()
    ).hexdigest()
    print("status=PASS")
    print("claim_label=experiment")
    print(f"symbolic_endpoint_checks={symbolic_checks}")
    print(
        "defect_shell_totals_mod_9="
        + ",".join(str(row["total_mod_9"]) for row in shell_table)
    )
    print("exact_defects_mod_9=" + ",".join(str(row["defect_mod_9"]) for row in exact_defects))
    for row in rows:
        print(
            f"epoch_{row['epoch']}=a{row['selected']},"
            f"hidden{row['hidden_carry_mod_9']},lift{row['next_lift_digit_pair']}"
        )
    print("visible_state_collision=a29_next_lifts_0_0_4")
    print("asserts_finite_state_impossibility_for_all_encodings=false")
    print("asserts_exceptional_path_decay=false")
    print("asserts_v1=false")
    print(f"exact_record_sha256={digest}")


if __name__ == "__main__":
    main()
