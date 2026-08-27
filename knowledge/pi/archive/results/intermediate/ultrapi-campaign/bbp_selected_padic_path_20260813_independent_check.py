#!/usr/bin/env python3
"""Disjoint standard-library replay of the selected three-adic BBP path.

Analytic congruences in the companion audit retain label ``proof sketch``.
Every bounded row computed here has label ``experiment``.  This checker does
not import the primary checker and asserts neither exceptional-path decay nor
the canonical pi digit claim.
"""

from __future__ import annotations

import hashlib
import json
import sys
from fractions import Fraction
from pathlib import Path


sys.set_int_max_str_digits(5_000_000)

SOURCE_SHA256 = (
    "2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825"
)
FROZEN = {
    "problems/local/pi-digits.txt": SOURCE_SHA256,
    "work/ultrapi-resume/bbp_selected_padic_path_20260813.md":
        "5d8a4259ec2ad4f0f0f0d77558ce854ac345a79b10b672060419cc6445e67481",
    "work/ultrapi-resume/bbp_selected_padic_path_20260813_check.py":
        "24f8858a1c80a4df6710c21d5aa09d8d7d4e2a402f789c0c41c9e6b95ff74563",
}

# Literal four-pole BBP data c / ((a*k+b)*16^k).
POLES = (
    (8, 1, 4, 1),
    (2, 1, -1, 2),
    (8, 5, -1, 1),
    (4, 3, -1, 2),
)
EPOCHS = tuple(range(2, 16, 2))
EXPECTED_ROWS = {
    2: (2, 2, 2, 3),
    4: (38, 29, 8, 0),
    6: (524, 29, 8, 0),
    8: (4898, 29, 3, 4),
    10: (57386, 26273, 2, 3),
    12: (175484, 203420, 2, 3),
    14: (3364130, 1797743, 0, 1),
}
EXPECTED_RECORD_SHA256 = (
    "ab6b5f4a7d4d8ffd38e59377c120b17581b2592f1530eaad7f593a287cfeae4b"
)


def root() -> Path:
    return Path(__file__).resolve().parents[2]


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def depth(epoch: int) -> int:
    assert epoch >= 2 and epoch % 2 == 0
    return (5 * 3**epoch - 13) // 8


def split_three(value: int) -> tuple[int, int]:
    assert value > 0
    height = 0
    while value % 3 == 0:
        height += 1
        value //= 3
    return height, value


def rational_mod(value: Fraction, modulus: int) -> int:
    """Reduce an element of Z_(3) modulo a power of three."""
    assert value.denominator % 3 != 0
    return value.numerator * pow(value.denominator, -1, modulus) % modulus


def literal_term(index: int) -> Fraction:
    power = 16**index
    return sum(
        (
            Fraction(coefficient_numerator,
                     coefficient_denominator * (slope * index + intercept) * power)
            for slope, intercept, coefficient_numerator, coefficient_denominator in POLES
        ),
        Fraction(),
    )


def exact_defects() -> list[dict[str, int]]:
    """Fresh literal-pole Fraction replay through the e=8 endpoint."""
    targets = {depth(epoch): epoch for epoch in (2, 4, 6, 8)}
    partial = Fraction()
    values: dict[int, Fraction] = {}
    for index in range(max(targets) + 1):
        partial += literal_term(index)
        if index in targets:
            values[targets[index]] = partial
    result = []
    for epoch in (2, 4, 6):
        defect = 9 * values[epoch + 2] - values[epoch]
        assert rational_mod(defect, 9) == 1
        result.append({
            "epoch": epoch,
            "numerator_mod_9": defect.numerator % 9,
            "denominator_mod_9": defect.denominator % 9,
            "defect_mod_9": 1,
        })
    return result


def shell_table() -> tuple[list[dict[str, int]], int]:
    """Independently enumerate every residue entering the mod-nine shell."""
    expected = (
        (1, 1, 0, 6, 2, 8),
        (4, 4, 0, 3, 5, 8),
        (5, 1, 3, 6, 0, 0),
        (6, 2, 3, 0, 0, 3),
    )
    rows: list[dict[str, int]] = []
    endpoint_checks = 0

    # The values below stabilize for every admissible even epoch.  Checking
    # many instances is only a regression test; the audit gives the algebraic
    # all-depth derivation from M = (5*3^e-13)/8 and N = 9*M+13.
    for epoch in range(2, 162, 2):
        old = depth(epoch)
        new = depth(epoch + 2)
        assert new == 9 * old + 13
        assert old % 9 == 4 and new % 9 == 4
        assert new - old == 5 * 3**epoch
        assert pow(10, new - old, 3 ** (epoch + 2)) == 1
        endpoint_checks += 1

    old = depth(2)
    new = depth(4)
    for pole_index, (slope, intercept, c_num, c_den) in enumerate(POLES):
        assert 8 % slope == 0
        multiplier = 8 // slope
        lift_residue = multiplier * intercept
        assert 0 <= lift_residue < 9

        # Coefficient and constant-term comparison gives the exact identities
        # a(9r+d)+b = 9(ar+b) and 9r+d-r = m(ar+b).
        assert slope * lift_residue + intercept == 9 * intercept
        assert multiplier * slope == 8
        assert multiplier * intercept == lift_residue

        paired_cutoff = (new - lift_residue) // 9
        expected_cutoff = old + (1 if pole_index < 2 else 0)
        assert paired_cutoff == expected_cutoff
        pair_count_mod_three = (paired_cutoff + 1) % 3

        c_mod_three = c_num * pow(c_den, -1, 3) % 3
        paired_each = 3 * (c_mod_three * multiplier % 3) % 9
        paired_total = paired_each * pair_count_mod_three % 9

        full_nonlift = 0
        partial_nonlift = 0
        for residue in range(9):
            linear = slope * residue + intercept
            height, unit = split_three(linear)
            if residue == lift_residue:
                assert height >= 2
                continue
            assert height <= 1
            if height == 1:
                contribution = 3 * (
                    c_mod_three * pow(unit % 3, -1, 3) % 3
                ) % 9
                full_nonlift = (full_nonlift + contribution) % 9
                if residue <= new % 9:
                    partial_nonlift = (partial_nonlift + contribution) % 9
        assert full_nonlift == 0

        boundary = 0
        for extra_index in range(old + 1, paired_cutoff + 1):
            linear = slope * extra_index + intercept
            assert linear % 3 != 0
            boundary += (
                c_num
                * pow(c_den, -1, 9)
                * pow(linear, -1, 9)
                * pow(pow(16, extra_index, 9), -1, 9)
            )
        boundary %= 9
        total = (paired_total + partial_nonlift + boundary) % 9
        observed = (
            lift_residue,
            multiplier,
            paired_total,
            partial_nonlift,
            boundary,
            total,
        )
        assert observed == expected[pole_index], (pole_index, observed)
        rows.append({
            "pole": pole_index + 1,
            "lift_residue": lift_residue,
            "multiplier": multiplier,
            "paired_cutoff_offset": paired_cutoff - old,
            "pair_count_mod_3": pair_count_mod_three,
            "paired_mod_9": paired_total,
            "full_nonlift_mod_9": full_nonlift,
            "partial_nonlift_mod_9": partial_nonlift,
            "boundary_mod_9": boundary,
            "total_mod_9": total,
        })
    assert sum(row["total_mod_9"] for row in rows) % 9 == 1
    return rows, endpoint_checks


def scaled_endpoint_units() -> dict[int, int]:
    """Compute all U_e independently by four separate pole contributions.

    One scan uses the common scale 3^14 and precision 3^16.  At an earlier
    endpoint e, exact divisibility by 3^(14-e) recovers U_e modulo 3^(e+2).
    This differs from the primary checker's combined rational summand and its
    separate scan at each precision.
    """
    scale_epoch = max(EPOCHS)
    modulus = 3 ** (scale_epoch + 2)
    targets = {depth(epoch): epoch for epoch in EPOCHS}
    inverse_sixteen = pow(16, -1, modulus)
    inverse_power = 1
    total = 0
    answer: dict[int, int] = {}

    for index in range(max(targets) + 1):
        for slope, intercept, c_num, c_den in POLES:
            height, unit = split_three(slope * index + intercept)
            shift = scale_epoch - height
            assert shift >= 0
            denominator_unit = c_den * unit
            assert denominator_unit % 3 != 0
            total += (
                c_num
                * 3**shift
                * pow(denominator_unit, -1, modulus)
                * inverse_power
            )
        total %= modulus

        if index in targets:
            epoch = targets[index]
            divisor = 3 ** (scale_epoch - epoch)
            assert total % divisor == 0
            answer[epoch] = total // divisor % 3 ** (epoch + 2)
        inverse_power = inverse_power * inverse_sixteen % modulus
    return answer


def path_rows(units: dict[int, int]) -> tuple[list[dict[str, int]], int]:
    rows: list[dict[str, int]] = []
    for epoch in EPOCHS:
        full_modulus = 3 ** (epoch + 2)
        unit_full = units[epoch]
        unit_visible = unit_full % 3**epoch
        phased = unit_full * pow(10, depth(epoch), full_modulus) % full_modulus
        selected = phased % 3**epoch
        hidden = (phased - selected) // 3**epoch
        lift = (hidden + 1) % 9
        observed = (unit_visible, selected, hidden, lift)
        assert observed == EXPECTED_ROWS[epoch], (epoch, observed)

        if epoch < max(EPOCHS):
            next_unit = units[epoch + 2] % full_modulus
            assert (next_unit - unit_full) % full_modulus == 3**epoch
        rows.append({
            "epoch": epoch,
            "depth": depth(epoch),
            "unit_mod_3e": unit_visible,
            "selected": selected,
            "hidden_carry_mod_9": hidden,
            "next_lift_digit_pair": lift,
            "predicted_next_selected": selected + lift * 3**epoch,
        })

    for lower, upper in zip(rows, rows[1:]):
        assert lower["predicted_next_selected"] == upper["selected"]

    assert [rows[index]["selected"] for index in (1, 2, 3)] == [29, 29, 29]
    assert [rows[index]["next_lift_digit_pair"] for index in (1, 2, 3)] == [0, 0, 4]

    predicted_a16 = rows[-1]["predicted_next_selected"]
    assert predicted_a16 == 1_797_743 + 3**14 == 6_580_712
    return rows, predicted_a16


def affine_recurrence_counts(rows: list[dict[str, int]]) -> tuple[int, int]:
    """Exhaust the usual affine order-one and order-two laws modulo nine."""
    word = [int(row["next_lift_digit_pair"]) for row in rows]
    order_one = 0
    for coefficient in range(9):
        for constant in range(9):
            if all(
                (coefficient * word[index] + constant - word[index + 1]) % 9 == 0
                for index in range(len(word) - 1)
            ):
                order_one += 1

    order_two = 0
    for newest in range(9):
        for older in range(9):
            for constant in range(9):
                if all(
                    (
                        newest * word[index + 1]
                        + older * word[index]
                        + constant
                        - word[index + 2]
                    ) % 9 == 0
                    for index in range(len(word) - 2)
                ):
                    order_two += 1
    assert order_one == order_two == 0
    return order_one, order_two


def main() -> None:
    observed_frozen = {
        relative: sha256(root() / relative)
        for relative in FROZEN
    }
    assert observed_frozen == FROZEN

    shell_rows, endpoint_checks = shell_table()
    defects = exact_defects()
    units = scaled_endpoint_units()
    rows, predicted_a16 = path_rows(units)
    order_one_count, order_two_count = affine_recurrence_counts(rows)

    record = {
        "frozen_inputs": observed_frozen,
        "analytic_claim_label": "proof sketch",
        "bounded_claim_label": "experiment",
        "shell_rows": shell_rows,
        "symbolic_endpoint_regression_checks": endpoint_checks,
        "exact_fraction_defects": defects,
        "rows": rows,
        "visible_state_collision": {"selected": 29, "next_lifts": [0, 0, 4]},
        "predicted_a16": predicted_a16,
        "affine_order_one_laws_mod_9": order_one_count,
        "affine_order_two_laws_mod_9": order_two_count,
        "asserts_all_finite_state_encodings_impossible": False,
        "asserts_exceptional_path_decay": False,
        "asserts_v1": False,
    }
    digest = hashlib.sha256(
        json.dumps(record, sort_keys=True, separators=(",", ":")).encode()
    ).hexdigest()
    if EXPECTED_RECORD_SHA256 != "TO_BE_FROZEN":
        assert digest == EXPECTED_RECORD_SHA256

    print("status=PASS")
    print("analytic_claim_label=proof sketch")
    print("bounded_claim_label=experiment")
    print(f"symbolic_endpoint_regression_checks={endpoint_checks}")
    print(
        "pole_shell_totals_mod_9="
        + ",".join(str(row["total_mod_9"]) for row in shell_rows)
    )
    print(
        "exact_fraction_defects_mod_9="
        + ",".join(str(row["defect_mod_9"]) for row in defects)
    )
    for row in rows:
        print(
            f"epoch_{row['epoch']}=a{row['selected']},"
            f"hidden{row['hidden_carry_mod_9']},"
            f"lift{row['next_lift_digit_pair']}"
        )
    print("visible_state_collision=a29_next_lifts_0_0_4")
    print(f"predicted_a16={predicted_a16}")
    print(f"affine_order_one_laws_mod_9={order_one_count}")
    print(f"affine_order_two_laws_mod_9={order_two_count}")
    print("asserts_all_finite_state_encodings_impossible=false")
    print("asserts_exceptional_path_decay=false")
    print("asserts_v1=false")
    print(f"exact_record_sha256={digest}")


if __name__ == "__main__":
    main()
