#!/usr/bin/env python3
"""Disjoint audit replay for the selected BBP three-adic shell limit.

The all-depth series derivation retains label ``proof sketch``.  All rows
computed here have label ``experiment``.  This standard-library checker does
not import or call the primary checker and asserts no correlation decay or V1.
"""

from __future__ import annotations

import hashlib
import json
import sys
from fractions import Fraction
from itertools import product
from math import gcd
from pathlib import Path


sys.set_int_max_str_digits(5_000_000)

FROZEN = {
    "problems/local/pi-digits.txt":
        "2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825",
    "work/ultrapi-resume/bbp_selected_limit_shell_series_20260813.md":
        "3a5b5c8604b21e9ff960c4b33933731d16eb7fec83d862dda0075df9da4c4664",
    "work/ultrapi-resume/bbp_selected_limit_shell_series_20260813_check.py":
        "2959de8d8952fa2255d4f725f3bba9eea813fdc497d85951ef7a2c655b63c764",
    "work/ultrapi-resume/bbp_selected_limit_shell_series_20260813_record.json":
        "3dd091a46e5f363e5c50f289c0c47ab932ab95c376a3287445acc1f23d9f4a8f",
    "work/ultrapi-resume/bbp_three_primary_decimation_20260813.md":
        "29d4f903dca429ebe2cedad248f0a726b985492bfd0f06471a668a47e652ede0",
    "work/theory/pi-quantitative-block-hitting/library/t4/bbp-1997.pdf":
        "e4e0b97fde01328ec41da5f2cd4d6ffc8bcd2b7bd7516b9d8afc320f6d1916c4",
}

# a_i, b_i, numerator(c_i), denominator(c_i)
POLES = ((8, 1, 4, 1), (2, 1, -1, 2), (8, 5, -1, 1), (4, 3, -1, 2))
DIRECT_EPOCHS = tuple(range(2, 16, 2))
LIMIT_PRECISION = 24
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
EXPECTED_RECORD_DIGEST = (
    "4bbe61999f11732ceb6007aabc1b37aaf838144a4a2083a65bbb60bb77c7989f"
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


def four_pole_term(index: int) -> Fraction:
    power = 16**index
    return sum(
        (
            Fraction(c_num, c_den * (a * index + b) * power)
            for a, b, c_num, c_den in POLES
        ),
        Fraction(),
    )


def combined_term(index: int) -> Fraction:
    return Fraction(
        120 * index * index + 151 * index + 47,
        (2 * index + 1)
        * (4 * index + 3)
        * (8 * index + 1)
        * (8 * index + 5)
        * 16**index,
    )


def endpoint_maxima(epoch: int) -> tuple[int, int, int, int]:
    m = depth(epoch)
    direct = tuple(a * m + b for a, b, _, _ in POLES)
    formula = (
        5 * 3**epoch - 12,
        (5 * 3**epoch - 9) // 4,
        5 * 3**epoch - 8,
        (5 * 3**epoch - 7) // 2,
    )
    assert direct == formula
    return direct


def stable_progression(pole: int, shell: int) -> tuple[int, int, int]:
    power = 3**shell
    if pole == 0:
        return 5 * power - 1, power % 8 or 8, 8
    if pole == 1:
        return (5 * power - 1) // 4, 1, 2
    if pole == 2:
        return 5 * power - 1, 5 * power % 8 or 8, 8
    if pole == 3:
        return (5 * power - 1) // 2, 3 * power % 4 or 4, 4
    raise AssertionError(pole)


def progression_values(bound: int, residue: int, step: int) -> list[int]:
    return [q for q in range(residue, bound + 1, step) if q % 3]


def actual_shell_values(pole: int, epoch: int, shell: int) -> list[int]:
    assert shell <= epoch
    a, b, _, _ = POLES[pole]
    scale = 3 ** (epoch - shell)
    maximum = endpoint_maxima(epoch)[pole]
    quotient_bound = maximum // scale
    return [
        q
        for q in range(1, quotient_bound + 1)
        if q % 3 and (q * scale - b) % a == 0
    ]


def endpoint_and_stabilization_audit() -> dict[str, object]:
    endpoint_checks = 0
    for epoch in range(2, 82, 2):
        maxima = endpoint_maxima(epoch)
        assert maxima[1] < 3 ** (epoch + 1)
        assert maxima[3] < 3 ** (epoch + 1)
        for pole in (0, 2):
            assert 3 ** (epoch + 1) <= maxima[pole] < 2 * 3 ** (epoch + 1)
            a, b, _, _ = POLES[pole]
            # q=1 is the only possible unit quotient at height e+1.
            assert (3 ** (epoch + 1) - b) % a != 0
        endpoint_checks += 1

    thresholds: dict[str, int] = {}
    equality_checks = 0
    for pole in range(4):
        for shell in range(9):
            bound, residue, step = stable_progression(pole, shell)
            stable = progression_values(bound, residue, step)
            first = None
            for epoch in range(2, 42, 2):
                if epoch < shell:
                    continue
                if actual_shell_values(pole, epoch, shell) == stable:
                    if all(
                        actual_shell_values(pole, later, shell) == stable
                        for later in range(epoch, 42, 2)
                    ):
                        first = epoch
                        break
            assert first is not None
            thresholds[f"pole_{pole + 1}_shell_{shell}"] = first
            equality_checks += (42 - first + 1) // 2
    return {
        "endpoint_formula_checks": endpoint_checks,
        "stable_shell_equality_checks": equality_checks,
        "first_stable_even_epochs": thresholds,
    }


def rho_mod(precision: int) -> int:
    """Newton-Hensel lift of rho^2=-2 from rho=1 (mod 3)."""
    value = 1
    known = 1
    while known < precision:
        new_known = min(2 * known, precision)
        modulus = 3**new_known
        value = (
            value
            - (value * value + 2) * pow(2 * value, -1, modulus)
        ) % modulus
        known = new_known
    assert value % 3 == 1
    assert (value * value + 2) % 3**precision == 0
    return value


def root_audit(precision: int) -> dict[str, int]:
    modulus = 3**precision
    rho = rho_mod(precision)
    roots = (rho, 4 % modulus, 4 * rho % modulus, -8 % modulus)
    for (a, b, _, _), root_value in zip(POLES, roots):
        assert root_value % 3 == 1
        assert pow(root_value, a, modulus) == pow(16, b, modulus)
    assert rho * rho % modulus == -2 % modulus
    assert pow(rho, 4, modulus) == 4
    return {
        "rho_mod_3pow24": rho,
        "root_1_8": roots[0],
        "root_1_2": roots[1],
        "root_5_8": roots[2],
        "root_3_4": roots[3],
    }


def pole_limit_root(pole: int, precision: int) -> int:
    modulus = 3**precision
    rho = rho_mod(precision)
    return (rho, 4 % modulus, 4 * rho % modulus, -8 % modulus)[pole]


def inverse_progression_sum(
    bound: int, residue: int, step: int, precision: int
) -> int:
    """Sum reciprocal units by deleting full 3^precision index blocks.

    Because step is a unit modulo 3^precision, a block of that many indices
    visits every residue once.  Inversion permutes the units, whose sum is
    zero modulo the odd prime power.  Only the incomplete index block remains.
    This derivation and implementation differ from the primary CRT grouping.
    """
    modulus = 3**precision
    assert gcd(step, modulus) == 1
    count = 0 if bound < residue else (bound - residue) // step + 1
    _, remainder = divmod(count, modulus)
    total = 0
    for index in range(remainder):
        q = residue + step * index
        if q % 3:
            total += pow(q % modulus, -1, modulus)
    return total % modulus


def shell_coefficient(shell: int, precision: int) -> int:
    modulus = 3**precision
    hs = []
    for pole in range(4):
        bound, residue, step = stable_progression(pole, shell)
        hs.append(inverse_progression_sum(bound, residue, step, precision))
    rho = rho_mod(precision)
    return (4 * rho * (hs[0] - hs[2]) - 2 * hs[1] + 4 * hs[3]) % modulus


def shell_phase_convergence_audit() -> int:
    """Check actual finite phases against their pole-shell limits."""
    checks = 0
    for pole, (a, b, c_num, c_den) in enumerate(POLES):
        for shell in range(7):
            bound, residue, step = stable_progression(pole, shell)
            stable = progression_values(bound, residue, step)
            for epoch in range(max(2, shell + (shell % 2)), 16, 2):
                if actual_shell_values(pole, epoch, shell) != stable:
                    continue
                precision = epoch + 1
                modulus = 3**precision
                actual = 0
                limiting = 0
                root_value = pole_limit_root(pole, precision)
                for q in stable:
                    k = (q * 3 ** (epoch - shell) - b) // a
                    assert k >= 0
                    scalar = (
                        c_num
                        * 3**shell
                        * pow(c_den * q, -1, modulus)
                    )
                    actual += scalar * pow(16, -k, modulus)
                    limiting += scalar * root_value
                # The phase quotient is a 3^(e-s)-th power in 1+3Z_3,
                # so its difference from one has valuation at least e-s+1.
                assert (actual - limiting) % modulus == 0
                checks += 1
    return checks


def radix_nine_refinement_audit() -> int:
    """Replay SL19 and a sufficiently long truncation of SL20 modulo 3^10."""
    precision = 10
    modulus = 3**precision
    digits = (1, 2, 4, 5, 7, 8)
    terms = (precision + 1) // 2
    checks = 0
    for shell in range(6):
        old_bound = 5 * 3**shell - 1
        new_bound = 5 * 3 ** (shell + 2) - 1
        assert new_bound == 9 * old_bound + 8
        for residue in range(1, 9):
            direct = inverse_progression_sum(new_bound, residue, 8, precision)
            decomposed = 0
            expanded = 0
            for digit in digits:
                for u in range(old_bound + 1):
                    if (u + digit - residue) % 8:
                        continue
                    denominator = 9 * u + digit
                    decomposed += pow(denominator, -1, modulus)
                    expanded += sum(
                        pow(-9, n, modulus)
                        * pow(u, n, modulus)
                        * pow(pow(digit, n + 1, modulus), -1, modulus)
                        for n in range(terms)
                    )
            assert (direct - decomposed) % modulus == 0
            assert (direct - expanded) % modulus == 0
            checks += 1
    return checks


def limit_mod(precision: int) -> int:
    modulus = 3**precision
    partial = 0
    for shell in range(precision):
        partial += 3**shell * shell_coefficient(shell, precision - shell)
    return partial % modulus


def direct_endpoint_units() -> dict[int, int]:
    """One scaled four-pole scan through e=14, unlike the primary replay."""
    scale_epoch = max(DIRECT_EPOCHS)
    modulus = 3**scale_epoch
    targets = {depth(epoch): epoch for epoch in DIRECT_EPOCHS}
    inverse_sixteen = pow(16, -1, modulus)
    inverse_power = 1
    total = 0
    answer: dict[int, int] = {}

    for index in range(max(targets) + 1):
        if index < 12:
            assert four_pole_term(index) == combined_term(index)
        for a, b, c_num, c_den in POLES:
            height, unit = split_three(a * index + b)
            shift = scale_epoch - height
            assert shift >= 0
            total += (
                c_num
                * 3**shift
                * pow(c_den * unit, -1, modulus)
                * inverse_power
            )
        total %= modulus
        if index in targets:
            epoch = targets[index]
            divisor = 3 ** (scale_epoch - epoch)
            assert total % divisor == 0
            answer[epoch] = total // divisor % 3**epoch
        inverse_power = inverse_power * inverse_sixteen % modulus
    return answer


def limit_and_direct_audit() -> tuple[int, list[dict[str, int]]]:
    limit = limit_mod(LIMIT_PRECISION)
    assert limit == EXPECTED_LIMIT_ROWS[LIMIT_PRECISION]
    for precision, expected in EXPECTED_LIMIT_ROWS.items():
        assert limit % 3**precision == expected

    direct = direct_endpoint_units()
    rows = []
    for epoch in DIRECT_EPOCHS:
        shell_approximation = limit_mod(epoch)
        assert direct[epoch] == shell_approximation == limit % 3**epoch
        assert direct[epoch] == EXPECTED_LIMIT_ROWS[epoch]
        rows.append({
            "epoch": epoch,
            "depth": depth(epoch),
            "direct_four_pole_unit": direct[epoch],
            "independent_shell_approximation": shell_approximation,
            "limit_reduction": limit % 3**epoch,
        })
    return limit, rows


def base_digits(value: int, base: int, count: int) -> list[int]:
    result = []
    for _ in range(count):
        result.append(value % base)
        value //= base
    return result


def selected_lifts(limit: int) -> list[dict[str, int]]:
    rows = []
    values = {}
    for epoch in range(2, LIMIT_PRECISION + 1, 2):
        selected = limit * pow(10, depth(epoch), 3**epoch) % 3**epoch
        values[epoch] = selected
    for epoch in range(2, LIMIT_PRECISION - 1, 2):
        lift = (values[epoch + 2] - values[epoch]) // 3**epoch
        assert values[epoch + 2] % 3**epoch == values[epoch]
        assert 0 <= lift < 9
        rows.append({
            "epoch": epoch,
            "selected": values[epoch],
            "next_lift_pair": lift,
            "next_selected": values[epoch + 2],
        })
    return rows


def complement_separator(lift_rows: list[dict[str, int]]) -> dict[str, int]:
    checked_terms = 0
    for row in lift_rows[:6]:
        epoch = row["epoch"]
        modulus = 3**epoch
        period = 3 ** (epoch - 2)
        selected = row["selected"]
        power = 1
        for _ in range(period):
            primary = selected * power % modulus
            artificial_weight_exponent = -primary % modulus
            assert (primary + artificial_weight_exponent) % modulus == 0
            power = power * 10 % modulus
            checked_terms += 1
    return {
        "exact_cancelled_terms": checked_terms,
        "all_resulting_characters_equal_one": True,
        "asserts_artificial_weight_is_bbp_complement": False,
    }


def bounded_falsifications(limit: int, digits: list[int]) -> dict[str, object]:
    modulus = 3**LIMIT_PRECISION
    height_bound = 100_000
    rational_found = False
    for denominator in range(1, height_bound + 1):
        if denominator % 3 == 0:
            continue
        numerator = limit * denominator % modulus
        numerator = min(numerator, numerator - modulus, key=abs)
        if abs(numerator) <= height_bound and gcd(abs(numerator), denominator) == 1:
            rational_found = True
            break

    square = limit * limit % modulus
    quadratic_found = False
    for linear in range(-height_bound, height_bound + 1):
        constant = -(square + linear * limit) % modulus
        constant = min(constant, constant - modulus, key=abs)
        if abs(constant) <= height_bound:
            quadratic_found = True
            break

    affine_counts = {}
    for order in (1, 2, 3):
        count = 0
        for parameters in product(range(9), repeat=order + 1):
            weights, constant = parameters[:-1], parameters[-1]
            if all(
                digits[index]
                == (
                    sum(
                        weights[offset] * digits[index - order + offset]
                        for offset in range(order)
                    )
                    + constant
                ) % 9
                for index in range(order, len(digits))
            ):
                count += 1
        affine_counts[str(order)] = count
    assert not rational_found and not quadratic_found
    assert affine_counts == {"1": 0, "2": 0, "3": 0}
    return {
        "height_bound": height_bound,
        "small_rational_found": rational_found,
        "small_monic_quadratic_found": quadratic_found,
        "affine_recurrence_counts_mod_9": affine_counts,
    }


def main() -> None:
    frozen = {relative: sha256(root() / relative) for relative in FROZEN}
    assert frozen == FROZEN
    endpoint_audit = endpoint_and_stabilization_audit()
    roots = root_audit(LIMIT_PRECISION)
    phase_convergence_checks = shell_phase_convergence_audit()
    radix_refinement_checks = radix_nine_refinement_audit()
    limit, direct_rows = limit_and_direct_audit()
    digits = base_digits(limit, 9, LIMIT_PRECISION // 2)
    assert digits == EXPECTED_BASE9
    lifts = selected_lifts(limit)
    separator = complement_separator(lifts)
    bounded = bounded_falsifications(limit, digits)

    record = {
        "frozen_inputs": frozen,
        "analytic_claim_label": "proof sketch",
        "bounded_claim_label": "experiment",
        "endpoint_and_stabilization": endpoint_audit,
        "root_audit": roots,
        "shell_phase_convergence_checks": phase_convergence_checks,
        "radix_nine_refinement_checks": radix_refinement_checks,
        "limit_mod_3pow24": limit,
        "base9_digits_least_significant_first": digits,
        "direct_shell_rows": direct_rows,
        "selected_lifts": lifts,
        "complement_separator": separator,
        "bounded_falsifications": bounded,
        "asserts_rationality_classification": False,
        "asserts_automaticity_classification": False,
        "asserts_actual_complement_control": False,
        "asserts_exceptional_path_decay": False,
        "asserts_v1": False,
    }
    digest = hashlib.sha256(
        json.dumps(record, sort_keys=True, separators=(",", ":")).encode()
    ).hexdigest()
    if EXPECTED_RECORD_DIGEST != "TO_BE_FROZEN":
        assert digest == EXPECTED_RECORD_DIGEST

    print("status=PASS")
    print("analytic_claim_label=proof sketch")
    print("bounded_claim_label=experiment")
    print(f"endpoint_formula_checks={endpoint_audit['endpoint_formula_checks']}")
    print(f"stable_shell_equality_checks={endpoint_audit['stable_shell_equality_checks']}")
    print(f"rho_mod_3pow24={roots['rho_mod_3pow24']}")
    print(f"shell_phase_convergence_checks={phase_convergence_checks}")
    print(f"radix_nine_refinement_checks={radix_refinement_checks}")
    print(f"limit_mod_3pow24={limit}")
    print("base9_digits=" + ",".join(map(str, digits)))
    print("direct_shell_matches=" + ",".join(f"e{e}" for e in DIRECT_EPOCHS))
    print("selected_lift_pairs=" + ",".join(str(row["next_lift_pair"]) for row in lifts))
    print(f"complement_separator_terms={separator['exact_cancelled_terms']}")
    print("small_rational_height_le_100000=false")
    print("small_monic_quadratic_height_le_100000=false")
    print("affine_recurrence_orders_1_2_3=false")
    print("asserts_actual_complement_control=false")
    print("asserts_exceptional_path_decay=false")
    print("asserts_v1=false")
    print(f"exact_record_sha256={digest}")


if __name__ == "__main__":
    main()
