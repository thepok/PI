#!/usr/bin/env python3
"""Exact finite checks for the leading three-adic unit of Machin seeds.

All computed output has claim status ``experiment``.  The checker uses exact
``Fraction`` and modular integer arithmetic.  It neither evaluates pi nor
reads a table of its digits.
"""

from __future__ import annotations

import argparse
import hashlib
from collections import defaultdict
from fractions import Fraction
from math import gcd
from pathlib import Path

from actual_numerator_phase_experiment import machin_seed, valuation


SOURCE_SHA256 = (
    "2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825"
)


def source_path() -> Path:
    return Path(__file__).resolve().parents[2] / "problems/local/pi-digits.txt"


def three_exponent(index: int) -> int:
    """Return the a for which 3^a <= 12*index+3 < 3^(a+1)."""
    cutoff = 12 * index + 3
    exponent = 0
    power = 1
    while 3 * power <= cutoff:
        power *= 3
        exponent += 1
    assert power <= cutoff < 3 * power
    return exponent


def rat_mod(value: Fraction, modulus: int) -> int:
    """Reduce a rational whose denominator is a unit modulo ``modulus``."""
    if gcd(value.denominator, modulus) != 1:
        raise AssertionError(("nonunit rational denominator", modulus))
    return value.numerator * pow(value.denominator, -1, modulus) % modulus


def cancellation_quotient_mod(exponent: int, modulus: int) -> int:
    """Return (4*239^exponent-5^exponent)/3 modulo ``modulus``."""
    lifted_modulus = 3 * modulus
    residue = (
        4 * pow(239, exponent, lifted_modulus)
        - pow(5, exponent, lifted_modulus)
    ) % lifted_modulus
    if residue % 3:
        raise AssertionError(("cancellation quotient", exponent, modulus))
    return residue // 3


def raw_shell_unit_mod(index: int, exponent_a: int, power_k: int) -> int:
    """Compute D_j*seed_j mod 3^k from only nonvanishing 3-adic shells."""
    modulus = 3**power_k
    cutoff = 12 * index + 3
    primary = 3 ** (exponent_a - 1)
    total = 0

    for exponent in range(1, cutoff + 1, 2):
        order = valuation(exponent, 3)
        scaled_order = exponent_a - order
        if scaled_order >= power_k:
            continue
        unit_exponent = exponent // (3**order)
        sign = -1 if ((exponent - 1) // 2) & 1 else 1
        cancellation = cancellation_quotient_mod(exponent, modulus)
        denominator = (
            unit_exponent
            * pow(5, exponent, modulus)
            * pow(239, exponent, modulus)
        ) % modulus
        contribution = (
            4
            * sign
            * 3**scaled_order
            * cancellation
            * pow(denominator, -1, modulus)
        )
        total = (total + contribution) % modulus

    # The base-239 Taylor prefix has the one extra exponent cutoff+2.
    # It disappears once 3^(a-1) itself is zero modulo 3^k.
    if exponent_a - 1 < power_k:
        endpoint = cutoff + 2
        sign = -1 if ((endpoint - 1) // 2) & 1 else 1
        denominator = endpoint * pow(239, endpoint, modulus) % modulus
        total += (
            primary * (-4) * sign * pow(denominator, -1, modulus)
        )

    return pow(10, index, modulus) * total % modulus


def stabilized_shell_unit_mod(index: int, exponent_a: int, power_k: int) -> int:
    """Finite epoch formula valid when a >= k+1.

    The retained common exponents are H*t with
    H=3^(a-k+1) and odd t<3^k.  Unit powers stabilize modulo 3^k, so only
    v_3(t), t modulo 4, and the moving cutoff remain.
    """
    if exponent_a < power_k + 1:
        raise ValueError("stabilized formula requires a >= k+1")
    modulus = 3**power_k
    cutoff = 12 * index + 3
    shell_step = 3 ** (exponent_a - power_k + 1)
    last_multiplier = cutoff // shell_step
    total = 0

    for multiplier in range(1, last_multiplier + 1, 2):
        multiplier_order = valuation(multiplier, 3)
        multiplier_unit = multiplier // (3**multiplier_order)
        if multiplier_order >= power_k:
            raise AssertionError(("shell multiplier range", multiplier))

        exponent = shell_step * multiplier
        sign = -1 if ((exponent - 1) // 2) & 1 else 1

        # After multiplication by 3^(k-1-s), only the residue modulo
        # 3^(s+1) matters.  Euler periodicity makes the displayed fixed
        # exponents equivalent to the actual exponent.
        local_modulus = 3 ** (multiplier_order + 1)
        cancellation = cancellation_quotient_mod(
            3 ** (multiplier_order + 1), local_modulus
        )
        base_product = pow(
            5 * 239, 3**multiplier_order, modulus
        )
        denominator = multiplier_unit * base_product % modulus
        contribution = (
            4
            * sign
            * 3 ** (power_k - 1 - multiplier_order)
            * cancellation
            * pow(denominator, -1, modulus)
        )
        total = (total + contribution) % modulus

    return pow(10, index, modulus) * total % modulus


def predicted_unit_mod_nine(index: int, exponent_a: int) -> int:
    """Closed three-stage formula for D_j*seed_j modulo nine, a>=3."""
    if exponent_a < 3:
        raise ValueError("mod-nine stage formula requires a >= 3")
    cutoff = 12 * index + 3
    primary = 3 ** (exponent_a - 1)
    stage = 1 + int(cutoff >= 5 * primary) + int(cutoff >= 7 * primary)
    if exponent_a & 1:
        return {1: 1, 2: 4, 3: 7}[stage]
    return {1: 8, 2: 5, 3: 2}[stage]


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-j", type=int, default=150)
    parser.add_argument("--max-k", type=int, default=6)
    args = parser.parse_args()
    if args.max_j < 2:
        raise SystemExit("--max-j must be at least two")
    if not 1 <= args.max_k <= 8:
        raise SystemExit("--max-k must lie in 1..8")

    digest = hashlib.sha256(source_path().read_bytes()).hexdigest()
    if digest != SOURCE_SHA256:
        raise AssertionError(("target hash", digest))

    seeds: list[Fraction | None] = [None]
    valuation_checks = 0
    unit_mod_three_checks = 0
    unit_mod_nine_checks = 0
    raw_shell_checks = 0
    stabilized_shell_checks = 0
    reduced_numerator_checks = 0
    coarse_selection_checks = 0
    recurrence_checks = 0
    forcing_mod_nine_pattern_checks = 0
    coarse_residues: dict[tuple[int, int], set[int]] = defaultdict(set)
    fine_residues: dict[tuple[int, int], set[int]] = defaultdict(set)
    first_coarse_not_unit: tuple[int, int, int] | None = None

    for index in range(1, args.max_j + 1):
        seed = machin_seed(index)
        seeds.append(seed)
        exponent_a = three_exponent(index)
        primary = 3 ** (exponent_a - 1)
        if valuation(seed.denominator, 3) != exponent_a - 1:
            raise AssertionError(("three-primary denominator", index))
        if valuation(abs(seed.numerator), 3) != 0:
            raise AssertionError(("three-primary numerator", index))
        valuation_checks += 1

        scaled_unit = primary * seed
        expected_mod_three = 1 if exponent_a & 1 else 2
        actual_mod_three = rat_mod(scaled_unit, 3)
        if actual_mod_three != expected_mod_three:
            raise AssertionError(("unit modulo three", index))
        unit_mod_three_checks += 1

        if exponent_a >= 3:
            actual_mod_nine = rat_mod(scaled_unit, 9)
            expected_mod_nine = predicted_unit_mod_nine(index, exponent_a)
            if actual_mod_nine != expected_mod_nine:
                raise AssertionError(("unit modulo nine", index))
            unit_mod_nine_checks += 1

        denominator = seed.denominator
        factor = denominator // primary
        if denominator != factor * primary or gcd(factor, primary) != 1:
            raise AssertionError(("coprime denominator split", index))
        residue = seed.numerator % denominator
        remainder = residue % factor
        coarse = (residue - remainder) // factor
        if not 0 <= coarse < primary:
            raise AssertionError(("coarse quotient range", index))

        unit_mod_primary = rat_mod(scaled_unit, primary)
        fine_mod_primary = remainder * pow(factor, -1, primary) % primary
        if coarse % primary != (unit_mod_primary - fine_mod_primary) % primary:
            raise AssertionError(("coarse selection identity", index))
        coarse_selection_checks += 1

        cutoff = 12 * index + 3
        stage = (
            1 + int(cutoff >= 5 * primary) + int(cutoff >= 7 * primary)
        )
        key = (exponent_a % 2, stage)
        coarse_residues[key].add(coarse % 3)
        fine_residues[key].add(fine_mod_primary % 3)
        if first_coarse_not_unit is None and coarse % 3 != actual_mod_three:
            first_coarse_not_unit = (index, coarse % 3, actual_mod_three)

        for power_k in range(1, args.max_k + 1):
            modulus = 3**power_k
            actual = rat_mod(scaled_unit, modulus)
            raw = raw_shell_unit_mod(index, exponent_a, power_k)
            if actual != raw:
                raise AssertionError(
                    ("raw shell formula", index, power_k, actual, raw)
                )
            raw_shell_checks += 1

            if seed.numerator % modulus != factor * actual % modulus:
                raise AssertionError(("reduced numerator formula", index, power_k))
            reduced_numerator_checks += 1

            if exponent_a >= power_k + 1:
                stabilized = stabilized_shell_unit_mod(
                    index, exponent_a, power_k
                )
                if actual != stabilized:
                    raise AssertionError(
                        ("stabilized shell formula", index, power_k,
                         actual, stabilized)
                    )
                stabilized_shell_checks += 1

    for index in range(1, args.max_j):
        seed = seeds[index]
        next_seed = seeds[index + 1]
        assert seed is not None and next_seed is not None
        exponent_a = three_exponent(index)
        next_a = three_exponent(index + 1)
        primary = 3 ** (exponent_a - 1)
        next_primary = 3 ** (next_a - 1)
        ratio = next_primary // primary
        if ratio not in (1, 3) or next_primary != ratio * primary:
            raise AssertionError(("primary schedule", index))
        forcing = next_seed - 10 * seed
        if next_primary * next_seed != (
            10 * ratio * (primary * seed) + next_primary * forcing
        ):
            raise AssertionError(("scaled unit recurrence", index))
        recurrence_checks += 1

        if exponent_a >= 3:
            actual_forcing_mod_nine = rat_mod(next_primary * forcing, 9)
            if ratio == 3:
                expected_forcing_mod_nine = 5 if exponent_a & 1 else 4
            else:
                cutoff = 12 * index + 3
                next_cutoff = cutoff + 12
                old_stage = (
                    1
                    + int(cutoff >= 5 * primary)
                    + int(cutoff >= 7 * primary)
                )
                next_stage = (
                    1
                    + int(next_cutoff >= 5 * primary)
                    + int(next_cutoff >= 7 * primary)
                )
                if next_stage == old_stage:
                    expected_forcing_mod_nine = 0
                elif next_stage == old_stage + 1:
                    expected_forcing_mod_nine = 3 if exponent_a & 1 else 6
                else:
                    raise AssertionError(("mod-nine stage jump", index))
            if actual_forcing_mod_nine != expected_forcing_mod_nine:
                raise AssertionError(
                    ("forcing modulo nine", index,
                     actual_forcing_mod_nine, expected_forcing_mod_nine)
                )
            forcing_mod_nine_pattern_checks += 1

    print("claim_status=experiment")
    print(f"source_sha256={digest}")
    print(f"j_range=1..{args.max_j}")
    print(f"k_range=1..{args.max_k}")
    print(f"exact_three_primary_valuation_checks={valuation_checks}")
    print(f"unit_mod_three_formula_checks={unit_mod_three_checks}")
    print(f"unit_mod_nine_stage_formula_checks={unit_mod_nine_checks}")
    print(f"raw_finite_shell_formula_checks={raw_shell_checks}")
    print(f"stabilized_epoch_shell_formula_checks={stabilized_shell_checks}")
    print(f"reduced_numerator_congruence_checks={reduced_numerator_checks}")
    print(f"coarse_selection_identity_checks={coarse_selection_checks}")
    print(f"scaled_unit_recurrence_checks={recurrence_checks}")
    print(
        "forcing_mod_nine_sparse_pattern_checks="
        f"{forcing_mod_nine_pattern_checks}"
    )
    print(f"first_c_mod_3_not_equal_U_mod_3={first_coarse_not_unit}")
    print("coarse_mod_3_by_(a_parity,stage)=" + repr(dict(coarse_residues)))
    print("fine_mod_3_by_(a_parity,stage)=" + repr(dict(fine_residues)))
    print("all exact checks passed")


if __name__ == "__main__":
    main()
