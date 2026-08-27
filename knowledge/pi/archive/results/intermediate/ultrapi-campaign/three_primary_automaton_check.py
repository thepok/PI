#!/usr/bin/env python3
"""Exact finite checks for the three-primary quotient automaton.

All printed observations have claim status ``experiment``.  The checker uses
the exact rational Machin seeds and integer/Fraction arithmetic; it neither
evaluates pi nor reads a decimal expansion of pi.
"""

from __future__ import annotations

import argparse
import hashlib
from fractions import Fraction
from math import gcd
from pathlib import Path

from actual_numerator_phase_experiment import machin_seed, valuation


ROOT = Path(__file__).resolve().parents[2]
TARGET = ROOT / "problems" / "local" / "pi-digits.txt"
TARGET_SHA256 = "2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825"
BASE_FACTOR = 5 * 239


def fractional_part(value: Fraction) -> Fraction:
    return Fraction(value.numerator % value.denominator, value.denominator)


def exponent_at_index(index: int) -> int:
    """The unique a with 3^a <= 12*index+3 < 3^(a+1)."""
    bound = 12 * index + 3
    exponent = 0
    power = 1
    while 3 * power <= bound:
        power *= 3
        exponent += 1
    return exponent


def three_modulus(index: int) -> int:
    return 3 ** (exponent_at_index(index) - 1)


def epoch_start(exponent: int) -> int:
    return (3**exponent - 3 + 11) // 12


def epoch_length(exponent: int) -> int:
    modulus = 3 ** (exponent - 1)
    return (modulus + (1 if exponent & 1 else -1)) // 2


def digit(value: Fraction) -> int:
    if not 0 <= value < 1:
        raise AssertionError(("phase range", value))
    return (10 * value.numerator) // value.denominator


def choose_constant_digit(word: str) -> int:
    """Choose a in 1..8 for which the constant word aaaa... avoids word."""
    if not word or any(character not in "0123456789" for character in word):
        raise ValueError("word must be a nonempty decimal word")
    for candidate in range(1, 9):
        if word != str(candidate) * len(word):
            return candidate
    raise AssertionError("eight candidates cannot all be excluded")


def nearest_matched_phase(
    target_digit: int,
    modulus: int,
    auxiliary: int,
    actual_phase: Fraction,
) -> Fraction:
    """Approximate target_digit/9 and match the actual leading 3-adic unit."""
    if modulus % 27:
        raise ValueError("the simple centered construction requires 27 | D")
    actual_factor = actual_phase.denominator // modulus
    if actual_phase.denominator != modulus * actual_factor:
        raise AssertionError("invalid actual factor split")
    if gcd(actual_factor, 3) != 1 or gcd(auxiliary, 3) != 1:
        raise AssertionError("non-three factors expected")

    center = target_digit * modulus * auxiliary // 9
    required = (
        actual_phase.numerator
        * (auxiliary % 3)
        * pow(actual_factor % 3, -1, 3)
    ) % 3
    choices = [offset for offset in (-1, 0, 1) if (center + offset) % 3 == required]
    if len(choices) != 1:
        raise AssertionError(("matched residue choice", choices))
    numerator = center + choices[0]
    if not 0 < numerator < modulus * auxiliary:
        raise AssertionError(("matched numerator range", numerator))
    return Fraction(numerator, modulus * auxiliary)


def kmp_step(word: str, state: int, next_digit: str) -> int:
    candidate = word[:state] + next_digit
    best = min(len(word), len(candidate))
    while best and not candidate.endswith(word[:best]):
        best -= 1
    return best


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-j", type=int, default=80)
    args = parser.parse_args()
    if args.max_j < 21:
        raise SystemExit("--max-j must be at least 21")

    source_hash = hashlib.sha256(TARGET.read_bytes()).hexdigest()
    if source_hash != TARGET_SHA256:
        raise AssertionError(("source hash", source_hash))

    seeds = [Fraction()] + [machin_seed(j) for j in range(1, args.max_j + 2)]
    phases = [Fraction()] + [fractional_part(seed) for seed in seeds[1:]]
    moduli = [0] + [three_modulus(j) for j in range(1, args.max_j + 2)]

    valuation_checks = 0
    ratio_checks = 0
    transition_checks = 0
    controlled_residue_checks = 0
    carry_checks = 0
    injection_checks = 0
    order_checks = 0

    for j in range(1, args.max_j + 2):
        actual_modulus = 3 ** valuation(phases[j].denominator, 3)
        if actual_modulus != moduli[j]:
            raise AssertionError(("T52 modulus", j, actual_modulus, moduli[j]))
        valuation_checks += 1

    for j in range(1, args.max_j + 1):
        modulus = moduli[j]
        next_modulus = moduli[j + 1]
        if next_modulus not in (modulus, 3 * modulus):
            raise AssertionError(("constant/tripling ratio", j, modulus, next_modulus))
        ratio = next_modulus // modulus
        ratio_checks += 1

        phase = phases[j]
        next_phase = phases[j + 1]
        forcing = seeds[j + 1] - 10 * seeds[j]
        full_denominator = phase.denominator
        factor = full_denominator // modulus
        if gcd(factor, modulus) != 1:
            raise AssertionError(("complete three-primary split", j))
        residue = phase.numerator
        fine = residue % factor
        fine_carry = (10 * fine) // factor

        images: set[int] = set()
        for label in range(modulus):
            next_label = ratio * 10 * label % next_modulus
            images.add(next_label)
            translated = fractional_part(phase + Fraction(label, modulus))
            translated_next = fractional_part(10 * translated + forcing)
            expected_next = fractional_part(
                next_phase + Fraction(next_label, next_modulus)
            )
            if translated_next != expected_next:
                raise AssertionError(("translation transition", j, label))
            transition_checks += 1

            translated_numerator = (residue + label * factor) % full_denominator
            if translated_numerator % factor != fine:
                raise AssertionError(("controlled residue", j, label))
            if Fraction(translated_numerator, full_denominator) != translated:
                raise AssertionError(("translated numerator", j, label))
            controlled_residue_checks += 1

            coarse = translated_numerator // factor
            carry_digit = (10 * coarse + fine_carry) // modulus
            next_coarse = (10 * coarse + fine_carry) % modulus
            raw_next = (10 * translated_numerator) % full_denominator
            if carry_digit != digit(translated):
                raise AssertionError(("T53 digit", j, label))
            if raw_next // factor != next_coarse or raw_next % factor != (10 * fine) % factor:
                raise AssertionError(("T53 next state", j, label))
            carry_checks += 1

        expected_images = (
            set(range(modulus))
            if ratio == 1
            else set(range(0, next_modulus, 3))
        )
        if images != expected_images:
            raise AssertionError(("transition image", j, ratio))
        injection_checks += 1

    complete_epochs: list[tuple[int, int, int, int]] = []
    exponent = 2
    while epoch_start(exponent + 1) <= args.max_j + 1:
        start = epoch_start(exponent)
        stop = epoch_start(exponent + 1)
        modulus = 3 ** (exponent - 1)
        if stop - start != epoch_length(exponent):
            raise AssertionError(("epoch length", exponent, start, stop))
        if any(moduli[j] != modulus for j in range(start, stop)):
            raise AssertionError(("epoch modulus", exponent))
        if modulus >= 9:
            expected_order = modulus // 9
            if pow(10, expected_order, modulus) != 1:
                raise AssertionError(("multiplicative order upper", exponent))
            if modulus >= 27 and pow(10, expected_order // 3, modulus) == 1:
                raise AssertionError(("multiplicative order lower", exponent))
            order_checks += 1
        complete_epochs.append((exponent, start, stop, modulus))
        exponent += 1

    # Couple the exact translation label to a few forbidden-word automata.
    # These are observations about finite epochs only.
    test_words = ("0", "00", "012", "314", "999")
    survivor_rows: list[str] = []
    automaton_steps = 0
    for exponent, start, stop, modulus in complete_epochs:
        if start < 2:
            continue
        for word in test_words:
            survivors = 0
            for initial_label in range(modulus):
                state = 0
                alive = True
                for j in range(start, stop):
                    label = pow(10, j - start, modulus) * initial_label % modulus
                    translated = fractional_part(phases[j] + Fraction(label, modulus))
                    state = kmp_step(word, state, str(digit(translated)))
                    automaton_steps += 1
                    if state == len(word):
                        alive = False
                        break
                survivors += int(alive)
            survivor_rows.append(
                f"a:{exponent},j:{start}..{stop - 1},D:{modulus},"
                f"word:{word},survivors:{survivors}"
            )

    # Strong structural separator.  On every complete epoch with 27 | D,
    # construct rational states driven by the *actual* Machin forcing.  Their
    # exact three-primary denominator agrees with T52, while their emitted
    # digit remains constant over the whole epoch.  The non-three fine state
    # is intentionally not the actual Machin fine state.
    separator_epochs = 0
    separator_digit_steps = 0
    separator_carry_steps = 0
    separator_padic_steps = 0
    separator_recurrence_steps = 0
    for exponent, start, stop, modulus in complete_epochs:
        if modulus % 27:
            continue
        # Include the first state after the epoch so the exact check crosses
        # the D -> 3D boundary rather than testing constant-D dynamics only.
        horizon = stop - start + 1
        auxiliary = BASE_FACTOR
        while modulus * auxiliary <= 180 * 10**horizon:
            auxiliary *= BASE_FACTOR

        for target_digit in range(1, 9):
            current = nearest_matched_phase(
                target_digit, modulus, auxiliary, phases[start]
            )
            initial_difference = current - phases[start]
            actual_order = valuation(phases[start].denominator, 3)
            difference_order = (
                valuation(abs(initial_difference.numerator), 3)
                - valuation(initial_difference.denominator, 3)
            )
            if difference_order <= -actual_order:
                raise AssertionError(("three-adic leading match", exponent, target_digit))

            for j in range(start, stop + 1):
                expected_modulus = moduli[j]
                if 3 ** valuation(current.denominator, 3) != expected_modulus:
                    raise AssertionError(("separator denominator", j, target_digit))
                separator_padic_steps += 1
                if digit(current) != target_digit:
                    raise AssertionError(("separator digit", j, target_digit))
                separator_digit_steps += 1

                factor = current.denominator // expected_modulus
                residue = current.numerator
                fine = residue % factor
                coarse = residue // factor
                fine_carry = (10 * fine) // factor
                carry_digit = (10 * coarse + fine_carry) // expected_modulus
                if carry_digit != target_digit:
                    raise AssertionError(("separator T53 carry", j, target_digit))
                separator_carry_steps += 1

                if j < stop:
                    forcing = seeds[j + 1] - 10 * seeds[j]
                    next_current = fractional_part(10 * current + forcing)
                    # Independently unroll the same recurrence from the start.
                    accumulation = seeds[j + 1] - 10 ** (j + 1 - start) * seeds[start]
                    expected = fractional_part(
                        10 ** (j + 1 - start)
                        * nearest_matched_phase(
                            target_digit, modulus, auxiliary, phases[start]
                        )
                        + accumulation
                    )
                    if next_current != expected:
                        raise AssertionError(("separator exact forcing", j, target_digit))
                    current = next_current
                    separator_recurrence_steps += 1
        separator_epochs += 1

    # Infinite algebraic model behind the structural separator: retain the
    # exact D_j profile and T53 carries, but replace the numerical Machin
    # forcing by another positive coboundary of the same form.  The normalized
    # coarse state (c+1)/D is then an exact invariant through both constant and
    # tripling steps.
    structural_model_steps = 0
    structural_model_recurrences = 0
    structural_model_tripling_steps = 0
    model_start = max(7, epoch_start(4))
    for target_digit in range(1, 9):
        for j in range(model_start, args.max_j + 1):
            modulus = moduli[j]
            next_modulus = moduli[j + 1]
            factor = BASE_FACTOR ** (j - model_start + 2)
            next_factor = factor * BASE_FACTOR
            phase = Fraction(
                target_digit * modulus * factor // 9 - 1,
                modulus * factor,
            )
            expected_phase = Fraction(target_digit, 9) - Fraction(
                1, modulus * factor
            )
            if phase != expected_phase:
                raise AssertionError(("structural model phase", j, target_digit))
            if 3 ** valuation(phase.denominator, 3) != modulus:
                raise AssertionError(("structural model denominator", j, target_digit))

            residue = phase.numerator
            reduced_factor = phase.denominator // modulus
            fine = residue % reduced_factor
            coarse = residue // reduced_factor
            if fine != reduced_factor - 1 or coarse != target_digit * modulus // 9 - 1:
                raise AssertionError(("structural model split", j, target_digit))
            fine_carry = (10 * fine) // reduced_factor
            carry_digit = (10 * coarse + fine_carry) // modulus
            next_coarse_raw = (10 * coarse + fine_carry) % modulus
            if fine_carry != 9 or carry_digit != target_digit or next_coarse_raw != coarse:
                raise AssertionError(("structural model T53", j, target_digit))
            if digit(phase) != target_digit:
                raise AssertionError(("structural model digit", j, target_digit))
            structural_model_steps += 1

            next_phase = Fraction(target_digit, 9) - Fraction(
                1, next_modulus * next_factor
            )
            forcing = (
                Fraction(10, modulus * factor)
                - Fraction(1, next_modulus * next_factor)
            )
            if forcing <= 0 or fractional_part(10 * phase + forcing) != next_phase:
                raise AssertionError(("structural model forcing", j, target_digit))
            ratio = next_modulus // modulus
            next_coarse = target_digit * next_modulus // 9 - 1
            if next_coarse != ratio * (coarse + 1) - 1:
                raise AssertionError(("structural coarse transition", j, target_digit))
            if Fraction(coarse + 1, modulus) != Fraction(next_coarse + 1, next_modulus):
                raise AssertionError(("normalized coarse invariant", j, target_digit))
            structural_model_recurrences += 1
            structural_model_tripling_steps += int(ratio == 3)

    # The constant-output separator avoids every nonempty word after choosing
    # one of the eight constant digits.  Exhaust all words through length 3.
    word_automaton_checks = 0
    for length in range(1, 4):
        for value in range(10**length):
            word = f"{value:0{length}d}"
            constant_digit = choose_constant_digit(word)
            state = 0
            for _ in range(length + 3):
                state = kmp_step(word, state, str(constant_digit))
                if state == len(word):
                    raise AssertionError(("constant separator word", word, constant_digit))
                word_automaton_checks += 1

    print("claim_status=experiment")
    print(f"source_sha256={source_hash}")
    print(f"j_range=1..{args.max_j}")
    print(f"t52_three_primary_modulus_checks={valuation_checks}")
    print(f"constant_or_tripling_ratio_checks={ratio_checks}")
    print(f"exact_actual_forcing_translation_checks={transition_checks}")
    print(f"actual_fine_residue_preservation_checks={controlled_residue_checks}")
    print(f"t53_candidate_carry_checks={carry_checks}")
    print(f"transition_image_checks={injection_checks}")
    print(f"complete_epoch_order_checks={order_checks}")
    print(f"forbidden_word_automaton_steps={automaton_steps}")
    print("finite_actual_epoch_survivors=" + repr(survivor_rows))
    print(f"separator_complete_epochs={separator_epochs}")
    print(f"separator_exact_three_primary_steps={separator_padic_steps}")
    print(f"separator_constant_digit_steps={separator_digit_steps}")
    print(f"separator_t53_carry_steps={separator_carry_steps}")
    print(f"separator_exact_forcing_steps={separator_recurrence_steps}")
    print(f"structural_infinite_model_steps={structural_model_steps}")
    print(f"structural_infinite_model_recurrences={structural_model_recurrences}")
    print(f"structural_infinite_model_tripling_steps={structural_model_tripling_steps}")
    print(f"constant_word_automaton_checks={word_automaton_checks}")
    print("all exact checks passed")


if __name__ == "__main__":
    main()
