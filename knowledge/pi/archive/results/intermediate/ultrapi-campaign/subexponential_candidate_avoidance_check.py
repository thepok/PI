#!/usr/bin/env python3
"""Exact checks for the shifted-grid/avoidance obstruction.

This script uses only integer arithmetic and fractions.  It neither evaluates
pi nor reads a digit table.  Its output is finite evidence (`experiment`), not
a proof of any asymptotic statement or of the every-word conjecture.
"""

from __future__ import annotations

from fractions import Fraction
from hashlib import sha256
from math import gcd
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
SOURCE = ROOT / "problems/local/pi-digits.txt"
EXPECTED_SOURCE_SHA256 = (
    "2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825"
)


def fractional_part(x: Fraction) -> Fraction:
    return x - x.numerator // x.denominator


def decimal_digits(x: Fraction, count: int) -> tuple[int, ...]:
    out: list[int] = []
    for _ in range(count):
        x *= 10
        digit = x.numerator // x.denominator
        assert 0 <= digit <= 9
        out.append(digit)
        x -= digit
    return tuple(out)


def avoids_word(digits: tuple[int, ...], word: tuple[int, ...], visits: int) -> bool:
    return all(digits[t : t + len(word)] != word for t in range(visits))


def choose_constant_digit(word: tuple[int, ...]) -> int:
    for digit in range(1, 9):
        if word != (digit,) * len(word):
            return digit
    raise AssertionError("one of the eight constant streams must avoid a fixed word")


def main() -> None:
    source_sha = sha256(SOURCE.read_bytes()).hexdigest()
    assert source_sha == EXPECTED_SOURCE_SHA256

    denominator_complement = 81
    zero_word = (0,)
    grid_rows: list[tuple[int, int, int, Fraction]] = []
    for horizon in (10, 50, 100, 200):
        frozen = (5 * 239) ** (horizon + 10)
        shift = Fraction(frozen - 1, frozen * denominator_complement)
        avoiding = 0
        reduced_avoiding = 0
        for coarse in range(denominator_complement):
            numerator = frozen * coarse + frozen - 1
            x = Fraction(numerator, frozen * denominator_complement)
            digits = decimal_digits(x, horizon)
            if avoids_word(digits, zero_word, horizon):
                avoiding += 1
                reduced_avoiding += int(
                    gcd(numerator, frozen * denominator_complement) == 1
                )
        zero_mode_main = Fraction(
            denominator_complement * 9**horizon, 10**horizon
        )
        grid_rows.append((horizon, avoiding, reduced_avoiding, zero_mode_main))

    sample_words = ((0,), (1,), (3, 3), (1, 2, 3), (9, 9, 9))
    carry_checks = 0
    itinerary_checks = 0
    word_avoidance_checks = 0
    reduced_seed_checks = 0
    horizon = 200
    frozen = (5 * 239) ** (horizon + 10)
    for digit in range(1, 9):
        coarse = 9 * digit - 1
        fine = frozen - 1
        numerator = frozen * coarse + fine
        full_denominator = frozen * denominator_complement
        assert numerator == 9 * digit * frozen - 1
        assert 0 < numerator < full_denominator
        assert gcd(numerator, frozen) == 1
        assert gcd(numerator, denominator_complement) == 1
        assert gcd(numerator, full_denominator) == 1
        reduced_seed_checks += 1

        x = Fraction(numerator, full_denominator)
        digits = decimal_digits(x, horizon)
        assert digits == (digit,) * horizon
        itinerary_checks += horizon

        current_coarse = coarse
        current_fine = fine
        for _ in range(horizon):
            fine_carry = (10 * current_fine) // frozen
            output_digit = (10 * current_coarse + fine_carry) // denominator_complement
            next_fine = 10 * current_fine - frozen * fine_carry
            next_coarse = (
                10 * current_coarse
                + fine_carry
                - denominator_complement * output_digit
            )
            assert fine_carry == 9
            assert output_digit == digit
            assert next_coarse == coarse
            current_fine = next_fine
            current_coarse = next_coarse
            carry_checks += 1

    for word in sample_words:
        digit = choose_constant_digit(word)
        numerator = 9 * digit * frozen - 1
        x = Fraction(numerator, frozen * denominator_complement)
        digits = decimal_digits(x, horizon + len(word) - 1)
        assert digits == (digit,) * len(digits)
        assert avoids_word(digits, word, horizon)
        word_avoidance_checks += horizon

    growth = (5 * 239) ** 12
    recurrence_checks = 0
    for digit in range(1, 9):
        for index in range(1, 21):
            frozen = growth ** (index + 1)
            frozen_next = growth ** (index + 2)
            x = Fraction(digit, 9) - Fraction(1, 81 * frozen)
            x_next = Fraction(digit, 9) - Fraction(1, 81 * frozen_next)
            forcing = Fraction(10, 81 * frozen) - Fraction(1, 81 * frozen_next)
            assert forcing > 0
            assert fractional_part(10 * x + forcing) == x_next
            recurrence_checks += 1

    print("claim_status=experiment")
    print(f"source_sha256={source_sha}")
    print(f"complementary_modulus={denominator_complement}")
    for horizon, avoiding, reduced_avoiding, main_term in grid_rows:
        print(
            "zero_avoidance_grid="
            f"horizon:{horizon},count:{avoiding},"
            f"reduced_count:{reduced_avoiding},"
            f"zero_mode_main:{float(main_term):.12g}"
        )
    print(f"constant_itinerary_checks={itinerary_checks}")
    print(f"word_avoidance_checks={word_avoidance_checks}")
    print(f"reduced_seed_checks={reduced_seed_checks}")
    print(f"fine_and_coarse_carry_checks={carry_checks}")
    print(f"positive_forcing_recurrence_checks={recurrence_checks}")
    print("all exact checks passed")


if __name__ == "__main__":
    main()
