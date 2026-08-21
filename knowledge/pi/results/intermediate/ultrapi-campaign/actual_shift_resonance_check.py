#!/usr/bin/env python3
"""Exact finite checks for the actual shifted-grid resonance.

Every reported conclusion has claim status ``experiment``.  The script uses
the exact rational Machin seed and integer arithmetic only; it does not
evaluate pi and does not read a digit table.
"""

from __future__ import annotations

import argparse
import hashlib
from fractions import Fraction
from math import gcd
from pathlib import Path

from actual_numerator_phase_experiment import machin_seed, valuation


SOURCE_SHA256 = (
    "2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825"
)


def source_path() -> Path:
    return Path(__file__).resolve().parents[2] / "problems/local/pi-digits.txt"


def decimal(value: Fraction, places: int = 12) -> str:
    """Deterministic rounded decimal display; proofs never use this value."""
    if value < 0:
        return "-" + decimal(-value, places)
    scale = 10**places
    rounded = (value.numerator * scale + value.denominator // 2) // value.denominator
    return f"{rounded // scale}.{rounded % scale:0{places}d}"


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-j", type=int, default=80)
    args = parser.parse_args()
    if args.max_j < 1:
        raise SystemExit("--max-j must be positive")

    digest = hashlib.sha256(source_path().read_bytes()).hexdigest()
    if digest != SOURCE_SHA256:
        raise AssertionError(("target hash", digest))

    digits = tuple(str(value) for value in range(10))
    last_survival: dict[str, int | None] = {digit: None for digit in digits}
    largest_ratio: Fraction = Fraction()
    largest_events: list[tuple[int, str, int, int, Fraction, Fraction, str]] = []
    subunit_survivors = 0
    relative_discrepancy_violations = 0
    prefix_checks = 0
    rows: dict[tuple[int, str], tuple[int, int, Fraction, Fraction]] = {}

    for j in range(1, args.max_j + 1):
        seed = machin_seed(j)
        denominator = seed.denominator
        residue = seed.numerator % denominator

        # Freeze every denominator component except the complete 3-primary
        # component.  This preserves the actual base and high-prime residues
        # and leaves a small, genuine coprime complementary grid.
        complementary = 3 ** valuation(denominator, 3)
        factor = denominator // complementary
        if gcd(factor, complementary) != 1:
            raise AssertionError(("coprime split", j))
        remainder = residue % factor

        length = 2 * j
        modulus = 10**length
        shift_prefix = modulus * remainder // factor

        words: list[str] = []
        for coarse in range(complementary):
            # This is exactly floor(10^length * (coarse/D + r/(FD))):
            # the discarded fractional part of 10^length*r/F is below one
            # and cannot cross the following division by the integer D.
            prefix_value = (modulus * coarse + shift_prefix) // complementary
            if not 0 <= prefix_value < modulus:
                raise AssertionError(("prefix range", j, coarse))
            words.append(f"{prefix_value:0{length}d}")
            prefix_checks += 1

        zero_mode = Fraction(complementary * 9**length, 10**length)
        for digit in digits:
            count = sum(digit not in word for word in words)
            if count:
                last_survival[digit] = j
            signed_resonance = abs(Fraction(count) - zero_mode)
            rows[(j, digit)] = (
                complementary,
                count,
                zero_mode,
                Fraction(count) - zero_mode,
            )
            if zero_mode < 1 and count:
                subunit_survivors += 1
            if signed_resonance > zero_mode:
                relative_discrepancy_violations += 1

            ratio = Fraction(count, 1) / zero_mode
            if ratio > largest_ratio:
                largest_ratio = ratio
                largest_events = []
            if ratio == largest_ratio:
                witnesses = [word for word in words if digit not in word]
                witness = witnesses[0] if witnesses else "none"
                largest_events.append(
                    (
                        j,
                        digit,
                        complementary,
                        count,
                        zero_mode,
                        signed_resonance,
                        witness,
                    )
                )

    print("claim_status=experiment")
    print(f"source_sha256={digest}")
    print("split=complementary modulus is the complete 3-primary denominator")
    print("pulse=one-digit avoidance at length 2*j")
    print(f"j_range=1..{args.max_j}")
    print(f"exact_prefix_checks={prefix_checks}")
    print(f"subunit_zero_mode_survivor_rows={subunit_survivors}")
    print(
        "naive_bound_abs_resonance_le_zero_mode_violations="
        f"{relative_discrepancy_violations}"
    )
    print(f"last_survival_by_digit={last_survival}")
    for j, digit, complementary, count, zero_mode, signed, witness in largest_events:
        print(
            "largest_resonance="
            f"j:{j},digit:{digit},D:{complementary},N:{count},"
            f"zero_mode:{decimal(zero_mode)},"
            f"signed_resonance:{decimal(signed)},"
            f"occupancy_over_zero_mode:{decimal(Fraction(count) / zero_mode)}"
        )
        print(f"largest_resonance_witness_prefix={witness}")
        next_row = rows.get((j + 1, digit))
        if next_row is not None:
            next_d, next_count, next_zero, next_signed = next_row
            print(
                "next_scale="
                f"j:{j + 1},digit:{digit},D:{next_d},N:{next_count},"
                f"zero_mode:{decimal(next_zero)},"
                f"signed_resonance:{decimal(next_signed)}"
            )
    print("all exact checks passed")


if __name__ == "__main__":
    main()
