#!/usr/bin/env python3
"""Exact finite checks for the cross-index complementary-quotient symmetry.

Every reported result has claim status ``experiment``.  The script imports
the exact rational Machin seed constructor used by the companion audit and
does not evaluate pi or read a decimal digit table.
"""

from __future__ import annotations

import argparse
import hashlib
from fractions import Fraction
from pathlib import Path

from actual_numerator_phase_experiment import machin_seed, primes_up_to, valuation


ROOT = Path(__file__).resolve().parents[2]
TARGET = ROOT / "problems" / "local" / "pi-digits.txt"
TARGET_SHA256 = "2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825"


def fractional_part(value: Fraction) -> Fraction:
    return Fraction(value.numerator % value.denominator, value.denominator)


def largest_three_power_exponent(bound: int) -> int:
    exponent = 0
    power = 1
    while 3 * power <= bound:
        power *= 3
        exponent += 1
    return exponent


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-j", type=int, default=80)
    args = parser.parse_args()
    if args.max_j < 2:
        raise SystemExit("--max-j must be at least two")

    source_hash = hashlib.sha256(TARGET.read_bytes()).hexdigest()
    if source_hash != TARGET_SHA256:
        raise AssertionError(("source hash", source_hash))

    primes = primes_up_to(12 * args.max_j + 5)
    seeds = [Fraction()] + [machin_seed(j) for j in range(1, args.max_j + 1)]
    rows: list[tuple[int, int, int, int, int, Fraction]] = []
    valuation_checks = 0

    for j in range(1, args.max_j + 1):
        seed = seeds[j]
        denominator = seed.denominator
        d = 12 * j + 3
        exponent = largest_three_power_exponent(d)
        expected = 1 - exponent
        actual = valuation(abs(seed.numerator), 3) - valuation(denominator, 3)
        if actual != expected:
            raise AssertionError(("three-adic valuation", j, actual, expected))
        valuation_checks += 1

        # This is the concrete two-band split used by the companion exact
        # experiment.  The proof-sketch symmetry applies to any controlled
        # factor prime to 3, not only to this finite choice.
        factor = 5 ** valuation(denominator, 5)
        factor *= 239 ** valuation(denominator, 239)
        cutoff = max(7, d // 3)
        for prime in primes:
            prime_exponent = valuation(denominator, prime)
            if prime > cutoff and prime not in (5, 239) and prime_exponent:
                factor *= prime**prime_exponent
        complementary = denominator // factor
        if denominator % factor or factor % 3 == 0:
            raise AssertionError(("factor split", j))
        if complementary % (3 ** (exponent - 1)):
            raise AssertionError(("persistent three part", j, complementary))
        rows.append((j, denominator, factor, complementary, exponent,
                     fractional_part(seed)))

    divisibility_checks = 0
    for start in range(1, args.max_j + 1):
        start_exponent = rows[start - 1][4]
        persistent = 3 ** (start_exponent - 1)
        for j in range(start, args.max_j + 1):
            if rows[j - 1][3] % persistent:
                raise AssertionError(("tail divisibility", start, j, persistent))
            divisibility_checks += 1

    # Replay every persistent translation at the last index whose tail has at
    # least twenty recurrence steps available.  Numerators are kept on the
    # same (possibly unreduced) denominator grid, which makes equality of the
    # controlled residues literal.
    start = max(1, args.max_j - 20)
    persistent = 3 ** (rows[start - 1][4] - 1)
    recurrence_checks = 0
    residue_checks = 0
    for shift in range(persistent):
        for j in range(start, args.max_j):
            _, denominator, factor, complementary, _, phase = rows[j - 1]
            if complementary % persistent:
                raise AssertionError(("translation denominator", j, persistent))
            multiplier = pow(10, j - start)
            translated_numerator = (
                phase.numerator
                + multiplier * shift * (denominator // persistent)
            ) % denominator
            if translated_numerator % factor != phase.numerator % factor:
                raise AssertionError(("controlled residue", start, shift, j))
            residue_checks += 1

            translated = fractional_part(
                phase + Fraction(multiplier * shift, persistent)
            )
            forcing = seeds[j + 1] - 10 * seeds[j]
            translated_next = fractional_part(10 * translated + forcing)
            expected_next = fractional_part(
                rows[j][5]
                + Fraction(multiplier * 10 * shift, persistent)
            )
            if translated_next != expected_next:
                raise AssertionError(("forced recurrence", start, shift, j))
            recurrence_checks += 1

    # At one index the persistent translations form a shifted uniform grid.
    # Check every decimal cylinder at each depth strictly below its mesh
    # threshold.
    end_phase = rows[-1][5]
    end_persistent = 3 ** (rows[-1][4] - 1)
    cylinder_depths: list[tuple[int, int]] = []
    depth = 1
    while 10**depth < end_persistent:
        scale = 10**depth
        occupied = {
            int(scale * fractional_part(end_phase + Fraction(shift, end_persistent)))
            for shift in range(end_persistent)
        }
        if len(occupied) != scale:
            raise AssertionError(("cylinder grid", depth, len(occupied), scale))
        cylinder_depths.append((depth, scale))
        depth += 1

    # Recheck the same depths using the genuinely forced alternative orbit,
    # not only the static decimal code of its initial phase.
    forced_itinerary_depths: list[tuple[int, int]] = []
    max_depth = cylinder_depths[-1][0] if cylinder_depths else 0
    tail_seeds = [machin_seed(args.max_j + offset)
                  for offset in range(max_depth + 1)]
    for depth, scale in cylinder_depths:
        occupied: set[int] = set()
        for shift in range(end_persistent):
            current = fractional_part(end_phase + Fraction(shift, end_persistent))
            word = 0
            for offset in range(depth):
                word = 10 * word + (10 * current.numerator) // current.denominator
                if offset + 1 < depth:
                    forcing = tail_seeds[offset + 1] - 10 * tail_seeds[offset]
                    current = fractional_part(10 * current + forcing)
            occupied.add(word)
        if len(occupied) != scale:
            raise AssertionError(
                ("forced itinerary grid", depth, len(occupied), scale)
            )
        forced_itinerary_depths.append((depth, scale))

    print("claim_status=experiment")
    print(f"source_sha256={source_hash}")
    print(f"j_range=1..{args.max_j}")
    print(f"three_adic_valuation_checks={valuation_checks}")
    print(f"tail_divisibility_checks={divisibility_checks}")
    print(f"cross_index_recurrence_checks={recurrence_checks}")
    print(f"controlled_residue_checks={residue_checks}")
    print(f"translation_start={start} persistent_modulus={persistent}")
    print(f"terminal_persistent_modulus={end_persistent}")
    print(f"full_cylinder_depths={cylinder_depths}")
    print(f"full_forced_itinerary_depths={forced_itinerary_depths}")
    print("all exact checks passed")


if __name__ == "__main__":
    main()
