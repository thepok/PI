#!/usr/bin/env python3
"""Exact/finite replay for the BBP fixed-period carry attack.

All BBP identities, modular residues, carry identities, and inequalities use
integers or ``fractions.Fraction``.  The printed orbit averages are explicitly
an experiment.  This script asserts no positive asymptotic defect, matching,
fixed return, or V1.
"""

from __future__ import annotations

from fractions import Fraction
from hashlib import sha256
import json
from math import gcd, log
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]

PINS = {
    "problems/local/pi-digits.txt":
        "2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825",
    "work/ultrapi-resume/bbp_adjacent_matching_breakthrough_report.md":
        "2b231d3c2e2ef717a2941a0452304ba402915318b72d305f6a6129ee8431f042",
    "work/ultrapi-resume/bbp_adjacent_matching_breakthrough_independent_audit.md":
        "32cf25b1b2d00a37de57b325134ba0a53e8f5f6c129b16d3f419000a1620af93",
    "work/theory/pi-digits/library/t6/bbp-1997-nasa.pdf":
        "e4e0b97fde01328ec41da5f2cd4d6ffc8bcd2b7bd7516b9d8afc320f6d1916c4",
    "work/theory/pi-lacunary-near-return-sparsity/library/t63/"
    "lagarias-math0101055v2.pdf":
        "a2a1171eb9c75c9fa3495ca3c3ceaa33c1d20b722bb56f82adb56d8c308209b9",
    "work/theory/pi-positive-decimal-factor-entropy/library/t87/"
    "zeilberger-zudilin-2020.pdf":
        "3b11c4bf3e25927227ac8f7f4e49d7f1d3efeb42beecd7f3b8c64efb162d20b5",
    "work/theory/pi-lacunary-near-return-sparsity/library/t89/"
    "kempner-1916.pdf":
        "99c4bf8d04d2dbdc63e8d274266f212072d4c248fcbc659e60ca7fa9350eb014",
    "work/ultrapi-resume/library/shallit-1979-simple-continued-fractions.pdf":
        "592a08ecf6df04414fe7bf5083d56898139b5d553679b244296833a1e2f1f981",
    "TheoryLib/PiPositiveDecimalFactorEntropy/"
    "T36T36DecimalPeriodicWindowGap.lean":
        "900e9fdeefbaea73236435b3845cd9dcc3c3b07b93d2e244b94dc39f4c109781",
    "TheoryLib/PiLongLagBlockCollisionDecay/"
    "T4T4PublishedIrrationalityOnset.lean":
        "73a70fc981bc5856e6c52f3c27143d1a54d84373f830c2b1d37faeb2fdbd71de",
}

DEPTH = 2048
FRACTION_DEPTH = 160
OVERSAMPLED_CARRY_DEPTH = 256
PERIODS = tuple(range(1, 13))
CHECKPOINTS = (256, 512, 1024, 2048)


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def digest(path: Path) -> str:
    return sha256(path.read_bytes()).hexdigest()


def coefficient_numerator(k: int) -> int:
    return 120 * k * k + 151 * k + 47


def coefficient_denominator(k: int) -> int:
    return (2 * k + 1) * (4 * k + 3) * (8 * k + 1) * (8 * k + 5)


def coefficient(k: int) -> Fraction:
    return Fraction(coefficient_numerator(k), coefficient_denominator(k))


def fractional(value: Fraction) -> Fraction:
    return value - value.numerator // value.denominator


def centered(value: Fraction) -> Fraction:
    residue = fractional(value)
    if 2 * residue < 1:
        return residue
    return residue - 1


def circle_norm(value: Fraction) -> Fraction:
    return abs(centered(value))


def lcm(a: int, b: int) -> int:
    return a // gcd(a, b) * b


def stable_ratio(numerator: int, denominator: int) -> float:
    """Convert a nonnegative huge rational in [0,1] without huge-int overflow."""
    require(0 <= numerator <= denominator, "ratio range")
    if numerator == 0:
        return 0.0
    shift = max(0, denominator.bit_length() - 52)
    return (numerator >> shift) / (denominator >> shift)


def centered_orbit(seed: Fraction, length: int) -> tuple[list[Fraction], list[int]]:
    errors = [centered(seed)]
    carries: list[int] = []
    value = seed
    for _ in range(length):
        value *= 10
        next_error = centered(value)
        carry = 10 * errors[-1] - next_error
        require(carry.denominator == 1, "centered carry is integral")
        carry_int = carry.numerator
        require(-5 <= carry_int <= 5, "centered carry range")
        carries.append(carry_int)
        errors.append(next_error)
    return errors, carries


def check_centered_carry_lemmas() -> dict[str, object]:
    checks = 0
    for seed in (Fraction(1, 7), Fraction(3, 13), Fraction(17, 97), Fraction(29, 101)):
        errors, carries = centered_orbit(seed, 512)
        for length in (31, 127, 509):
            expansion = sum(
                Fraction(carries[n], 10 ** (n + 1)) for n in range(length)
            ) + errors[length] / 10**length
            require(expansion == errors[0], "finite centered expansion")

            energy = sum(error * error for error in errors[:length])
            nonzero = sum(carry != 0 for carry in carries[:length])
            require(
                Fraction(nonzero) <= 121 * energy + Fraction(11, 4),
                "carry-energy inequality",
            )

            for window in (1, 3, 7):
                extended_nonzero = sum(
                    carry != 0 for carry in carries[: length + window]
                )
                require(
                    energy / length
                    <= Fraction(window * extended_nonzero, 4 * length)
                    + Fraction(1, 4 * 10 ** (2 * window)),
                    "window converse inequality",
                )
            checks += 1

    # The constant 121 is sharp for the generic centered carry inequality:
    # 10 == -1 (mod 11), so e_n=(-1)^n/11 and c_n=(-1)^n.
    errors, carries = centered_orbit(Fraction(1, 11), 256)
    require(all(error == Fraction((-1) ** n, 11) for n, error in enumerate(errors)),
            "sharp alternating errors")
    require(all(carry == (-1) ** n for n, carry in enumerate(carries)),
            "sharp alternating carries")
    require(sum(error * error for error in errors[:256]) == Fraction(256, 121),
            "sharp energy")
    return {"generic_rows": checks, "sharp_constant": 121, "sharp_seed": "1/11"}


def kempner_tail(n: int) -> float:
    """Floating tail {10^n sum_r 10^(-2^r)} for a labeled experiment."""
    exponent = 1
    while exponent <= n:
        exponent *= 2
    total = 0.0
    while exponent - n <= 330:
        total += 10.0 ** (n - exponent)
        exponent *= 2
    return total


def kempner_diagnostics() -> dict[str, object]:
    checkpoints = (1024, 4096, 16384, 65536)
    periods = (1, 2, 4, 8)
    energy = {period: 0.0 for period in periods}
    rows: dict[str, object] = {}
    for n in range(max(checkpoints)):
        tail = kempner_tail(n)
        for period in periods:
            value = ((10**period - 1) * tail) % 1.0
            distance = min(value, 1.0 - value)
            energy[period] += distance * distance
        size = n + 1
        if size in checkpoints:
            rows[str(size)] = {
                str(period): {
                    "mean_square_defect": energy[period] / size,
                    "energy_over_log_N": energy[period] / log(size),
                }
                for period in periods
            }
    return rows


def replay() -> dict[str, object]:
    for relative, expected in PINS.items():
        path = ROOT / relative
        require(path.is_file(), f"missing pin: {relative}")
        require(digest(path) == expected, f"pin mismatch: {relative}")

    t36 = (ROOT / "TheoryLib/PiPositiveDecimalFactorEntropy/"
           "T36T36DecimalPeriodicWindowGap.lean").read_text()
    t4 = (ROOT / "TheoryLib/PiLongLagBlockCollisionDecay/"
          "T4T4PublishedIrrationalityOnset.lean").read_text()
    require("effectiveIrrationality_periodic_window_gap" in t36,
            "T36 periodic-window marker")
    require("def IrrationalityMeasureBelow" in t4,
            "T4 irrationality-measure marker")

    # L_n is an unreduced common odd denominator for a(0),...,a(n), and
    # A_n/(16^n L_n) is the exact BBP partial sum B_n.
    common_denominator = coefficient_denominator(0)
    scaled_numerator = coefficient_numerator(0)
    five_power = 1
    exact_partial = coefficient(0)

    sums = {period: 0.0 for period in PERIODS}
    minima = {period: 0.5 for period in PERIODS}
    nonzero_terms = {period: 0 for period in PERIODS}
    checkpoints: dict[str, object] = {}
    modular_checks = 0
    fraction_checks = 0
    forced_carry_checks = 0
    previous_errors: dict[int, Fraction] = {}
    oversampled_previous_nearest: dict[int, int] = {}
    oversampled_nonzero = {period: 0 for period in PERIODS}
    oversampled_rows: dict[str, object] = {}
    oversampled_carry_checks = 0

    for n in range(DEPTH):
        if n > 0:
            denominator_n = coefficient_denominator(n)
            next_common = lcm(common_denominator, denominator_n)
            scaled_numerator = (
                16 * (next_common // common_denominator) * scaled_numerator
                + coefficient_numerator(n) * (next_common // denominator_n)
            )
            common_denominator = next_common
            five_power *= 5
            if n < FRACTION_DEPTH:
                exact_partial += coefficient(n) / 16**n

        modulus = 8**n * common_denominator
        orbit_numerator = five_power * scaled_numerator

        if n < FRACTION_DEPTH:
            require(
                Fraction(scaled_numerator, 16**n * common_denominator)
                == exact_partial,
                f"common-denominator BBP identity n={n}",
            )
            direct_u = fractional(10**n * exact_partial)
            modular_u = fractional(Fraction(orbit_numerator, modulus))
            require(direct_u == modular_u, f"modular orbit identity n={n}")
            fraction_checks += 1

        for period in PERIODS:
            multiplier = 10**period - 1
            residue = (multiplier * orbit_numerator) % modulus
            least = min(residue, modulus - residue)
            require(least > 0, f"finite nonzero defect n={n}, P={period}")
            distance = stable_ratio(least, modulus)
            sums[period] += distance * distance
            minima[period] = min(minima[period], distance)
            nonzero_terms[period] += 1
            modular_checks += 1

            if n < FRACTION_DEPTH:
                direct_u = fractional(Fraction(orbit_numerator, modulus))
                direct_distance = circle_norm(multiplier * direct_u)
                require(
                    direct_distance == Fraction(least, modulus),
                    f"exact defect residue n={n}, P={period}",
                )
                current_error = centered(multiplier * direct_u)
                if n > 0 and period <= 6:
                    forcing = coefficient(n) * Fraction(5, 8) ** n
                    carry = (
                        10 * previous_errors[period]
                        + multiplier * forcing
                        - current_error
                    )
                    require(carry.denominator == 1,
                            f"forced carry integral n={n}, P={period}")
                    forced_carry_checks += 1
                previous_errors[period] = current_error

        # At BBP depth m=7n, q*10^n*B_m is the rational shadow used in
        # the report's eventual exact centered-carry coding.  This loop only
        # computes its finite integer carries; the eventual equality with pi
        # uses the external irrationality-measure premise and is not asserted.
        if n % 7 == 0 and n // 7 <= OVERSAMPLED_CARRY_DEPTH:
            orbit_index = n // 7
            shadow_denominator = 16**n * common_denominator
            for period in PERIODS:
                multiplier = 10**period - 1
                shadow_numerator = (
                    multiplier * 10**orbit_index * scaled_numerator
                )
                nearest = (
                    2 * shadow_numerator + shadow_denominator
                ) // (2 * shadow_denominator)
                if orbit_index > 0:
                    carry = nearest - 10 * oversampled_previous_nearest[period]
                    oversampled_nonzero[period] += carry != 0
                    oversampled_carry_checks += 1
                oversampled_previous_nearest[period] = nearest

            if orbit_index in (64, 128, 256):
                oversampled_rows[str(orbit_index)] = {
                    str(period): {
                        "nonzero_carries": oversampled_nonzero[period],
                        "observed_fraction": (
                            oversampled_nonzero[period] / orbit_index
                        ),
                    }
                    for period in PERIODS
                }

        size = n + 1
        if size in CHECKPOINTS:
            checkpoints[str(size)] = {
                str(period): sums[period] / size for period in PERIODS
            }

    for k in range(1, DEPTH + 1):
        require(coefficient(k) > 0, f"coefficient positivity k={k}")
        require(coefficient(k) < Fraction(1, k * k), f"coefficient bound k={k}")

    # Sum rho^n/15 = 8/45 is the endpoint-safe total shadow allowance.
    require(Fraction(1, 15) / (1 - Fraction(5, 8)) == Fraction(8, 45),
            "BBP total shadow constant")

    carry_replay = check_centered_carry_lemmas()
    kempner = kempner_diagnostics()

    return {
        "status": "PASS",
        "claim_label": "experiment",
        "pinned_artifacts": len(PINS),
        "depth": DEPTH,
        "periods": list(PERIODS),
        "exact_common_denominator_checks": fraction_checks,
        "exact_modular_defect_checks": modular_checks,
        "exact_forced_carry_checks": forced_carry_checks,
        "exact_oversampled_rational_carry_checks": oversampled_carry_checks,
        "oversampled_rational_carry_diagnostics": oversampled_rows,
        "centered_carry_replay": carry_replay,
        "bbp_periodic_defect_means": checkpoints,
        "bbp_minimum_finite_defects": {
            str(period): minima[period] for period in PERIODS
        },
        "kempner_sparse_separator": kempner,
        "irrationality_exponent_used_in_report": "888/125",
        "carry_energy_constant": 121,
        "log_energy_constant": 1 / (121 * log(Fraction(888, 125))),
        "asserts_positive_cesaro_defect": False,
        "asserts_matching": False,
        "asserts_fixed_return": False,
        "asserts_v1": False,
    }


if __name__ == "__main__":
    print(json.dumps(replay(), indent=2, sort_keys=True))
