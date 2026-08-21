#!/usr/bin/env python3
"""Exact/finite checks for the adjacent-BBP infinite-support reduction.

The asymptotic matching, periodic-defect lower bounds, fixed-sixteen return,
and V1 are deliberately not asserted.  Every bounded orbit diagnostic is an
``experiment``.
"""

from __future__ import annotations

from fractions import Fraction
from hashlib import sha256
import json
from math import floor, gcd, log2
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]

PINS = {
    "problems/local/pi-digits.txt":
        "2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825",
    "work/ultrapi-resume/bbp_adjacent_shift_matching_attack.md":
        "2764624665fcb2bd4f7a7f8d4a1c4d1094e9459297e018cb095e0a76ff0feba6",
    "work/ultrapi-resume/bbp_adjacent_shift_matching_independent_audit.md":
        "2a4027b9a33806425903c5d5a460349230ad716f3e9672f19300f0874b2a4866",
    "work/theory/pi-digits/library/t44/furstenberg-1967-disjointness.pdf":
        "cd07faa4521080272cf2c303ee4e3a41ee6a3ba9e6aea114604becaca0ba9358",
    "work/theory/pi-lacunary-near-return-sparsity/library/t63/"
    "lagarias-math0101055v2.pdf":
        "a2a1171eb9c75c9fa3495ca3c3ceaa33c1d20b722bb56f82adb56d8c308209b9",
    "work/ultrapi-resume/library/chen-ye-zheng-2604.14036v1.pdf":
        "a17f776537f415e4f0b0508024cf95389b1ed4da05a347efda6b149bb2e4924d",
    "work/theory/pi-lacunary-near-return-sparsity/library/t104/"
    "rudnick-technau-2001.08820.pdf":
        "364164f781a31ad5267b3c43d91b0593418744e8ac9073407e24581981b887b2",
    "TheoryLib/PiPositiveDecimalFactorEntropy/"
    "T39T39ErgodicAffinityRigidity.lean":
        "f4982dacc90a436ca14e52d0529acbbfa8067d47e80679fb0173dff559d2ba09",
    "TheoryLib/PiQuantitativeBlockHitting/T70T70EmpiricalRigidityBridge.lean":
        "f8ecbfd2d9f8a13216e75d5ebb3732b98f7844147776b30de7f2666fc7ddec55",
}

DEPTH = 192
CHECKPOINTS = (48, 96, 192)
PERIODS = tuple(range(1, 7))


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def digest(path: Path) -> str:
    return sha256(path.read_bytes()).hexdigest()


def c0_clean(path: Path) -> bool:
    data = path.read_bytes()
    return all(byte in (9, 10, 13) or byte >= 32 for byte in data)


def coefficient(index: int) -> Fraction:
    split = (
        Fraction(4, 8 * index + 1)
        - Fraction(2, 8 * index + 4)
        - Fraction(1, 8 * index + 5)
        - Fraction(1, 8 * index + 6)
    )
    combined = Fraction(
        120 * index * index + 151 * index + 47,
        (2 * index + 1)
        * (4 * index + 3)
        * (8 * index + 1)
        * (8 * index + 5),
    )
    require(split == combined > 0, f"coefficient identity k={index}")
    return combined


def fractional(value: Fraction) -> Fraction:
    return value - value.numerator // value.denominator


def circle_norm(value: Fraction) -> Fraction:
    residue = fractional(value)
    return min(residue, 1 - residue)


def multiplicative_order_10(modulus: int) -> int:
    require(gcd(modulus, 10) == 1, "order requires gcd(modulus, 10)=1")
    residue = 10 % modulus
    period = 1
    while residue != 1:
        residue = (10 * residue) % modulus
        period += 1
        require(period <= modulus, f"order bound modulus={modulus}")
    return period


def sparse_bad_starts(sample_size: int, window: int) -> tuple[int, int]:
    powers = []
    value = 2
    while value <= sample_size + window:
        powers.append(value)
        value *= 2
    bad = sum(
        any(start < position <= start + window for position in powers)
        for start in range(1, sample_size + 1)
    )
    bound = window * (1 + floor(log2(sample_size + window)))
    require(bad <= bound, f"sparse-window bound N={sample_size}, L={window}")
    return bad, bound


def replay() -> dict[str, object]:
    u = [fractional(coefficient(0))]
    power = Fraction(1)
    for n in range(1, DEPTH + max(PERIODS) + 1):
        power *= Fraction(5, 8)
        u.append(fractional(10 * u[-1] + coefficient(n) * power))

    v = [fractional(Fraction(1, 30) + coefficient(1))]
    power = Fraction(1)
    for n in range(1, DEPTH + 1):
        power *= Fraction(5, 8)
        v.append(fractional(10 * v[-1] + coefficient(n + 1) * power))

    adjacent_checks = 0
    five_eight_checks = 0
    for n in range(1, DEPTH + 1):
        displacement = coefficient(n + 1) * Fraction(5, 8) ** n
        require(
            v[n] == fractional(16 * u[n] + displacement),
            f"adjacent identity n={n}",
        )
        require(
            fractional(5 * v[n]) == fractional(8 * u[n + 1]),
            f"five-eight identity n={n}",
        )
        adjacent_checks += 1
        five_eight_checks += 1

    periodic_defect_diagnostics: dict[str, dict[str, object]] = {}
    lag_comparison_checks = 0
    for size in CHECKPOINTS:
        row: dict[str, object] = {}
        for period in PERIODS:
            multiplier = 10**period - 1
            defect_sum = Fraction()
            lag_sum = Fraction()
            forcing_sum = Fraction()
            global_forcing_bound = (
                Fraction(10**period, 9)
                * (1 - Fraction(1, 16**period))
            )
            geometric_form = Fraction(5, 3) * sum(
                Fraction(10 ** (period - shift))
                * Fraction(5, 8) ** shift
                for shift in range(1, period + 1)
            )
            require(
                geometric_form == global_forcing_bound,
                f"global forcing constant P={period}",
            )
            for n in range(1, size + 1):
                defect_term = circle_norm(multiplier * u[n]) ** 2
                lag_term = circle_norm(u[n + period] - u[n]) ** 2
                forcing = sum(
                    10 ** (period - shift)
                    * coefficient(n + shift)
                    * Fraction(5, 8) ** (n + shift)
                    for shift in range(1, period + 1)
                )
                require(
                    abs(lag_term - defect_term) <= forcing,
                    f"fixed-lag comparison N={size}, P={period}, n={n}",
                )
                defect_sum += defect_term
                lag_sum += lag_term
                forcing_sum += forcing
                lag_comparison_checks += 1
            require(
                forcing_sum <= global_forcing_bound,
                f"partial forcing bounded by global series N={size}, P={period}",
            )
            defect = defect_sum / size
            lag = lag_sum / size
            require(defect > 0, f"finite defect N={size}, P={period}")
            require(
                abs(lag - defect) <= forcing_sum / size,
                f"averaged lag comparison N={size}, P={period}",
            )
            row[str(period)] = {
                "periodic_defect": float(defect),
                "fixed_lag_square_distance": float(lag),
                "certified_average_difference_bound": float(forcing_sum / size),
                "universal_average_difference_bound": float(
                    global_forcing_bound / size
                ),
            }
        periodic_defect_diagnostics[str(size)] = row

    finite_common_invariant_checks = 0
    finite_common_invariant_examples = []
    for modulus in range(3, 81):
        if gcd(modulus, 10) != 1:
            continue
        period = multiplicative_order_10(modulus)
        residues = set(range(modulus))
        require(
            {(10 * r) % modulus for r in residues} == residues,
            f"times-ten grid permutation q={modulus}",
        )
        require(
            {(16 * r) % modulus for r in residues} == residues,
            f"times-sixteen grid permutation q={modulus}",
        )
        for residue in residues:
            require(
                (10**period - 1) * residue % modulus == 0,
                f"periodic defect vanishes q={modulus}, r={residue}",
            )
            finite_common_invariant_checks += 1
        if len(finite_common_invariant_examples) < 8:
            finite_common_invariant_examples.append(
                {"modulus": modulus, "common_decimal_period": period}
            )

    # For mu = (delta_0 + Lebesgue)/2, every periodic defect is 1/24,
    # while the diagonal atom contributes 1/4 to the small-scale pair energy.
    lebesgue_circle_square_integral = Fraction(1, 12)
    mixed_periodic_defect = lebesgue_circle_square_integral / 2
    mixed_atomic_pair_mass = Fraction(1, 4)
    require(mixed_periodic_defect == Fraction(1, 24), "mixed defect")
    require(mixed_atomic_pair_mass > 0, "mixed atom survives")

    sparse_checks = {}
    for sample_size in (1_000, 10_000, 100_000):
        window = max(2, floor(log2(sample_size) ** 0.5))
        bad, bound = sparse_bad_starts(sample_size, window)
        delta_bound = Fraction(5, 3) * Fraction(1, 10**window)
        sparse_checks[str(sample_size)] = {
            "window": window,
            "bad_fraction": bad / sample_size,
            "stated_bad_fraction_bound": bound / sample_size,
            "indexwise_good_matching_distance_bound": float(delta_bound),
        }

    mathlib_markers = {
        "support_mono": "lemma support_mono" in (
            ROOT / ".lake/packages/mathlib/Mathlib/MeasureTheory/Measure/Support.lean"
        ).read_text(),
        "absolutely_continuous_support_mono":
            "AbsolutelyContinuous.support_mono" in (
                ROOT
                / ".lake/packages/mathlib/Mathlib/MeasureTheory/Measure/Support.lean"
            ).read_text(),
        "mutually_singular": "def MutuallySingular" in (
            ROOT
            / ".lake/packages/mathlib/Mathlib/MeasureTheory/Measure/MutuallySingular.lean"
        ).read_text(),
    }
    require(all(mathlib_markers.values()), f"mathlib marker failure: {mathlib_markers}")

    return {
        "depth": DEPTH,
        "adjacent_checks": adjacent_checks,
        "five_v_equals_eight_u_next_checks": five_eight_checks,
        "fixed_lag_comparison_checks": lag_comparison_checks,
        "periodic_defect_diagnostics": periodic_defect_diagnostics,
        "finite_common_invariant_grid_checks": finite_common_invariant_checks,
        "finite_common_invariant_examples": finite_common_invariant_examples,
        "strict_weakening_example": {
            "measure": "(delta_0 + Lebesgue)/2",
            "every_periodic_defect": "1/24",
            "limiting_atomic_pair_mass_at_least": "1/4",
        },
        "sparse_matching_separator": sparse_checks,
        "mathlib_markers": mathlib_markers,
        "warning": "all bounded BBP values and sparse counts are experiment only",
    }


def main() -> None:
    pins = {}
    for relative, expected in PINS.items():
        actual = digest(ROOT / relative)
        require(actual == expected, f"pin mismatch {relative}: {actual}")
        if Path(relative).suffix in {".lean", ".md", ".py", ".txt"}:
            require(c0_clean(ROOT / relative), f"C0 control byte in {relative}")
        pins[relative] = actual

    report = ROOT / "work/ultrapi-resume/bbp_adjacent_matching_breakthrough_report.md"
    require(c0_clean(report), "C0 control byte in breakthrough report")
    require(c0_clean(Path(__file__)), "C0 control byte in breakthrough checker")

    output = {
        "status": "PASS",
        "claim_label": "experiment",
        "source_pins": pins,
        "c0_hygiene": "PASS",
        "replay": replay(),
        "asserts_asymptotic_matching": False,
        "asserts_periodic_defect_lower_bounds_for_pi": False,
        "asserts_fixed_sixteen_return": False,
        "asserts_v1": False,
    }
    print(json.dumps(output, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
