#!/usr/bin/env python3
"""Independent exact checks for BBP three-primary ninefold decimation.

This checker imports no primary checker code. Every bounded result printed
here has claim status ``experiment``; it does not prove canonical V1.
"""

from __future__ import annotations

import hashlib
import math
import re
import subprocess
import sys
from fractions import Fraction
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
PINS = {
    "problems/local/pi-digits.txt":
        "2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825",
    "work/ultrapi-resume/bbp_three_primary_epoch_20260813.md":
        "5b34ceb3aa2857b9227cce5ac7ae84cafbbac47d2c12adf889c37f11280d6fd7",
    "work/ultrapi-resume/bbp_three_primary_decimation_20260813.md":
        "29d4f903dca429ebe2cedad248f0a726b985492bfd0f06471a668a47e652ede0",
    "work/ultrapi-resume/bbp_three_primary_decimation_20260813_check.py":
        "abda4aa38bc575439320ecc60a44d0df8418be042b2bb0558f70f05c1c2dfc71",
    "TheoryLib/PiQuantitativeBlockHitting/T73T73ThreePrimaryOrbit.lean":
        "1499b29893a05fe91d64ee468ff320f0f59c23eb07f13220dab64b9fbfe23009",
    "TheoryLib/PiQuantitativeBlockHitting/T74T74ThreePrimaryDecimation.lean":
        "eb103c72fd7cf7b0f91c85a102d8d7ed5165028b1d64ae23dac714f6093f2727",
    "work/theory/pi-quantitative-block-hitting/library/t4/bbp-1997.pdf":
        "e4e0b97fde01328ec41da5f2cd4d6ffc8bcd2b7bd7516b9d8afc320f6d1916c4",
}

# slope, intercept, rational coefficient, fold offset, exponent multiplier
POLES = (
    (8, 1, Fraction(4), 1, 1),
    (2, 1, Fraction(-1, 2), 4, 4),
    (8, 5, Fraction(-1), 5, 1),
    (4, 3, Fraction(-1, 2), 6, 2),
)
T74_THEOREMS = {
    "poleOne_affine_fold", "poleTwo_affine_fold",
    "poleThree_affine_fold", "poleFour_affine_fold",
    "poleOne_exponent_fold", "poleTwo_exponent_fold",
    "poleThree_exponent_fold", "poleFour_exponent_fold",
    "poleOne_decimation", "poleTwo_decimation",
    "poleThree_decimation", "poleFour_decimation",
}
MAX_FINITE_DEPTH = 729
MAX_ENDPOINT_EXPONENT = 180
MAX_BETA_EXPONENT = 12


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def v3_integer(value: int) -> int:
    require(value != 0, "valuation at zero is not used")
    value = abs(value)
    answer = 0
    while value % 3 == 0:
        answer += 1
        value //= 3
    return answer


def v3_rational(value: Fraction) -> int:
    require(value != 0, "valuation at zero is not used")
    return v3_integer(value.numerator) - v3_integer(value.denominator)


def pole_term(pole: tuple[int, int, Fraction, int, int], k: int) -> Fraction:
    slope, intercept, coefficient, _, _ = pole
    return coefficient / ((slope * k + intercept) * 16**k)


def partial_fraction_sum(k: int) -> Fraction:
    return sum((pole_term(pole, k) for pole in POLES), Fraction())


def collapsed_term(k: int) -> Fraction:
    numerator = 120 * k * k + 151 * k + 47
    denominator = ((2 * k + 1) * (4 * k + 3) *
                   (8 * k + 1) * (8 * k + 5) * 16**k)
    return Fraction(numerator, denominator)


def localized_pole(pole: tuple[int, int, Fraction, int, int],
                   k: int, scale: int, modulus: int) -> int:
    """Return 3^scale times one pole term modulo 3^scale."""
    slope, intercept, coefficient, _, _ = pole
    linear = slope * k + intercept
    num, den = coefficient.numerator, coefficient.denominator * linear
    num_height, den_height = v3_integer(num), v3_integer(den)
    num_unit, den_unit = num // 3**num_height, den // 3**den_height
    shift = scale + num_height - den_height
    require(shift >= 0, f"scale {scale} does not localize pole at k={k}")
    if shift >= scale:
        return 0
    return (num_unit * 3**shift * pow(den_unit, -1, modulus) *
            pow(pow(16, k, modulus), -1, modulus)) % modulus


def endpoint_units(e: int) -> tuple[int, int, int]:
    """Compute M_e^-, U_e^- mod 3^e, U_e^+ mod 3^(e-1)."""
    require(e >= 2 and e % 2 == 0, "positive even epoch required")
    modulus = 3**e
    A = (modulus - 1) // 8
    pre_depth = 5 * A - 1
    scaled = 0
    for k in range(pre_depth + 1):
        for pole in POLES:
            scaled = (scaled + localized_pole(pole, k, e, modulus)) % modulus
    pre = scaled
    for pole in POLES:
        scaled = (scaled + localized_pole(pole, pre_depth + 1, e, modulus)) % modulus
    require(scaled % 3 == 0, f"top cluster fails to cancel at e={e}")
    post = scaled // 3
    require(pre % 3 == 2 and post % 3 == 2, f"wrong endpoint unit at e={e}")
    return pre_depth, pre, post


def residual_g(n: int, modulus: int) -> int:
    """Return (10^n-16)/3 modulo modulus without enormous powers."""
    if modulus == 1:
        return 0
    numerator = pow(10, n, 3 * modulus) - 16
    require(numerator % 3 == 0, "residual division by three failed")
    return (numerator // 3) % modulus


def v3_sixteen_power_minus_one(exponent: int) -> int:
    """Determine the valuation using only two powers beyond LTE's prediction."""
    predicted = 1 + v3_integer(exponent)
    modulus = 3 ** (predicted + 1)
    residue = (pow(16, exponent, modulus) - 1) % modulus
    require(residue != 0, f"valuation exceeds prediction at q={exponent}")
    return v3_integer(residue)


def run() -> dict[str, object]:
    if hasattr(sys, "set_int_max_str_digits"):
        sys.set_int_max_str_digits(0)
    for relative, expected in PINS.items():
        path = ROOT / relative
        require(path.is_file(), f"missing pinned artifact: {relative}")
        require(digest(path) == expected, f"hash mismatch: {relative}")

    coefficient_checks = 0
    for k in range(2049):
        require(partial_fraction_sum(k) == collapsed_term(k),
                f"partial fraction at k={k}")
        coefficient_checks += 1

    # Independently check the folds and exact LTE valuation. The general LTE
    # proof is in the audit; these bounded checks are falsification attempts.
    fold_checks = term_identity_checks = lte_checks = nonfold_checks = 0
    for pole_number, pole in enumerate(POLES, start=1):
        slope, intercept, _, offset, multiplier = pole
        require(slope * offset + intercept == 9 * intercept,
                f"constant affine fold for pole {pole_number}")
        for r in range(4097):
            old_linear = slope * r + intercept
            new_index = 9 * r + offset
            increment = 8 * r + offset
            require(slope * new_index + intercept == 9 * old_linear,
                    f"affine fold pole={pole_number}, r={r}")
            require(increment == multiplier * old_linear,
                    f"exponent fold pole={pole_number}, r={r}")
            require(v3_sixteen_power_minus_one(increment)
                    == 1 + v3_integer(increment),
                    f"LTE value pole={pole_number}, r={r}")
            fold_checks += 1
            lte_checks += 1
            if r <= 256:
                lhs = 9 * pole_term(pole, new_index) - pole_term(pole, r)
                rhs = pole_term(pole, r) * (Fraction(1, 16**increment) - 1)
                require(lhs == rhs, f"term identity pole={pole_number}, r={r}")
                require(v3_rational(lhs) == 1,
                        f"lift error valuation pole={pole_number}, r={r}")
                term_identity_checks += 1
                lte_checks += 1

        solutions = [k for k in range(9)
                     if (slope * k + intercept) % 9 == 0]
        require(solutions == [offset],
                f"wrong modulo-nine fold class for pole {pole_number}")
        for k in range(8193):
            if k % 9 == offset:
                continue
            linear = slope * k + intercept
            require(v3_integer(linear) <= 1,
                    f"unfolded pole has height >=2: pole={pole_number}, k={k}")
            require(v3_rational(9 * pole_term(pole, k)) >= 1,
                    f"unfolded term not in 3Z_(3): pole={pole_number}, k={k}")
            nonfold_checks += 1

    # Direct finite sums with an explicit floor and negative-cutoff convention.
    prefixes: list[list[Fraction]] = [[] for _ in POLES]
    for pole_index, pole in enumerate(POLES):
        running = Fraction()
        for k in range(MAX_FINITE_DEPTH + 1):
            running += pole_term(pole, k)
            prefixes[pole_index].append(running)

    def finite_pole_sum(pole_index: int, cutoff: int) -> Fraction:
        return Fraction() if cutoff < 0 else prefixes[pole_index][cutoff]

    expected_small_cutoffs = {
        0: (-1, -1, -1, -1), 1: (0, -1, -1, -1),
        3: (0, -1, -1, -1), 4: (0, 0, -1, -1),
        5: (0, 0, 0, -1), 6: (0, 0, 0, 0),
    }
    cutoff_checks = finite_sum_checks = 0
    total = Fraction()
    for M in range(MAX_FINITE_DEPTH + 1):
        total += partial_fraction_sum(M)
        cutoffs = tuple((M - pole[3]) // 9 for pole in POLES)
        if M in expected_small_cutoffs:
            require(cutoffs == expected_small_cutoffs[M],
                    f"negative-cutoff boundary at M={M}: {cutoffs}")
            cutoff_checks += 1
        decimated = sum(
            (finite_pole_sum(i, cutoff) for i, cutoff in enumerate(cutoffs)),
            Fraction(),
        )
        require(v3_rational(9 * total - decimated) >= 1,
                f"finite decimation not in 3Z_(3) at M={M}")
        finite_sum_checks += 1

    # Symbolic endpoint and cutoff relations, including the e=4/e=2 edge.
    endpoint_checks = 0
    for e in range(4, MAX_ENDPOINT_EXPONENT + 1, 2):
        old_A = (3 ** (e - 2) - 1) // 8
        old_pre, old_post = 5 * old_A - 1, 5 * old_A
        A = (3**e - 1) // 8
        pre, post = 5 * A - 1, 5 * A
        require(pre == 9 * old_pre + 13, f"pre recurrence e={e}")
        require(post == 9 * old_post + 5, f"post recurrence e={e}")
        require(tuple((pre - p[3]) // 9 for p in POLES)
                == (old_pre + 1, old_pre + 1, old_pre, old_pre),
                f"pre cutoffs e={e}")
        require(tuple((post - p[3]) // 9 for p in POLES)
                == (old_post, old_post, old_post, old_post - 1),
                f"post cutoffs e={e}")
        require((8 * old_post + 1) % 3 != 0, f"pre extra pole 1 e={e}")
        require((2 * old_post + 1) % 3 != 0, f"pre extra pole 2 e={e}")
        require((4 * old_post + 3) % 3 != 0, f"post missing pole e={e}")
        endpoint_checks += 1

    expected_rows = [
        (2, 4, 2, 2), (4, 49, 38, 23), (6, 454, 524, 185),
        (8, 4099, 4898, 914), (10, 36904, 57386, 18410),
        (12, 332149, 175484, 175874),
    ]
    beta_rows: list[tuple[int, int, int, int]] = []
    beta_nesting_checks = 0
    previous: tuple[int, int] | None = None
    for e in range(2, MAX_BETA_EXPONENT + 1, 2):
        row = (e, *endpoint_units(e))
        beta_rows.append(row)
        require(row == expected_rows[(e - 2) // 2], f"endpoint table e={e}: {row}")
        if previous is not None:
            require(row[2] % 3 ** (e - 2) == previous[0], f"pre nesting e={e}")
            require(row[3] % 3 ** (e - 3) == previous[1], f"drop nesting e={e}")
            beta_nesting_checks += 2
        previous = (row[2], row[3])

    # The inverse maps distinguish the exceptional first drop refinement.
    fixed_exponent_checks = grid_map_checks = 0
    exceptional_drop_fibres = generic_drop_fibres = 0
    units = {e: (pre, post) for e, _, pre, post in beta_rows}
    for e in range(4, MAX_BETA_EXPONENT + 1, 2):
        pre, post = units[e]
        old_pre, old_post = units[e - 2]
        pre_modulus, old_pre_modulus = 3 ** (e - 1), 3 ** (e - 3)
        drop_modulus = 3 ** (e - 2)
        old_drop_modulus = 1 if e == 4 else 3 ** (e - 4)

        for n in range(1, min(500, 3 ** (e - 2)) + 1):
            new_value = pre * residual_g(n, pre_modulus) % pre_modulus
            old_value = old_pre * residual_g(n, old_pre_modulus) % old_pre_modulus
            require(new_value % old_pre_modulus == old_value,
                    f"pre fixed-n inverse map e={e}, n={n}")
            new_drop = post * residual_g(n, drop_modulus) % drop_modulus
            old_drop = (old_post * residual_g(n, old_drop_modulus)
                        % old_drop_modulus if old_drop_modulus > 1 else 0)
            require(new_drop % old_drop_modulus == old_drop,
                    f"drop fixed-n inverse map e={e}, n={n}")
            fixed_exponent_checks += 2

        pre_period, old_pre_period = 3 ** (e - 2), 3 ** (e - 4)
        pre_counts = {x: 0 for x in range(old_pre_modulus)}
        for n in range(1, pre_period + 1):
            value = pre * residual_g(n, pre_modulus) % pre_modulus
            pre_counts[value % old_pre_modulus] += 1
        old_grid = {
            old_pre * residual_g(n, old_pre_modulus) % old_pre_modulus
            for n in range(1, old_pre_period + 1)
        }
        require({x for x, count in pre_counts.items() if count} == old_grid,
                f"pre grid image e={e}")
        require({pre_counts[x] for x in old_grid} == {9},
                f"pre grid fibre e={e}")
        grid_map_checks += len(old_grid)

        drop_period = 3 ** (e - 3)
        old_drop_period = 1 if e == 4 else 3 ** (e - 5)
        drop_counts = {x: 0 for x in range(old_drop_modulus)}
        for n in range(1, drop_period + 1):
            value = post * residual_g(n, drop_modulus) % drop_modulus
            drop_counts[value % old_drop_modulus] += 1
        old_drop_grid = ({0} if e == 4 else {
            old_post * residual_g(n, old_drop_modulus) % old_drop_modulus
            for n in range(1, old_drop_period + 1)
        })
        require({x for x, count in drop_counts.items() if count} == old_drop_grid,
                f"drop grid image e={e}")
        fibre = 3 if e == 4 else 9
        require({drop_counts[x] for x in old_drop_grid} == {fibre},
                f"drop grid fibre e={e}")
        if e == 4:
            exceptional_drop_fibres += len(old_drop_grid)
        else:
            generic_drop_fibres += len(old_drop_grid)
        grid_map_checks += len(old_drop_grid)

    # Positive coefficient and real-shadow algebra.
    coefficient_bound_checks = 0
    for k in range(1, 4097):
        numerator = 120 * k * k + 151 * k + 47
        denominator = ((2 * k + 1) * (4 * k + 3) *
                       (8 * k + 1) * (8 * k + 5))
        require(0 < numerator * k * k <= denominator,
                f"tail coefficient bound k={k}")
        coefficient_bound_checks += 1

    shadow_checks = 0
    contraction = Fraction(31250, 32768)
    require(contraction < 1, "shadow ratio must contract")
    for e in range(2, MAX_ENDPOINT_EXPONENT + 1, 2):
        period = 3 ** (e - 2)
        M = (45 * period - 13) // 8
        require(8 * M == 45 * period - 13, f"depth identity e={e}")
        require(M >= 5 * (period - 1), f"period margin e={e}")
        # The direct huge-power inequality is checked at the first four
        # epochs; all depths follow monotonically from the margin above.
        if e <= 8:
            lhs = Fraction(10 ** (M + period), 16**M)
            rhs = Fraction(8, 5) ** 5 * contraction**period
            require(lhs <= rhs, f"direct shadow inequality e={e}")
        shadow_checks += 1

    # Exact declaration/registration sets and forbidden-construct scan.
    t74_path = ROOT / "TheoryLib/PiQuantitativeBlockHitting/T74T74ThreePrimaryDecimation.lean"
    t74_text = t74_path.read_text()
    declared = set(re.findall(r"^theorem\s+([A-Za-z0-9_]+)", t74_text, re.MULTILINE))
    require(declared == T74_THEOREMS,
            f"unexpected T74 theorem set: {sorted(declared ^ T74_THEOREMS)}")
    forbidden = re.findall(
        r"(?m)^\s*(?:sorry|admit|axiom|opaque|unsafe\b)|\bnative_decide\b",
        t74_text,
    )
    require(not forbidden, f"forbidden T74 constructs: {forbidden}")
    audit_text = (ROOT / "audit/AxiomAudit.lean").read_text()
    prefix = r"Theory\.PiDigits\.T74ThreePrimaryDecimation\."
    registered = set(re.findall(
        r"#print axioms " + prefix + r"([A-Za-z0-9_]+)", audit_text
    ))
    require(registered == T74_THEOREMS,
            f"T74 registration mismatch: {sorted(registered ^ T74_THEOREMS)}")
    require(audit_text.count(
        "import TheoryLib.PiQuantitativeBlockHitting.T74T74ThreePrimaryDecimation"
    ) == 1, "T74 audit import count is not one")

    lean = subprocess.run(
        ["lake", "env", "lean", "--trust=0",
         "TheoryLib/PiQuantitativeBlockHitting/T74T74ThreePrimaryDecimation.lean"],
        cwd=ROOT, check=False, text=True,
        stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
    )
    require(lean.returncode == 0, f"T74 trust-zero compile failed:\n{lean.stdout}")
    printed = set(re.findall(
        r"'Theory\.PiDigits\.T74ThreePrimaryDecimation\.([A-Za-z0-9_]+)'",
        lean.stdout,
    ))
    require(printed == T74_THEOREMS,
            f"T74 printed theorem mismatch: {sorted(printed ^ T74_THEOREMS)}")
    found_axioms = set(re.findall(
        r"\b(?:propext|Classical\.choice|Quot\.sound|sorryAx)\b", lean.stdout
    ))
    allowed = {"propext", "Classical.choice", "Quot.sound"}
    require(found_axioms <= allowed and "sorryAx" not in lean.stdout,
            f"unexpected T74 axioms: {sorted(found_axioms)}")

    return {
        "claim_status": "experiment",
        "pinned_artifact_checks": len(PINS),
        "partial_fraction_checks": coefficient_checks,
        "fold_identity_checks": fold_checks,
        "exact_term_identity_checks": term_identity_checks,
        "lte_and_exact_valuation_checks": lte_checks,
        "nonfold_integrality_checks": nonfold_checks,
        "negative_cutoff_boundary_checks": cutoff_checks,
        "finite_sum_decimation_checks": finite_sum_checks,
        "symbolic_endpoint_checks": endpoint_checks,
        "beta_nesting_checks": beta_nesting_checks,
        "fixed_exponent_inverse_checks": fixed_exponent_checks,
        "grid_map_checks": grid_map_checks,
        "exceptional_e4_drop_three_fibres": exceptional_drop_fibres,
        "generic_drop_nine_fibres": generic_drop_fibres,
        "positive_tail_coefficient_checks": coefficient_bound_checks,
        "real_shadow_checks": shadow_checks,
        "t74_theorem_count": len(declared),
        "t74_registered_theorem_count": len(registered),
        "t74_trust_zero": "PASS",
        "t74_axioms": ",".join(sorted(found_axioms)),
        "beta_rows": ";".join(
            f"e{e}:M{depth}:pre{pre}:post{post}"
            for e, depth, pre, post in beta_rows
        ),
        "asserts_joint_crt_control": "false",
        "asserts_fixed_return": "false",
        "asserts_v1": "false",
        "status": "PASS_WITH_BOUNDARY_QUALIFICATION",
    }


if __name__ == "__main__":
    for key, value in run().items():
        print(f"{key}={value}")
