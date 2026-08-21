#!/usr/bin/env python3
"""Independent exact checks for the BBP infinite-support reduction.

This checker was written independently of the primary replay.  Its finite
orbit values are experiments; it does not assert an asymptotic matching,
periodic-defect lower bound for pi, fixed-sixteen return, or V1.
"""

from __future__ import annotations

from fractions import Fraction
from hashlib import sha256
import json
from math import floor, gcd, log2
from pathlib import Path
import re


ROOT = Path(__file__).resolve().parents[2]
REPORT = ROOT / "work/ultrapi-resume/bbp_adjacent_matching_breakthrough_report.md"

PINS = {
    "problems/local/pi-digits.txt":
        "2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825",
    "work/ultrapi-resume/bbp_adjacent_shift_matching_attack.md":
        "2764624665fcb2bd4f7a7f8d4a1c4d1094e9459297e018cb095e0a76ff0feba6",
    "work/ultrapi-resume/bbp_adjacent_shift_matching_independent_audit.md":
        "2a4027b9a33806425903c5d5a460349230ad716f3e9672f19300f0874b2a4866",
    "work/ultrapi-resume/bbp_adjacent_matching_breakthrough_report.md":
        "2b231d3c2e2ef717a2941a0452304ba402915318b72d305f6a6129ee8431f042",
    "work/ultrapi-resume/bbp_adjacent_matching_breakthrough_check.py":
        "2844f28d7ecdf13c02c623a3ba17c43dcde347efa4e8c4e864d48530eac873e9",
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

DEPTH = 149
CHECKPOINTS = (31, 79, 137)
PERIODS = (1, 2, 3, 5, 8)


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def digest(path: Path) -> str:
    return sha256(path.read_bytes()).hexdigest()


def hygienic_text(path: Path) -> None:
    data = path.read_bytes()
    text = data.decode("utf-8")
    require(
        all(byte in (9, 10, 13) or byte >= 32 for byte in data),
        f"C0 control byte: {path}",
    )
    require("\t" not in text, f"tab: {path}")
    require(
        all(line.rstrip() == line for line in text.splitlines()),
        f"trailing whitespace: {path}",
    )


def frac(value: Fraction) -> Fraction:
    return value - value.numerator // value.denominator


def circle_norm(value: Fraction) -> Fraction:
    residue = frac(value)
    return min(residue, 1 - residue)


def coefficient(k: int) -> Fraction:
    require(k >= 0, "coefficient index")
    poles = (
        Fraction(4, 8 * k + 1)
        - Fraction(2, 8 * k + 4)
        - Fraction(1, 8 * k + 5)
        - Fraction(1, 8 * k + 6)
    )
    rational = Fraction(
        120 * k * k + 151 * k + 47,
        (2 * k + 1) * (4 * k + 3) * (8 * k + 1) * (8 * k + 5),
    )
    require(poles == rational > 0, f"four-pole coefficient k={k}")
    if k >= 1:
        positive_polynomial = (
            392 * k**4 + 873 * k**3 + 665 * k**2 + 194 * k + 15
        )
        require(
            Fraction(1, k * k) - rational
            == Fraction(
                positive_polynomial,
                k * k
                * (2 * k + 1)
                * (4 * k + 3)
                * (8 * k + 1)
                * (8 * k + 5),
            ),
            f"coefficient upper-bound identity k={k}",
        )
    return rational


def partial_bbp(n: int) -> Fraction:
    return sum((coefficient(k) / 16**k for k in range(n + 1)), Fraction())


def shifted_partial_bbp(n: int) -> Fraction:
    return Fraction(1, 30) + sum(
        (coefficient(k + 1) / 16**k for k in range(n + 1)), Fraction()
    )


def multiplicative_order(base: int, modulus: int) -> int:
    require(gcd(base, modulus) == 1, "multiplicative order domain")
    value = base % modulus
    order = 1
    while value != 1:
        value = value * base % modulus
        order += 1
        require(order <= modulus, f"order search q={modulus}")
    return order


def local_links(markdown: Path) -> list[str]:
    targets = re.findall(r"\[[^\]]+\]\(([^)]+)\)", markdown.read_text())
    missing = []
    for target in targets:
        if target.startswith(("https://", "http://", "#")):
            continue
        candidate = (markdown.parent / target.split("#", 1)[0]).resolve()
        if not candidate.exists():
            missing.append(target)
    return missing


def replay() -> dict[str, object]:
    # Build both rows from their defining partial sums, not from the primary
    # checker's recurrences.
    u = [frac(10**n * partial_bbp(n)) for n in range(DEPTH + max(PERIODS) + 1)]
    v = [frac(10**n * shifted_partial_bbp(n)) for n in range(DEPTH + 2)]

    adjacent = 0
    recurrence = 0
    five_eight = 0
    for n in range(1, DEPTH + 1):
        qn = Fraction(5, 8) ** n
        require(
            v[n] == frac(16 * u[n] + coefficient(n + 1) * qn),
            f"adjacent identity n={n}",
        )
        require(
            u[n + 1]
            == frac(10 * u[n] + coefficient(n + 1) * Fraction(5, 8) ** (n + 1)),
            f"u recurrence n={n}",
        )
        require(
            v[n + 1] == frac(
                10 * v[n] + coefficient(n + 2) * Fraction(5, 8) ** (n + 1)
            ),
            f"v recurrence n={n}",
        )
        require(frac(5 * v[n]) == frac(8 * u[n + 1]), f"5v=8u n={n}")
        adjacent += 1
        recurrence += 2
        five_eight += 1

    lag_checks = 0
    lag_rows: dict[str, dict[str, object]] = {}
    for size in CHECKPOINTS:
        row: dict[str, object] = {}
        for period in PERIODS:
            exact_error = Fraction()
            defect_average = Fraction()
            lag_average = Fraction()
            for n in range(1, size + 1):
                forcing = sum(
                    (
                        10 ** (period - r)
                        * coefficient(n + r)
                        * Fraction(5, 8) ** (n + r)
                    )
                    for r in range(1, period + 1)
                )
                require(
                    u[n + period] == frac(10**period * u[n] + forcing),
                    f"iterated recurrence n={n}, P={period}",
                )
                defect = circle_norm((10**period - 1) * u[n]) ** 2
                lag = circle_norm(u[n + period] - u[n]) ** 2
                require(abs(lag - defect) <= forcing, f"lag Lipschitz n={n}, P={period}")
                exact_error += forcing
                defect_average += defect
                lag_average += lag
                lag_checks += 1

            universal = Fraction(10**period, 9) * (1 - Fraction(1, 16**period))
            independent_geometric = Fraction(5, 3) * sum(
                (Fraction(10 ** (period - r)) * Fraction(5, 8) ** r)
                for r in range(1, period + 1)
            )
            require(universal == independent_geometric, f"series constant P={period}")
            require(exact_error <= universal, f"endpoint bound N={size}, P={period}")
            require(
                abs(lag_average - defect_average) <= exact_error,
                f"averaged comparison N={size}, P={period}",
            )
            row[str(period)] = {
                "periodic_defect": float(defect_average / size),
                "fixed_lag_square_distance": float(lag_average / size),
                "actual_average_error_bound": float(exact_error / size),
                "universal_average_error_bound": float(universal / size),
            }
        lag_rows[str(size)] = row

    grid_checks = 0
    grids = []
    for modulus in range(2, 114):
        if gcd(modulus, 10) != 1:
            continue
        residues = set(range(modulus))
        require({10 * r % modulus for r in residues} == residues, f"T10 grid q={modulus}")
        require({16 * r % modulus for r in residues} == residues, f"T16 grid q={modulus}")
        period = multiplicative_order(10, modulus)
        require(
            all((10**period - 1) * r % modulus == 0 for r in residues),
            f"common periodic defect q={modulus}",
        )
        grid_checks += modulus
        if len(grids) < 10:
            grids.append({"modulus": modulus, "period": period})

    # Integral over the circle of ||x||^2 is 2*Integral_0^(1/2) x^2 dx.
    lebesgue_second_moment = 2 * Fraction(1, 3) * Fraction(1, 2) ** 3
    require(lebesgue_second_moment == Fraction(1, 12), "Lebesgue circle moment")
    require(lebesgue_second_moment / 2 == Fraction(1, 24), "mixed defect")
    require(Fraction(1, 2) ** 2 == Fraction(1, 4), "mixed collision atom")

    sparse = {}
    for size in (997, 9_973, 99_991):
        window = max(2, floor(log2(size) ** 0.5))
        powers = []
        p = 2
        while p <= size + window:
            powers.append(p)
            p *= 2
        bad = sum(
            any(start < position <= start + window for position in powers)
            for start in range(1, size + 1)
        )
        bound = window * (1 + floor(log2(size + window)))
        require(bad <= bound, f"sparse separator N={size}")
        sparse[str(size)] = {
            "window": window,
            "bad_fraction": bad / size,
            "certified_bad_fraction_bound": bound / size,
            "good_matching_distance_bound": float(Fraction(5, 3 * 10**window)),
        }

    t39 = (
        ROOT
        / "TheoryLib/PiPositiveDecimalFactorEntropy/T39T39ErgodicAffinityRigidity.lean"
    ).read_text()
    t70 = (
        ROOT / "TheoryLib/PiQuantitativeBlockHitting/T70T70EmpiricalRigidityBridge.lean"
    ).read_text()
    lean_markers = {
        marker: marker in t39
        for marker in (
            "theorem timesTen_timesSixteen_commute",
            "theorem timesSixteenPushforward_ergodic",
            "theorem ergodic_eq_or_mutuallySingular",
            "theorem common_ergodic_not_mutuallySingular_eq",
        )
    }
    lean_markers["T70 nonsingularity bridge"] = (
        "theorem notMutuallySingular_implies_timesSixteen_invariant" in t70
    )
    require(all(lean_markers.values()), f"Lean source markers: {lean_markers}")

    report = REPORT.read_text()
    required_report_markers = {
        "typed matching map": r"\sigma_j:G_j\to\{1,\ldots,N_j\}",
        "same subsequence": "on the same\nsequence \\(N_j\\)",
        "all fixed periods": r"for every fixed integer \(P\geq1\)",
        "positive matching mass": r"\liminf_j{|G_j|\over N_j}>0",
        "no V1 claim": "V1 remains a conjecture",
    }
    marker_results = {
        label: marker in report for label, marker in required_report_markers.items()
    }
    require(all(marker_results.values()), f"report markers: {marker_results}")
    require(not local_links(REPORT), f"missing local links: {local_links(REPORT)}")

    return {
        "explicit_row_depth": DEPTH,
        "adjacent_identity_checks": adjacent,
        "recurrence_checks": recurrence,
        "five_eight_identity_checks": five_eight,
        "fixed_lag_checks": lag_checks,
        "fixed_lag_experiments": lag_rows,
        "finite_invariant_grid_point_checks": grid_checks,
        "finite_invariant_grid_examples": grids,
        "strict_weakening_exact_values": {
            "periodic_defect": "1/24",
            "atomic_close_pair_mass": "1/4",
        },
        "sparse_separator_experiments": sparse,
        "lean_source_markers": lean_markers,
        "report_quantifier_and_boundary_markers": marker_results,
        "local_link_hygiene": "PASS",
    }


def main() -> None:
    pins = {}
    for relative, expected in PINS.items():
        path = ROOT / relative
        actual = digest(path)
        require(actual == expected, f"pin mismatch {relative}: {actual}")
        if path.suffix in {".lean", ".md", ".py", ".txt"}:
            hygienic_text(path)
        pins[relative] = actual
    hygienic_text(Path(__file__))

    print(json.dumps({
        "status": "PASS",
        "claim_label_for_finite_outputs": "experiment",
        "source_pins": pins,
        "replay": replay(),
        "utf8_c0_whitespace_hygiene": "PASS",
        "asserts_adjacent_matching_for_pi": False,
        "asserts_periodic_defect_lower_bound_for_pi": False,
        "asserts_fixed_sixteen_return": False,
        "asserts_v1": False,
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
