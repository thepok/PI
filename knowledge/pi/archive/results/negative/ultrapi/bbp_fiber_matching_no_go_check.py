#!/usr/bin/env python3
"""Exact replay for the BBP fibre-matching no-go.

Exact assertions cover rational identities, periodic Bernoulli approximants,
and source pins. Finite orbit diagnostics are ``experiment`` only. This
script asserts no asymptotic matching, fixed-sixteen return, or V1 result.
"""

from __future__ import annotations

from collections import Counter, deque
from fractions import Fraction
from hashlib import sha256
import json
from pathlib import Path
import subprocess
import tempfile


ROOT = Path(__file__).resolve().parents[2]
PINS = {
    "problems/local/pi-digits.txt":
        "2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825",
    "work/theory/pi-digits/library/t6/bbp-1997-nasa.pdf":
        "e4e0b97fde01328ec41da5f2cd4d6ffc8bcd2b7bd7516b9d8afc320f6d1916c4",
    "work/ultrapi-resume/bbp_adjacent_matching_breakthrough_report.md":
        "2b231d3c2e2ef717a2941a0452304ba402915318b72d305f6a6129ee8431f042",
    "work/ultrapi-resume/bbp_adjacent_matching_breakthrough_independent_audit.md":
        "32cf25b1b2d00a37de57b325134ba0a53e8f5f6c129b16d3f419000a1620af93",
    "work/theory/multiplicative-avoidance-gap/library/t1/"
    "S04_Blanchard_Host_Maass_1996.pdf":
        "c69b437a2c963d856f4f0026c1716434329b916f961a07da07d2421118d984fa",
    "work/theory/multiplicative-avoidance-gap/library/t1/"
    "S09_Badea_Grivaux_2303.01089v3.pdf":
        "6275f964abab16b16394523367709fa5b7c9ddec5b72ee29dbcc6292284430b1",
    "work/theory/pi-positive-decimal-factor-entropy/library/t32/"
    "T32_MEASURE_RIGIDITY_VIABILITY_AUDIT.md":
        "6c91794046a9ea8f51a75ad70d297d44f1607abbef4ac871e7920d766de4ffb6",
    "TheoryLib/PiPositiveDecimalFactorEntropy/"
    "T39T39ErgodicAffinityRigidity.lean":
        "f4982dacc90a436ca14e52d0529acbbfa8067d47e80679fb0173dff559d2ba09",
    ".lake/packages/mathlib/Mathlib/MeasureTheory/Measure/"
    "Decomposition/Lebesgue.lean":
        "3a76ea50d06939ad77c7815fc8ef376a0b5cb44cc40d59b90ee898fbdfb56b30",
    ".lake/packages/mathlib/Mathlib/Combinatorics/SimpleGraph/Hall.lean":
        "8fb655e948a848c420a75f7e404ea5e756942c871bc244c358b894e50a5d25e3",
}
EXACT_DEPTH = 320
TAIL_HORIZON = 96
BERNOULLI_DEPTHS = (4, 8, 12)
MATCHING_SIZES = (64, 128, 256)
MATCHING_RADII = (Fraction(1, 20), Fraction(1, 50), Fraction(1, 100))


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def digest(path: Path) -> str:
    return sha256(path.read_bytes()).hexdigest()


def c0_clean(path: Path) -> bool:
    return all(byte in (9, 10, 13) or byte >= 32 for byte in path.read_bytes())


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


def pdf_text(relative: str) -> str:
    with tempfile.TemporaryDirectory(prefix="bbp-fibre-") as tmp:
        target = Path(tmp) / "source.txt"
        subprocess.run(
            ["pdftotext", "-layout", str(ROOT / relative), str(target)],
            check=True,
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
        )
        return " ".join(target.read_text(errors="replace").split())


def source_markers() -> dict[str, bool]:
    bbp = pdf_text("work/theory/pi-digits/library/t6/bbp-1997-nasa.pdf")
    bhm = pdf_text(
        "work/theory/multiplicative-avoidance-gap/library/t1/"
        "S04_Blanchard_Host_Maass_1996.pdf"
    )
    bg = pdf_text(
        "work/theory/multiplicative-avoidance-gap/library/t1/"
        "S09_Badea_Grivaux_2303.01089v3.pdf"
    )
    checks = {
        "bbp_theorem_1": "Theorem 1." in bbp
        and "The following identity holds" in bbp,
        "bhm_theorem_3_3": "THÉORÈME 3.3" in bhm,
        "bhm_corollaire_3_4": "COROLLAIRE 3.4" in bhm,
        "bhm_corollaire_3_5": "COROLLAIRE 3.5" in bhm,
        "badea_grivaux_theorem_1_5":
            "Theorem 1.5 (large Fourier coefficients)" in bg,
    }
    require(all(checks.values()), f"source marker failure: {checks}")
    return checks


def actual_rows(depth: int) -> tuple[list[Fraction], list[Fraction]]:
    u = [fractional(coefficient(0))]
    v = [fractional(Fraction(1, 30) + coefficient(1))]
    power = Fraction(1)
    for n in range(1, depth + 2):
        power *= Fraction(5, 8)
        u.append(fractional(10 * u[-1] + coefficient(n) * power))
        if n <= depth:
            v.append(fractional(10 * v[-1] + coefficient(n + 1) * power))
    return u, v


def exact_row_checks() -> tuple[dict[str, object], list[Fraction], list[Fraction]]:
    u, v = actual_rows(EXACT_DEPTH)
    carry_histogram: Counter[int] = Counter()
    checks = 0
    for n in range(1, EXACT_DEPTH + 1):
        power = Fraction(5, 8) ** n
        displacement = coefficient(n + 1) * power
        epsilon = coefficient(n + 1) * power * Fraction(5, 8)
        require(v[n] == fractional(16 * u[n] + displacement), f"adjacent n={n}")
        require(u[n + 1] == fractional(10 * u[n] + epsilon), f"recurrence n={n}")
        require(fractional(5 * v[n]) == fractional(8 * u[n + 1]), f"fibre n={n}")
        r_n = 10 * u[n] + epsilon - u[n + 1]
        s_n = 16 * u[n] + displacement - v[n]
        label = 5 * v[n] - 8 * u[n + 1]
        require(r_n.denominator == s_n.denominator == label.denominator == 1,
                f"integral carries n={n}")
        require(label == 8 * r_n - 5 * s_n, f"carry refinement n={n}")
        carry_histogram[label.numerator] += 1
        checks += 5
    result = {
        "depth": EXACT_DEPTH,
        "exact_identity_checks": checks,
        "actual_row_carry_histogram_experiment": dict(sorted(carry_histogram.items())),
    }
    return result, u, v


def finite_tail_checks() -> dict[str, int]:
    tails = [
        sum(
            coefficient(k) * Fraction(10**n, 16**k)
            for k in range(n + 1, TAIL_HORIZON + 1)
        )
        for n in range(TAIL_HORIZON + 1)
    ]
    alpha = Fraction(101001000101, 10**12)
    u_phase = [
        fractional(fractional(10**n * alpha) - tails[n])
        for n in range(TAIL_HORIZON + 1)
    ]
    v_phase = [
        fractional(
            16 * u_phase[n]
            + coefficient(n + 1) * Fraction(5, 8) ** n
        )
        for n in range(TAIL_HORIZON)
    ]
    checks = 0
    for n in range(TAIL_HORIZON):
        epsilon = coefficient(n + 1) * Fraction(5, 8) ** (n + 1)
        require(tails[n + 1] == 10 * tails[n] - epsilon, f"tail n={n}")
        require(u_phase[n + 1] == fractional(10 * u_phase[n] + epsilon),
                f"phase original n={n}")
        require(fractional(5 * v_phase[n]) == fractional(8 * u_phase[n + 1]),
                f"phase fibre n={n}")
        checks += 3
        if n + 1 < TAIL_HORIZON:
            forcing = coefficient(n + 2) * Fraction(5, 8) ** (n + 1)
            require(v_phase[n + 1] == fractional(10 * v_phase[n] + forcing),
                    f"phase shifted n={n}")
            checks += 1
    return {"finite_tail_horizon": TAIL_HORIZON, "exact_checks": checks}


def periodic_binary_points(depth: int) -> list[Fraction]:
    denominator = 10**depth - 1
    points = []
    for mask in range(2**depth):
        numerator = 0
        for index in range(depth):
            digit = (mask >> (depth - 1 - index)) & 1
            numerator = 10 * numerator + digit
        points.append(Fraction(numerator, denominator))
    require(len(set(points)) == 2**depth, f"binary coding injective L={depth}")
    return points


def bernoulli_checks() -> dict[str, object]:
    output: dict[str, object] = {}
    left, right = Fraction(3, 5), Fraction(7, 9)
    for depth in BERNOULLI_DEPTHS:
        points = periodic_binary_points(depth)
        images = [fractional(16 * point) for point in points]
        size = len(points)
        require({fractional(10 * point) for point in points} == set(points),
                f"finite T10 invariance L={depth}")
        require(not any(left <= point <= right for point in points),
                f"mu interval L={depth}")
        image_count = sum(left <= point <= right for point in images)
        require(2 * image_count == size, f"nu interval half L={depth}")
        defects = {}
        for period in range(1, min(5, depth - 1) + 1):
            defect = sum(
                circle_norm((10**period - 1) * point) ** 2
                for point in points
            ) / size
            require(defect > 0, f"finite defect L={depth},P={period}")
            defects[str(period)] = float(defect)
        output[str(depth)] = {
            "point_count": size,
            "T10_invariance": "exact",
            "binary_coding_ambiguity": "none: only digits 0 and 1",
            "mu_mass_[3/5,7/9]": "0",
            "T16_pushforward_mass_[3/5,7/9]": "1/2",
            "periodic_defects_experiment": defects,
        }
    return output


def maximum_matching_size(adjacency: list[list[int]], right_size: int) -> int:
    left_size = len(adjacency)
    pair_left = [-1] * left_size
    pair_right = [-1] * right_size
    distance = [0] * left_size
    infinity = left_size + right_size + 1

    def breadth_first() -> bool:
        queue: deque[int] = deque()
        found = False
        for left in range(left_size):
            if pair_left[left] == -1:
                distance[left] = 0
                queue.append(left)
            else:
                distance[left] = infinity
        while queue:
            left = queue.popleft()
            for right in adjacency[left]:
                partner = pair_right[right]
                if partner == -1:
                    found = True
                elif distance[partner] == infinity:
                    distance[partner] = distance[left] + 1
                    queue.append(partner)
        return found

    def depth_first(left: int) -> bool:
        for right in adjacency[left]:
            partner = pair_right[right]
            if partner == -1 or (
                distance[partner] == distance[left] + 1 and depth_first(partner)
            ):
                pair_left[left] = right
                pair_right[right] = left
                return True
        distance[left] = infinity
        return False

    cardinality = 0
    while breadth_first():
        for left in range(left_size):
            if pair_left[left] == -1 and depth_first(left):
                cardinality += 1
    return cardinality


def matching_experiment(u: list[Fraction], v: list[Fraction]) -> dict[str, object]:
    output: dict[str, object] = {}
    for size in MATCHING_SIZES:
        row = {}
        for radius in MATCHING_RADII:
            adjacency = [
                [m for m, right in enumerate(u[1:size + 1])
                 if circle_norm(left - right) <= radius]
                for left in v[1:size + 1]
            ]
            matched = maximum_matching_size(adjacency, size)
            row[str(float(radius))] = {
                "maximum_injective_matches": matched,
                "matched_fraction": matched / size,
            }
        output[str(size)] = row
    return output


def replay() -> dict[str, object]:
    exact, u, v = exact_row_checks()
    return {
        "exact_actual_row": exact,
        "exact_finite_tail_phase_lift": finite_tail_checks(),
        "finite_periodic_bernoulli_approximants": bernoulli_checks(),
        "actual_row_matching_experiment": matching_experiment(u, v),
    }


def main() -> None:
    pins = {}
    for relative, expected in PINS.items():
        path = ROOT / relative
        actual = digest(path)
        require(actual == expected, f"pin mismatch {relative}: {actual}")
        if path.suffix in {".lean", ".md", ".py", ".txt"}:
            require(c0_clean(path), f"C0 control byte in {relative}")
        pins[relative] = actual

    report = ROOT / "work/ultrapi-resume/bbp_fiber_matching_no_go_20260813.md"
    require(c0_clean(report), "C0 control byte in primary report")
    require(c0_clean(Path(__file__)), "C0 control byte in primary checker")
    report_text = report.read_text()
    for marker in (
        "Proposition 2.1",
        "Proposition 2.2",
        "Same-forcing ergodic separator",
        "No bounded-congestion matching for the actual pi rows",
        "V1 remains a",
    ):
        require(marker in report_text, f"missing report marker: {marker}")

    print(json.dumps({
        "status": "PASS",
        "claim_label": "experiment",
        "source_pins": pins,
        "source_markers": source_markers(),
        "c0_hygiene": "PASS",
        "replay": replay(),
        "asserts_matching_for_actual_pi_rows": False,
        "asserts_fixed_sixteen_return": False,
        "asserts_v1": False,
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
