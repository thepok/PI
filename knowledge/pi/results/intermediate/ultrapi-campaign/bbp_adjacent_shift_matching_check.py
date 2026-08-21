#!/usr/bin/env python3
"""Exact replay for the BBP adjacent-shift matching report.

All orbit diagnostics have claim status ``experiment``. Exact assertions
check the actual four-pole coefficient, the endpoint-corrected adjacent
coefficient shift, its two recurrences, finite tail bounds, and the sparse
atomic separator. They do not establish an asymptotic matching, collision
anti-concentration, a fixed return, or V1.
"""

from __future__ import annotations

from fractions import Fraction
from hashlib import sha256
import json
from math import floor, log2
from pathlib import Path
import subprocess
import tempfile


ROOT = Path(__file__).resolve().parents[2]

PINS = {
    "problems/local/pi-digits.txt":
        "2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825",
    "work/theory/pi-digits/library/t6/bbp-1997-nasa.pdf":
        "e4e0b97fde01328ec41da5f2cd4d6ffc8bcd2b7bd7516b9d8afc320f6d1916c4",
    "work/theory/pi-lacunary-near-return-sparsity/library/t63/"
    "lagarias-math0101055v2.pdf":
        "a2a1171eb9c75c9fa3495ca3c3ceaa33c1d20b722bb56f82adb56d8c308209b9",
    "work/theory/pi-digits/library/t44/furstenberg-1967-disjointness.pdf":
        "cd07faa4521080272cf2c303ee4e3a41ee6a3ba9e6aea114604becaca0ba9358",
    "TheoryLib/PiQuantitativeBlockHitting/T69T69FixedSixteenReturn.lean":
        "fb7eb54d99bb904c28da0f49d33f8a40979ffcbf22a4024fcae73de7149886f9",
    "TheoryLib/PiQuantitativeBlockHitting/T70T70EmpiricalRigidityBridge.lean":
        "f8ecbfd2d9f8a13216e75d5ebb3732b98f7844147776b30de7f2666fc7ddec55",
    "work/ultrapi-resume/bbp_empirical_rigidity_attack.md":
        "80fc0a6f9bd159dc36438a78ec10b35c76b433c2bae084750b3c34199d97534c",
    "work/ultrapi-resume/bbp_four_pole_overlap_attack.md":
        "9d9ff606cf0de438061e2a9245d0f0d3fc1cbfb784b1ca6be6aac76195a13545",
}

MAX_DEPTH = 320
DIRECT_DEPTH = 140
CHECKPOINTS = (40, 80, 160, 320)
RADII = (0.1, 0.03, 0.01)


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def digest(path: Path) -> str:
    return sha256(path.read_bytes()).hexdigest()


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
    require(split == combined > 0, f"coefficient identity at k={index}")
    return combined


def coefficient_difference(index: int) -> Fraction:
    polynomial = (
        40960 * index**5
        + 220672 * index**4
        + 453632 * index**3
        + 443480 * index**2
        + 206712 * index
        + 36903
    )
    denominator = (
        (2 * index + 1)
        * (2 * index + 3)
        * (4 * index + 3)
        * (4 * index + 7)
        * (8 * index + 1)
        * (8 * index + 5)
        * (8 * index + 9)
        * (8 * index + 13)
    )
    return Fraction(-3 * polynomial, denominator)


def fractional(value: Fraction) -> Fraction:
    return value - value.numerator // value.denominator


def circle_distance_exact(left: Fraction, right: Fraction) -> Fraction:
    difference = fractional(left - right)
    return min(difference, 1 - difference)


def circle_distance_float(left: float, right: float) -> float:
    difference = abs(left - right) % 1.0
    return min(difference, 1.0 - difference)


def pdf_text(relative: str) -> str:
    with tempfile.TemporaryDirectory(prefix="bbp-adjacent-") as tmp:
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
    lagarias = pdf_text(
        "work/theory/pi-lacunary-near-return-sparsity/library/t63/"
        "lagarias-math0101055v2.pdf"
    )
    furstenberg = pdf_text(
        "work/theory/pi-digits/library/t44/furstenberg-1967-disjointness.pdf"
    )
    checks = {
        "bbp_theorem_1": "Theorem 1." in bbp
        and "The following identity holds" in bbp,
        "lagarias_theorem_3_1": "Theorem 3.1" in lagarias
        and "same sets of limit points" in lagarias,
        "lagarias_theorem_3_3": "Theorem 3.3" in lagarias
        and "asymptotically approaches" in lagarias,
        "furstenberg_theorem_iv_1": "T H E O R E M IV. 1" in furstenberg,
    }
    require(all(checks.values()), f"source marker failure: {checks}")
    return checks


def cyclic_order_bottleneck(
    left: list[Fraction], right: list[Fraction]
) -> dict[str, float | int]:
    """Minimum over cyclic shifts of the sorted order-preserving bijection."""

    a = sorted(float(value) for value in left)
    b = sorted(float(value) for value in right)
    require(len(a) == len(b) > 0, "equal nonempty matching rows")
    size = len(a)
    best_max = 1.0
    best_mean = 1.0
    best_shift = -1
    for shift in range(size):
        distances = [
            circle_distance_float(a[index], b[(index + shift) % size])
            for index in range(size)
        ]
        candidate = max(distances)
        if candidate < best_max:
            best_max = candidate
            best_mean = sum(distances) / size
            best_shift = shift
    return {
        "cyclic_shift": best_shift,
        "bottleneck": best_max,
        "mean_distance": best_mean,
        "congestion": 1,
    }


def collision_energy(states: list[Fraction], radius: float) -> float:
    values = [float(value) for value in states]
    count = sum(
        circle_distance_float(left, right) < radius
        for left in values
        for right in values
    )
    return count / (len(values) ** 2)


def sparse_bad_starts(sample_size: int, window: int) -> tuple[int, int]:
    powers = []
    value = 2
    while value <= sample_size + window:
        powers.append(value)
        value *= 2
    bad = 0
    for start in range(sample_size):
        if any(start < position <= start + window for position in powers):
            bad += 1
    bound = window * (1 + floor(log2(sample_size + window)))
    require(bad <= bound, f"sparse bound N={sample_size}, L={window}")
    return bad, bound


def replay() -> dict[str, object]:
    require(coefficient(0) == Fraction(47, 15), "a(0)=47/15")
    require(
        16 * coefficient(0) - Fraction(1, 30) == Fraction(501, 10),
        "endpoint correction 501/10",
    )

    u_values = [fractional(coefficient(0))]
    v_values = [fractional(Fraction(1, 30) + coefficient(1))]
    power = Fraction(1)
    recurrence_checks = 0
    adjacent_checks = 0
    difference_checks = 0
    coefficient_bounds = 0
    coupling_sum = Fraction()
    shifted_tail_bound_sum = Fraction()

    for n in range(1, MAX_DEPTH + 1):
        power *= Fraction(5, 8)
        epsilon = coefficient(n) * power
        shifted_epsilon = coefficient(n + 1) * power
        u_values.append(fractional(10 * u_values[-1] + epsilon))
        v_values.append(fractional(10 * v_values[-1] + shifted_epsilon))
        recurrence_checks += 2

        displacement = coefficient(n + 1) * power
        require(
            v_values[n] == fractional(16 * u_values[n] + displacement),
            f"adjacent shift at n={n}",
        )
        require(
            circle_distance_exact(v_values[n], fractional(16 * u_values[n]))
            <= displacement,
            f"circle coupling at n={n}",
        )
        coupling_sum += displacement
        shifted_tail_bound_sum += power / (15 * (n + 2) ** 2)
        adjacent_checks += 2

        require(coefficient(n) < Fraction(1, n * n), f"a(n)<1/n^2 at {n}")
        coefficient_bounds += 1

    for k in range(MAX_DEPTH + 1):
        require(
            coefficient(k + 1) - coefficient(k) == coefficient_difference(k),
            f"coefficient difference at k={k}",
        )
        require(coefficient_difference(k) < 0, f"strict decrease at k={k}")
        difference_checks += 2

    require(coupling_sum < Fraction(5, 3), "universal adjacent coupling sum")
    require(
        shifted_tail_bound_sum < Fraction(1, 9),
        "universal shifted-tail empirical sum",
    )

    partials = []
    partial = Fraction()
    for k in range(DIRECT_DEPTH + 2):
        partial += coefficient(k) / 16**k
        partials.append(partial)

    direct_checks = 0
    shifted_partial = Fraction(1, 30)
    for n in range(DIRECT_DEPTH + 1):
        shifted_partial += coefficient(n + 1) / 16**n
        require(
            shifted_partial
            == Fraction(1, 30) + 16 * (partials[n + 1] - coefficient(0)),
            f"partial adjacent identity at n={n}",
        )
        require(
            u_values[n] == fractional(10**n * partials[n]),
            f"direct original state at n={n}",
        )
        require(
            v_values[n] == fractional(10**n * shifted_partial),
            f"direct shifted state at n={n}",
        )
        direct_checks += 3

        if n < DIRECT_DEPTH:
            finite_shifted_tail = Fraction()
            for k in range(n + 1, DIRECT_DEPTH + 1):
                finite_shifted_tail += coefficient(k + 1) / 16**k
            finite_shifted_tail *= 10**n
            require(finite_shifted_tail > 0, f"positive shifted tail n={n}")
            require(
                finite_shifted_tail
                <= Fraction(5, 8) ** n / (15 * (n + 2) ** 2),
                f"shifted-tail bound n={n}",
            )
            direct_checks += 2

    sparse_checks = {}
    for sample_size in (100, 1_000, 10_000):
        for window in (3, 10, 30):
            bad, bound = sparse_bad_starts(sample_size, window)
            sparse_checks[f"N={sample_size},L={window}"] = {
                "bad_starts": bad,
                "stated_bound": bound,
            }

    diagnostics = {}
    for size in CHECKPOINTS:
        original = u_values[1:size + 1]
        shifted = v_values[1:size + 1]
        diagnostics[str(size)] = {
            "cyclic_order_matching": cyclic_order_bottleneck(original, shifted),
            "close_pair_energy": {
                str(radius): collision_energy(original, radius)
                for radius in RADII
            },
        }

    return {
        "max_depth": MAX_DEPTH,
        "recurrence_checks": recurrence_checks,
        "adjacent_checks": adjacent_checks,
        "coefficient_difference_checks": difference_checks,
        "coefficient_bound_checks": coefficient_bounds,
        "direct_partial_and_tail_checks": direct_checks,
        "finite_coupling_sum_decimal": float(coupling_sum),
        "universal_coupling_sum_bound": "5/3",
        "finite_shifted_tail_bound_sum_decimal": float(shifted_tail_bound_sum),
        "universal_shifted_tail_sum_bound": "1/9",
        "sparse_separator_checks": sparse_checks,
        "finite_matching_and_collision_diagnostics": diagnostics,
        "warning": "finite matching and collision data are experiment only",
    }


def main() -> None:
    pins = {}
    for relative, expected in PINS.items():
        actual = digest(ROOT / relative)
        require(actual == expected, f"pin mismatch {relative}: {actual}")
        pins[relative] = actual

    output = {
        "status": "PASS",
        "claim_label": "experiment",
        "source_pins": pins,
        "source_markers": source_markers(),
        "replay": replay(),
        "asserts_asymptotic_matching": False,
        "asserts_collision_anti_concentration": False,
        "asserts_fixed_return": False,
        "asserts_v1": False,
    }
    print(json.dumps(output, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
