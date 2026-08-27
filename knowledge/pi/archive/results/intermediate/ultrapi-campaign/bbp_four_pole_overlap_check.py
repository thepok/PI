#!/usr/bin/env python3
"""Exact replay and finite diagnostics for the BBP Fourier-overlap audit.

All finite orbit output is an ``experiment``.  The exact assertions verify
the four-pole recurrence, finite-tail conjugacy, frequency-ray obstruction,
and Cesaro endpoint identities.  They do not prove overlap of an empirical
limit with its times-sixteen pushforward, a Fourier limit, or V1.
"""

from __future__ import annotations

from cmath import exp
from collections import Counter, defaultdict
from fractions import Fraction
from hashlib import sha256
import json
from math import log2, pi
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]

PINS = {
    "problems/local/pi-digits.txt":
        "2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825",
    "work/ultrapi-resume/bbp_empirical_rigidity_attack.md":
        "80fc0a6f9bd159dc36438a78ec10b35c76b433c2bae084750b3c34199d97534c",
    "work/ultrapi-resume/bbp_empirical_rigidity_check.py":
        "0b943566c03dc083be1321499b66e6f6cf1766ad7f11d87b657ebf52f6572953",
    "work/ultrapi-resume/fixed_return_dynamics_attack.md":
        "147969553dbb57d9678b9351953d2142f3d4984af4ff5ffa752362a6dd7839e7",
    "work/ultrapi-resume/fixed_return_dynamics_independent_audit.md":
        "9cf83b4db60886d0d4488d0e93ff31c410748681309fc95e677778d5a81c7d32",
    "work/theory/pi-digits/library/t6/bbp-1997-nasa.pdf":
        "e4e0b97fde01328ec41da5f2cd4d6ffc8bcd2b7bd7516b9d8afc320f6d1916c4",
    "work/theory/pi-lacunary-near-return-sparsity/library/t63/"
    "lagarias-math0101055v2.pdf":
        "a2a1171eb9c75c9fa3495ca3c3ceaa33c1d20b722bb56f82adb56d8c308209b9",
    "work/theory/pi-lacunary-near-return-sparsity/library/t63/"
    "bailey-crandall-2001-bcrandom.pdf":
        "701067697e8c1dace60cd8695ef509edae31f9da3bffd64b548624ccc2e4cfa8",
    "TheoryLib/PiQuantitativeBlockHitting/T25T25PowerTenFrequencyShift.lean":
        "8fcef4b46de5f2589390327e4f0c9dc929855920120eede74692621416cabf80",
}


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
    require(split == combined > 0, f"four-pole coefficient at {index}")
    return combined


def fractional(value: Fraction) -> Fraction:
    return value - value.numerator // value.denominator


def character(frequency: int, point: Fraction) -> complex:
    return exp(2j * pi * frequency * float(point))


def ten_ray_core(frequency: int) -> int:
    require(frequency != 0, "zero has no nonzero frequency ray")
    while frequency % 10 == 0:
        frequency //= 10
    return frequency


def clean_polynomial(poly: dict[int, int]) -> dict[int, int]:
    return {frequency: coefficient for frequency, coefficient in poly.items() if coefficient}


def ten_coboundary(poly: dict[int, int]) -> dict[int, int]:
    """Fourier coefficients of psi(10x)-psi(x)."""

    answer: defaultdict[int, int] = defaultdict(int)
    for frequency, value in poly.items():
        answer[10 * frequency] += value
        answer[frequency] -= value
    return clean_polynomial(dict(answer))


def ray_signature(poly: dict[int, int]) -> dict[int, int]:
    """Sum coefficients on each equivalence class m ~ 10^j m."""

    answer: defaultdict[int, int] = defaultdict(int)
    for frequency, value in poly.items():
        if frequency == 0:
            answer[0] += value
        else:
            answer[ten_ray_core(frequency)] += value
    return clean_polynomial(dict(answer))


def target_polynomial(frequency: int) -> dict[int, int]:
    """Fourier coefficients of e(16 q x)-e(q x), including q=0."""

    answer: defaultdict[int, int] = defaultdict(int)
    answer[16 * frequency] += 1
    answer[frequency] -= 1
    return clean_polynomial(dict(answer))


MAX_DEPTH = 1_200
SURROGATE_DEPTH = 180
CHECKPOINTS = (50, 100, 200, 400, 800, 1_200)
FREQUENCIES = tuple(range(1, 9))


# Reconstruct the exact diagonal BBP state from the actual four-pole forcing.
u_values = [fractional(coefficient(0))]
epsilon_values: list[Fraction | None] = [None]
five_eighths_power = Fraction(1)
hypergeometric_ratio_checks = 0
bailey_crandall_coefficient_checks = 0
for n in range(1, MAX_DEPTH + 1):
    bailey_crandall_coefficient = Fraction(
        120 * n * n - 89 * n + 16,
        512 * n**4 - 1_024 * n**3 + 712 * n * n - 206 * n + 21,
    )
    require(
        bailey_crandall_coefficient == coefficient(n - 1),
        f"Bailey-Crandall equation (3) at n={n}",
    )
    bailey_crandall_coefficient_checks += 1
    five_eighths_power *= Fraction(5, 8)
    epsilon = coefficient(n) * five_eighths_power
    epsilon_values.append(epsilon)
    u_values.append(fractional(10 * u_values[-1] + epsilon))
    if n < MAX_DEPTH:
        next_ratio = Fraction(
            5
            * (2 * n + 1)
            * (4 * n + 3)
            * (8 * n + 1)
            * (8 * n + 5)
            * (120 * n * n + 391 * n + 318),
            8
            * (2 * n + 3)
            * (4 * n + 7)
            * (8 * n + 9)
            * (8 * n + 13)
            * (120 * n * n + 151 * n + 47),
        )
        require(
            coefficient(n + 1) * Fraction(5, 8) ** (n + 1) / epsilon
            == next_ratio,
            f"hypergeometric forcing ratio at n={n}",
        )
        hypergeometric_ratio_checks += 1


# Independently construct B_n and check u_n={10^n B_n}.  A finite deeper
# partial sum B_M supplies a wholly rational surrogate for pi and exactly
# replays the moving-tail coboundary without using a decimal expansion of pi.
partial_sums: list[Fraction] = []
partial = Fraction()
for n in range(SURROGATE_DEPTH + 1):
    partial += coefficient(n) / 16**n
    partial_sums.append(partial)
    require(
        u_values[n] == fractional(10**n * partial),
        f"direct diagonal state at n={n}",
    )

finite_tail_coboundary_checks = 0
surrogate = partial_sums[SURROGATE_DEPTH]
for n in range(SURROGATE_DEPTH):
    finite_tail = 10**n * (surrogate - partial_sums[n])
    next_finite_tail = 10 ** (n + 1) * (surrogate - partial_sums[n + 1])
    require(finite_tail >= 0, f"positive finite tail at n={n}")
    require(
        fractional(u_values[n] + finite_tail)
        == fractional(10**n * surrogate),
        f"finite coefficient erasure at n={n}",
    )
    require(
        10 * finite_tail - next_finite_tail == epsilon_values[n + 1],
        f"finite tail coboundary at n={n}",
    )
    require(
        finite_tail
        <= Fraction(5, 8) ** n / (15 * (n + 1) ** 2),
        f"finite tail majorant at n={n}",
    )
    finite_tail_coboundary_checks += 1


# The elementary coefficient majorant and its universal tail-sum constant.
for n in range(1, MAX_DEPTH + 1):
    require(coefficient(n) < Fraction(1, n * n), f"a(n)<1/n^2 at n={n}")
tail_bound_sum = sum(
    (Fraction(5, 8) ** n) / (15 * (n + 1) ** 2)
    for n in range(MAX_DEPTH + 1)
)
require(tail_bound_sum < Fraction(8, 45), "sum t_n < 8/45")


# Exact phase-argument recurrence.  The multiplier changes m only to 10m;
# the scalar phase e(m epsilon_n) does not mix ten-frequency rays.
phase_argument_checks = 0
for n in range(MAX_DEPTH):
    epsilon = epsilon_values[n + 1]
    assert epsilon is not None
    for frequency in FREQUENCIES:
        require(
            fractional(frequency * u_values[n + 1])
            == fractional(10 * frequency * u_values[n] + frequency * epsilon),
            f"Fourier transfer at n={n}, q={frequency}",
        )
        phase_argument_checks += 1


# Every finite trigonometric coboundary has zero total coefficient on each
# ten-frequency ray.  The target e(16qx)-e(qx) has two nonzero signatures on
# distinct rays for every q != 0.
trial_polynomial = {-37: 2, -10: -3, -1: 5, 2: 7, 20: -11, 300: 13}
require(ray_signature(ten_coboundary(trial_polynomial)) == {}, "ray cancellation")
require(target_polynomial(0) == {}, "q=0 target is identically zero")
for q in range(-128, 129):
    if q == 0:
        continue
    require(ten_ray_core(q) != ten_ray_core(16 * q), f"ray separation q={q}")
    target = target_polynomial(q)
    signature = ray_signature(target)
    require(signature != {}, f"target signature q={q}")


# For 3 not dividing q, x=1/9 is a fixed point of times ten on which the
# proposed continuous stationary coboundary has a nonzero periodic sum.
fixed_point = Fraction(1, 9)
require(fractional(10 * fixed_point) == fixed_point, "times-ten fixed point")
for q in range(-128, 129):
    if q and q % 3:
        require(
            fractional(16 * q * fixed_point) != fractional(q * fixed_point),
            f"fixed-point obstruction q={q}",
        )


# Exact numerical replay of the frequency recurrence and bounded power-ten
# telescope.  The times-sixteen values are diagnostics only: no convergence
# assertion is made or inferred from them.
target_sums = {q: 0j for q in FREQUENCIES}
times_ten_sums = {q: 0j for q in FREQUENCIES}
diagnostics: dict[str, dict[str, dict[str, float]]] = {}
for n in range(MAX_DEPTH):
    point = u_values[n]
    for q in FREQUENCIES:
        target_sums[q] += character(16 * q, point) - character(q, point)
        times_ten_sums[q] += character(10 * q, point) - character(q, point)
    if n + 1 in CHECKPOINTS:
        diagnostics[str(n + 1)] = {
            "times_sixteen_normalized_magnitude": {
                str(q): abs(target_sums[q]) / (n + 1) for q in FREQUENCIES
            },
            "times_ten_normalized_magnitude": {
                str(q): abs(times_ten_sums[q]) / (n + 1) for q in FREQUENCIES
            },
        }

for q in FREQUENCIES:
    endpoint_and_error = character(q, u_values[MAX_DEPTH]) - character(q, u_values[0])
    for n in range(MAX_DEPTH):
        epsilon = epsilon_values[n + 1]
        assert epsilon is not None
        endpoint_and_error += (
            character(-q, epsilon) - 1
        ) * character(q, u_values[n + 1])
    require(
        abs(times_ten_sums[q] - endpoint_and_error) < 2e-10,
        f"complex power-ten telescope at q={q}",
    )
    forcing_sum = sum(value for value in epsilon_values[1:] if value is not None)
    require(
        abs(times_ten_sums[q]) <= 2 + 2 * pi * q * float(forcing_sum) + 1e-10,
        f"bounded power-ten sum at q={q}",
    )


# Cesaro averaging of pushed measures has an endpoint identity but does not
# force adjacent overlap.  The three distinct times-ten fixed Dirac masses
# below form a times-sixteen cycle and are pairwise singular.
dirac_cycle = [Fraction(1, 9)]
for _ in range(2):
    dirac_cycle.append(fractional(16 * dirac_cycle[-1]))
require(dirac_cycle == [Fraction(1, 9), Fraction(7, 9), Fraction(4, 9)], "Dirac cycle")
require(fractional(16 * dirac_cycle[-1]) == dirac_cycle[0], "Dirac cycle closes")
require(len(set(dirac_cycle)) == 3, "Dirac masses are distinct")
for point in dirac_cycle:
    require(fractional(10 * point) == point, "each Dirac mass is times-ten invariant")

slice_cesaro_endpoint_checks = 0
for length in (1, 2, 3, 10, 101, 1_000):
    before = Counter(dirac_cycle[index % 3] for index in range(length))
    after = Counter(dirac_cycle[(index + 1) % 3] for index in range(length))
    l1_distance = sum(
        abs(Fraction(after[point] - before[point], length))
        for point in set(before) | set(after)
    )
    require(l1_distance <= Fraction(2, length), f"slice Cesaro endpoint at M={length}")
    slice_cesaro_endpoint_checks += 1


# Sparse nonperiodic decimal digits (zeros at powers of two, ones elsewhere)
# give an irrational orbit whose empirical measures converge to delta_(1/9).
# The checker verifies the exact density estimate behind that proof.
sparse_bad_start_diagnostics = {}
window = 12
for length in (100, 1_000, 10_000, 100_000):
    powers = {1 << exponent for exponent in range(int(log2(length + window)) + 1)}
    bad = sum(
        any(position in powers for position in range(start + 1, start + window + 1))
        for start in range(length)
    )
    upper = window * (int(log2(length + window)) + 1)
    require(bad <= upper, f"sparse exceptional starts at N={length}")
    sparse_bad_start_diagnostics[str(length)] = {
        "bad_starts": bad,
        "upper_bound": upper,
        "proportion": bad / length,
    }


pins = {}
for relative, expected in PINS.items():
    actual = digest(ROOT / relative)
    require(actual == expected, f"pin mismatch: {relative}: {actual}")
    pins[relative] = actual


print(json.dumps({
    "status": "PASS",
    "claim_label": "experiment",
    "asserts_overlap": False,
    "asserts_fourier_limit": False,
    "asserts_v1": False,
    "max_exact_depth": MAX_DEPTH,
    "bailey_crandall_coefficient_checks": bailey_crandall_coefficient_checks,
    "hypergeometric_ratio_checks": hypergeometric_ratio_checks,
    "finite_tail_coboundary_checks": finite_tail_coboundary_checks,
    "phase_argument_checks": phase_argument_checks,
    "ten_ray_obstruction": "q and 16q lie on distinct times-ten rays for every nonzero q",
    "continuous_coboundary_obstruction": "x=1/9 for q not divisible by 3",
    "coefficient_erasure_bound": "272*pi*abs(q)/(45*N)",
    "average_domain": "N is a positive integer; N=0 is undefined",
    "zero_frequency_boundary": "q=0 gives the identically zero target",
    "slice_cesaro_endpoint_checks": slice_cesaro_endpoint_checks,
    "sparse_bad_start_diagnostics": sparse_bad_start_diagnostics,
    "finite_fourier_diagnostics": diagnostics,
    "source_and_input_pins": pins,
    "warning": "finite Fourier magnitudes are not evidence for a limit",
}, indent=2, sort_keys=True))
