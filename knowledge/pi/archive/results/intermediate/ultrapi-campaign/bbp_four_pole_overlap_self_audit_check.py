#!/usr/bin/env python3
"""Adversarial exact replay for the BBP four-pole overlap self-audit.

This is a second implementation, not an import of the primary checker.  Its
randomized tests use a fixed seed and exact rational/group-ring arithmetic.
The output is an ``experiment``; it proves neither a Fourier limit nor V1.
"""

from __future__ import annotations

from collections import Counter, defaultdict
from fractions import Fraction
from hashlib import sha256
import json
from pathlib import Path
from random import Random


ROOT = Path(__file__).resolve().parents[2]
SEED = 0xBBF01610
RNG = Random(SEED)

PINS = {
    "problems/local/pi-digits.txt":
        "2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825",
    "work/ultrapi-resume/bbp_four_pole_overlap_attack.md":
        "9d9ff606cf0de438061e2a9245d0f0d3fc1cbfb784b1ca6be6aac76195a13545",
    "work/ultrapi-resume/bbp_four_pole_overlap_check.py":
        "418191b0e515a724c9bb51fb3c0853e27884fa0b155f68487831aa703168e750",
    "TheoryLib/PiQuantitativeBlockHitting/T25T25PowerTenFrequencyShift.lean":
        "8fcef4b46de5f2589390327e4f0c9dc929855920120eede74692621416cabf80",
}


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def digest(path: Path) -> str:
    return sha256(path.read_bytes()).hexdigest()


def fractional(value: Fraction) -> Fraction:
    return value - value.numerator // value.denominator


# Polynomials have ascending exact rational coefficients.
Polynomial = tuple[Fraction, ...]


def polynomial(values: list[int | Fraction] | tuple[int | Fraction, ...]) -> Polynomial:
    answer = [Fraction(value) for value in values]
    while len(answer) > 1 and answer[-1] == 0:
        answer.pop()
    return tuple(answer)


def poly_add(*terms: Polynomial) -> Polynomial:
    size = max(map(len, terms), default=1)
    answer = [Fraction(0) for _ in range(size)]
    for term in terms:
        for index, value in enumerate(term):
            answer[index] += value
    return polynomial(answer)


def poly_scale(scalar: int | Fraction, term: Polynomial) -> Polynomial:
    return polynomial([Fraction(scalar) * value for value in term])


def poly_multiply(*terms: Polynomial) -> Polynomial:
    answer = polynomial([1])
    for term in terms:
        product = [Fraction(0) for _ in range(len(answer) + len(term) - 1)]
        for left_index, left in enumerate(answer):
            for right_index, right in enumerate(term):
                product[left_index + right_index] += left * right
        answer = polynomial(product)
    return answer


def poly_shift_degree(term: Polynomial, amount: int) -> Polynomial:
    return polynomial([0] * amount + list(term))


# Independently cross-multiply the four poles in equation (2).
two_n_plus_one = polynomial([1, 2])
four_n_plus_three = polynomial([3, 4])
eight_n_plus_one = polynomial([1, 8])
eight_n_plus_five = polynomial([5, 8])
combined_denominator = poly_multiply(
    two_n_plus_one,
    four_n_plus_three,
    eight_n_plus_one,
    eight_n_plus_five,
)
combined_numerator = poly_add(
    poly_scale(4, poly_multiply(two_n_plus_one, four_n_plus_three, eight_n_plus_five)),
    poly_scale(Fraction(-1, 2), poly_multiply(four_n_plus_three, eight_n_plus_one, eight_n_plus_five)),
    poly_scale(-1, poly_multiply(two_n_plus_one, four_n_plus_three, eight_n_plus_one)),
    poly_scale(Fraction(-1, 2), poly_multiply(two_n_plus_one, eight_n_plus_one, eight_n_plus_five)),
)
require(combined_numerator == polynomial([47, 151, 120]), "equation (2) numerator")

# Independently expand equation (14): denominator - n^2 numerator.
majorant_numerator = poly_add(
    combined_denominator,
    poly_scale(-1, poly_shift_degree(combined_numerator, 2)),
)
require(
    majorant_numerator == polynomial([15, 194, 665, 873, 392]),
    "equation (14) numerator",
)

# Independently shift k=n-1 in Bailey--Crandall equation (3).
shifted_numerator = polynomial([16, -89, 120])
shifted_denominator = poly_multiply(
    polynomial([-1, 2]),
    polynomial([-1, 4]),
    polynomial([-7, 8]),
    polynomial([-3, 8]),
)
require(shifted_denominator == polynomial([21, -206, 712, -1024, 512]), "shifted denominator")


def coefficient(index: int) -> Fraction:
    require(index >= 0, "coefficient domain")
    return Fraction(
        120 * index * index + 151 * index + 47,
        (2 * index + 1) * (4 * index + 3) * (8 * index + 1) * (8 * index + 5),
    )


# Re-derive every constant in equations (4), (5), and (8).
geometric_ratio = Fraction(5, 8)
one_tail_geometric_factor = Fraction(1, 15)
summed_tail_majorant = one_tail_geometric_factor / (1 - geometric_ratio)
character_lipschitz_multiplier = 2 * (16 + 1)
erasure_constant_without_pi = character_lipschitz_multiplier * summed_tail_majorant
require(summed_tail_majorant == Fraction(8, 45), "equation (5) constant")
require(character_lipschitz_multiplier == 34, "two character Lipschitz constants")
require(erasure_constant_without_pi == Fraction(272, 45), "equation (8) constant")


def erasure_coefficient(frequency: int, length: int) -> Fraction:
    if length < 1:
        raise ValueError("D_N is defined only for N >= 1")
    return erasure_constant_without_pi * abs(frequency) / length


require(erasure_coefficient(0, 1) == 0, "q=0 boundary")
require(erasure_coefficient(0, 10**6) == 0, "q=0 boundary at large N")
require(erasure_coefficient(-37, 91) == erasure_coefficient(37, 91), "negative q symmetry")
try:
    erasure_coefficient(1, 0)
except ValueError:
    pass
else:
    raise AssertionError("N=0 must be outside the normalized-average domain")


# Build a second exact BBP state table.
MAX_INDEX = 192
partial_sums: list[Fraction] = []
partial = Fraction(0)
u_values: list[Fraction] = []
epsilon_values: list[Fraction | None] = [None]
for n in range(MAX_INDEX + 1):
    partial += coefficient(n) / 16**n
    partial_sums.append(partial)
    u_values.append(fractional(10**n * partial))
    if n >= 1:
        epsilon_values.append(coefficient(n) * Fraction(5, 8) ** n)

for n in range(1, MAX_INDEX + 1):
    require(coefficient(n) < Fraction(1, n * n), f"universal majorant sample n={n}")
for n in range(MAX_INDEX):
    epsilon = epsilon_values[n + 1]
    assert epsilon is not None
    require(u_values[n + 1] == fractional(10 * u_values[n] + epsilon), f"recurrence n={n}")


random_recurrence_checks = 0
random_finite_tail_checks = 0
random_fixed_lag_checks = 0
random_phase_checks = 0
for trial in range(800):
    n = RNG.randrange(MAX_INDEX)
    q = RNG.randrange(-10_000, 10_001)
    epsilon = epsilon_values[n + 1]
    assert epsilon is not None
    require(
        fractional(q * u_values[n + 1])
        == fractional(10 * q * u_values[n] + q * epsilon),
        f"random phase recurrence trial={trial}",
    )
    random_phase_checks += 1

    m = RNG.randrange(n + 1, MAX_INDEX + 1)
    finite_tail = 10**n * (partial_sums[m] - partial_sums[n])
    next_tail = 10 ** (n + 1) * (partial_sums[m] - partial_sums[n + 1])
    require(10 * finite_tail - next_tail == epsilon, f"random finite tail trial={trial}")
    require(
        fractional(u_values[n] + finite_tail) == fractional(10**n * partial_sums[m]),
        f"random finite surrogate trial={trial}",
    )
    require(
        finite_tail <= Fraction(5, 8) ** n / (15 * (n + 1) ** 2),
        f"random finite tail bound trial={trial}",
    )
    random_finite_tail_checks += 1
    random_recurrence_checks += 1

    h = RNG.randrange(1, min(12, MAX_INDEX - n) + 1)
    accumulated = sum(
        10 ** (h - j) * epsilon_values[n + j]
        for j in range(1, h + 1)
        if epsilon_values[n + j] is not None
    )
    require(
        u_values[n + h] == fractional(10**h * u_values[n] + accumulated),
        f"random fixed lag trial={trial}",
    )
    lag_majorant = (
        Fraction(5, 8) ** n
        / (n + 1) ** 2
        * sum(10 ** (h - j) * Fraction(5, 8) ** j for j in range(1, h + 1))
    )
    require(0 < accumulated <= lag_majorant, f"random fixed-lag bound trial={trial}")
    random_fixed_lag_checks += 1


# Replay equation (13) in the exact group ring of rational circle phases.
def add_atom(expression: Counter[Fraction], phase: Fraction, weight: int = 1) -> None:
    expression[fractional(phase)] += weight
    if expression[fractional(phase)] == 0:
        del expression[fractional(phase)]


exact_group_ring_telescope_checks = 0
for trial in range(400):
    length = RNG.randrange(0, 97)  # Includes the valid empty-sum identity N=0.
    frequency = RNG.randrange(-2_000, 2_001)  # Includes negative values; q=0 is forced below.
    if trial == 0:
        frequency = 0
    left: Counter[Fraction] = Counter()
    right: Counter[Fraction] = Counter()
    for n in range(length):
        add_atom(left, 10 * frequency * u_values[n], 1)
        add_atom(left, frequency * u_values[n], -1)
    add_atom(right, frequency * u_values[length], 1)
    add_atom(right, frequency * u_values[0], -1)
    for n in range(length):
        epsilon = epsilon_values[n + 1]
        assert epsilon is not None
        add_atom(right, -frequency * epsilon + frequency * u_values[n + 1], 1)
        add_atom(right, frequency * u_values[n + 1], -1)
    require(left == right, f"exact group-ring telescope trial={trial}")
    exact_group_ring_telescope_checks += 1


# Frequency-ray invariant for finite Fourier coboundaries.
def ten_ray_core(frequency: int) -> int:
    require(frequency != 0, "nonzero ray core")
    while frequency % 10 == 0:
        frequency //= 10
    return frequency


def clean_counter(counter: Counter[int]) -> Counter[int]:
    return Counter({key: value for key, value in counter.items() if value})


def coboundary(poly: Counter[int]) -> Counter[int]:
    answer: Counter[int] = Counter()
    for frequency, value in poly.items():
        answer[10 * frequency] += value
        answer[frequency] -= value
    return clean_counter(answer)


def ray_signature(poly: Counter[int]) -> Counter[int]:
    answer: Counter[int] = Counter()
    for frequency, value in poly.items():
        answer[0 if frequency == 0 else ten_ray_core(frequency)] += value
    return clean_counter(answer)


def target(frequency: int) -> Counter[int]:
    answer: Counter[int] = Counter()
    answer[16 * frequency] += 1
    answer[frequency] -= 1
    return clean_counter(answer)


require(target(0) == Counter(), "zero-frequency Fourier target")
random_ray_checks = 0
for trial in range(1_000):
    poly: Counter[int] = Counter()
    for _ in range(RNG.randrange(0, 40)):
        poly[RNG.randrange(-20_000, 20_001)] += RNG.randrange(-20, 21)
    poly = clean_counter(poly)
    require(ray_signature(coboundary(poly)) == Counter(), f"random ray cancellation trial={trial}")
    q = RNG.randrange(-100_000, 100_001)
    if q == 0:
        require(target(q) == Counter(), f"random q=0 trial={trial}")
    else:
        require(ten_ray_core(q) != ten_ray_core(16 * q), f"random ray separation trial={trial}")
        signature = ray_signature(target(q))
        require(len(signature) == 2 and set(signature.values()) == {-1, 1}, f"target signature trial={trial}")
    random_ray_checks += 1


# Fixed-point obstruction: it applies exactly when 3 does not divide q.
fixed_point = Fraction(1, 9)
require(fractional(10 * fixed_point) == fixed_point, "times-ten fixed point")
fixed_point_checks = 0
for q in range(-2_000, 2_001):
    vanishes = fractional(16 * q * fixed_point) == fractional(q * fixed_point)
    require(vanishes == (q % 3 == 0), f"fixed-point divisibility q={q}")
    fixed_point_checks += 1


# Positive-lag pair correlations never acquire a zero frequency for q != 0.
fixed_lag_frequency_checks = 0
for trial in range(1_000):
    q = RNG.choice([value for value in range(-1_000, 1_001) if value])
    h = RNG.randrange(1, 20)
    differences = (
        16 * q * 10**h - 16 * q,
        16 * q * 10**h - q,
        q * 10**h - 16 * q,
        q * 10**h - q,
    )
    require(all(value != 0 for value in differences), f"fixed-lag frequencies trial={trial}")
    fixed_lag_frequency_checks += 1


# Exact finite-state replay of the general Cesaro endpoint identity (24).
Measure = Counter[int]


def clean_measure(measure: Measure) -> Measure:
    return Counter({state: weight for state, weight in measure.items() if weight})


def push(measure: Measure, mapping: dict[int, int]) -> Measure:
    answer: Measure = Counter()
    for state, weight in measure.items():
        answer[mapping[state]] += weight
    return clean_measure(answer)


def cesaro_endpoint(measure: Measure, mapping: dict[int, int], length: int) -> tuple[Measure, Measure]:
    if length < 1:
        raise ValueError("slice Cesaro averages require M >= 1")
    average: Measure = Counter()
    current = measure
    for _ in range(length):
        for state, weight in current.items():
            average[state] += weight / length
        current = push(current, mapping)
    left = push(average, mapping)
    for state, weight in average.items():
        left[state] -= weight
    right: Measure = Counter()
    for state, weight in current.items():
        right[state] += weight / length
    for state, weight in measure.items():
        right[state] -= weight / length
    return clean_measure(left), clean_measure(right)


try:
    cesaro_endpoint(Counter({0: Fraction(1)}), {0: 0}, 0)
except ValueError:
    pass
else:
    raise AssertionError("M=0 must be outside the Cesaro-average domain")

random_cesaro_checks = 0
for trial in range(500):
    state_count = RNG.randrange(1, 15)
    image = list(range(state_count))
    RNG.shuffle(image)
    mapping = dict(enumerate(image))
    raw_weights = [RNG.randrange(1, 30) for _ in range(state_count)]
    total_weight = sum(raw_weights)
    measure = Counter({state: Fraction(weight, total_weight) for state, weight in enumerate(raw_weights)})
    length = RNG.randrange(1, 100)
    left, right = cesaro_endpoint(measure, mapping, length)
    require(left == right, f"random Cesaro endpoint trial={trial}")
    random_cesaro_checks += 1


cycle = {Fraction(1, 9): Fraction(7, 9), Fraction(7, 9): Fraction(4, 9), Fraction(4, 9): Fraction(1, 9)}
cycle_measure: Counter[Fraction] = Counter({Fraction(1, 9): Fraction(1)})
cycle_stationarity_checks = 0
for length in range(1, 61):
    left, right = cesaro_endpoint(cycle_measure, cycle, length)
    require(left == right, f"three-cycle endpoint M={length}")
    require((left == Counter()) == (length % 3 == 0), f"exact stationarity iff 3|M, M={length}")
    cycle_stationarity_checks += 1


# Exact safe exceptional-start bound for the sparse irrational example.
def sparse_bad_starts(length: int, window: int) -> int:
    powers: set[int] = set()
    power = 1
    while power <= length + window:
        powers.add(power)
        power *= 2
    return sum(
        any(position in powers for position in range(start + 1, start + window + 1))
        for start in range(length)
    )


random_sparse_bound_checks = 0
for trial in range(300):
    length = RNG.randrange(1, 5_001)
    window = RNG.randrange(1, 61)
    bad = sparse_bad_starts(length, window)
    safe_bound = window * (length + window).bit_length()
    require(bad <= safe_bound, f"sparse bound trial={trial}")
    random_sparse_bound_checks += 1


pins = {}
for relative, expected in PINS.items():
    actual = digest(ROOT / relative)
    require(actual == expected, f"pin mismatch: {relative}: {actual}")
    pins[relative] = actual


print(json.dumps({
    "status": "PASS",
    "claim_label": "experiment",
    "audited_report_label": "proof sketch",
    "asserts_overlap": False,
    "asserts_fourier_limit": False,
    "asserts_v1": False,
    "seed": SEED,
    "symbolic_equations_checked": [2, 5, 8, 14],
    "boundary_cases": {
        "q=0": "target and erasure bound are identically zero",
        "N=0": "normalized defects are undefined; telescope empty-sum identity remains valid",
        "M=0": "slice Cesaro average is undefined",
        "negative_q": "handled through abs(q) and exact phase/ray checks",
    },
    "scope": {
        "finite_fourier": "no trigonometric-polynomial stationary coboundary for q != 0",
        "stationary_continuous": "fixed-point obstruction proved for q not divisible by 3; q=1 suffices",
        "uniform_nonstationary": "only universal identities with uniform transfer/residual limits are excluded",
        "cesaro_only": "endpoint stationarity does not imply adjacent overlap",
    },
    "exact_check_counts": {
        "phase_recurrence": random_phase_checks,
        "finite_tail": random_finite_tail_checks,
        "fixed_lag": random_fixed_lag_checks,
        "group_ring_telescope": exact_group_ring_telescope_checks,
        "frequency_ray": random_ray_checks,
        "fixed_point": fixed_point_checks,
        "fixed_lag_frequency": fixed_lag_frequency_checks,
        "cesaro_endpoint": random_cesaro_checks,
        "cycle_stationarity": cycle_stationarity_checks,
        "sparse_bound": random_sparse_bound_checks,
    },
    "source_pins": pins,
    "warning": "PASS validates the named derivations and scopes, not T70 overlap or V1",
}, indent=2, sort_keys=True))
