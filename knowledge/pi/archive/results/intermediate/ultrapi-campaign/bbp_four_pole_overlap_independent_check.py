#!/usr/bin/env python3
"""Independent exact audit of the BBP four-pole overlap obstruction.

This file does not import either earlier checker.  Its exact and bounded
calculations audit the identities and scopes in the accompanying report;
they do not prove a Fourier limit, overlap of measures, or V1.
"""

from __future__ import annotations

from collections import Counter
from fractions import Fraction
from hashlib import sha256
import json
from pathlib import Path
from random import Random


ROOT = Path(__file__).resolve().parents[2]
RNG = Random(0x1A2B3C4D)

PINS = {
    "problems/local/pi-digits.txt":
        "2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825",
    "work/ultrapi-resume/bbp_four_pole_overlap_attack.md":
        "9d9ff606cf0de438061e2a9245d0f0d3fc1cbfb784b1ca6be6aac76195a13545",
    "work/ultrapi-resume/bbp_four_pole_overlap_check.py":
        "418191b0e515a724c9bb51fb3c0853e27884fa0b155f68487831aa703168e750",
    "work/ultrapi-resume/bbp_four_pole_overlap_self_audit.md":
        "e38fb9568e1665082dd15575f2359e6dab5c680527944fa37c5d60d15e81a5cb",
    "work/ultrapi-resume/bbp_four_pole_overlap_self_audit_check.py":
        "9b2dde3acb182cd5e31282aa3673ea45a7e09c6028a7fe3e2a4a21924479ab9c",
}


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def digest(relative: str) -> str:
    return sha256((ROOT / relative).read_bytes()).hexdigest()


def frac(value: Fraction) -> Fraction:
    return value - value.numerator // value.denominator


# Ascending coefficient order.  This symbolic implementation is independent
# of the polynomial helpers in the self-audit checker.
def mul(left: tuple[int, ...], right: tuple[int, ...]) -> tuple[int, ...]:
    result = [0] * (len(left) + len(right) - 1)
    for i, a in enumerate(left):
        for j, b in enumerate(right):
            result[i + j] += a * b
    return tuple(result)


def add(left: tuple[int, ...], right: tuple[int, ...]) -> tuple[int, ...]:
    result = [0] * max(len(left), len(right))
    for i, value in enumerate(left):
        result[i] += value
    for i, value in enumerate(right):
        result[i] += value
    while len(result) > 1 and result[-1] == 0:
        result.pop()
    return tuple(result)


def scale(value: int, poly: tuple[int, ...]) -> tuple[int, ...]:
    return tuple(value * coefficient for coefficient in poly)


factors = ((1, 2), (3, 4), (1, 8), (5, 8))
denominator_poly = (1,)
for factor in factors:
    denominator_poly = mul(denominator_poly, factor)
require(denominator_poly == (15, 194, 712, 1024, 512), "combined denominator")

# Cross-multiplication of 4/(8k+1)-2/(8k+4)-1/(8k+5)-1/(8k+6),
# after reducing 2/(8k+4) and 1/(8k+6).
twice_numerator_poly = (0,)
weighted_omissions = (
    (8, 2),       # twice 4/(8k+1)
    (-1, 0),      # twice -1/[2(2k+1)]
    (-2, 3),      # twice -1/(8k+5)
    (-1, 1),      # twice -1/[2(4k+3)]
)
for weight, omitted in weighted_omissions:
    product = (1,)
    for index, factor in enumerate(factors):
        if index != omitted:
            product = mul(product, factor)
    twice_numerator_poly = add(twice_numerator_poly, scale(weight, product))
require(twice_numerator_poly == (94, 302, 240), "twice four-pole numerator")
numerator_poly = tuple(value // 2 for value in twice_numerator_poly)
require(numerator_poly == (47, 151, 120), "four-pole numerator")

# D(k)-k^2 A(k) is the positive numerator in 1/k^2-a(k).
majorant_poly = add(denominator_poly, scale(-1, (0, 0) + numerator_poly))
require(majorant_poly == (15, 194, 665, 873, 392), "majorant numerator")


def a(index: int) -> Fraction:
    require(index >= 0, "coefficient index")
    split = (
        Fraction(4, 8 * index + 1)
        - Fraction(2, 8 * index + 4)
        - Fraction(1, 8 * index + 5)
        - Fraction(1, 8 * index + 6)
    )
    combined = Fraction(
        120 * index * index + 151 * index + 47,
        (2 * index + 1) * (4 * index + 3) * (8 * index + 1) * (8 * index + 5),
    )
    require(split == combined and combined > 0, f"coefficient index {index}")
    return combined


for k in range(513):
    value = a(k)
    if k:
        require(value < Fraction(1, k * k), f"a(k)<1/k^2 at {k}")


# Re-derive the entire constant in the erasure estimate over Q.  The factor
# pi is the usual character Lipschitz factor and is intentionally not
# approximated here.
tail_prefactor = Fraction(1, 15)
tail_ratio = Fraction(5, 8)
summed_tail_majorant = tail_prefactor / (1 - tail_ratio)
two_character_multiplier = 2 * (16 + 1)
erasure_multiplier_without_pi = two_character_multiplier * summed_tail_majorant
require(summed_tail_majorant == Fraction(8, 45), "summed tail constant")
require(two_character_multiplier == 34, "two Lipschitz contributions")
require(erasure_multiplier_without_pi == Fraction(272, 45), "erasure constant")


def normalized_erasure_coefficient(q: int, length: int) -> Fraction:
    if length < 1:
        raise ValueError("a normalized average requires N >= 1")
    return erasure_multiplier_without_pi * abs(q) / length


require(normalized_erasure_coefficient(0, 1) == 0, "zero frequency")
require(
    normalized_erasure_coefficient(-19, 37)
    == normalized_erasure_coefficient(19, 37),
    "negative frequency",
)
try:
    normalized_erasure_coefficient(1, 0)
except ValueError:
    pass
else:
    raise AssertionError("N=0 is outside the normalized-average domain")


# Independently build inclusive BBP sums and their diagonal decimal states.
DEPTH = 240
partials: list[Fraction] = []
states: list[Fraction] = []
forcing: list[Fraction | None] = [None]
running = Fraction(0)
for n in range(DEPTH + 1):
    running += a(n) / 16**n
    partials.append(running)
    states.append(frac(10**n * running))
    if n:
        forcing.append(a(n) * Fraction(5, 8) ** n)

recurrence_checks = 0
for n in range(DEPTH):
    eps = forcing[n + 1]
    assert eps is not None
    require(states[n + 1] == frac(10 * states[n] + eps), f"state recurrence n={n}")
    recurrence_checks += 1


# Exact rational finite surrogates audit both the indexing and the tail
# coboundary without using decimal digits of pi.
finite_surrogate_checks = 0
for _ in range(1_000):
    n = RNG.randrange(0, DEPTH)
    m = RNG.randrange(n + 1, DEPTH + 1)
    tail = 10**n * (partials[m] - partials[n])
    next_tail = 10 ** (n + 1) * (partials[m] - partials[n + 1])
    eps = forcing[n + 1]
    assert eps is not None
    require(frac(states[n] + tail) == frac(10**n * partials[m]), "surrogate conjugacy")
    require(10 * tail - next_tail == eps, "surrogate tail recurrence")
    require(tail <= Fraction(5, 8) ** n / (15 * (n + 1) ** 2), "tail majorant")
    finite_surrogate_checks += 1


# Equation (13), checked in the exact group ring of Q/Z.  Equality of these
# counters implies equality after applying the character e, without any
# floating-point trigonometry.
def atom_add(expression: Counter[Fraction], phase: Fraction, coefficient: int) -> None:
    key = frac(phase)
    expression[key] += coefficient
    if expression[key] == 0:
        del expression[key]


telescope_checks = 0
for trial in range(600):
    length = RNG.randrange(0, DEPTH + 1)
    q = RNG.randrange(-5000, 5001)
    if trial == 0:
        q = 0
    left: Counter[Fraction] = Counter()
    right: Counter[Fraction] = Counter()
    for n in range(length):
        atom_add(left, 10 * q * states[n], 1)
        atom_add(left, q * states[n], -1)
    atom_add(right, q * states[length], 1)
    atom_add(right, q * states[0], -1)
    for n in range(length):
        eps = forcing[n + 1]
        assert eps is not None
        atom_add(right, -q * eps + q * states[n + 1], 1)
        atom_add(right, q * states[n + 1], -1)
    require(left == right, f"exact Fourier telescope trial={trial}")
    telescope_checks += 1


def ray_core(frequency: int) -> int:
    require(frequency != 0, "zero has no nonzero ray")
    while frequency % 10 == 0:
        frequency //= 10
    return frequency


def clean(counter: Counter[int]) -> Counter[int]:
    return Counter({key: value for key, value in counter.items() if value})


def coboundary(poly: Counter[int]) -> Counter[int]:
    result: Counter[int] = Counter()
    for frequency, coefficient in poly.items():
        result[10 * frequency] += coefficient
        result[frequency] -= coefficient
    return clean(result)


def signature(poly: Counter[int]) -> Counter[int]:
    result: Counter[int] = Counter()
    for frequency, coefficient in poly.items():
        result[0 if frequency == 0 else ray_core(frequency)] += coefficient
    return clean(result)


def target(q: int) -> Counter[int]:
    result: Counter[int] = Counter()
    result[16 * q] += 1
    result[q] -= 1
    return clean(result)


require(target(0) == Counter(), "q=0 target")
ray_checks = 0
for q in range(-5_000, 5_001):
    if q:
        require(ray_core(q) != ray_core(16 * q), f"distinct rays q={q}")
        sig = signature(target(q))
        require(len(sig) == 2 and sorted(sig.values()) == [-1, 1], f"target signature q={q}")
    ray_checks += 1
for trial in range(1_000):
    poly: Counter[int] = Counter()
    for _ in range(RNG.randrange(0, 50)):
        poly[RNG.randrange(-50_000, 50_001)] += RNG.randrange(-50, 51)
    require(signature(coboundary(clean(poly))) == Counter(), f"ray cancellation trial={trial}")
    ray_checks += 1


# The fixed point x=1/9 obstructs stationary continuous coboundaries exactly
# for q not divisible by 3.  In particular q=1, needed by the proposed
# all-frequency target, is obstructed.
fixed = Fraction(1, 9)
require(frac(10 * fixed) == fixed, "T10 fixed point")
fixed_point_checks = 0
for q in range(-10_000, 10_001):
    target_vanishes = frac(16 * q * fixed) == frac(q * fixed)
    require(target_vanishes == (q % 3 == 0), f"fixed point q={q}")
    fixed_point_checks += 1


# Fixed-lag recurrence, its majorant, and the absence of zero frequencies in
# the first positive-lag two-character expansion.
fixed_lag_checks = 0
for n in range(0, DEPTH - 20):
    for h in range(1, 21):
        error = sum(
            10 ** (h - j) * forcing[n + j]
            for j in range(1, h + 1)
            if forcing[n + j] is not None
        )
        require(states[n + h] == frac(10**h * states[n] + error), "fixed-lag recurrence")
        upper = (
            Fraction(5, 8) ** n
            / (n + 1) ** 2
            * sum(10 ** (h - j) * Fraction(5, 8) ** j for j in range(1, h + 1))
        )
        require(0 < error <= upper, "fixed-lag majorant")
        fixed_lag_checks += 1
for q in range(-100, 101):
    if not q:
        continue
    for h in range(1, 11):
        differences = (
            16 * q * 10**h - 16 * q,
            16 * q * 10**h - q,
            q * 10**h - 16 * q,
            q * 10**h - q,
        )
        require(all(difference != 0 for difference in differences), "nonzero lag frequency")
        fixed_lag_checks += 1


# Exact endpoint stationarity and the singular three-cycle separator.
cycle = (Fraction(1, 9), Fraction(7, 9), Fraction(4, 9))
for index, point in enumerate(cycle):
    require(frac(10 * point) == point, "T10-invariant Dirac point")
    require(frac(16 * point) == cycle[(index + 1) % 3], "T16 cycle")
require(len(set(cycle)) == 3, "pairwise distinct Dirac atoms")

cycle_checks = 0
for length in range(1, 301):
    before = Counter(cycle[index % 3] for index in range(length))
    after = Counter(cycle[(index + 1) % 3] for index in range(length))
    l1 = sum(
        abs(Fraction(after[point] - before[point], length))
        for point in set(before) | set(after)
    )
    require(l1 <= Fraction(2, length), "Cesaro endpoint norm")
    require((l1 == 0) == (length % 3 == 0), "cycle stationarity iff 3 divides M")
    cycle_checks += 1


# The safe sparse-digit exceptional-window estimate used for the irrational
# generic separator.  This is a bounded replay, not the irrationality proof.
def bad_starts(length: int, window: int) -> int:
    powers = set()
    power = 1
    while power <= length + window:
        powers.add(power)
        power *= 2
    return sum(
        any(position in powers for position in range(start + 1, start + window + 1))
        for start in range(length)
    )


sparse_checks = 0
for _ in range(500):
    length = RNG.randrange(1, 10_001)
    window = RNG.randrange(1, 101)
    count = bad_starts(length, window)
    safe = window * (length + window).bit_length()
    require(count <= safe, "sparse exceptional-window bound")
    sparse_checks += 1


pins = {}
for path, expected in PINS.items():
    actual = digest(path)
    require(actual == expected, f"pin mismatch: {path}: {actual}")
    pins[path] = actual


print(json.dumps({
    "status": "PASS",
    "claim_label": "experiment",
    "audited_claim_label": "proof sketch",
    "asserts_overlap": False,
    "asserts_fourier_limit": False,
    "asserts_v1": False,
    "erasure_bound": "272*pi*abs(q)/(45*N), for N>=1",
    "exact_check_counts": {
        "state_recurrence": recurrence_checks,
        "finite_surrogate": finite_surrogate_checks,
        "group_ring_telescope": telescope_checks,
        "ray_and_coboundary": ray_checks,
        "fixed_point": fixed_point_checks,
        "fixed_lag": fixed_lag_checks,
        "dirac_cycle": cycle_checks,
        "sparse_windows": sparse_checks,
    },
    "scope": {
        "finite_fourier": "excluded for every nonzero q",
        "stationary_continuous": "fixed-point proof applies when 3 does not divide q; q=1 suffices",
        "nonautonomous": "only universal identities with uniform transfer and residual limits are excluded",
        "orbit_specific": "not excluded",
    },
    "source_pins": pins,
    "warning": "This PASS does not establish T70 overlap, any Fourier limit, or V1.",
}, indent=2, sort_keys=True))
