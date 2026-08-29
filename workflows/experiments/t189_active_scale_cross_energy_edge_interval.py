#!/usr/bin/env python3
"""
Directed-interval experiment for an active-scale T139/cross-energy separator.

Candidate decimal orbit:
  alpha_0 = 0.W0000...
where W is generated from the tracked pi digit source and an explicit packet.
It has length 20007, consists of the first 10015 certified fractional
digits of pi, then zeros through position 20000, then the packet 5133428
at positions 20001..20007.  The expansion terminates after W.

The computation uses the exact T139 generalized score through the closed
T128 kernel plus the exact primitive-shift endpoint.  All elementary
transcendental evaluations use mpmath.iv outward intervals.

Claim label: directed-interval experiment, not a formal proof.
Tested with Python 3.13 and mpmath 1.3.0.
"""

from __future__ import annotations

import hashlib
from functools import lru_cache
from pathlib import Path
import re
from typing import Iterable

import mpmath
from mpmath import iv, mp

mp.dps = 60
iv.dps = 30

PREFIX_LENGTH = 10_015
WORD_LENGTH = 20_007
PACKET_START = 20_001          # one-based decimal position
PACKET = "5133428"
ORBIT_PREFIX_DIGITS = 45

EXPECTED_PREFIX_SHA256 = (
    "97f28d126aefbf16c98d17737197bf41ca8d32bc3b204aedcde293c338ffc331"
)
EXPECTED_WORD_SHA256 = (
    "7fb44517b3d61021d9ad7edf6257ef5478cbbb9b3d2d9159ab9e4050dde36ee0"
)
EXPECTED_DIGIT_FILE_SHA256 = (
    "77eeccb0067283e14c460b33dc230de54ef15c2e825fc2a35c984fb6984bf684"
)

REPO = Path(__file__).resolve().parents[2]
DIGIT_PATH = REPO / "workflows/research/pi/data/pi_digits_1048596.txt"
T173_PATH = (
    REPO
    / "TheoryLib/PiQuantitativeBlockHitting/"
    "T173T173MachinIntegerCertificate10015.lean"
)


def load_certified_prefix() -> str:
    raw = DIGIT_PATH.read_bytes()
    assert hashlib.sha256(raw).hexdigest() == EXPECTED_DIGIT_FILE_SHA256
    digits = raw.rstrip(b"\n").decode("ascii")
    assert len(digits) == 1_048_596 and digits.isdigit()

    lean = T173_PATH.read_text(encoding="utf-8")
    match = re.search(
        r"abbrev certifiedPiPrefix : Nat :=\s*(\d+)\s*"
        r"private abbrev piPrefix",
        lean,
    )
    assert match is not None
    assert match.group(1) == "3" + digits[:PREFIX_LENGTH]
    return digits[:PREFIX_LENGTH]


certified_prefix = load_certified_prefix()
word = certified_prefix + "0" * (PACKET_START - 1 - PREFIX_LENGTH) + PACKET

assert len(word) == WORD_LENGTH
assert word.isdigit()
assert hashlib.sha256(word.encode("ascii")).hexdigest() == EXPECTED_WORD_SHA256
assert (
    hashlib.sha256(word[:PREFIX_LENGTH].encode("ascii")).hexdigest()
    == EXPECTED_PREFIX_SHA256
)
assert word[PREFIX_LENGTH : PACKET_START - 1] == "0" * (
    PACKET_START - 1 - PREFIX_LENGTH
)
assert word[PACKET_START - 1 :] == PACKET


def lower(x: iv.mpf) -> mp.mpf:
    return mp.mpf(x.a)


def upper(x: iv.mpf) -> mp.mpf:
    return mp.mpf(x.b)


def interval_text(x: iv.mpf, digits: int = 28) -> str:
    return f"[{mp.nstr(lower(x), digits)}, {mp.nstr(upper(x), digits)}]"


def orbit_interval(n: int) -> iv.mpf:
    """Enclose x_n={10^n alpha_0}; alpha_0 terminates after WORD_LENGTH digits."""
    if n >= WORD_LENGTH:
        return iv.mpf(0)

    remaining = WORD_LENGTH - n
    if remaining <= ORBIT_PREFIX_DIGITS:
        return iv.mpf("0." + word[n:])

    prefix = word[n : n + ORBIT_PREFIX_DIGITS]
    p = int(prefix)
    lo = "0." + prefix
    p1 = p + 1
    if p1 == 10**ORBIT_PREFIX_DIGITS:
        hi = "1"
    else:
        hi = "0." + f"{p1:0{ORBIT_PREFIX_DIGITS}d}"
    return iv.mpf([lo, hi])


orbit = [orbit_interval(n) for n in range(WORD_LENGTH + 6)]


def x_at(n: int) -> iv.mpf:
    return orbit[n] if n < len(orbit) else iv.mpf(0)


@lru_cache(maxsize=None)
def scalar_parameters(m: int) -> tuple[iv.mpf, iv.mpf, iv.mpf]:
    """Return 1-beta_m, beta_m, and the exact-form zero coefficient."""
    one_minus_beta = 2 * iv.sin(iv.pi / (2 * m)) ** 2
    beta = 1 - one_minus_beta
    alpha_zero = (
        one_minus_beta * iv.mpf(2 * m * m + 1) / (3 * m)
        - iv.mpf(1) / m
    )
    return one_minus_beta, beta, alpha_zero


def positive_boundary_coefficient(
    m: int, h: int, one_minus_beta: iv.mpf
) -> iv.mpf:
    """Literal T142 coefficient, 1 <= h < 2m."""
    assert 1 <= h < 2 * m
    if h <= m:
        numerator = (
            4 * m**3 + 2 * m - 6 * m * h**2 + 3 * h**3 - 3 * h
        )
        fejer_coefficient = iv.mpf(numerator) / (6 * m * m)
        edge_coefficient = iv.mpf(3 * h - 2 * m) / (2 * m * m)
    else:
        j = 2 * m - h
        fejer_coefficient = iv.mpf((j - 1) * j * (j + 1)) / (6 * m * m)
        edge_coefficient = iv.mpf(j) / (2 * m * m)
    return one_minus_beta * fejer_coefficient + edge_coefficient


def ten_valuation_and_primitive(h: int) -> tuple[int, int]:
    valuation = 0
    while h % 10 == 0:
        h //= 10
        valuation += 1
    return valuation, h


def target_constants(m: int, labels: list[int]) -> list[tuple[iv.mpf, ...]]:
    """Precompute the literal target rotations for a common scale."""
    data: list[tuple[iv.mpf, ...]] = []
    for label in labels:
        center = iv.mpf(2 * label + 1) / (2 * m)
        data.append(
            (
                iv.sin(iv.pi * center),
                iv.cos(iv.pi * center),
                iv.sin(2 * iv.pi * center),
                iv.cos(2 * iv.pi * center),
            )
        )
    return data


def boundary_kernel_vector(
    x: iv.mpf,
    m: int,
    target_data: list[tuple[iv.mpf, ...]],
    cosine_step: iv.mpf,
) -> list[iv.mpf]:
    """
    Closed T128 kernels for all labels, sharing the orbit trigonometry.

    Since m*c_{m,C}=C+1/2,
        sin(pi*m*(x-c_{m,C}))^4 = cos(pi*m*x)^4.
    This exact identity avoids evaluating the same high-frequency sine ten
    times and retains every literal target denominator.
    """
    sx = iv.sin(iv.pi * x)
    cx = iv.cos(iv.pi * x)
    sin_2x = 2 * sx * cx
    cos_2x = cx * cx - sx * sx
    numerator_fourth = iv.cos(iv.pi * m * x) ** 4

    result: list[iv.mpf] = []
    for sin_c, cos_c, sin_2c, cos_2c in target_data:
        sin_t = sx * cos_c - cx * sin_c
        cos_2t = cos_2x * cos_2c + sin_2x * sin_2c
        result.append(
            (cos_2t - cosine_step)
            * numerator_fourth
            / (m * m * sin_t**4)
        )
    return result


def kernel_sums_many(
    m: int, labels: list[int], horizons: Iterable[int]
) -> dict[int, dict[int, iv.mpf]]:
    horizons = sorted(set(horizons))
    max_horizon = max(horizons)
    stop = min(max_horizon, WORD_LENGTH)
    requested = set(horizons)

    data = target_constants(m, labels)
    cosine_step = iv.cos(iv.pi / m)
    totals = [iv.mpf(0) for _ in labels]
    result = {label: {} for label in labels}

    for n in range(stop):
        values = boundary_kernel_vector(x_at(n), m, data, cosine_step)
        for i, value in enumerate(values):
            totals[i] += value
        if n + 1 in requested:
            for i, label in enumerate(labels):
                result[label][n + 1] = totals[i]

    if max_horizon > WORD_LENGTH:
        zero_values = boundary_kernel_vector(
            iv.mpf(0), m, data, cosine_step
        )
        for horizon in horizons:
            if horizon > WORD_LENGTH:
                tail = horizon - WORD_LENGTH
                for i, label in enumerate(labels):
                    result[label][horizon] = totals[i] + tail * zero_values[i]

    for label in labels:
        assert set(result[label]) == set(horizons)
    return result


@lru_cache(maxsize=None)
def primitive_endpoint(m: int, label: int, horizon: int) -> iv.mpf:
    """
    Exact T139 primitive-shift endpoint.

    Terms with v_10(h)=0 vanish, so only h divisible by ten are traversed.
    """
    one_minus_beta, _, _ = scalar_parameters(m)
    center = iv.mpf(2 * label + 1) / (2 * m)
    total = iv.mpf(0)

    for h in range(10, 2 * m, 10):
        valuation, primitive = ten_valuation_and_primitive(h)
        coefficient = positive_boundary_coefficient(
            m, h, one_minus_beta
        )

        block_re = iv.mpf(0)
        block_im = iv.mpf(0)
        for j in range(valuation):
            terminal_angle = 2 * iv.pi * primitive * x_at(horizon + j)
            initial_angle = 2 * iv.pi * primitive * x_at(j)
            block_re += iv.cos(terminal_angle) - iv.cos(initial_angle)
            block_im += iv.sin(terminal_angle) - iv.sin(initial_angle)

        target_angle = -2 * iv.pi * h * center
        total += coefficient * (
            iv.cos(target_angle) * block_re
            - iv.sin(target_angle) * block_im
        )

    return total


def bellman_from_parts(
    m: int,
    horizon: int,
    closed_kernel_sum: iv.mpf,
    endpoint: iv.mpf,
) -> iv.mpf:
    _, _, alpha_zero = scalar_parameters(m)
    re_z = (closed_kernel_sum - alpha_zero * horizon) / 2 - endpoint
    return m * re_z - iv.mpf(7 * horizon) / (3 * m)


def score(m: int, label: int, horizon: int) -> iv.mpf:
    kernels = kernel_sums_many(m, [label], [horizon])
    endpoint = primitive_endpoint(m, label, horizon)
    return bellman_from_parts(
        m, horizon, kernels[label][horizon], endpoint
    )


def stable_sign(x: iv.mpf) -> str:
    if lower(x) > 0:
        return "+"
    if upper(x) < 0:
        return "-"
    raise ArithmeticError(f"interval crosses zero: {interval_text(x)}")


def corrected_energy(
    fresh: list[iv.mpf], final: list[iv.mpf]
) -> tuple[iv.mpf, list[str]]:
    """
    Evaluate E=sum D_d F_d-sum D_d^-F_d^- using certified signs.

    On a common-negative coordinate, the two products cancel identically.
    """
    total = iv.mpf(0)
    patterns: list[str] = []
    for d, (D, F) in enumerate(zip(fresh, final)):
        pattern = stable_sign(D) + stable_sign(F)
        patterns.append(pattern)
        if pattern == "--":
            continue
        total += D * F
    return total, patterns


def evaluate_node(
    q: int, A: int, parent_score: iv.mpf
) -> dict[str, object]:
    Q = 10 * q

    # For h divisible by ten, the T139 endpoint is exactly invariant under
    # label -> label + d*q at scale Q:
    # exp(-2*pi*i*h*(d*q/Q)) = exp(-2*pi*i*(h/10)*d) = 1.
    endpoint_old = primitive_endpoint(Q, A, q)
    endpoint_final = primitive_endpoint(Q, A, Q)

    old_scores: list[iv.mpf] = []
    final_scores: list[iv.mpf] = []
    G: list[iv.mpf] = []
    D: list[iv.mpf] = []
    F: list[iv.mpf] = []

    labels = [A + digit * q for digit in range(10)]
    kernel_table = kernel_sums_many(Q, labels, [q, Q])

    for digit, child_label in enumerate(labels):
        kernels = kernel_table[child_label]
        old = bellman_from_parts(Q, q, kernels[q], endpoint_old)
        final = bellman_from_parts(Q, Q, kernels[Q], endpoint_final)

        old_scores.append(old)
        final_scores.append(final)
        G.append(old - parent_score)
        D.append(final - old)
        F.append(final - parent_score)

    energy, patterns = corrected_energy(D, F)
    fmr = [d for d, pattern in enumerate(patterns) if pattern == "++"]

    return {
        "q": q,
        "A": A,
        "Q": Q,
        "parent_score": parent_score,
        "old_scores": old_scores,
        "final_scores": final_scores,
        "G": G,
        "D": D,
        "F": F,
        "E": energy,
        "patterns": patterns,
        "FMR": fmr,
    }


def print_node(node: dict[str, object]) -> None:
    q = int(node["q"])
    A = int(node["A"])
    print()
    print(f"NODE q={q} A={A}")
    print(f"parent_score={interval_text(node['parent_score'])}")
    print("d  sign(D,F)  G_interval  D_interval  F_interval")
    for d in range(10):
        print(
            f"{d}  {node['patterns'][d]:>2}  "
            f"{interval_text(node['G'][d])}  "
            f"{interval_text(node['D'][d])}  "
            f"{interval_text(node['F'][d])}"
        )
    print(f"E={interval_text(node['E'])}")
    print(f"FMR={node['FMR']}")


root_score = score(1000, 334, 1000)
root = evaluate_node(1000, 334, root_score)

# This explicit edge is the counter-instance to a universal edgewise claim.
selected_root_digit = 1
reached_score = root["final_scores"][selected_root_digit]
reached = evaluate_node(10_000, 1_334, reached_score)

# The reached node has the explicit literal FMR child e=5.
selected_reached_digit = 5

assert lower(root_score) > 0
assert root["FMR"] == [0, 1, 2, 3, 4, 8, 9]
assert stable_sign(root["D"][selected_root_digit]) == "+"
assert stable_sign(root["F"][selected_root_digit]) == "+"
assert lower(root["E"]) > mp.mpf("5889773540")

assert lower(reached_score) > 0
assert reached["FMR"] == [5]
assert stable_sign(reached["D"][selected_reached_digit]) == "+"
assert stable_sign(reached["F"][selected_reached_digit]) == "+"
assert upper(reached["E"]) < mp.mpf("-4380913919")
assert reached["patterns"] == [
    "--", "--", "--", "--", "--", "++", "--", "--", "-+", "--"
]

print("status: PASS (directed-interval experiment; not a formal proof)")
print(f"python={__import__('sys').version.split()[0]}")
print(f"mpmath={mpmath.__version__}")
print(f"iv_dps={iv.dps}")
print(f"word_length={len(word)}")
print(f"prefix_length={PREFIX_LENGTH}")
print(f"prefix_sha256={EXPECTED_PREFIX_SHA256}")
print(f"word_sha256={EXPECTED_WORD_SHA256}")
print(f"packet_positions={PACKET_START}..{PACKET_START + len(PACKET) - 1}")
print(f"packet={PACKET}")
print("fixed_edge=(1000,334) --d=1--> (10000,1334)")
print("fixed_reached_child=e=5")
print_node(root)
print_node(reached)
