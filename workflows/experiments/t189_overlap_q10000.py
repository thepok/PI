#!/usr/bin/env python3
"""Replay the corrected second-node T189 Bellman-overlap experiment.

This is a floating-point falsification/diagnostic replay, not a certificate.
It uses the registered decimal prefix, T142's exact piecewise coefficient
formula, the closed boundary kernel, and the literal terminal endpoint.
"""

from __future__ import annotations

import hashlib
import math
from pathlib import Path


DIGIT_PATH = (
    Path(__file__).resolve().parents[2].parent
    / "AllMath"
    / "workflows/research/pi/data/pi_digits_1048596.txt"
)
EXPECTED_SHA256 = (
    "77eeccb0067283e14c460b33dc230de54ef15c2e825fc2a35c984fb6984bf684"
)

PARENT_Q = 10_000
PARENT_A = 3_334
CHILD_Q = 100_000
N = 100_000
H = 1_000_000
SUFFIX_DIGITS = 22
CHUNK = 10_000


raw = DIGIT_PATH.read_bytes()
actual_hash = hashlib.sha256(raw).hexdigest()
assert actual_hash == EXPECTED_SHA256, (actual_hash, EXPECTED_SHA256)
digits = raw.rstrip(b"\n").decode("ascii")
assert len(digits) == 1_048_596 and digits.isdigit()
assert len(digits) >= H + SUFFIX_DIGITS

suffix_denominator = 10**SUFFIX_DIGITS
orbit = [
    int(digits[n : n + SUFFIX_DIGITS]) / suffix_denominator
    for n in range(H + SUFFIX_DIGITS)
]


def scalar_parameters(q: int) -> tuple[float, float, float]:
    """Return 1-beta, beta, and the exact-form zero coefficient."""
    one_sub_beta = 2.0 * math.sin(math.pi / (2.0 * q)) ** 2
    beta = 1.0 - one_sub_beta
    alpha_zero = one_sub_beta * (2 * q * q + 1) / (3 * q) - 1 / q
    return one_sub_beta, beta, alpha_zero


def boundary_kernel(x: float, q: int, center: float, beta: float) -> float:
    """Closed T128 boundary kernel, using stable cosine subtraction."""
    t = x - center
    cosine_difference = -2.0 * math.sin(
        math.pi * t + math.pi / (2.0 * q)
    ) * math.sin(math.pi * t - math.pi / (2.0 * q))
    denominator_sine = math.sin(math.pi * t)
    if abs(denominator_sine) < 1e-15:
        fejer = float(q)
    else:
        numerator_sine = math.sin(math.pi * q * t)
        fejer = numerator_sine**2 / (q * denominator_sine**2)
    return cosine_difference * fejer**2


def positive_boundary_coefficient(q: int, h: int, one_sub_beta: float) -> float:
    """T142's literal positive-frequency coefficient for 1 <= h < 2q."""
    assert 1 <= h <= 2 * q - 1
    if h <= q:
        fejer_coefficient = (
            4 * q**3 + 2 * q - 6 * q * h**2 + 3 * h**3 - 3 * h
        ) / (6 * q**2)
        edge_coefficient = (3 * h - 2 * q) / (2 * q**2)
    else:
        fejer_coefficient = (
            (2 * q - h - 1) * (2 * q - h) * (2 * q - h + 1)
        ) / (6 * q**2)
        edge_coefficient = (2 * q - h) / (2 * q**2)
    return one_sub_beta * fejer_coefficient + edge_coefficient


def ten_valuation_and_primitive(h: int) -> tuple[int, int]:
    valuation = 0
    while h % 10 == 0:
        valuation += 1
        h //= 10
    return valuation, h


def endpoint_re(q: int, label: int, horizon: int, one_sub_beta: float) -> float:
    """Literal T139 terminal endpoint, real part, over 10-divisible h."""
    center = (2 * label + 1) / (2 * q)
    terms: list[float] = []
    for h in range(10, 2 * q, 10):
        valuation, primitive = ten_valuation_and_primitive(h)
        coefficient = positive_boundary_coefficient(q, h, one_sub_beta)
        target_angle = -2.0 * math.pi * h * center
        target_re = math.cos(target_angle)
        target_im = math.sin(target_angle)
        block_re = 0.0
        block_im = 0.0
        for j in range(valuation):
            terminal_angle = 2.0 * math.pi * primitive * orbit[horizon + j]
            initial_angle = 2.0 * math.pi * primitive * orbit[j]
            block_re += math.cos(terminal_angle) - math.cos(initial_angle)
            block_im += math.sin(terminal_angle) - math.sin(initial_angle)
        terms.append(coefficient * (target_re * block_re - target_im * block_im))
    return math.fsum(terms)


def kernel_sum(q: int, label: int, horizon: int, beta: float) -> float:
    center = (2 * label + 1) / (2 * q)
    chunks: list[float] = []
    for start in range(0, horizon, CHUNK):
        stop = min(start + CHUNK, horizon)
        chunks.append(
            math.fsum(boundary_kernel(orbit[n], q, center, beta) for n in range(start, stop))
        )
    return math.fsum(chunks)


def re_z(q: int, label: int, horizon: int) -> float:
    """Literal Re(primitiveBoundaryFourierSum q label horizon)."""
    one_sub_beta, beta, alpha_zero = scalar_parameters(q)
    closed_sum = kernel_sum(q, label, horizon, beta)
    endpoint = endpoint_re(q, label, horizon, one_sub_beta)
    return (closed_sum - alpha_zero * horizon) / 2.0 - endpoint


def bellman_surplus(q: int, re_score: float, horizon: int) -> float:
    return q * re_score - horizon * 7.0 / (3.0 * q)


parent_re = re_z(PARENT_Q, PARENT_A, N)
parent_bellman = bellman_surplus(PARENT_Q, parent_re, N)

rows: list[tuple[int, int, float, float, float, float, float, float]] = []
for digit in range(10):
    child_label = PARENT_A + digit * PARENT_Q
    re_n = re_z(CHILD_Q, child_label, N)
    re_h = re_z(CHILD_Q, child_label, H)
    bellman_n = bellman_surplus(CHILD_Q, re_n, N)
    bellman_h = bellman_surplus(CHILD_Q, re_h, H)
    inherited_improvement = bellman_n - parent_bellman
    fresh_margin = (bellman_h - bellman_n) / PARENT_Q
    fresh_margin_check = 10.0 * (re_h - re_n) - 21.0 / PARENT_Q
    assert abs(fresh_margin - fresh_margin_check) < 1e-10
    rows.append(
        (
            digit,
            child_label,
            re_n,
            re_h,
            bellman_n,
            bellman_h,
            inherited_improvement,
            fresh_margin,
        )
    )

improving = {digit for digit, _, _, _, _, _, p, _ in rows if p > 0}
fresh_positive = {digit for digit, _, _, _, _, _, _, m in rows if m > 0}
overlap = improving & fresh_positive

def dc1_envelope(gains: list[float], fresh: list[float]) -> tuple[float, ...]:
    """Return the sharp first-sector envelope for Y_d=D_d-(-G_d)_+."""
    compensated = [d - max(0.0, -g) for g, d in zip(gains, fresh)]
    mean = math.fsum(compensated) / 10.0
    hat_re = math.fsum(
        value * math.cos(2.0 * math.pi * digit / 10.0)
        for digit, value in enumerate(compensated)
    ) / 10.0
    hat_im = math.fsum(
        value * math.sin(2.0 * math.pi * digit / 10.0)
        for digit, value in enumerate(compensated)
    ) / 10.0
    inradius = math.cos(math.pi / 10.0)
    gauge_at_neg_hat = max(
        (
            -hat_re * math.cos((2 * face + 1) * math.pi / 10.0)
            -hat_im * math.sin((2 * face + 1) * math.pi / 10.0)
        )
        / inradius
        for face in range(10)
    )
    return mean, hat_re, hat_im, gauge_at_neg_hat, mean + gauge_at_neg_hat, max(compensated)


# The original replay is the generalized two-step N=10q -> H=100q envelope.
two_step_dc1 = dc1_envelope(
    [row[6] for row in rows], [PARENT_Q * row[7] for row in rows]
)

# Separately evaluate the literal natural-diagonal q -> 10q DC1 node used by
# the active frontier. This remains a floating-point falsifier, not a theorem.
natural_n = PARENT_Q
natural_h = CHILD_Q
natural_parent_re = re_z(PARENT_Q, PARENT_A, natural_n)
natural_parent_bellman = bellman_surplus(PARENT_Q, natural_parent_re, natural_n)
natural_gains: list[float] = []
natural_fresh: list[float] = []
for digit in range(10):
    child_label = PARENT_A + digit * PARENT_Q
    natural_b_n = bellman_surplus(
        CHILD_Q, re_z(CHILD_Q, child_label, natural_n), natural_n
    )
    natural_b_h = bellman_surplus(
        CHILD_Q, re_z(CHILD_Q, child_label, natural_h), natural_h
    )
    natural_gains.append(natural_b_n - natural_parent_bellman)
    natural_fresh.append(natural_b_h - natural_b_n)
natural_dc1 = dc1_envelope(natural_gains, natural_fresh)

assert improving == {0, 4, 5, 6, 7, 8}
assert fresh_positive == {0, 3, 5, 6}
assert overlap == {0, 5, 6}
assert two_step_dc1[4] > 0.0
assert natural_dc1[4] > 0.0

print("status: PASS (floating-point experiment; not a certificate)")
print(f"digit_path={DIGIT_PATH}")
print(f"digit_sha256={actual_hash}")
print(f"suffix_digits={SUFFIX_DIGITS}")
print(f"parent_ReZ={parent_re:.15f}")
print(f"parent_B={parent_bellman:.12f}")
print("d child_label ReZ_N ReZ_H B_N B_H G_d M_d")
for row in rows:
    d, label, re_n, re_h, b_n, b_h, p_value, m_value = row
    print(
        f"{d} {label} {re_n:.15f} {re_h:.15f} "
        f"{b_n:.12f} {b_h:.12f} {p_value:.12f} {m_value:.12f}"
    )
print(f"improving={sorted(improving)}")
print(f"fresh_positive={sorted(fresh_positive)}")
print(f"overlap={sorted(overlap)}")
print(f"two_step_dc1_compensated_mean={two_step_dc1[0]:.12f}")
print(
    "two_step_dc1_hatY1="
    f"({two_step_dc1[1]:.12f},{two_step_dc1[2]:.12f})"
)
print(f"two_step_dc1_gauge_at_neg_hatY1={two_step_dc1[3]:.12f}")
print(f"two_step_dc1_lower_bound={two_step_dc1[4]:.12f}")
print(f"two_step_dc1_literal_max={two_step_dc1[5]:.12f}")
print(f"natural_dc1_compensated_mean={natural_dc1[0]:.12f}")
print(f"natural_dc1_hatY1=({natural_dc1[1]:.12f},{natural_dc1[2]:.12f})")
print(f"natural_dc1_gauge_at_neg_hatY1={natural_dc1[3]:.12f}")
print(f"natural_dc1_lower_bound={natural_dc1[4]:.12f}")
print(f"natural_dc1_literal_max={natural_dc1[5]:.12f}")
