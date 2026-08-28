#!/usr/bin/env python3
"""Replay the q=10000 parity/sector-5 T189 separator.

This is a high-precision experiment, not a directed-interval certificate.
It evaluates the machine-checked closed-kernel and endpoint identities with
72 retained decimal suffix digits. Install ``mpmath`` if it is unavailable.
"""

from __future__ import annotations

from concurrent.futures import ProcessPoolExecutor
from pathlib import Path

import mpmath as mp


mp.mp.dps = 60
DIGITS = (Path(__file__).resolve().parents[1] / "research/pi/data/pi_digits_1048596.txt").read_text().strip()
SUFFIX_DIGITS = 72
ORBIT = [mp.mpf("0." + DIGITS[n : n + SUFFIX_DIGITS]) for n in range(100_006)]


def parameters(q: int) -> tuple[mp.mpf, mp.mpf, mp.mpf]:
    one_minus_beta = 2 * mp.sin(mp.pi / (2 * q)) ** 2
    alpha_zero = one_minus_beta * (2 * q * q + 1) / (3 * q) - mp.mpf(1) / q
    return one_minus_beta, 1 - one_minus_beta, alpha_zero


def coefficient(q: int, h: int, one_minus_beta: mp.mpf) -> mp.mpf:
    if h <= q:
        fejer = mp.mpf(4 * q**3 + 2 * q - 6 * q * h * h + 3 * h**3 - 3 * h) / (6 * q * q)
        edge = mp.mpf(3 * h - 2 * q) / (2 * q * q)
    else:
        fejer = mp.mpf((2 * q - h - 1) * (2 * q - h) * (2 * q - h + 1)) / (6 * q * q)
        edge = mp.mpf(2 * q - h) / (2 * q * q)
    return one_minus_beta * fejer + edge


def primitive_part(h: int) -> tuple[int, int]:
    valuation = 0
    while h % 10 == 0:
        valuation += 1
        h //= 10
    return valuation, h


def endpoint(q: int, label: int, horizon: int, one_minus_beta: mp.mpf) -> mp.mpf:
    center = mp.mpf(2 * label + 1) / (2 * q)
    values = []
    for h in range(10, 2 * q, 10):
        valuation, primitive = primitive_part(h)
        block = sum(
            mp.expj(2 * mp.pi * primitive * ORBIT[horizon + j])
            - mp.expj(2 * mp.pi * primitive * ORBIT[j])
            for j in range(valuation)
        )
        values.append(mp.re(coefficient(q, h, one_minus_beta) * mp.expj(-2 * mp.pi * h * center) * block))
    return mp.fsum(values)


def score(task: tuple[int, int, int, int]) -> tuple[int, mp.mpf, mp.mpf]:
    q, label, first_horizon, final_horizon = task
    one_minus_beta, _, alpha_zero = parameters(q)
    center = mp.mpf(2 * label + 1) / (2 * q)
    kernel_values = []
    first_sum = None
    for n in range(final_horizon):
        t = ORBIT[n] - center
        cosine_difference = -2 * mp.sin(mp.pi * t + mp.pi / (2 * q)) * mp.sin(mp.pi * t - mp.pi / (2 * q))
        fejer = mp.sin(mp.pi * q * t) ** 2 / (q * mp.sin(mp.pi * t) ** 2)
        kernel_values.append(cosine_difference * fejer**2)
        if n + 1 == first_horizon:
            first_sum = mp.fsum(kernel_values)
    assert first_sum is not None
    final_sum = mp.fsum(kernel_values)
    first = (first_sum - alpha_zero * first_horizon) / 2 - endpoint(q, label, first_horizon, one_minus_beta)
    final = (final_sum - alpha_zero * final_horizon) / 2 - endpoint(q, label, final_horizon, one_minus_beta)
    return label, first, final


def surplus(q: int, real_score: mp.mpf, horizon: int) -> mp.mpf:
    return q * real_score - mp.mpf(7) * horizon / (3 * q)


if __name__ == "__main__":
    root = score((1_000, 334, 1_000, 1_000))
    root_surplus = surplus(1_000, root[2], 1_000)
    edge = score((10_000, 1_334, 1_000, 10_000))
    edge_g = surplus(10_000, edge[1], 1_000) - root_surplus
    edge_d = surplus(10_000, edge[2], 10_000) - surplus(10_000, edge[1], 1_000)
    parent_surplus = surplus(10_000, edge[2], 10_000)

    tasks = [(100_000, 1_334 + d * 10_000, 10_000, 100_000) for d in range(10)]
    with ProcessPoolExecutor(max_workers=10) as pool:
        children = sorted(pool.map(score, tasks))

    y_values = []
    print("claim_label=experiment")
    print("root_B", mp.nstr(root_surplus, 25))
    print("edge_d1", *(mp.nstr(x, 25) for x in (edge_g, edge_d, edge_g + edge_d)))
    print("parent_B", mp.nstr(parent_surplus, 25))
    print("d G D G_plus_D Y")
    for d, (_, first, final) in enumerate(children):
        child_first = surplus(100_000, first, 10_000)
        child_final = surplus(100_000, final, 100_000)
        g = child_first - parent_surplus
        fresh = child_final - child_first
        y = fresh - max(mp.mpf(0), -g)
        y_values.append(y)
        print(d, *(mp.nstr(x, 25) for x in (g, fresh, g + fresh, y)))

    pairs = [(y_values[d] + y_values[(d + 1) % 10]) / 2 for d in range(10)]
    even_max = max(y_values[0::2])
    odd_max = max(y_values[1::2])
    threshold = (even_max + odd_max) / (odd_max - even_max)
    assert [d for d, y in enumerate(y_values) if y > 0] == [5]
    assert max(pairs) < 0
    print("cyclic_pair_max", mp.nstr(max(pairs), 25))
    print("parity_balanced_upper", mp.nstr((even_max + odd_max) / 2, 25))
    print("mu5_required_below", mp.nstr(threshold, 25))
