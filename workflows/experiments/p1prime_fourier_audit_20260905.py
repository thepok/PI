#!/usr/bin/env python3
"""Finite algebra audit for the full-shift sparse-forcing proof.

Python 3, standard library only. Run: python p1prime_fourier_audit.py

Checks Fourier coefficients in two independent finite representations and
checks the exact radix-block transfer identity. Also computes exact density
ratios for N_j=2**(j*j), ell_j=N_j//j.

These floating-point tests do NOT prove the infinite theorem or certify
Jordan--Sahlsten Fourier constants. The proof supplies those analytic steps.
"""
from __future__ import annotations

import cmath
import itertools
import math
from fractions import Fraction
from typing import Dict, List


def e(t: float) -> complex:
    return cmath.exp(2j * math.pi * t)


def digits(value: int, base: int, length: int) -> List[int]:
    out = [0] * length
    for pos in range(length - 1, -1, -1):
        value, out[pos] = divmod(value, base)
    if value:
        raise ValueError("Value exceeds specified digit length")
    return out


def mask(allowed: List[int], t: float) -> complex:
    return sum(e(-a * t) for a in allowed) / len(allowed)


def interval_tail(k: int, scale: int) -> complex:
    if k == 0:
        return 1 + 0j
    z = k / scale
    return e(-z / 2) * math.sin(math.pi * z) / (math.pi * z)


def audit(base: int, length: int, blocks: int,
          forced: Dict[int, int]) -> None:
    n = length * blocks
    B = base ** length
    if any(not 1 <= p <= n or not 0 <= d < base
           for p, d in forced.items()):
        raise ValueError("Invalid forced position or digit")
    alphabets = [[forced[p]] if p in forced else list(range(base))
                 for p in range(1, n + 1)]
    prefixes = []
    for word in itertools.product(*alphabets):
        value = 0
        for d in word:
            value = base * value + d
        prefixes.append(value)
    scale = base ** n
    test_k = sorted(set([0, 1, -1, 2, 7, -19, scale // 2,
                        scale - 1, scale, scale + 1]))
    coefficient_error = 0.0
    for k in test_k:
        by_cells = (sum(e(-k * p / scale) for p in prefixes)
                    / len(prefixes)) * interval_tail(k, scale)
        by_digits = interval_tail(k, scale)
        for j, allowed in enumerate(alphabets, 1):
            by_digits *= mask(allowed, k / (base ** j))
        coefficient_error = max(coefficient_error, abs(by_cells - by_digits))
    assert coefficient_error < 2e-10, coefficient_error

    block_alphabets = []
    for j in range(blocks):
        allowed = []
        for value in range(B):
            word = digits(value, base, length)
            if all(j * length + r + 1 not in forced
                   or forced[j * length + r + 1] == word[r]
                   for r in range(length)):
                allowed.append(value)
        block_alphabets.append(allowed)

    def prefix_product(k: int, j: int) -> float:
        result = 1.0
        for r in range(j):
            result *= abs(mask(block_alphabets[r], k / B ** (r + 1)))
        return result

    S_prev = 1.0
    transfer_error = 0.0
    for j in range(1, blocks + 1):
        S = sum(prefix_product(k, j) for k in range(B ** j))
        transfer = sum(
            prefix_product(k, j - 1)
            * sum(abs(mask(block_alphabets[j - 1], k / B ** j + a / B))
                  for a in range(B))
            for k in range(B ** (j - 1))
        )
        transfer_error = max(transfer_error, abs(S - transfer))
        clean = len(block_alphabets[j - 1]) == B
        bound = min(B, 4 * (1 + math.log(B))) if clean else B
        assert S <= bound * S_prev + 2e-9
        assert abs(S - transfer) < 2e-9
        S_prev = S
    print(f"b={base}, L={length}, J={blocks}, forced={forced}")
    print(f"  coefficient identity max error: {coefficient_error:.3e}")
    print(f"  transfer identity max error:    {transfer_error:.3e}")


def schedule_audit(last_packet: int = 16) -> None:
    previous_total = 0
    print("\nSchedule: N_j=2**(j*j), ell_j=N_j//j")
    for j in range(1, last_packet + 1):
        N = 2 ** (j * j)
        ell = N // j
        assert N + ell <= 2 ** ((j + 1) ** 2)
        if j >= 2:
            assert previous_total <= 2 * 2 ** ((j - 1) ** 2)
            # For every integer m in [N_j,N_{j+1}], f(m)/m is at most:
            all_scale_bound = Fraction(1, j) + Fraction(1, 2 ** (2 * j - 2))
            assert Fraction(previous_total + ell, N) <= all_scale_bound
            if j in (2, 4, 8, 16):
                print(f"  j={j:2d}: all-scale upper bound {float(all_scale_bound):.9f}")
        previous_total += ell


if __name__ == "__main__":
    audit(2, 4, 2, {5: 1, 6: 0})
    audit(2, 3, 3, {2: 1, 7: 0, 8: 1})
    audit(3, 2, 3, {1: 2, 4: 1})
    schedule_audit()
    print("\nAll finite checks passed. Infinite assertions require the analytic proof.")
