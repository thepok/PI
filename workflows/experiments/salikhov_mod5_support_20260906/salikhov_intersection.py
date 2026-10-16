#!/usr/bin/env python3
"""Exact checks for the Salikhov binary-family/mod-five intersection.

No evaluation of pi, floating point, decimal digits, network, or dependencies.
The graph identities are exhaustive. The family census is a finite experiment,
not the all-index proof; see the accompanying mathematical note.

Example:
  python3 workflows/experiments/salikhov_mod5_support_20260906/salikhov_intersection.py --max-k 18
"""
from __future__ import annotations

import argparse
from collections import Counter
from math import gcd

from full_pair import (
    COMPACT_START, SINK, build_and_certify_pair, compact_output, compact_step,
    evaluate, graph_certificates,
)


def support_counts(edges, outputs, count):
    """Count live digit words, from the actual full-pair transition graph."""
    v = [int(z != (0, 0)) for z in outputs]
    result = []
    for _ in range(count):
        result.append(v[0])
        v = [sum(v[j] for j in row) for row in edges]
    return result


def r_for_length(length):
    """Return (r,5**r), with 5**r <= length < 5**(r+1)."""
    assert length >= 1
    r, modulus = 0, 1
    while 5 * modulus <= length:
        r += 1
        modulus *= 5
    return r, modulus


def live_residue(n, digits):
    st = COMPACT_START
    for _ in range(digits):
        st = compact_step(st, n % 5)
        n //= 5
    return st is not SINK


def verify_absorption(states, edges, outputs, sink):
    assert states[sink] is SINK
    assert edges[sink] == [sink] * 5
    # Crucial: live words and nonzero outputs coincide. Output sparsity alone
    # would not justify a bound on allowable low-digit residue classes.
    assert all((st is SINK) == (z == (0, 0))
               for st, z in zip(states, outputs))
    assert all((st is SINK) == (z[0] == 0)
               for st, z in zip(states, outputs))
    # Padding the top of an integer with zero digits preserves its output.
    assert all(outputs[row[0]] == outputs[i]
               for i, row in enumerate(edges))
    assert all(compact_output(compact_step(st, 0)) == compact_output(st)
               for st in states)
    print('Exhaustive prefix certificate: zero output iff absorbing sink; zero-padding preserves outputs.')


def verify_small_progressions(h):
    # Exhaust every offset and invertible step modulo 125. For several lengths
    # spanning the next modulus, the residue certificate checks the exact
    # occupancy argument, independently of the particular dyadic family.
    modulus, r = 125, 3
    allowed = [live_residue(n, r) for n in range(modulus)]
    assert sum(allowed) == h[r]
    for offset in range(modulus):
        for step in range(1, modulus):
            if gcd(step, 5) != 1:
                continue
            for length in (1, 17, 124, 125, 126, 249):
                count = sum(allowed[(offset + step * j) % modulus]
                            for j in range(length))
                assert count <= h[r] * ((length + modulus - 1) // modulus)
    # Check actual, possibly much larger integers against their low-digit
    # admissibility. The implication itself follows from sink absorption.
    for step in (1, 2, 8, 64, 1024):
        for offset in (1, 3, 21, 512):
            values = [offset + step * j for j in range(500)]
            for n in values:
                if evaluate(n) != (0, 0):
                    assert live_residue(n, r)
            actual = sum(evaluate(n) != (0, 0) for n in values)
            assert actual <= h[r] * ((len(values) + modulus - 1) // modulus)
    print('All offsets and 5-coprime steps modulo 125 satisfy the exact residue-occupancy bound.')


def family_block(k):
    return (2**k * m for m in range(1, 2**(k - 1), 2))


def family_size_below(limit):
    return sum(min(2**(k - 2), ((limit // 2**k) + 1) // 2)
               for k in range(2, limit.bit_length()))


def family_below(limit):
    for k in range(2, limit.bit_length()):
        top = min(2**(k - 1) - 1, limit // 2**k)
        for m in range(1, top + 1, 2):
            yield 2**k * m


def census(max_k, h):
    print('k | family size | Z=(0,0) | Z!=0 | exact AP upper bound')
    for k in range(2, max_k + 1):
        length = 2**(k - 2)
        r, modulus = r_for_length(length)
        count = Counter(evaluate(n) for n in family_block(k))
        nonzero = length - count[(0, 0)]
        upper = min(length, h[r] * ((length + modulus - 1) // modulus))
        assert sum(count.values()) == length
        assert nonzero <= upper
        print(k, length, count[(0, 0)], nonzero, upper, sep=' | ')
    # Independently exercise the truncated-block count and uniform estimate.
    for limit in (63, 127, 1000, 10000, 100000, 1000000):
        values = list(family_below(limit))
        assert len(values) == len(set(values)) == family_size_below(limit)
        count = Counter(evaluate(n) for n in values)
        upper = 0
        for k in range(2, limit.bit_length()):
            length = min(2**(k - 2), ((limit // 2**k) + 1) // 2)
            if not length:
                continue
            r, modulus = r_for_length(length)
            upper += min(length, h[r] * ((length + modulus - 1) // modulus))
            assert length <= min(2**(k - 2), limit // 2**k)
        nonzero = len(values) - count[(0, 0)]
        assert nonzero <= upper
        print(f'N={limit}: family={len(values)}, zero={count[(0,0)]}, nonzero={nonzero}, upper={upper}')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--max-k', type=int, default=18)
    args = parser.parse_args()
    if args.max_k < 2:
        parser.error('--max-k must be >= 2')
    states, edges, outputs, sink = build_and_certify_pair()
    graph_certificates(states, edges, outputs, sink)
    verify_absorption(states, edges, outputs, sink)
    h = support_counts(edges, outputs, max(args.max_k, 20))
    assert h[:5] == [1, 4, 16, 65, 267]
    verify_small_progressions(h)
    census(args.max_k, h)
    print('Exact certificates and finite census passed. The asymptotic and sign theorems require the proof.')


if __name__ == '__main__':
    main()
