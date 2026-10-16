#!/usr/bin/env python3
"""Finite exact certificates for the Salikhov prime-power absorption proof.

All assertions use integer or finite-field arithmetic.  No optional packages.
This checks the small mod-5 module, its survival majorant, and the two rational
inequalities used in the quantitative growing-precision argument.  It does
not replace the infinite-state weighted-degree and residue proof in the note.
"""
from collections import deque
from fractions import Fraction
from math import log

from prime_power import mul, powers, trim


MODULUS = 5
D = [3, 3, 1, 4]  # (2-w)^3 modulo 5
F0 = mul([1, 3, 1], mul([2, 3, 1], [2, 3, 1], 5), 5)
FF, DD = powers(F0, 4, 5), powers(D, 4, 5)
FACTORS = [mul(FF[d], DD[4-d], 5) for d in range(5)]


def transition(state, digit):
    poly, carry = state
    e, next_carry = (3*digit+carry) % 5, (3*digit+carry) // 5
    image = tuple(trim(mul(list(poly), FACTORS[digit], 5)[e::5] or [0]))
    assert len(image) <= next_carry+3
    return image, next_carry


def build_graph():
    basis = [((0,)*j+(1,), c) for c in range(3) for j in range(c+3)]
    states = list(basis)
    ids = {s: j for j, s in enumerate(states)}
    queue = deque(basis)
    graph = []
    while queue:
        state = queue.popleft()
        row = []
        for d in range(5):
            successor = transition(state, d)
            if successor not in ids:
                ids[successor] = len(states)
                states.append(successor)
                queue.append(successor)
            row.append(ids[successor])
        graph.append(row)
    return basis, states, ids, graph


def precision_parameters(a):
    assert a >= 2
    m, h = 5, 1
    while 4*m//5 < a-1:
        m, h = 5*m, h+1
    return m, h, 5*h+100


def a_for_digits(length):
    """Largest a>=2 with 4*a*(5*h_a+100)<=length; 0 if none."""
    low, high = 1, max(2, length//400+1)
    while low+1 < high:
        mid = (low+high)//2
        if 4*mid*precision_parameters(mid)[2] <= length:
            low = mid
        else:
            high = mid
    return low if low >= 2 else 0


def main():
    import argparse
    import json
    from pathlib import Path
    parser = argparse.ArgumentParser()
    parser.add_argument('--json', type=Path, help='Save the full finite certificate')
    args = parser.parse_args()
    basis, states, ids, graph = build_graph()
    assert len(basis) == 12
    assert len(states) == 111
    for state in basis:
        assert not any(transition(transition(state, 0), 3)[0])
    print('Word 03 kills all 12 basis states; full reachable graph:', len(states))

    nonzero = [int(any(poly)) for poly, carry in states]
    apply = lambda values: [sum(values[t] for t in row) for row in graph]
    v2 = apply(apply(nonzero))
    v3 = apply(v2)
    assert all(5*x <= 21*y for x, y in zip(v3, v2))
    live_v2 = [x for x, live in zip(v2, nonzero) if live]
    assert min(live_v2) == 9 and max(live_v2) == 22
    assert all(x == 0 for x, live in zip(v2, nonzero) if not live)
    print('Exact certificate: 5*M*v2 <= 21*v2; live v2 range:', min(live_v2), max(live_v2))
    print('Number of zero-numerator states:', nonzero.count(0))
    assert Fraction(5*22, 9) < 13

    # These two exact comparisons prove the required block inequality for
    # every h>=1 after raising the first one to the hth power.
    assert Fraction(21, 25)**12 <= Fraction(91, 100)**20
    assert 16*13**3*Fraction(21, 25)**300 <= Fraction(91, 100)**400
    print('Both rational block-count inequalities passed')
    # beta<19/20<H(3/8)<H((3-sqrt(5))/2), without rounded comparisons.
    assert 91**20 < 20**20 * 5**19
    assert 2**82 > 3**15 * 5**25
    # The global G corollary uses beta<33/35<H(4/11).
    assert 91**35 < 20**35 * 5**33
    assert 11**385 > 2**363 * 4**140 * 7**245
    print('Exact entropy-gap inequalities passed')

    beta, kappa = log(Fraction(91, 20), 5), 5*log(Fraction(100, 91), 5)
    print('beta =', format(beta, '.15f'), '; kappa =', format(kappa, '.15f'))
    entropy = lambda t: -t*log(t, 2)-(1-t)*log(1-t, 2)
    eta = Fraction(11, 15)*entropy(Fraction(4, 11))
    print('global G exceptional exponent eta =', format(eta, '.15f'))
    for length in [839, 840, 1000, 10000, 100000, 1000000, 100000000]:
        a = a_for_digits(length)
        assert a == 0 or 4*a*precision_parameters(a)[2] <= length
        assert 4*max(2, a+1)*precision_parameters(max(2, a+1))[2] > length
        print('base-5 prefix length', length, 'certified precision', a)

    if args.json:
        data = {
            'modulus': 5,
            'basis_states': [ids[s] for s in basis],
            'state_count': len(states),
            'states': [{'polynomial': list(poly), 'carry': carry} for poly, carry in states],
            'digit_transitions': graph,
            'nonzero_indicator': nonzero,
            'v2': v2,
            'Mv2': v3,
            'componentwise_inequality': '5 M v2 <= 21 v2',
            'live_v2_range': [min(live_v2), max(live_v2)],
            'basis_killing_word_lsf': [0, 3],
            'rational_inequalities': [
                '(21/25)^12 <= (91/100)^20',
                '16*13^3*(21/25)^300 <= (91/100)^400',
                '91^20 < 20^20*5^19',
                '2^82 > 3^15*5^25',
                '91^35 < 20^35*5^33',
                '11^385 > 2^363*4^140*7^245',
            ],
        }
        args.json.write_text(json.dumps(data, indent=2)+'\n')
        print('Saved certificate:', args.json)


if __name__ == '__main__':
    main()
