#!/usr/bin/env python3
"""Exact signed-coefficient lattice audit for two actual-pi target multipliers.

Label: experiment. Standard library only; no pi digits or floating point.
The source recurrence and the proof of the lattice classification are in README.md.
This is not a proof of an unbounded decimal return. Run without Python -O.
"""
from __future__ import annotations

import argparse
from dataclasses import dataclass
from fractions import Fraction as F
from functools import reduce
from itertools import product
import hashlib
import json
from math import comb, gcd, lcm
from pathlib import Path


def recurrence(n: int) -> tuple[int, int, int, int]:
    return (
        -1024*(2*n+5)*(2*n+3)*(2*n+1)*(n+2)*(n+1)
        *(559455*n**4+5637736*n**3+21207869*n**2+35294652*n+21926016),
        64*(2*n+5)*(2*n+3)*(n+2)
        *(1208982255*n**6+14601112006*n**5+71554462078*n**4
          +181444545414*n**3+250049018747*n**2+176898555884*n+50159702880),
        -6*(2*n+5)
        *(440102548665*n**8+7075613606958*n**7+49182254436312*n**6
          +192978557313766*n**5+467319046780891*n**4+714892923466956*n**3
          +674376299494052*n**2+358497976451216*n+82191375084672),
        3*(4*n+11)*(3*n+8)*(3*n+7)*(4*n+9)*(n+3)
        *(559455*n**4+3399916*n**3+7651391*n**2+7554302*n+2760952),
    )


def source_pairs(limit: int) -> list[tuple[F, int]]:
    a = [F(0), -F(11272, 3), -F(6156093056, 105)]
    b = [F(1, 4), F(1196), F(18662336)]
    for n in range(max(0, limit-2)):
        r = recurrence(n)
        a.append(-sum(r[j]*a[n+j] for j in range(3))/r[3])
        b.append(-sum(r[j]*b[n+j] for j in range(3))/r[3])
    result = []
    for n in range(limit+1):
        scale = F(2)**(2-5*n//2)
        q = scale*b[n]
        assert q.denominator == 1 and q > 0
        result.append((scale*a[n], int(q)))
    return result


def direct_q(n: int) -> int:
    # Independent root-coordinate extraction; see PR18's fixed_coefficient.
    p = [1]
    for _ in range(2*n):
        out = [0]*min(3*n+1, len(p)+5)
        for j, x in enumerate(p):
            for k, y in enumerate([2, -18, 67, -128, 125, -50]):
                if j+k < len(out):
                    out[j+k] += x*y
        p = out
    value = F((-1)**n*sum(x*comb(6*n-j, 3*n-j) for j, x in enumerate(p)),
              2**(n//2))
    assert value.denominator == 1
    return int(value)


def bezout(a: int, b: int) -> tuple[int, int, int]:
    aa, bb = abs(a), abs(b)
    x, y, u, v = 1, 0, 0, 1
    while bb:
        t = aa//bb
        aa, bb = bb, aa-t*bb
        x, u = u, x-t*u
        y, v = v, y-t*v
    return aa, x*(-1 if a < 0 else 1), y*(-1 if b < 0 else 1)


def vector_sum(a: int, u: list[int], b: int, v: list[int]) -> list[int]:
    return [a*x+b*y for x, y in zip(u, v)]


def evaluate(v: list[int], columns: list[tuple[int, int]]) -> tuple[int, int]:
    return tuple(sum(a*c[j] for a, c in zip(v, columns)) for j in range(2))


@dataclass
class IntegralLattice:
    G: int
    p0: int
    M: int
    q_witness: list[int]
    p_witness: list[int]


def classify(columns: list[tuple[int, int]], D: int) -> IntegralLattice:
    """Classify all (Q,P) with (Q,-D*P) in the integer column span.

    Returns exactly Z*(G,p0) + Z*(0,M), with explicit column witnesses.
    Positive first-column coordinates and rank two are required.
    """
    if D <= 0 or len(columns) < 2 or any(q <= 0 for q, _ in columns):
        raise ValueError('Require D>0 and at least two columns with q>0')
    count = len(columns)
    g, A = columns[0]
    d, u, v = 0, [1]+[0]*(count-1), [0]*count
    for i, (q, a) in enumerate(columns[1:], 1):
        new_g, s, t = bezout(g, q)
        ei = [int(j == i) for j in range(count)]
        kernel = vector_sum(q//new_g, u, -g//new_g, ei)
        k = (q//new_g)*A-(g//new_g)*a
        new_d, ss, tt = bezout(d, k)
        new_v = vector_sum(ss, v, tt, kernel)
        new_u = vector_sum(s, u, t, ei)
        new_A = s*A+t*a
        if new_d:
            quotient, new_A = divmod(new_A, new_d)
            new_u = vector_sum(1, new_u, -quotient, new_v)
        g, A, d, u, v = new_g, new_A, new_d, new_u, new_v
    if not d:
        raise ValueError('Rank-one source block')
    assert evaluate(u, columns) == (g, A)
    assert evaluate(v, columns) == (0, d)
    assert all(q % g == 0 and (a-A*(q//g)) % d == 0 for q, a in columns)
    # Independent determinantal-divisor identity, not used by the construction.
    minors = (q*a2-q2*a for i, (q, a) in enumerate(columns)
              for q2, a2 in columns[i+1:])
    assert g*d == abs(reduce(gcd, minors, 0))
    e = gcd(D, d)
    t = e//gcd(A, e)
    G, M = g*t, d//e
    p0 = (-(A*t//e)*pow(D//e, -1, M)) % M if M > 1 else 0
    k = (-D*p0-A*t)//d
    assert -D*p0-A*t == k*d
    qw = vector_sum(t, u, k, v)
    pw = [-(D//e)*x for x in v]
    assert evaluate(qw, columns) == (G, -D*p0)
    assert evaluate(pw, columns) == (0, -D*M)
    return IntegralLattice(G, p0, M, qw, pw)


def small_lattice_tests() -> dict:
    matrices = combinations = 0
    for q, r, a, b, D in product(range(1, 4), range(1, 4),
                                range(-2, 3), range(-2, 3), range(1, 5)):
        if q*b == r*a:
            continue
        lat = classify([(q, a), (r, b)], D)
        matrices += 1
        for u, v in product(range(-2, 3), repeat=2):
            Q, A = u*q+v*r, u*a+v*b
            if A % D:
                continue
            P = -A//D
            assert Q % lat.G == 0
            assert (P-lat.p0*(Q//lat.G)) % lat.M == 0
            combinations += 1
    return {'rank_two_toy_lattices': matrices,
            'integral_toy_combinations_checked': combinations,
            'basis_witnesses_and_minor_gcd_checked': True}


def measure_tests() -> dict:
    """Exact finite tests for |{x in [3,4]: dist(Q*x,M*Z)<1}| <= 18/M."""
    cases = 0
    for exponent in range(2, 13):
        M = 2**exponent
        for Q in range(1, 257):
            measure = F(0)
            for a in range(max(0, (3*Q-1)//M), (4*Q+1)//M+1):
                left = max(F(3), F(M*a-1, Q))
                right = min(F(4), F(M*a+1, Q))
                measure += max(F(0), right-left)
            assert measure <= F(18, M)
            if 4*Q < M:
                assert measure == 0
            cases += 1
    return {'exact_interval_measure_cases': cases}


def atan_fixed(q: int, scale: int) -> tuple[int, int]:
    center, j, power = 0, 0, q
    while True:
        term = scale//((2*j+1)*power)
        if not term:
            return center, j+1
        center += term if j % 2 == 0 else -term
        j += 1
        power *= q*q


def pi_enclosure(bits: int) -> tuple[int, int, int]:
    S = 1 << bits
    a, ea = atan_fixed(5, S)
    b, eb = atan_fixed(239, S)
    C, E = 16*a-4*b, 16*ea+4*eb
    assert 3*S < C-E < C+E < 4*S
    return S, C, E


def scan(lat: IntegralLattice, shift: int, horizon: int,
         enclosure: tuple[int, int, int]) -> dict:
    S, C, E = enclosure
    modulus = lat.M*S
    r, power, allowed = C % modulus, 1, 0
    best = None
    second_low = None
    upper_min = None
    hits = []
    for h in range(1, horizon+1):
        power *= 10
        r = (10*r) % modulus
        if h < 2:
            continue
        Q = power-shift
        if Q % lat.G:
            continue
        allowed += 1
        p0 = lat.p0*(Q//lat.G) % lat.M
        residue = (r-shift*C-p0*S) % modulus
        distance = min(residue, modulus-residue)
        radius = E*Q
        assert radius < S  # The enclosure still resolves unit-scale distances.
        low, high = max(0, distance-radius), distance+radius
        if best is None or low < best[0]:
            if best is not None:
                second_low = best[0] if second_low is None else min(second_low, best[0])
            best = low, high, h
        else:
            second_low = low if second_low is None else min(second_low, low)
        upper_min = high if upper_min is None else min(upper_min, high)
        assert high < S or low > S, 'Increase precision to resolve the unit test'
        if high < S:
            hits.append(h)
    result = {'multiplier': f'10^h-{shift}', 'h_range': [2, horizon],
              'attainable_multiplier_count': allowed,
              'unit_error_possible_h': hits}
    if best is not None:
        low, high, h = best
        assert upper_min == high
        assert second_low is None or high < second_low, 'Minimum not isolated'
        digits = 10**12
        result.update({'minimum_error_lower_numerator': low*digits//S,
                       'minimum_error_upper_numerator': (high*digits+S-1)//S,
                       'error_bound_denominator': digits, 'best_h': h})
    return result


def witness_at_best(lat: IntegralLattice, columns: list[tuple[int, int]], D: int,
                    h: int, shift: int, enclosure: tuple[int, int, int]) -> int:
    S, C, _ = enclosure
    Q = 10**h-shift
    u = Q//lat.G
    v = (Q*C-lat.p0*u*S+(lat.M*S)//2)//(lat.M*S)
    P = lat.p0*u+lat.M*v
    weights = vector_sum(u, lat.q_witness, v, lat.p_witness)
    assert evaluate(weights, columns) == (Q, -D*P)
    return sum(abs(w) for w in weights).bit_length()


def run(horizon: int) -> dict:
    pairs = source_pairs(127)
    for n in range(13):
        assert pairs[n][1] == direct_q(n)
    checks = {**small_lattice_tests(), **measure_tests()}
    bits = max(4096, 4*horizon+512)
    enclosure = pi_enclosure(bits)
    blocks = [(4, 4), (8, 8), (16, 4), (16, 8), (16, 16),
              (16, 64), (32, 16), (32, 32), (64, 16), (64, 64)]
    rows, cache = [], {}
    for first, count in blocks:
        selected = pairs[first:first+count]
        D = lcm(*(c.denominator for c, _ in selected))
        columns = [(q, int(D*c)) for c, q in selected]
        assert all((D*c).denominator == 1 for c, _ in selected)
        lat = classify(columns, D)
        S, C, E = enclosure
        positive = negative = 0
        for c, q in selected:
            center = c.numerator*S+q*C*c.denominator
            radius = q*E*c.denominator
            assert abs(center) > radius
            positive += center > radius
            negative += center < -radius
        row = {'source_indices_inclusive': [first, first+count-1],
               'positive_source_errors': positive, 'negative_source_errors': negative,
               'G': lat.G, 'p0': lat.p0, 'M': lat.M,
               'common_denominator_bits': D.bit_length(),
               'exact_basis_witnesses_verified': True, 'scans': []}
        rough = lat.G
        for p in (2, 5):
            while rough % p == 0:
                rough //= p
        row['all_h_ge_1_decimal_multiplier_excluded_by_rough_G'] = rough > 1
        row['all_h_ge_1_return_multiplier_excluded_by_five_dividing_G'] = lat.G % 5 == 0
        for shift in (0, 16):
            key = lat.G, lat.p0, lat.M, shift
            if key not in cache:
                cache[key] = scan(lat, shift, horizon, enclosure)
            result = dict(cache[key])
            if 'best_h' in result:
                result['constructed_best_witness_l1_bits'] = witness_at_best(
                    lat, columns, D, result['best_h'], shift, enclosure)
            row['scans'].append(result)
        rows.append(row)
    baseline = scan(IntegralLattice(1, 0, 1, [], []), 16, horizon, enclosure)
    # The full hit list is unnecessary for the unconstrained control.
    baseline['unit_error_possible_count'] = len(baseline.pop('unit_error_possible_h'))
    S, C, E = enclosure
    h = baseline['best_h']
    Q = 10**h-16
    P = (Q*C+S//2)//S
    baseline['nearest_integer_mod_1024'] = P % 1024
    baseline['nearest_integer_mod_262144'] = P % 262144
    baseline['signed_error_is_positive'] = Q*(C-E) > S*P
    if horizon == 4096:
        expected = [4, 4, 53940, 620, 4, 4, 28, 4, 36822656860, 4]
        assert [row['G'] for row in rows] == expected
        assert all(row['p0'] == 0 and row['M'] == 2**(2*first+2)
                   for row, (first, _) in zip(rows, blocks))
        assert baseline['best_h'] == 3723 and baseline['nearest_integer_mod_1024'] == 627
        assert all(not sc['unit_error_possible_h'] for row in rows[1:] for sc in row['scans'])
    return {'label': 'experiment', 'source_pi_commit': '2ab024737878cd9f1567cc296ef53f051a5ff10b',
            'source_pr18_commit': 'f5794f090c9025a8bc92ff426d68f5afd220d434',
            'checks': {**checks, 'independent_multiplier_checks': 13,
                       'source_recurrence_max_index': 127, 'pi_enclosure_bits': bits,
                       'pi_enclosure_halfwidth_integer': E},
            'blocks': rows, 'unconstrained_fixed_sixteen_control': baseline,
            'scope': ['All integer coefficient vectors are classified, with both signs allowed.',
                      'The 4096-shift comparison is finite and is not a V1 result.',
                      'Different source blocks or rational coefficient normalization are not excluded.',
                      'No independent agent review or Lean verification was performed in this pass.']}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--horizon', type=int, default=4096)
    parser.add_argument('--json', type=Path)
    parser.add_argument('--check', type=Path)
    args = parser.parse_args()
    if not __debug__:
        parser.error('Assertions must be enabled; do not run with -O')
    if args.horizon < 2:
        parser.error('--horizon must be at least two')
    if args.json and args.check:
        parser.error('Choose --json or --check, not both')
    result = run(args.horizon)
    text = json.dumps(result, indent=2)+'\n'
    if args.check:
        if args.check.read_text(encoding='utf-8') != text:
            raise SystemExit('FAIL: generated certificate differs from tracked certificate')
        print('PASS: exact lattice witnesses, target scans, and certificate identity')
    elif args.json:
        args.json.parent.mkdir(parents=True, exist_ok=True)
        args.json.write_text(text, encoding='utf-8')
        print(hashlib.sha256(text.encode()).hexdigest())
    else:
        print(text, end='')


if __name__ == '__main__':
    main()
