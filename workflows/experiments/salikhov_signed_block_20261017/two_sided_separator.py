#!/usr/bin/env python3
"""Exact finite checks for the two-sided Thue--Morse precision separator."""

import argparse
from fractions import Fraction
from math import gcd
import json
from pathlib import Path


def valuation(value, prime):
    assert value
    value = abs(value)
    depth = 0
    while value % prime == 0:
        value //= prime
        depth += 1
    return depth


def thue_morse_interval(digits):
    numerator = 0
    for index in range(1, digits + 1):
        numerator = 10 * numerator + index.bit_count() % 2
    denominator = 10 ** digits
    lower = Fraction(numerator, denominator)
    return lower, lower + Fraction(1, 9 * denominator)


def common_convergents(lower, upper):
    p0, p1, q0, q1 = 0, 1, 1, 0
    result = []
    while True:
        a = lower.numerator // lower.denominator
        if a != upper.numerator // upper.denominator:
            return result
        p, q = a * p1 + p0, a * q1 + q0
        result.append((p, q))
        p0, p1, q0, q1 = p1, p, q1, q
        lower, upper = lower - a, upper - a
        if not lower or not upper:
            return result
        lower, upper = 1 / upper, 1 / lower


def construct(k, minimum_depth, lower, upper, convergents):
    threshold = max(5 ** (100 * (k + 1)), 2 ** 200, 2 ** (2 * minimum_depth))
    for index in range(1, len(convergents) - 1):
        p, q = convergents[index]
        pp, qp = convergents[index - 1]
        _, qn = convergents[index + 1]
        if q >= threshold and qp ** 100 >= q ** 99 and qn ** 100 <= q ** 101:
            break
    else:
        raise ValueError('Increase --digits to reach a certified suitable convergent')
    h = (q.bit_length() - 1) // 2
    two, five = 2 ** h, 5 ** (k + 1)
    modulus = two * five
    assert modulus ** 100 <= q ** 51
    target_p = two * pow(two, -1, five) % modulus
    target_q = (5 ** k + five * ((1 - 5 ** k) * pow(five, -1, two) % two)) % modulus
    determinant = p * qp - pp * q
    assert determinant in (-1, 1)
    a0 = determinant * (qp * target_p - pp * target_q) % modulus or modulus
    b0 = determinant * (-q * target_p + p * target_q) % modulus or modulus
    boost = (qn + q - 1) // q + 2
    choices = [(a0 + boost * modulus, b0), (a0, b0 + modulus)]
    rows = []
    for a, b in choices:
        assert max(a, b) ** 100 <= (5 * modulus) ** 100 * q
        raw_p, raw_q = a * p + b * pp, a * q + b * qp
        assert raw_p % two == 0 and raw_p % five == 1
        assert raw_q % two == 1 and raw_q % five == 5 ** k
        assert gcd(gcd(raw_p, raw_q), 10) == 1
        assert raw_q ** 20 <= q ** 31
        value = Fraction(raw_p, raw_q)
        side = 'below' if value < lower else 'above' if value > upper else None
        assert side is not None
        numerator, denominator = value.numerator, value.denominator
        depth = valuation(numerator, 2)
        assert denominator % 2 == 1 and valuation(denominator, 5) == k
        assert depth >= h >= minimum_depth
        assert 2 ** (4 * depth) >= denominator
        error = max(abs(lower - value), abs(upper - value))
        assert error ** 5 * denominator ** 6 <= 1
        rows.append({'side': side, 'numerator_two_depth': depth,
                     'denominator_five_depth': k, 'denominator_bits': denominator.bit_length(),
                     'certified_error_at_most_Q_minus_six_fifths': True,
                     'certified_two_depth_at_least_quarter_log2Q': True})
    assert {r['side'] for r in rows} == {'below', 'above'}
    return {'k': k, 'continued_fraction_index': index, 'convergent_denominator_bits': q.bit_length(),
            'H': h, 'prescribed_minimum_two_depth': minimum_depth,
            'current_column_boost': boost, 'fractions': sorted(rows, key=lambda r: r['side'])}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--digits', type=int, default=1024)
    parser.add_argument('--depths', type=int, default=5)
    parser.add_argument('--minimum-two-depth', type=int, default=200)
    parser.add_argument('--json', type=Path)
    args = parser.parse_args()
    if args.digits < 1 or args.depths < 1 or args.minimum_two_depth < 0:
        parser.error('Require positive digit/depth counts and nonnegative numerator depth')
    lower, upper = thue_morse_interval(args.digits)
    cf = common_convergents(lower, upper)
    report = {'label': 'experiment', 'avoided_digit': 2,
              'certified_decimal_digits': args.digits, 'common_continued_fraction_length': len(cf),
              'cases': [construct(k, args.minimum_two_depth, lower, upper, cf)
                        for k in range(1, args.depths + 1)],
              'scope': 'Finite exact checks; arbitrary prescribed depths use the accompanying infinite proof sketch.'}
    output = json.dumps(report, indent=2) + '\n'
    if args.json:
        args.json.write_text(output, encoding='utf-8')
    print(output, end='')


if __name__ == '__main__':
    main()
