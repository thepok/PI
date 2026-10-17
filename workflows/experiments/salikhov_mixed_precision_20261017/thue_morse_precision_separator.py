#!/usr/bin/env python3
"""Exact finite checks for a two/five-adic Thue--Morse word-avoider.

The infinite existence argument uses the exponent-two theorem. Every
finite case here is checked directly from a rigorous decimal interval,
common continued-fraction digits, exact CRT, and rational inequalities.
"""

import argparse
from fractions import Fraction
import json
from pathlib import Path


def integer_valuation(value, prime):
    assert value
    value = abs(value)
    answer = 0
    while value % prime == 0:
        value //= prime
        answer += 1
    return answer


def thue_morse_interval(digits):
    numerator = 0
    for index in range(1, digits+1):
        numerator = 10*numerator+index.bit_count()%2
    denominator = 10**digits
    lower = Fraction(numerator, denominator)
    upper = lower+Fraction(1, 9*denominator)
    return lower, upper


def common_convergents(lower, upper):
    p0, p1, q0, q1 = 0, 1, 1, 0
    output = []
    while True:
        digit_lower = lower.numerator//lower.denominator
        digit_upper = upper.numerator//upper.denominator
        if digit_lower != digit_upper:
            return output
        digit = digit_lower
        p, q = digit*p1+p0, digit*q1+q0
        output.append((p, q))
        p0, p1, q0, q1 = p1, p, q1, q
        lower -= digit
        upper -= digit
        if lower == 0 or upper == 0:
            return output
        lower, upper = 1/upper, 1/lower


def construct_case(k, lower, upper, convergents):
    threshold = max(5**(20*(k+1)), 2**40)
    for index in range(1, len(convergents)):
        p, q = convergents[index]
        previous_p, previous_q = convergents[index-1]
        if q >= threshold and previous_q**10 >= q**9:
            break
    else:
        raise ValueError('Increase the number of certified Thue--Morse digits')
    h = (q.bit_length()-1)//2
    two, five = 2**h, 5**(k+1)
    modulus = two*five
    target_p = two*pow(two, -1, five) % modulus
    target_q = (5**k+five*((1-5**k)*pow(five, -1, two) % two)) % modulus
    determinant = p*previous_q-previous_p*q
    assert determinant in (-1, 1)
    a = determinant*(previous_q*target_p-previous_p*target_q) % modulus
    b = determinant*(-q*target_p+p*target_q) % modulus
    a = a or modulus
    b = b or modulus
    assert 1 <= a <= modulus and 1 <= b <= modulus
    mixed_p, mixed_q = a*p+b*previous_p, a*q+b*previous_q
    assert mixed_p % two == 0 and mixed_p % five == 1
    assert mixed_q % two == 1 and mixed_q % five == 5**k
    approximation = Fraction(mixed_p, mixed_q)
    numerator, denominator = approximation.numerator, approximation.denominator
    assert denominator % 2 == 1
    assert integer_valuation(denominator, 5) == k
    two_depth = integer_valuation(numerator, 2)
    assert two_depth >= h
    assert 2**(4*two_depth) >= denominator
    error = max(abs(lower-approximation), abs(upper-approximation))
    assert error**5*denominator**6 <= 1
    return {'k': k, 'continued_fraction_index': index,
            'convergent_denominator_bits': q.bit_length(), 'H': h,
            'reduced_numerator_two_depth': two_depth,
            'reduced_denominator_five_depth': k,
            'reduced_denominator_bits': denominator.bit_length(),
            'exact_error_bound_Q_minus_six_fifths': True,
            'exact_two_depth_at_least_quarter_log2Q': True}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--digits', type=int, default=512)
    parser.add_argument('--depths', type=int, default=8)
    parser.add_argument('--json', type=Path)
    args = parser.parse_args()
    if args.digits < 1 or args.depths < 1:
        parser.error('Require positive digit and depth counts')
    lower, upper = thue_morse_interval(args.digits)
    convergents = common_convergents(lower, upper)
    report = {'status': 'experiment; infinite existence is in the accompanying proof sketch',
              'avoided_digit': 2, 'certified_decimal_digits': args.digits,
              'common_continued_fraction_length': len(convergents),
              'cases': [construct_case(k, lower, upper, convergents)
                        for k in range(1, args.depths+1)]}
    output = json.dumps(report, indent=2)+'\n'
    if args.json:
        args.json.write_text(output, encoding='utf-8')
    print(output, end='')


if __name__ == '__main__':
    main()
