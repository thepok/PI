"""Exact finite period certificates for the first three mixed fractions.

Label: experiment. Uses Python's standard library only. The recurrence and
mixed construction are copied from the tracked PR16 source at
2f49f0370b2dc1c61488b96cb45a8b4353821c86:
workflows/experiments/salikhov_mixed_precision_20261017/mixed_branch.py.

This checks three finite instances; it proves no all-index order bound and
no decimal occurrence for pi. No external pi digits are inputs.
"""

import json
from fractions import Fraction
from math import gcd, isqrt, lcm


def recurrence_coefficients(n):
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


def recurrence_pairs(bound):
    a = [Fraction(0), -Fraction(11272, 3), -Fraction(6156093056, 105)]
    b = [Fraction(1, 4), Fraction(1196), Fraction(18662336)]
    for n in range(min(3, bound+1)):
        yield n, a[n], b[n]
    for n in range(max(0, bound-2)):
        coefficients = recurrence_coefficients(n)
        next_a = -sum(coefficients[j]*a[j] for j in range(3))/coefficients[3]
        next_b = -sum(coefficients[j]*b[j] for j in range(3))/coefficients[3]
        a = a[1:]+[next_a]
        b = b[1:]+[next_b]
        yield n+3, next_a, next_b


def floor_log_five(value):
    exponent = 0
    while value >= 5:
        value //= 5
        exponent += 1
    return exponent


def arctan_interval(reciprocal, terms):
    """Alternating-series bounds on atan(1/reciprocal), exactly rational."""
    assert reciprocal > 1 and terms > 0
    partial = sum((Fraction((-1)**j, (2*j+1)*reciprocal**(2*j+1))
                   for j in range(terms)), Fraction(0))
    adjacent = partial + Fraction((-1)**terms,
                                  (2*terms+1)*reciprocal**(2*terms+1))
    return min(partial, adjacent), max(partial, adjacent)


def pi_interval():
    # Machin's identity pi = 16 atan(1/5) - 4 atan(1/239).
    lower5, upper5 = arctan_interval(5, 320)
    lower239, upper239 = arctan_interval(239, 100)
    return 16*lower5-4*upper239, 16*upper5-4*lower239


def error_exponent(rational, lower_pi, upper_pi):
    """Certify E with 10^(-E-1) < |rational-pi| < 10^(-E)."""
    if rational < lower_pi:
        low, high, side = lower_pi-rational, upper_pi-rational, 'below'
    else:
        assert rational > upper_pi, 'Pi enclosure is not yet narrow enough'
        low, high, side = rational-upper_pi, rational-lower_pi, 'above'
    exponent, threshold = 0, Fraction(1)
    while high < threshold/10:
        exponent += 1
        threshold /= 10
    assert threshold/10 < low <= high < threshold
    return exponent, side


def primes_through(n):
    sieve = bytearray(b'\x01') * (n + 1)
    sieve[:2] = b'\x00\x00'
    for p in range(2, isqrt(n) + 1):
        if sieve[p]:
            sieve[p * p::p] = b'\x00' * ((n - p * p) // p + 1)
    return [p for p in range(2, n + 1) if sieve[p]]


def order_ten_prime_power(p, exponent):
    modulus = p ** exponent
    phi = (p - 1) * p ** (exponent - 1)
    order = phi
    for ell in primes_through(p):
        while order % ell == 0 and pow(10, order // ell, modulus) == 1:
            order //= ell
    assert pow(10, order, modulus) == 1
    return order


def main():
    rows = [{'k': k, 'n': (5**k+1)//2,
             'r': 1 << (((5**k+1)//2-1).bit_length())}
            for k in range(1, 4)]
    needed = {row[key] for row in rows for key in ('n', 'r')}
    pairs = {}
    for j, a, b in recurrence_pairs(max(needed)):
        if j in needed:
            scale = Fraction(1, 2 ** (5 * j // 2 - 2))
            assert (scale*b).denominator == 1 and scale*b > 0
            pairs[j] = (scale*a, int(scale*b))
    lower_pi, upper_pi = pi_interval()
    output = []
    for row in rows:
        k, n, r = (row[key] for key in ('k', 'n', 'r'))
        cn, qn = pairs[n]
        cr, qr = pairs[r]
        exponent_five = k+floor_log_five(4*r)+1
        base_weight = 5**exponent_five
        assert qr % 8 == 4  # r is a power of two, and v_2(q_r)=2.
        choice = 1 if (qn+base_weight*qr) % 16 else 3
        weight = choice*base_weight
        rational = -(cn + weight * cr) / (qn + weight * qr)
        p, q = rational.numerator, rational.denominator
        assert q % 5 ** k == 0
        cofactor = q // 5 ** k
        assert cofactor > 1 and gcd(cofactor, 10) == 1
        error_power, side = error_exponent(rational, lower_pi, upper_pi)
        generous_horizon = 6 * max(n, r)
        residue = 1
        first_return = None
        for j in range(1, generous_horizon + 1):
            residue = residue * 10 % cofactor
            if residue == 1:
                first_return = j
                break
        factors, lower_order = [], 1
        remaining = cofactor
        for ell in primes_through(1000):
            if remaining % ell == 0:
                exponent = 0
                while remaining % ell == 0:
                    remaining //= ell
                    exponent += 1
                order = order_ten_prime_power(ell, exponent)
                factors.append([ell, exponent, order])
                lower_order = lcm(lower_order, order)
        output.append({
            'k': k, 'n': n, 'r': r,
            'coefficient_choice': choice,
            'denominator_bits': q.bit_length(),
            'cofactor_bits': cofactor.bit_length(),
            'pi_side': side,
            'absolute_error_decimal_exponent': error_power,
            'absolute_error_certificate':
                '10^(-E-1) < |P/Q-pi| < 10^(-E), where E is the exponent above',
            'scanned_horizon': generous_horizon,
            'complete_period_within_scanned_horizon': first_return,
            'small_prime_power_factors_and_orders': factors,
            'proved_order_multiple': lower_order,
            'unfactored_cofactor_bits': remaining.bit_length(),
        })
    print(json.dumps(output, indent=2))


if __name__ == '__main__':
    main()
