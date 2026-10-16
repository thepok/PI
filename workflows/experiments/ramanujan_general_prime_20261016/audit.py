#!/usr/bin/env python3
"""Exact low-precision checks for the proposed general-prime extension.

No global Frobenius comparison is checked here.  The coefficient calculation
uses the separately proved facts G_p-1 in p^3*x^3*Z_p<x> and B_p in p*Z_p<x>;
thus the G_p factor contributes zero modulo p^4.  All arithmetic is integer.
The direct cutoff checks independently use exact central binomial coefficients.
Standard library only.  This script writes no files.
Repository command:
    python3 workflows/experiments/ramanujan_general_prime_20261016/audit.py
"""
from math import comb


def valuation(n, p):
    assert n
    e = 0
    while n % p == 0:
        n //= p
        e += 1
    return e


def multiply(a, b, modulus):
    out = [0] * 4
    for i, ai in enumerate(a):
        for j, bj in enumerate(b):
            if i + j < 4:
                out[i + j] = (out[i + j] + ai * bj) % modulus
    return out


def log_power(p):
    modulus = p**4
    work = p**6
    z = (pow(256, p - 1, work) - 1) % work
    answer = 0
    for j in range(1, 9):
        e = valuation(j, p)
        term = pow(z, j, work)
        assert term % p**e == 0
        answer += (-1)**(j + 1) * (term // p**e) * pow(j // p**e, -1, modulus)
    return answer % modulus


def forcing_mod_p4(p):
    modulus = p**4
    product = [1, 0, 0, 0]
    block = [0, 0, 0, 0]
    for a in range(p):
        term = multiply([6*a + 1, 6*p], product, modulus)
        block = [(x + y) % modulus for x, y in zip(block, term)]
        if a < p - 1:
            numerator = [comb(3, j)*(2*a + 1)**(3-j)*(2*p)**j for j in range(4)]
            denominator = [(-1)**j*comb(j+2, 2)*p**j*pow(a+1, -j-3, modulus)
                           for j in range(4)]
            ratio = [x*pow(32, -1, modulus) % modulus
                     for x in multiply(numerator, denominator, modulus)]
            product = multiply(product, ratio, modulus)
    assert all(x % p == 0 for x in block), (p, block)
    ell = -log_power(p) % modulus
    exponential = [1, ell, ell**2*pow(2, -1, modulus) % modulus,
                   ell**3*pow(6, -1, modulus) % modulus]
    raw = multiply(exponential, block, modulus)
    character = (-1)**((p-1)//2)
    raw[0] = (raw[0] - character*p) % modulus
    raw[1] = (raw[1] - 6*character*p) % modulus
    return raw


def euler_number(n):
    values = [0] * (n+1)
    values[0] = 1
    for j in range(2, n+1, 2):
        values[j] = -sum(comb(j, k)*values[k] for k in range(0, j, 2))
    return values[n]


def direct_cutoff(p, n):
    central = comb(2*n, n)
    divisor_val = 3 + 3*valuation(n, p) + 3*valuation(central, p)
    modulus = p**(divisor_val + 1)
    inverse256 = pow(256, -1, modulus)
    power = 1
    small = large = 0
    for j in range(p*n):
        term = (6*j + 1)*pow(comb(2*j, j), 3, modulus)*power % modulus
        large = (large + term) % modulus
        if j < n:
            small = (small + term) % modulus
        power = power*inverse256 % modulus
    numerator = (large - (-1)**((p-1)//2)*p*small) % modulus
    assert numerator % p**divisor_val == 0, (p, n, "divisibility")
    denominator_unit = (n // p**valuation(n, p))**3
    denominator_unit *= (central // p**valuation(central, p))**3
    denominator_unit *= pow(256, -n, p)
    answer = (numerator // p**divisor_val)*pow(denominator_unit, -1, p) % p
    return answer


def main():
    primes = [p for p in range(5, 100) if all(p % d for d in range(2, int(p**0.5)+1))]
    rows = []
    for p in primes:
        raw = forcing_mod_p4(p)
        assert all(x % p**3 == 0 for x in raw), (p, raw)
        normalized = [x // p**3 for x in raw]
        predicted = -32*euler_number(p-3) % p
        assert predicted != 0, (p, "zero Euler constant")
        image = [predicted*x*pow(32, -1, p) % p for x in [1, 6, 12, -24]]
        assert normalized == image, (p, normalized, image)
        rows.append((p, predicted))
    checked = 0
    for p in [5, 7, 11, 13, 17]:
        cutoffs = sorted(set([1, 2, 3, (p+1)//2, p-1, p, p+1, p*p-1, p*p]))
        predicted = -32*euler_number(p-3) % p
        for n in cutoffs:
            assert direct_cutoff(p, n) == predicted, (p, n)
            checked += 1
    print({"coefficient_primes": len(rows), "prime_constants": rows,
           "direct_cutoffs": checked,
           "status": "exact finite checks; no global comparison certification"})


if __name__ == "__main__":
    main()
