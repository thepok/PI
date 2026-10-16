#!/usr/bin/env python3
"""Exact finite checks for the Ramanujan five-adic metric refinement.

No floating-point arithmetic and no pi digit data. This is an experiment,
not a proof of the infinite interpolation theorem. Standard library only.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
from math import comb


def v5(n: int) -> int:
    if n == 0:
        raise ValueError("valuation of zero was not requested")
    n = abs(n)
    result = 0
    while n % 5 == 0:
        result += 1
        n //= 5
    return result


def poly_add(a: list[int], b: list[int], modulus: int) -> list[int]:
    out = [0] * max(len(a), len(b))
    for i, c in enumerate(a):
        out[i] += c
    for i, c in enumerate(b):
        out[i] += c
    return [c % modulus for c in out]


def poly_mul(a: list[int], b: list[int], modulus: int) -> list[int]:
    out = [0] * (len(a) + len(b) - 1)
    for i, c in enumerate(a):
        for j, d in enumerate(b):
            out[i + j] += c * d
    return [c % modulus for c in out]


def check_certificate() -> None:
    # These are the raw 5^7 representatives obtained from the repository's
    # coefficientwise expansion, not interpolated from values of U_N.
    modulus = 5**7
    h = [1, 3030, 59200, 38000, 7500, 47500, 50000, 46875]
    b = [77005, 49380, 47225, 2375, 0, 3125]
    forcing_raw = poly_add(poly_mul(h, b, modulus), [-5, -30], modulus)
    assert all(c % 125 == 0 for c in forcing_raw)
    forcing = [c // 125 for c in forcing_raw]
    p = [512, 100, 550, 425]
    shifted = [sum(c * comb(j, i) for j, c in enumerate(p) if j >= i)
               for i in range(len(p))]
    first = [c * pow(32, -1, 625) % 625
             for c in poly_mul([1, 6, 12, 8], shifted, 625)]
    lp = poly_add(first, [0, 0, 0] + [-c for c in p], 625)
    forcing += [0] * max(0, len(lp) - len(forcing))
    lp += [0] * max(0, len(forcing) - len(lp))
    assert forcing == lp
    # The divided differences are constant 20 mod 25 on the exceptional
    # residue ball, and the reduction mod 5 permutes the five residue balls.
    v = lambda x: (20 + 4*x + 22*x*x + 17*x*x*x)
    assert [v(a) % 5 for a in range(5)] == [0, 3, 2, 4, 1]
    assert v(3) % 25 == 14
    for x in range(3, 25, 5):
        for y in range(3, 25, 5):
            quotient = 4 + 22*(x+y) + 17*(x*x+x*y+y*y)
            assert quotient % 25 == 20


def residues(max_n: int, precision: int) -> tuple[list[int], int]:
    central = [comb(2*n, n) for n in range(max_n + 1)]
    losses = [0] + [3 + 3*v5(n) + 3*v5(central[n])
                    for n in range(1, max_n + 1)]
    work_precision = precision + max(losses) + 1
    work_modulus = 5**work_precision
    output_modulus = 5**precision
    sums = [0] * (5*max_n + 1)
    inv256 = pow(256, -1, work_modulus)
    inverse_power = 1
    c = 1
    for n in range(5*max_n):
        term = (6*n+1) * pow(c % work_modulus, 3, work_modulus)
        sums[n+1] = (sums[n] + term * inverse_power) % work_modulus
        c = c * 2 * (2*n+1) // (n+1)
        inverse_power = inverse_power * inv256 % work_modulus
    result = [0]
    for n in range(1, max_n + 1):
        d = (sums[5*n] - 5*sums[n]) % work_modulus
        ppart = 5**losses[n]
        assert d % ppart == 0
        unit = (n // 5**v5(n)) * (central[n] // 5**v5(central[n]))
        u = d // ppart * pow(256, n, output_modulus)
        u = u * pow(pow(unit, 3, output_modulus), -1, output_modulus)
        result.append(u % output_modulus)
    return result, work_precision


def exact_initial_values(values: list[int], precision: int, count: int) -> None:
    sums = [Fraction(0)]
    for n in range(5*count):
        sums.append(sums[-1] + Fraction((6*n+1)*comb(2*n,n)**3, 256**n))
    modulus = 5**precision
    for n in range(1, count+1):
        b = Fraction(comb(2*n,n)**3, 256**n)
        u = (sums[5*n]-5*sums[n]) / (125*n**3*b)
        assert u.denominator % 5 != 0
        observed = u.numerator * pow(u.denominator, -1, modulus) % modulus
        assert observed == values[n]


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-n", type=int, default=1250)
    parser.add_argument("--precision", type=int, default=10)
    args = parser.parse_args()
    if args.max_n < 2 or args.precision < 4:
        raise ValueError("Need max-n >= 2 and precision >= 4")
    check_certificate()
    values, working = residues(args.max_n, args.precision)
    exact_initial_values(values, args.precision, min(30, args.max_n))
    pairs = 0
    exception_pairs = 0
    for n in range(1, args.max_n+1):
        assert values[n] % 25 == 12
        normalized = (values[n]-12) // 25
        if n % 5 == 3:
            assert normalized % 25 == 14
        for m in range(1, n):
            exceptional = m % 5 == n % 5 == 3
            expected = 2 + v5(n-m) + exceptional
            if expected >= args.precision:
                raise ValueError("Increase precision to resolve every tested pair")
            difference = values[n] - values[m]
            assert difference != 0, (m, n, "unexpected equality")
            actual = v5(difference)
            assert actual == expected, (m, n, actual, expected)
            pairs += 1
            exception_pairs += exceptional
    print("PASS: cubic coefficient identity modulo 5^4 and divided differences")
    print(f"PASS: N=1..{args.max_n}; working modulus 5^{working}; U output 5^{args.precision}")
    print(f"PASS: {pairs} exact pairwise valuations, including {exception_pairs} exceptional pairs")
    print(f"PASS: independent exact rational values for N=1..{min(30,args.max_n)}")
    print("U residues modulo 625 at N=1..25:", [u % 625 for u in values[1:26]])
    print("Status: experiment; the infinite result uses the separate proof sketch.")


if __name__ == "__main__":
    main()
