#!/usr/bin/env python3
"""Exact finite audit of a proposed 5-adic regularity statement.

S_N = sum_{j=0}^{N-1} (6*j+1) * binom(2*j,j)^3 / 256^j.
U_N = 256^N*(S_{5N}-5*S_N)/(125*N^3*binom(2N,N)^3).

Candidate (NOT a theorem): U_N = 12 + 25*V(N), where V extends to a
1-Lipschitz map Z_5 -> Z_5. No decimal digits of pi are computed.
Only exact integer modular arithmetic is used. Python >= 3.8; no packages.
"""
from __future__ import annotations
import argparse


def v5(n: int) -> int:
    if n == 0:
        raise ValueError('v5(0) is not finite')
    n = abs(n)
    e = 0
    while n % 5 == 0:
        n //= 5
        e += 1
    return e


def audit(max_n: int, precision: int) -> None:
    if max_n < 1 or precision < 2:
        raise ValueError('Require max_n >= 1 and precision >= 2')
    central = [1] * (max_n + 1)
    for n in range(max_n):
        central[n+1] = central[n] * 2 * (2*n+1) // (n+1)
    exponents = [0] + [3 + 3*v5(n) + 3*v5(central[n])
                       for n in range(1, max_n+1)]
    # Precision lost in division is known in advance. Add one guard digit.
    working_precision = max(exponents) + precision + 1
    modulus = 5 ** working_precision
    inv256 = pow(256, -1, modulus)
    sums = [0] * (5*max_n + 1)
    c, invpower = 1, 1
    for j in range(5*max_n):
        # Reduce before cubing to avoid unnecessary huge intermediates.
        term = (6*j+1) * pow(c % modulus, 3, modulus) * invpower
        sums[j+1] = (sums[j] + term) % modulus
        c = c * 2 * (2*j+1) // (j+1)
        invpower = invpower * inv256 % modulus
    output_modulus = 5 ** precision
    residues = {}
    for n in range(1, max_n+1):
        d = (sums[5*n] - 5*sums[n]) % modulus
        e = exponents[n]
        if d % (5**e) != 0:
            raise AssertionError(f'Candidate integrality fails at N={n}')
        n_unit = n // 5**v5(n)
        c_unit = central[n] // 5**v5(central[n])
        unit_den = pow(n_unit, 3, output_modulus) * pow(c_unit, 3, output_modulus)
        u = ((d // 5**e) * pow(256, n, output_modulus)
             * pow(unit_den, -1, output_modulus)) % output_modulus
        if u % 25 != 12:
            raise AssertionError(f'U_N == 12 (mod 25) fails at N={n}: {u % 25}')
        residues[n] = u
        # A separately derived absolute congruence, weaker than the candidate:
        # S_{5N}-5S_N == 250*N^3*b_N (mod 625).
        rhs = 250 * n**3 * pow(central[n], 3, 625) * pow(pow(256,n,625), -1, 625)
        if (d-rhs) % 625 != 0:
            raise AssertionError(f'Absolute block congruence fails at N={n}')
    for r in range(precision-1):
        input_mod, value_mod = 5**r, 5**(r+2)
        seen = {}
        for n, u in residues.items():
            key = n % input_mod
            value = u % value_mod
            if key in seen and seen[key][1] != value:
                m, old = seen[key]
                raise AssertionError(
                    f'Lipschitz condition fails: N={n}, M={m}, '
                    f'N==M mod {input_mod}, but U_N={value}, U_M={old} mod {value_mod}')
            seen[key] = (n, value)
    print(f'PASS: N=1,...,{max_n}; working modulus 5^{working_precision}; U_N output modulus 5^{precision}.')
    print('PASS: U_N == 12 (mod 25), including all nonunit cutoff cases.')
    print(f'PASS: all truncated Lipschitz comparisons through 5^{precision}.')
    print('PASS: independently derived absolute block congruence modulo 625.')
    print('First ten U_N residues:', [(n, residues[n]) for n in range(1,min(max_n,10)+1)])
    print('These are finite checks, not a proof of the candidate.')


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--max-n', type=int, default=1000)
    parser.add_argument('--precision', type=int, default=6,
                        help='test U_N modulo this power of 5 (default: 6)')
    args = parser.parse_args()
    audit(args.max_n, args.precision)

if __name__ == '__main__':
    main()
