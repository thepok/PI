#!/usr/bin/env python3
"""Experiment: exact arithmetic checks, not a proof of any infinite claim.
Python standard library only. No pi digit file or floating-point pi is used.
"""
from fractions import Fraction as F
from math import gcd, lcm
import json
import sys

if hasattr(sys, 'set_int_max_str_digits'):
    sys.set_int_max_str_digits(0)

def term(N):
    return F(8, N * 3**N) + F(4, N * 7**N)

def vp(a, p):
    if a == 0:
        raise ValueError('valuation of zero requested')
    a = abs(a)
    v = 0
    while a % p == 0:
        a //= p
        v += 1
    return v

def flog_ratio(num, den, base=10):
    """floor(log_base(num/den)), for positive integers num >= den."""
    assert num >= den > 0
    n = 0
    while den * base <= num:
        den *= base
        n += 1
    return n

def mod_rational(q, modulus):
    return (q.numerator * pow(q.denominator, -1, modulus)) % modulus

M = 551
L = F(8, 3) - F(8, 81) + F(4, 7) - F(4, 1029)
ells = 3
states = []
recurrence_checks = 0
residue_checks = 0
sparse = []
separator_checks = 0
separator_previous = None
separator_examples = []
for m in range(M + 1):
    N = 4*m + 3
    W = term(N)
    U = L + W
    D = lcm(L.denominator, U.denominator)
    A = int(D*L)
    Delta = int(D*W)
    assert F(A, D) == L and F(Delta, D) == W
    e = flog_ratio(N, 1, 5)
    assert vp(L.denominator, 5) == e
    assert vp(D, 5) == e
    H = 21**N * ells
    B, Z = int(H*L), int(H*W)
    assert F(B, H) == L and F(Z, H) == W
    g = gcd(H, gcd(B, Z))
    assert (H//g, B//g, Z//g) == (D, A, Delta)
    C = F(8, N*3**N*10) + F(4, N*7**N*50)
    lo, hi = L + F(N, N+2)*C, L + C
    states.append((L, U, lo, hi))

    # Rational 1/9 separator, retaining the same widths, sharp remainder
    # inequalities, carrier H, five-adic law, and the sparse 3-adic constraint.
    alpha = F(1, 9)
    mod, cls = 1, 0
    rr = vp(N, 3)
    sparse_power = 3**rr == N
    if sparse_power:
        mod = 3**(rr+2)
        cls = (-8*(H//3**(N+rr))) % mod
    lower_int_bound = H*(alpha-C)
    upper_int_bound = H*(alpha-F(N, N+2)*C)
    Bs = cls + mod*((lower_int_bound-cls)//mod + 1)
    if Bs % 5 == 0:
        Bs += mod
    assert lower_int_bound < Bs < upper_int_bound
    Ls = F(Bs, H)
    Us = Ls+W
    assert Ls < alpha < Us
    assert F(N, N+2)*C < alpha-Ls < C
    assert vp(Ls.denominator, 5) == e
    if sparse_power:
        assert vp(Ls.denominator, 3) == N+rr
        assert mod_rational(3**(N+rr)*Ls+8, mod) == 0
        if m <= 6:
            separator_examples.append({'m': m, 'lower': str(Ls), 'upper': str(Us)})
    if separator_previous is not None:
        prev_Ls, prev_Us = separator_previous
        assert prev_Ls < Ls and Us < prev_Us
    separator_previous = Ls, Us
    separator_checks += 1

    if N in (3, 27, 243, 2187):
        r = vp(N, 3)
        assert 3**r == N and r % 2 == 1
        assert vp(L.denominator, 3) == N+r
        z3 = L * 3**(N+r)
        assert z3.denominator % 3 != 0
        modulus = 3**(r+2)
        assert mod_rational(z3 + 8, modulus) == 0
        h = flog_ratio(W.denominator, W.numerator) if W < 1 else -1
        row = {'m': m, 'N': N, 'r': r, 'h': h,
               'v3_denL': vp(L.denominator, 3),
               'period_lower_bound_exponent_of_3': N+r-2,
               'v5_D': e, 'first_certificates': {}}
        for k in (1, 2, 3):
            res, scaled_width_num = A % D, Delta
            first_zero = first_nine = None
            last_n = h-k
            for n in range(max(0, last_n+1)):
                if first_zero is None and 10**k*(res+scaled_width_num) <= D:
                    first_zero = n
                if (first_nine is None and 10**k*(D-res) <= D
                        and res+scaled_width_num <= D):
                    first_nine = n
                res = (10*res) % D
                scaled_width_num *= 10
            row['first_certificates'][str(k)] = {
                'admissible_n_through': last_n,
                'zero': first_zero, 'nine': first_nine}
        sparse.append(row)

    if m < M:
        Np = N + 4
        ellp = lcm(ells, N+2, N+4)
        Hp = 21**Np * ellp
        b = Hp // H
        E = term(N+2) - term(N+4)
        K = int(Hp*E)
        assert F(K, Hp) == E and K > 0
        Lp = L + E
        Bp = int(Hp*Lp)
        assert Bp == b*B + K
        assert Lp+term(N+4) == U-term(N)+term(N+2)
        recurrence_checks += 1
        for n, d in ((0, 0), (1, 1), (3, 2), (17, 2)):
            lhs = (pow(10, n+d, Hp)*Bp) % Hp
            rhs = (10**d*b*((pow(10, n, H)*B) % H)
                   + pow(10, n+d, Hp)*K) % Hp
            assert lhs == rhs
            residue_checks += 1
        L, ells = Lp, ellp

# A deeper ORIGINAL Machin bracket certifies the refined enclosure in these
# finite cases; this is not numerical integration or floating-point testing.
for m in range(547):
    lm5, um5, _, _ = states[m+5]
    _, _, lo, hi = states[m]
    assert lo < lm5 < um5 < hi

output = {
    'label': 'experiment',
    'adjacent_recurrences_checked': recurrence_checks,
    'joint_residue_recurrences_checked': residue_checks,
    'refined_enclosures_certified_with_deeper_brackets': 547,
    'sparse_rows': sparse,
    'rational_separator_cases_checked': separator_checks,
    'separator_examples': separator_examples,
}
print(json.dumps(output, indent=2))
