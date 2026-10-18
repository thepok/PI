#!/usr/bin/env python3
"""Exact audit of the third Salikhov contour and a noncancellation determinant.

The formal polynomial identity is an exhaustive algebraic certificate.
Finite coefficient and index samples are experiments, not substitutes for
the contour, floor, Fourier, or asymptotic proofs in the accompanying note.
Standard library only; no pi digit evaluation or network access.
"""
import argparse
from fractions import Fraction as Q
from itertools import product
from math import comb, factorial
from pathlib import Path
import importlib.util
import json
import time


def padd(a, b):
    c = [Q(0)]*max(len(a), len(b))
    for j, v in enumerate(a):
        c[j] += v
    for j, v in enumerate(b):
        c[j] += v
    return c


def scale(a, v):
    return [v*x for x in a]

fp = None


def load_source(repo_root=None):
    relative = Path('workflows/experiments/salikhov_mod5_support_20260906/full_pair.py')
    roots = [repo_root] if repo_root is not None else [Path.cwd(), *Path(__file__).resolve().parents]
    for root in roots:
        source = root / relative
        if source.is_file():
            spec = importlib.util.spec_from_file_location('salikhov_full_pair_source', source)
            module = importlib.util.module_from_spec(spec)
            spec.loader.exec_module(module)
            return module
    raise FileNotFoundError('Supply --repo-root for the PI checkout containing '+str(relative))


def real_companion(n):
    """2*(-1)^n Re F_n(-1+2i), where F_n is the rational odd primitive."""
    H = [32, -112, 156, -100, 25]
    F = fp.mul([1, -2, 1], fp.mul(H, H))
    num = fp.power(F, n, 3*n)
    inv = [Q(comb(3*n+k, k), 2**(3*n+1+k)) for k in range(3*n+1)]
    A = fp.mul(num, inv, 3*n)
    value = Q(0)
    for j in range(1, 3*n+1):
        real = (fp.gp((Q(3, 4), Q(1, 4)), j)[0]
                - fp.gp((Q(1), Q(1, 2)), j)[0])
        value += 2*(-1)**n*A[3*n-j]*real/j
    if n:
        nump = fp.power([1, 6, 25], 2*n, 2*n-1)
        invp = [comb(3*n+k, k)*25**k for k in range(2*n)]
        coeff = fp.mul(nump, invp, 2*n-1)
        for k in range(2*n):
            j = 4*n-1-2*k
            value -= 10*coeff[k]*fp.gp((Q(-1), Q(2)), j)[0]/j
    return value


def determinant(rows):
    a, b, c = rows
    return (a[0]*(b[1]*c[2]-b[2]*c[1])
            - a[1]*(b[0]*c[2]-b[2]*c[0])
            + a[2]*(b[0]*c[1]-b[1]*c[0]))


def vp(value, p=5):
    if not value:
        return None
    value = Q(value)
    num, den = value.numerator, value.denominator
    result = 0
    while num % p == 0:
        num //= p
        result += 1
    while den % p == 0:
        den //= p
        result -= 1
    return result


def operator_coefficients():
    Y = [0, 1]
    V = [25, 6, 1]
    T = [25, -1]
    U = fp.mul(Y, fp.mul(V, V))
    A = scale(fp.mul(Y, fp.mul(V, T)), 2)
    VPART = [25, 18, 5]  # V+2*y*V'
    B0 = padd(fp.mul(VPART, T), scale(fp.mul(Y, V), 18))
    B1 = padd(scale(fp.mul(VPART, T), 2), scale(fp.mul(Y, V), 6))
    return T, U, A, B0, B1


def telescoper_at(n):
    """Solve the triangular coefficient system at one integer n."""
    T, U, OP_A, OP_B0, OP_B1 = operator_coefficients()
    rhs = [Q(0)]*16
    for j, p in enumerate(fp.recurrence_coefficients(n)):
        term = fp.mul(fp.power(scale(U, -1), j), fp.power(T, 9-3*j))
        rhs = padd(rhs, scale(term, p))
    B = padd(OP_B0, scale(OP_B1, n))
    remainder = rhs[:]
    S = [Q(0)]*13
    for degree in range(12, -1, -1):
        image = [Q(0)]*16
        for j, c in enumerate(B):
            image[degree+j] += c
        if degree:
            for j, c in enumerate(OP_A):
                image[degree-1+j] += degree*c
        leading = image[degree+3]
        assert leading == 13-4*n-2*degree
        S[degree] = remainder[degree+3]/leading
        remainder = padd(remainder, scale(image, -S[degree]))
    assert all(c == 0 for c in remainder)
    return S


def dm(a, b):
    out = {}
    for (an, ay), av in a.items():
        for (bn, by), bv in b.items():
            key = (an+bn, ay+by)
            out[key] = out.get(key, Q(0))+av*bv
    return {key: v for key, v in out.items() if v}


def da(*polys):
    out = {}
    for poly in polys:
        for key, value in poly.items():
            out[key] = out.get(key, Q(0))+value
    return {key: v for key, v in out.items() if v}


def ypoly(a):
    return {(0, j): Q(v) for j, v in enumerate(a) if v}


def telescoper_certificate():
    """Reconstruct degree<=8 coefficients, then verify the full formal identity."""
    T, U, OP_A, OP_B0, OP_B1 = operator_coefficients()
    samples = [telescoper_at(n) for n in range(9)]
    coefficients = [fp.coefficients_from_values([sample[j] for sample in samples])
                    for j in range(13)]
    S = {(j, k): v for k, row in enumerate(coefficients)
         for j, v in enumerate(row) if v}
    derivative = {(j, k-1): k*v for (j, k), v in S.items() if k}
    B = da(ypoly(OP_B0), {(1, j): v for j, v in enumerate(OP_B1) if v})
    lhs = da(dm(ypoly(OP_A), derivative), dm(B, S))
    rhs = {}
    for j in range(4):
        p = fp.coefficients_from_values([fp.recurrence_coefficients(n)[j]
                                        for n in range(10)])
        y = fp.mul(fp.power(scale(U, -1), j), fp.power(T, 9-3*j))
        rhs = da(rhs, {(np, yp): pv*yv for np, pv in enumerate(p)
                      for yp, yv in enumerate(y) if pv and yv})
    assert lhs == rhs
    assert max(np for np, yp in S) <= 8
    assert max(yp for np, yp in S) == 12
    return {
        'formal_bivariate_identity': True,
        'n_degree': max(np for np, yp in S),
        'y_degree': max(yp for np, yp in S),
        'coefficients_low_y_then_low_n': [[str(v) for v in row] for row in coefficients],
    }


def shell(value, prime=5):
    assert value > 0
    answer = 0
    while value >= prime:
        value //= prime
        answer += 1
    return answer


def g(n):
    return 559455*n**4+3399916*n**3+7651391*n*n+7554302*n+2760952


def factorial_valuation(n, prime=5):
    answer = 0
    while n:
        n //= prime
        answer += n
    return answer


def casoratian_valuation(n):
    f = factorial_valuation
    return (2+vp(g(n))+f(2*n)+f(2*n+2)+2*f(2*n+4)+f(n+1)
            -2*f(n+2)-f(4*n+8)-f(3*n+5))


def casoratian_exact(n):
    f = factorial
    return (Q(800, 3)*512**n*g(n)
            * Q(f(2*n)*f(2*n+2)*f(2*n+4)**2*f(n+1),
                f(n+2)**2*f(4*n+8)*f(3*n+5)))


def formal_casoratian_quotient():
    numerator = scale(fp.coefficients_from_values([g(n+1) for n in range(5)]), 512)
    denominator = fp.coefficients_from_values([g(n) for n in range(5)])
    for factor in ([1, 2], [2, 2], [3, 2], [4, 2],
                   [5, 2], [5, 2], [6, 2], [6, 2], [2, 1]):
        numerator = fp.mul(numerator, factor)
    for factor in ([3, 1], [3, 1], [9, 4], [10, 4], [11, 4],
                   [12, 4], [6, 3], [7, 3], [8, 3]):
        denominator = fp.mul(denominator, factor)
    p0 = fp.coefficients_from_values([fp.recurrence_coefficients(n)[0] for n in range(10)])
    p3 = fp.coefficients_from_values([fp.recurrence_coefficients(n)[3] for n in range(10)])
    assert fp.mul(numerator, p3) == scale(fp.mul(denominator, p0), -1)
    assert casoratian_exact(0) == Q(2760952, 63)
    return {'formal_polynomial_quotient_identity': True,
            'initial_value': str(casoratian_exact(0))}


def exact_contour_checks(N=16):
    a, b = fp.recurrence_sequences(N)
    d = [real_companion(n) for n in range(N+1)]
    assert d[:3] == [Q(0), Q(1658), Q(2716506572, 105)]
    residual = [sum(p*d[n+j] for j, p in enumerate(fp.recurrence_coefficients(n)))
                for n in range(N-2)]
    assert all(value == 0 for value in residual)
    W = [determinant([[seq[n+j] for seq in (a, b, d)] for j in range(3)])
         for n in range(N-1)]
    for n in range(N+1):
        assert fp.exact_companion(n) == (a[n], b[n])
        if n:
            assert vp(a[n]) >= -shell(4*n)
            assert vp(d[n]) >= -shell(4*n)
            assert vp(b[n]) >= 0
        if n < len(W):
            assert W[n] == casoratian_exact(n)
            assert vp(W[n]) == casoratian_valuation(n)
    return {
        'direct_endpoint_comparison_through': N,
        'd_initial': list(map(str, d[:4])),
        'recurrence_pass': True,
        'W_initial': str(W[0]),
        'W_nonzero': bool(all(W)),
        'factorial_formula_matches_all_determinants': True,
        'valuation_records': [dict(n=n, va=vp(a[n]), vb=vp(b[n]), vd=vp(d[n]),
                                   W=vp(W[n]) if n < len(W) else None)
                              for n in range(N+1)]
    }


def floor_contribution(n, M):
    return ((2*n)//M+(2*n+2)//M+2*((2*n+4)//M)+(n+1)//M
            -2*((n+2)//M)-(4*n+8)//M-(3*n+5)//M)


def language_words(free_digits):
    for digits in product((1, 2), repeat=free_digits):
        yield 36+sum(d*5**(j+3) for j, d in enumerate(digits)), digits


def language_certificate(depth=10):
    total, counts = 0, []
    for h in range(depth+1):
        L = h+3
        M = 5**L
        for n, digits in language_words(h):
            count_two = digits.count(2)
            assert Q(M+19, 4) <= n <= Q(M-53, 2)
            assert vp(g(n)) == 0
            assert [floor_contribution(n, 5**j) for j in (1, 2, 3)] == [-1]*3
            assert all(floor_contribution(n, 5**j) == -digits[j-4]
                       for j in range(4, L+1))
            assert floor_contribution(n, 5**(L+1)) == 0
            assert casoratian_valuation(n) == 2-L-count_two
            assert all(shell(4*(n+r)) == L for r in range(3))
            total += 1
        bad = sum(comb(h, t) for t in range(h+1) if 3*t < h)
        # Cube the Chernoff bound to make this finite comparison integral.
        assert bad**3*2**(2*h) <= 3**(3*h)
        counts.append({'free_digits': h, 'words': 2**h,
                       'deleted_small_two_count': bad})
    assert 27 < 32
    return {'maximum_free_digits': depth, 'words_checked': total,
            'floor_and_shell_formulas_exact': True, 'counts': counts}


def phase_certificate(bits=100):
    a, b, c, d = 108, -2359989, 138304, -2048
    disc = b*b*c*c-4*a*c**3-4*b**3*d-27*a*a*d*d+18*a*b*c*d
    assert disc == -57*4475640000**2 < 0
    assert all((a*x**3+b*x*x+c*x+d) % 11 for x in range(11))
    root_sum, root_product = Q(87407, 4), Q(512, 27)

    def polynomial(x):
        return a*x**3+b*x*x+c*x+d

    short_lo = Q(218516913962, 10**7)
    short_hi = Q(218516913963, 10**7)
    assert polynomial(short_lo) < 0 < polynomial(short_hi)
    assert 0 < root_sum-short_hi < root_sum-short_lo
    short_lower = short_lo*(root_sum-short_hi)**2/root_product
    short_upper = short_hi*(root_sum-short_lo)**2/root_product
    assert Q(162, 41) < short_lower <= short_upper < Q(384, 97)

    lo, hi = Q(21851), root_sum
    assert polynomial(lo) < 0 < polynomial(hi)
    assert 324*lo*lo-4719978*lo+138304 > 0
    assert 648*lo-4719978 > 0
    for _ in range(bits):
        mid = (lo+hi)/2
        if polynomial(mid) < 0:
            lo = mid
        else:
            hi = mid
    lower = lo*(root_sum-hi)**2/root_product
    upper = hi*(root_sum-lo)**2/root_product
    assert Q(162, 41) < lower <= upper < Q(384, 97)
    assert Q(9, 20)-Q(1, 27) == Q(223, 540) > Q(2, 5)
    return {'cubic_discriminant': disc, 'irreducible_modulo_11': True,
            'short_root_lower': str(short_lo), 'short_root_upper': str(short_hi),
            'short_S_lower': str(short_lower), 'short_S_upper': str(short_upper),
            'root_lower': str(lo), 'root_upper': str(hi),
            'S_lower': str(lower), 'S_upper': str(upper),
            'tan_squared_bounds': ['1/96', '1/81'],
            'theta_upper_bound': '1/9',
            'phase_interval_relative_length_lower_bound': '223/540',
            'claimed_eventual_sign_fraction': '2/5',
            'all_comparisons_exact': True}


def selected_valuation_checks(depth=3, target=16, exact_compare=100):
    """A finite recurrence computation with a reserved division-loss budget."""
    bases = [(n, digits) for h in range(depth+1) for n, digits in language_words(h)]
    N = max(n+2 for n, _ in bases)
    wanted = {n+r for n, _ in bases for r in range(3)}
    wanted.update(range(1, min(exact_compare, N)+1))
    S = shell(4*N)
    parameters = [fp.recurrence_coefficients(n) for n in range(N-2)]
    losses = [vp(p[3]) for p in parameters]
    final_precision = S+target
    initial_precision = final_precision+sum(losses)
    modulus = 5**initial_precision

    def residue(x):
        return x.numerator*pow(x.denominator, -1, modulus) % modulus

    a_initial, b_initial = fp.recurrence_sequences(2)
    aa = [residue(x*5**S) for x in a_initial]
    bb = [residue(x) for x in b_initial]
    observed = {}

    def record(n, av, bv):
        if n not in wanted:
            return
        assert av and bv
        va, vb = vp(av), vp(bv)
        assert va < final_precision and vb < final_precision
        observed[n] = (va-S, vb)

    record(1, aa[1], bb[1])
    record(2, aa[2], bb[2])
    for n, (p, loss) in enumerate(zip(parameters, losses)):
        factor = 5**loss
        next_modulus = modulus//factor
        inverse = pow(p[3]//factor, -1, next_modulus)
        for seq in (aa, bb):
            numerator = -sum(p[j]*seq[j] for j in range(3)) % modulus
            assert numerator % factor == 0
            new = (numerator//factor)*inverse % next_modulus
            seq[:] = [seq[1] % next_modulus, seq[2] % next_modulus, new]
        modulus = next_modulus
        record(n+3, aa[2], bb[2])
    assert modulus == 5**final_precision
    assert wanted == set(observed)

    a, b = fp.recurrence_sequences(min(exact_compare, N))
    for n in range(1, min(exact_compare, N)+1):
        assert observed[n] == (vp(a[n]), vp(b[n]))
    records = []
    for n, digits in bases:
        t = digits.count(2)
        values = [observed[n+r] for r in range(3)]
        r = min(range(3), key=lambda r: values[r][0])
        va, vb = values[r]
        assert va <= 2-t
        assert max(0, vb-va) >= max(0, t-2)
        records.append({'base': n, 'free_digits_low_first': list(digits),
                        'count_two': t, 'selected_offset': r,
                        'a_valuations': [v[0] for v in values],
                        'b_valuations': [v[1] for v in values],
                        'selected_denominator_depth': max(0, vb-va),
                        'proved_companion_upper_bound': 2-t})
    return {'cutoff': N, 'initial_precision': initial_precision,
            'final_precision': final_precision,
            'clearing_exponent': S, 'unresolved': [],
            'exact_recurrence_comparison_through': min(exact_compare, N),
            'triples': records}


def main():
    global fp
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo-root', type=Path)
    parser.add_argument('--direct', type=int, default=16)
    parser.add_argument('--word-depth', type=int, default=10)
    parser.add_argument('--coefficient-depth', type=int, default=3)
    parser.add_argument('--json', type=Path)
    args = parser.parse_args()
    if args.direct < 3 or args.word_depth < 0 or args.coefficient_depth < 0:
        parser.error('Require direct>=3 and nonnegative word/coefficient depths')
    fp = load_source(args.repo_root)
    start = time.monotonic()
    report = {
        'status': 'exact formal identity certificate and separate finite experiments',
        'telescoper': telescoper_certificate(),
        'casoratian_quotient': formal_casoratian_quotient(),
        'direct_contour_checks': exact_contour_checks(args.direct),
        'language': language_certificate(args.word_depth),
        'phase': phase_certificate(),
        'selected_valuations': selected_valuation_checks(args.coefficient_depth),
        'infinite_Fourier_and_sign_proof': 'in the accompanying note; not finite sampling',
    }
    elapsed_seconds = round(time.monotonic()-start, 3)
    payload = json.dumps(report, indent=2)+'\n'
    if args.json:
        args.json.write_text(payload, encoding='utf-8')
    # The full coefficient array is preserved in the file; keep terminal output brief.
    summary = dict(report)
    summary['seconds'] = elapsed_seconds
    summary['telescoper'] = {k: v for k, v in report['telescoper'].items()
                            if k != 'coefficients_low_y_then_low_n'}
    summary['direct_contour_checks'] = {k: v for k, v in report['direct_contour_checks'].items()
                                       if k != 'valuation_records'}
    print(json.dumps(summary, indent=2))


if __name__ == '__main__':
    main()
