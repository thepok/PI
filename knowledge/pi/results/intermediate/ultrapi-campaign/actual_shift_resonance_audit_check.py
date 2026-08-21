#!/usr/bin/env python3
"""Independent finite checks for actual_shift_resonance_attack.md.

These checks exercise exact integer/rational consequences of the displayed
Fourier, automaton, CRT, and reciprocity formulas.  The one Fourier-series
convergence diagnostic uses floating point and is reported separately; it is
an experiment, not a proof of the identities or of the pi digit conjecture.
"""

from __future__ import annotations

from collections import Counter
from fractions import Fraction
from hashlib import sha256
from itertools import combinations, product
from math import cos, gcd, pi, sin
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
SOURCE = ROOT / "problems/local/pi-digits.txt"
EXPECTED_SOURCE_SHA256 = (
    "2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825"
)


def avoids(k: int, n: int, word: tuple[int, ...]) -> bool:
    digits = tuple(map(int, f"{k:0{n}d}"))
    m = len(word)
    return all(digits[i : i + m] != word for i in range(n - m + 1))


def avoiders(n: int, word: tuple[int, ...]) -> list[int]:
    return [k for k in range(10**n) if avoids(k, n, word)]


def transition(word: tuple[int, ...], state: int, digit: int) -> int | None:
    """KMP prefix-state transition; None is the forbidden completed word."""
    candidate = word[:state] + (digit,)
    if len(candidate) >= len(word) and candidate[-len(word) :] == word:
        return None
    for length in range(min(len(word) - 1, len(candidate)), -1, -1):
        if length == 0 or candidate[-length:] == word[:length]:
            return length
    raise AssertionError("the empty prefix must always match")


def automaton_fourier_coefficients(
    n: int, word: tuple[int, ...], h: int
) -> Counter[int]:
    """Coefficient vector in Z[z]/(z^(10^n)-1) for formula (11)."""
    modulus = 10**n
    dp: Counter[tuple[int, int]] = Counter({(0, 0): 1})
    for position in range(1, n + 1):
        place = 10 ** (n - position)
        nxt: Counter[tuple[int, int]] = Counter()
        for (state, exponent), count in dp.items():
            for digit in range(10):
                new_state = transition(word, state, digit)
                if new_state is None:
                    continue
                new_exponent = (exponent - h * digit * place) % modulus
                nxt[(new_state, new_exponent)] += count
        dp = nxt
    result: Counter[int] = Counter()
    for (_, exponent), count in dp.items():
        result[exponent] += count
    return result


def direct_fourier_coefficients(
    n: int, word: tuple[int, ...], h: int
) -> Counter[int]:
    modulus = 10**n
    return Counter((-h * k) % modulus for k in avoiders(n, word))


def e(x: float) -> complex:
    return complex(cos(2 * pi * x), sin(2 * pi * x))


def finite_grid_count(F: int, D: int, r: int, n: int, word: tuple[int, ...]) -> int:
    Q = F * D
    M = 10**n
    allowed = set(avoiders(n, word))
    return sum((M * (F * c + r) // Q) in allowed for c in range(D))


def finite_dft_count(F: int, D: int, r: int, n: int, word: tuple[int, ...]) -> complex:
    Q = F * D
    M = 10**n
    allowed = set(avoiders(n, word))
    g = [int((M * a // Q) in allowed) for a in range(Q)]
    result = 0j
    for u in range(F):
        h = D * u
        G = sum(g[a] * e(-h * a / Q) for a in range(Q))
        result += G * e(u * r / F)
    return result / F


def hat_indicator(h: int, n: int, word: tuple[int, ...]) -> complex:
    M = 10**n
    A = avoiders(n, word)
    if h == 0:
        return len(A) / M
    digital = sum(e(-h * k / M) for k in A)
    return (1 - e(-h / M)) / (2j * pi * h) * digital


def poisson_partial(
    F: int, D: int, r: int, n: int, word: tuple[int, ...], H: int
) -> complex:
    alpha = r / (F * D)
    total = D * hat_indicator(0, n, word)
    for ell in range(1, H + 1):
        positive = D * hat_indicator(ell * D, n, word) * e(ell * D * alpha)
        negative = D * hat_indicator(-ell * D, n, word) * e(-ell * D * alpha)
        total += positive + negative
    return total


def primary_components(F: int) -> list[int]:
    components = []
    remaining = F
    p = 2
    while p * p <= remaining:
        if remaining % p == 0:
            q = 1
            while remaining % p == 0:
                q *= p
                remaining //= p
            components.append(q)
        p += 1
    if remaining > 1:
        components.append(remaining)
    return components


def run() -> None:
    source_hash = sha256(SOURCE.read_bytes()).hexdigest()
    assert source_hash == EXPECTED_SOURCE_SHA256

    automaton_cases = 0
    words = [(d,) for d in range(10)]
    words += [tuple(ds) for ds in product(range(10), repeat=2)]
    for word in words:
        for n in range(len(word), 5):
            for h in (0, 1, 7, 13, 37):
                assert automaton_fourier_coefficients(n, word, h) == (
                    direct_fourier_coefficients(n, word, h)
                )
                automaton_cases += 1

    grid_cases = 0
    max_dft_error = 0.0
    endpoint_iff_cases = 0
    test_words = ((0,), (7,), (0, 0), (1, 2), (9, 9))
    for F in (3, 4, 7, 9, 11):
        for D in (2, 5, 8, 13):
            if gcd(F, D) != 1:
                continue
            for r in range(F):
                if gcd(r, F) != 1:
                    continue
                for n in (1, 2):
                    M = 10**n
                    endpoint_exists = any(
                        M * (F * c + r) % (F * D) == 0 for c in range(D)
                    )
                    assert endpoint_exists == (M % F == 0)
                    endpoint_iff_cases += 1
                    for word in test_words:
                        if len(word) > n:
                            continue
                        exact = finite_grid_count(F, D, r, n, word)
                        dft = finite_dft_count(F, D, r, n, word)
                        error = abs(dft - exact)
                        max_dft_error = max(max_dft_error, error)
                        assert error < 1e-10
                        grid_cases += 1

    crt_cases = 0
    reciprocity_cases = 0
    for F in (15, 40, 63, 77, 495):
        components = primary_components(F)
        assert all(gcd(q1, q2) == 1 for q1, q2 in combinations(components, 2))
        for D in range(2, 18):
            if gcd(F, D) != 1:
                continue
            Q = F * D
            for a in range(1, min(Q, 80)):
                if gcd(a, Q) != 1:
                    continue
                r = a % F
                rhs = Fraction(0)
                for q in components:
                    u = (a * pow(Q // q, -1, q)) % q
                    rhs += Fraction((D * u) % q, q)
                assert (Fraction(r, F) - rhs).denominator == 1
                crt_cases += 1
                b = a % Q
                c = b // F
                assert b == F * c + r
                for ell in (-7, -1, 0, 1, 11):
                    difference = Fraction(ell * r, F) - Fraction(ell * D * b, Q)
                    assert difference.denominator == 1
                    assert difference == -ell * c
                    reciprocity_cases += 1

    # One deliberately non-endpoint example for the symmetric Dirichlet
    # reconstruction.  This is only a numerical convergence diagnostic.
    poisson_F, poisson_D, poisson_r = 7, 5, 1
    poisson_n, poisson_word = 2, (0,)
    poisson_exact = finite_grid_count(
        poisson_F, poisson_D, poisson_r, poisson_n, poisson_word
    )
    poisson_value = poisson_partial(
        poisson_F, poisson_D, poisson_r, poisson_n, poisson_word, 20_000
    )
    poisson_error = abs(poisson_value - poisson_exact)
    assert poisson_error < 2e-3

    print(f"source_sha256={source_hash}")
    print(f"automaton_exact_cases={automaton_cases}")
    print(
        f"grid_dft_cases={grid_cases} max_floating_dft_error={max_dft_error:.3e}"
    )
    print(f"endpoint_iff_exact_cases={endpoint_iff_cases}")
    print(f"crt_exact_cases={crt_cases}")
    print(f"reciprocity_exact_cases={reciprocity_cases}")
    print(
        "poisson_symmetric_H=20000 "
        f"exact={poisson_exact} value={poisson_value.real:.12f} "
        f"imag={poisson_value.imag:.3e} error={poisson_error:.3e}"
    )


if __name__ == "__main__":
    run()
