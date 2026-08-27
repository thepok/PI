#!/usr/bin/env python3
"""Exact finite checks for automaton_pade_attack.md.

These checks validate finite algebraic identities and counting formulas only.
They do not inspect digits of pi and do not constitute evidence for V1.
"""

from __future__ import annotations

from fractions import Fraction
from itertools import product
from math import factorial, gcd

import sympy as sp


DIGITS = tuple(range(10))


def next_state(word: tuple[int, ...], state: int, digit: int) -> int | None:
    """KMP-prefix transition, with the full forbidden state deleted."""
    trial = word[:state] + (digit,)
    if len(trial) >= len(word) and trial[-len(word) :] == word:
        return None
    for size in range(min(len(word) - 1, len(trial)), -1, -1):
        if trial[-size:] == word[:size] if size else True:
            return size
    raise AssertionError("unreachable")


def automaton_count(word: tuple[int, ...], n: int) -> int:
    states = [0] * len(word)
    states[0] = 1
    for _ in range(n):
        updated = [0] * len(word)
        for state, count in enumerate(states):
            for digit in DIGITS:
                target = next_state(word, state, digit)
                if target is not None:
                    updated[target] += count
        states = updated
    return sum(states)


def avoiding_values(word: tuple[int, ...], n: int) -> list[int]:
    values: list[int] = []
    for digits in product(DIGITS, repeat=n):
        if all(digits[j : j + len(word)] != word for j in range(n - len(word) + 1)):
            value = 0
            for digit in digits:
                value = 10 * value + digit
            values.append(value)
    return values


def product_one_plus_monomials(exponents: list[int]) -> dict[int, int]:
    coeffs = {0: 1}
    for exponent in exponents:
        updated = dict(coeffs)
        for old_degree, coefficient in coeffs.items():
            new_degree = old_degree + exponent
            updated[new_degree] = updated.get(new_degree, 0) + coefficient
        coeffs = updated
    return coeffs


def check_automata_and_arithmetic_counts() -> None:
    for word, max_n in [((0,), 3), ((0, 0), 3), ((3, 1, 4), 3)]:
        forbidden_digit = word[0]
        for n in range(1, max_n + 1):
            values = avoiding_values(word, n)
            assert automaton_count(word, n) == len(values)
            assert len(values) >= 9**n

            q = 10**n
            coprime_count = sum(gcd(3 * q + value, q) == 1 for value in values)
            assert coprime_count >= 3 * 9 ** (n - 1)

            # The explicit subsystem excluding one digit of the forbidden word.
            subsystem = [
                value
                for digits in product(tuple(d for d in DIGITS if d != forbidden_digit), repeat=n)
                for value in [sum(d * 10 ** (n - 1 - j) for j, d in enumerate(digits))]
            ]
            assert len(subsystem) == 9**n
            assert set(subsystem).issubset(values)


def check_exponential_selector_polynomial() -> None:
    word = (0,)
    n = 2
    q = 10**n
    values = avoiding_values(word, n)
    exponents = [3 * q + value for value in values]
    coeffs = product_one_plus_monomials(exponents)

    assert max(coeffs) == sum(exponents)
    assert sum(coeffs.values()) == 2 ** len(exponents)
    assert len(coeffs) >= len(exponents) + 1
    assert 3 * q * len(exponents) <= max(coeffs) < 4 * q * len(exponents)


def check_resultant_identity() -> None:
    y, x = sp.symbols("y x")
    for q in (2, 4, 6, 10):
        for p in range(1, 13):
            common = gcd(p, q)
            quotient = q // common
            actual = sp.resultant(y**q - x, 1 + y**p, y)
            expected = (1 - (-1) ** quotient * x ** (p // common)) ** common
            assert sp.expand(actual - expected) == 0


def check_gcd_sum_and_arc_bounds() -> None:
    for n in range(1, 6):
        q = 10**n
        actual = sum(gcd(a, q) for a in range(q))
        expected = q * (n + 2) * (4 * n + 5) // 10
        assert actual == expected

    # The alternating cosine series gives
    #   S_3 < cos(2) < S_4,
    # hence 262/315 < rho=-2*cos(2) < 38/45 < 1.
    partial_3 = sum(Fraction((-1) ** k * 2 ** (2 * k), factorial(2 * k)) for k in range(4))
    partial_4 = sum(Fraction((-1) ** k * 2 ** (2 * k), factorial(2 * k)) for k in range(5))
    assert partial_3 == Fraction(-19, 45)
    assert partial_4 == Fraction(-131, 315)
    assert Fraction(1, 10) < -2 * partial_4 < -2 * partial_3 < 1


def check_parameter_separator() -> None:
    # The report's logarithmic comparison only uses
    #   0 < c=-log(rho) < log(q),  mu>1,  b=log(pi/2)>0.
    # Algebraically, after dividing by the multiplicity t:
    #   A = log(q)+(s-1)c < s*log(q)
    #   B = s*(mu*log(q)+b) > s*log(q).
    # The rational surrogate below verifies the strict coefficient pattern
    # for arbitrary positive stand-ins satisfying those hypotheses.
    for s in range(1, 20):
        for t in range(1, 8):
            log_q = Fraction(7, 3)
            c = Fraction(1, 5)
            mu = Fraction(71, 10)
            b = Fraction(2, 5)
            upper_exponent = t * (log_q + (s - 1) * c)
            lower_exponent = t * s * (mu * log_q + b)
            assert upper_exponent <= t * s * log_q < lower_exponent


def main() -> None:
    check_automata_and_arithmetic_counts()
    check_exponential_selector_polynomial()
    check_resultant_identity()
    check_gcd_sum_and_arc_bounds()
    check_parameter_separator()
    print("PASS: automaton counts, selector size, resultants, gcd sums, and separator inequalities")


if __name__ == "__main__":
    main()
