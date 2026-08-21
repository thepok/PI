#!/usr/bin/env python3
"""Independent stress checks for the cyclotomic language-product audit.

Exact checks use integer/rational or symbolic arithmetic.  The Gamma,
Euler--Maclaurin, and cocycle checks are explicitly numerical experiments;
they check signs and constants but are not proofs of an asymptotic theorem.
"""

from __future__ import annotations

from fractions import Fraction
from math import floor, gcd, log, pi, sin

import mpmath as mp
import sympy as sp


DIGITS = range(10)


def transition(word: tuple[int, ...], state: int, digit: int) -> int | None:
    trial = word[:state] + (digit,)
    if len(trial) >= len(word) and trial[-len(word) :] == word:
        return None
    for size in range(min(len(word) - 1, len(trial)), -1, -1):
        if size == 0 or trial[-size:] == word[:size]:
            return size
    raise AssertionError("unreachable")


def legal_values(word: tuple[int, ...], length: int) -> list[tuple[int, int]]:
    active = [(0, 0)]
    for _ in range(length):
        active = [
            (10 * value + digit, target)
            for value, state in active
            for digit in DIGITS
            if (target := transition(word, state, digit)) is not None
        ]
    return active


def check_exact_cyclotomic_and_gcd() -> None:
    z = sp.symbols("z")
    for exponent in range(1, 61):
        factors = sp.prod(
            sp.cyclotomic_poly(divisor, z)
            for divisor in sp.divisors(2 * exponent)
            if exponent % divisor != 0
        )
        assert sp.expand(factors - (1 + z**exponent)) == 0
    for first in range(1, 51):
        for second in range(1, 51):
            common = gcd(first, second)
            expected = (
                z**common + 1
                if (first // common) % 2 and (second // common) % 2
                else 1
            )
            actual = sp.Poly(
                sp.gcd(z**first + 1, z**second + 1), z
            ).monic().as_expr()
            assert sp.expand(actual - expected) == 0


def check_exact_child_parent_ledger() -> None:
    words = ((0,), (0, 0), (3, 1, 4), (9, 9))
    for word in words:
        for length in range(1, 5):
            parent_scale = 10 ** (length - 1)
            child_exponents: list[int] = []
            parent_exponents: list[int] = []
            for value, state in legal_values(word, length - 1):
                exponent = 3 * parent_scale + value
                allowed = [
                    digit
                    for digit in DIGITS
                    if transition(word, state, digit) is not None
                ]
                child_exponents.extend(10 * exponent + digit for digit in allowed)
                parent_exponents.extend([10 * exponent] * len(allowed))
            expected = [
                3 * 10**length + value
                for value, _ in legal_values(word, length)
            ]
            assert sorted(child_exponents) == sorted(expected)
            assert len(child_exponents) == len(parent_exponents) == len(expected)
            assert sum(child_exponents) - sum(parent_exponents) == sum(
                exponent % 10 for exponent in child_exponents
            )

    # Expand one small instance, including exponent collisions, to distinguish
    # coefficient l1-length from the number of distinct monomials.
    exponents = list(range(31, 40))
    comparison_exponents = [30] * 9
    for source in (exponents, comparison_exponents):
        coefficients = {0: 1}
        for exponent in source:
            updated = dict(coefficients)
            for degree, coefficient in coefficients.items():
                updated[degree + exponent] = (
                    updated.get(degree + exponent, 0) + coefficient
                )
            coefficients = updated
        assert max(coefficients) == sum(source)
        assert sum(abs(value) for value in coefficients.values()) == 2 ** len(source)


def check_exact_shell_ledger() -> None:
    words = ((0,), (0, 0), (3, 1, 4))
    centers = (Fraction(7, 23), Fraction(11, 37), Fraction(19, 41))
    length = 4
    for word in words:
        points = [
            Fraction(value, 10**length)
            for value, _ in legal_values(word, length)
        ]
        for center in centers:
            depths: list[int] = []
            for point in points:
                distance = abs(point - center)
                depth = 0
                threshold = Fraction(1, 10)
                while distance < threshold:
                    depth += 1
                    threshold /= 10
                depths.append(depth)
            shell_sum = sum(
                sum(
                    abs(point - center) < Fraction(1, 10**level)
                    for point in points
                )
                for level in range(1, max(depths, default=0) + 1)
            )
            assert shell_sum == sum(depths)
            for level in range(1, length + 1):
                cells = {
                    floor(point * 10**level)
                    for point in points
                    if abs(point - center) < Fraction(1, 10**level)
                }
                assert len(cells) <= 3


def smooth_part(value: mp.mpf) -> mp.mpf:
    if not value:
        return mp.mpf(0)
    return mp.log(2 * mp.sin(abs(value) / 2) / abs(value))


def potential(value: mp.mpf) -> mp.mpf:
    return mp.log(2 * abs(mp.sin(value / 2)))


def check_gamma_and_second_order_numerically() -> None:
    mp.mp.dps = 100
    centers = (mp.pi - 3, mp.sqrt(2) - 1, mp.mpf(7) / 23)
    for center in centers:
        for scale in (10, 37, 100):
            direct = mp.fprod(
                abs(mp.mpf(residue) / scale - center)
                for residue in range(scale)
            )
            reflected = (
                mp.power(scale, -scale)
                * mp.gamma(scale * center + 1)
                * mp.gamma(scale * (1 - center))
                * abs(mp.sin(mp.pi * scale * center))
                / mp.pi
            )
            assert abs(direct / reflected - 1) < mp.mpf("1e-85")

        integral = mp.quad(
            lambda x: potential(x - center), [0, center, 1]
        )
        constant = (
            mp.log(center / (1 - center)) / 2
            + (smooth_part(-center) - smooth_part(1 - center)) / 2
        )
        for scale in (100, 200, 400):
            actual = mp.fsum(
                potential(mp.mpf(residue) / scale - center)
                for residue in range(scale)
            )
            approximation = (
                scale * integral
                + mp.log(2 * abs(mp.sin(mp.pi * scale * center)))
                + constant
            )
            assert abs(actual - approximation) < mp.mpf("0.02")


def check_cocycle_numerically() -> None:
    center = pi - 3

    def log_factor(value: float) -> float:
        return log(2 * abs(sin((value - center) / 2)))

    for word in ((0,), (0, 0), (3, 1, 4), (9, 9)):
        for length in range(2, 7):
            scale = 10**length
            parent_scale = scale // 10
            difference = 0.0
            for value, state in legal_values(word, length - 1):
                for digit in DIGITS:
                    if transition(word, state, digit) is not None:
                        difference += log_factor((10 * value + digit) / scale)
                        difference -= log_factor(value / parent_scale)
            assert abs(difference) < 5 * log(scale)


def main() -> None:
    check_exact_cyclotomic_and_gcd()
    check_exact_child_parent_ledger()
    check_exact_shell_ledger()
    print("PASS: independent exact cyclotomic, gcd, tree, degree/l1, and shell checks")
    check_gamma_and_second_order_numerically()
    check_cocycle_numerically()
    print("EXPERIMENT PASS: Gamma/reflection, second-order sign, and cocycle scales")


if __name__ == "__main__":
    main()
