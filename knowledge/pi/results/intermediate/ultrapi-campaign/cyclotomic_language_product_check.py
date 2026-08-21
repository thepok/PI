#!/usr/bin/env python3
"""Finite checks for cyclotomic_language_product_attack.md.

The exact checks cover finite polynomial, automaton, and shell-count
identities.  Floating-point checks only illustrate asymptotic formulas and
are explicitly reported as experiments; none inspects enough digits of pi to
constitute evidence for V1.
"""

from __future__ import annotations

from fractions import Fraction
from itertools import product
from math import cos, exp, floor, gcd, log, pi, sin

import mpmath as mp
import sympy as sp


DIGITS = tuple(range(10))


def transition(word: tuple[int, ...], state: int, digit: int) -> int | None:
    """KMP-prefix transition with the full forbidden state removed."""
    trial = word[:state] + (digit,)
    if len(trial) >= len(word) and trial[-len(word) :] == word:
        return None
    for size in range(min(len(word) - 1, len(trial)), -1, -1):
        if size == 0 or trial[-size:] == word[:size]:
            return size
    raise AssertionError("unreachable")


def legal_values(word: tuple[int, ...], n: int) -> list[tuple[int, int]]:
    """Return (value, terminal state) for every legal length-n word."""
    active = [(0, 0)]
    for _ in range(n):
        updated: list[tuple[int, int]] = []
        for value, state in active:
            for digit in DIGITS:
                target = transition(word, state, digit)
                if target is not None:
                    updated.append((10 * value + digit, target))
        active = updated
    return active


def transfer_fourier(word: tuple[int, ...], n: int, frequency: float) -> complex:
    """Matrix/dynamic-program evaluation of sum exp(i*k*[u]/10^n)."""
    active = [0.0j] * len(word)
    active[0] = 1.0 + 0.0j
    for position in range(1, n + 1):
        updated = [0.0j] * len(word)
        for state, coefficient in enumerate(active):
            for digit in DIGITS:
                target = transition(word, state, digit)
                if target is None:
                    continue
                phase = frequency * digit / 10**position
                updated[target] += coefficient * complex(cos(phase), sin(phase))
        active = updated
    return sum(active)


def check_cyclotomic_factorization_and_common_roots() -> None:
    z = sp.symbols("z")
    for exponent in range(1, 25):
        factors = sp.Integer(1)
        for divisor in sp.divisors(2 * exponent):
            if exponent % divisor != 0:
                factors *= sp.cyclotomic_poly(divisor, z)
        assert sp.expand(factors - (1 + z**exponent)) == 0

    # gcd(Z^p+1,Z^r+1) is nontrivial exactly when p/g and r/g are odd.
    for first in range(1, 20):
        for second in range(1, 20):
            common = gcd(first, second)
            expected = z**common + 1 if (first // common) % 2 and (second // common) % 2 else 1
            actual = sp.Poly(sp.gcd(z**first + 1, z**second + 1), z).monic().as_expr()
            assert sp.expand(actual - expected) == 0


def check_transfer_and_tree_identities() -> None:
    for word in ((0,), (0, 0), (3, 1, 4)):
        for n in range(1, 4):
            values = legal_values(word, n)
            brute = []
            word_text = "".join(map(str, word))
            for digits in product(DIGITS, repeat=n):
                text = "".join(map(str, digits))
                if word_text not in text:
                    value = sum(digit * 10 ** (n - 1 - j) for j, digit in enumerate(digits))
                    brute.append(value)
            assert sorted(value for value, _ in values) == sorted(brute)

            frequency = 7.0 / 13.0
            direct = sum(
                complex(cos(frequency * value / 10**n), sin(frequency * value / 10**n))
                for value in brute
            )
            assert abs(transfer_fourier(word, n, frequency) - direct) < 1e-11

        # The last-digit tree partition and its state-weighted comparison
        # polynomial have exactly the same number of binomial factors.
        n = 3
        parents = legal_values(word, n - 1)
        child_count = 0
        replicated_parent_count = 0
        actual_children: list[int] = []
        for parent_value, state in parents:
            allowed = [d for d in DIGITS if transition(word, state, d) is not None]
            child_count += len(allowed)
            replicated_parent_count += len(allowed)
            actual_children.extend(10 * parent_value + d for d in allowed)
        assert child_count == replicated_parent_count == len(legal_values(word, n))
        assert sorted(actual_children) == sorted(value for value, _ in legal_values(word, n))


def check_shell_ledger_exactly() -> None:
    """Check sum floor(-log_10 distance) = sum nested shell counts."""
    center = Fraction(7, 23)
    q = 10**3
    points = [Fraction(value, q) for value, _ in legal_values((0, 0), 3)]

    def decimal_depth(distance: Fraction) -> int:
        depth = 0
        threshold = Fraction(1, 10)
        while distance < threshold:
            depth += 1
            threshold /= 10
        return depth

    depths = [decimal_depth(abs(point - center)) for point in points]
    shell_sum = 0
    for level in range(1, max(depths, default=0) + 1):
        radius = Fraction(1, 10**level)
        shell_sum += sum(abs(point - center) < radius for point in points)
    assert shell_sum == sum(depths)

    # A radius-10^-k interval meets at most three length-k decimal cells.
    for level in range(1, 4):
        cells = {floor(point * 10**level) for point in points if abs(point - center) < Fraction(1, 10**level)}
        assert len(cells) <= 3


def check_full_grid_distance_product_exactly() -> None:
    """An exact rational version of the distance-product identity."""
    center = Fraction(7, 23)
    for q in (10, 100):
        direct = Fraction(1, 1)
        integer_numerator = 1
        for residue in range(q):
            direct *= abs(Fraction(residue, q) - center)
            integer_numerator *= abs(23 * residue - 7 * q)
        reconstructed = Fraction(integer_numerator, (23 * q) ** q)
        assert direct == reconstructed


def log_factor(x: float, center: float) -> float:
    return log(2.0 * abs(sin((x - center) / 2.0)))


def check_selected_factor_and_rates() -> dict[str, float]:
    """Floating-point experiments used only for the report's scale table."""
    center = pi - 3.0
    selected_errors = []
    for n in range(1, 7):
        q = 10**n
        numerator = floor(q * pi)
        tail = q * pi - numerator
        direct = abs(1.0 + complex(cos(numerator / q), sin(numerator / q)))
        exact_trig = 2.0 * sin(tail / (2.0 * q))
        assert abs(direct - exact_trig) < 5e-15
        selected_errors.append(abs(log(exact_trig) - (-log(q) + log(tail))))
    assert max(selected_errors) < 0.01

    rates: dict[str, float] = {}
    for label, word in (("0", (0,)), ("00", (0, 0)), ("314", (3, 1, 4)), ("99", (9, 9))):
        n = 5
        q = 10**n
        values = legal_values(word, n)
        total = sum(log_factor(value / q, center) for value, _ in values)
        rates[label] = -total / len(values)
    crude_constant = -log(-2.0 * cos(2.0))
    assert all(rate > crude_constant for rate in rates.values())
    return rates


def check_full_grid_second_order() -> float:
    """Numerically check the stated Gamma/Euler--Maclaurin control formula."""
    mp.mp.dps = 60
    center = mp.pi - 3

    def potential(x: mp.mpf) -> mp.mpf:
        return mp.log(abs(1 - mp.e ** (1j * (x - center))))

    def smooth_part(u: mp.mpf) -> mp.mpf:
        if not u:
            return mp.mpf(0)
        return mp.log(2 * mp.sin(abs(u) / 2) / abs(u))

    integral = mp.quad(potential, [0, center, 1])
    constant = (
        mp.log(center / (1 - center)) / 2
        + (smooth_part(-center) - smooth_part(1 - center)) / 2
    )
    previous_scaled_error = None
    for n in (2, 3, 4):
        q = 10**n
        actual = mp.fsum(potential(mp.mpf(residue) / q) for residue in range(q))
        approximation = (
            q * integral
            + mp.log(2 * abs(mp.sin(mp.pi * q * center)))
            + constant
        )
        scaled_error = q * (actual - approximation)
        assert abs(scaled_error) < 1
        if previous_scaled_error is not None:
            assert abs(scaled_error - previous_scaled_error) < mp.mpf("0.01")
        previous_scaled_error = scaled_error
    return float(-integral)


def main() -> None:
    check_cyclotomic_factorization_and_common_roots()
    check_transfer_and_tree_identities()
    check_shell_ledger_exactly()
    check_full_grid_distance_product_exactly()
    rates = check_selected_factor_and_rates()
    unrestricted_rate = check_full_grid_second_order()
    print("PASS: exact cyclotomic, transfer-tree, shell, and distance-product identities")
    print(
        "EXPERIMENT: -N^-1 log products at n=5: "
        + ", ".join(f"w={word}: {rate:.10f}" for word, rate in rates.items())
    )
    print(f"EXPERIMENT: unrestricted limiting rate: {unrestricted_rate:.10f}")


if __name__ == "__main__":
    main()
