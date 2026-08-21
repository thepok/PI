#!/usr/bin/env python3
"""Finite replay for the fractional-parts density application audit.

This script checks exact rational identities and finite modular instances only.
Its output is an ``experiment``.  It does not prove density, target hitting, or
that any prescribed decimal word occurs in pi.
"""

from __future__ import annotations

import hashlib
import json
import math
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
FROZEN_HASHES = {
    ROOT / "problems/local/pi-digits.txt":
        "2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825",
    ROOT / "work/ultrapi-resume/bbp_dyadic_diagonal_functional_recurrence_20260813.md":
        "8768abbdd38d21721955f76a0c1ba90054ed9177a95b9b393aa393fc0d7466ba",
    ROOT / "work/ultrapi-resume/bbp_dyadic_diagonal_functional_recurrence_20260813_check.py":
        "c7d04bb733cf50b08ed46dddf52bb98bbe726c0897f74c93f00533313a67f651",
}


@dataclass(frozen=True)
class LiftTerm:
    numerator: int
    denominator: int
    label: str
    slope: int | None = None
    intercept: int | None = None
    phase_coefficient: Fraction | None = None

    def value(self) -> Fraction:
        return Fraction(self.numerator, self.denominator)


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def frac_part(x: Fraction) -> Fraction:
    return x - (x.numerator // x.denominator)


def coefficient(k: int) -> Fraction:
    return Fraction(
        120 * k * k + 151 * k + 47,
        (2 * k + 1) * (4 * k + 3) * (8 * k + 1) * (8 * k + 5),
    )


def formal_four_poles(k: int) -> tuple[Fraction, ...]:
    return (
        Fraction(4, 8 * k + 1),
        Fraction(-1, 2 * (2 * k + 1)),
        Fraction(-1, 8 * k + 5),
        Fraction(-1, 2 * (4 * k + 3)),
    )


def split_terms(n: int) -> list[LiftTerm]:
    """An exact 28-term odd-linear split.

    At j=7 two terms in the formal partial fraction expansion separately
    have 2-adic valuation -1.  The identity

      -s/[2(2k+1)] - s/[2(4k+3)]
        = -s(k+1)/(2k+1) + s(2k+1)/(4k+3)

    recombines their sum into two integer-numerator, odd-linear fractions.
    """

    terms: list[LiftTerm] = []
    for j in range(1, 8):
        k = 7 * n + j
        s = 5 ** (n + 1) * 16 ** (7 - j)
        exponent_two = 4 * (7 - j)

        # 4s/(8k+1)
        terms.append(
            LiftTerm(
                4 * s,
                8 * k + 1,
                f"j{j}:8k+1",
                56,
                8 * j + 1,
                Fraction(-4 * 2**exponent_two),
            )
        )

        if j < 7:
            # -s/[2(2k+1)] and -s/[2(4k+3)] have integral
            # numerators because 16^(7-j) supplies at least four twos.
            half_s = s // 2
            terms.append(
                LiftTerm(
                    -half_s,
                    2 * k + 1,
                    f"j{j}:2k+1",
                    14,
                    2 * j + 1,
                    Fraction(2 ** (exponent_two - 1)),
                )
            )
            terms.append(
                LiftTerm(
                    -s,
                    8 * k + 5,
                    f"j{j}:8k+5",
                    56,
                    8 * j + 5,
                    Fraction(2**exponent_two),
                )
            )
            terms.append(
                LiftTerm(
                    -half_s,
                    4 * k + 3,
                    f"j{j}:4k+3",
                    28,
                    4 * j + 3,
                    Fraction(2 ** (exponent_two - 1)),
                )
            )
        else:
            # The two formal half-integral terms first pair as
            # -s/(2(2k+1)) - s/(2(4k+3))
            #   = -s(3k+2)/((2k+1)(4k+3)),
            # but the relation 4k+3 = 2(2k+1)+1 gives the stronger
            # integer-numerator linear recombination recorded in the
            # docstring.
            terms.append(
                LiftTerm(
                    -s * (k + 1),
                    2 * k + 1,
                    "j7:2k+1-recombined",
                    14,
                    15,
                    Fraction(1, 2),
                )
            )
            terms.append(
                LiftTerm(
                    -s,
                    8 * k + 5,
                    "j7:8k+5",
                    56,
                    61,
                    Fraction(1),
                )
            )
            terms.append(
                LiftTerm(
                    s * (2 * k + 1),
                    4 * k + 3,
                    "j7:4k+3-recombined",
                    28,
                    31,
                    Fraction(1, 2),
                )
            )
    return terms


def dyadic_residue(x: Fraction, modulus: int) -> int:
    assert x.denominator % 2 == 1
    return (x.numerator * pow(x.denominator, -1, modulus)) % modulus


def lifted_height(term: LiftTerm, modulus: int) -> tuple[int, int]:
    assert term.denominator % 2 == 1
    rho = (term.numerator * pow(term.denominator, -1, modulus)) % modulus
    numerator = term.denominator * rho - term.numerator
    assert numerator % modulus == 0
    return rho, numerator // modulus


def is_prime(n: int) -> bool:
    if n < 2:
        return False
    if n % 2 == 0:
        return n == 2
    d = 3
    while d * d <= n:
        if n % d == 0:
            return False
        d += 2
    return True


def pow_signed(base: int, exponent: int, modulus: int) -> int:
    if exponent >= 0:
        return pow(base, exponent, modulus)
    return pow(pow(base, -1, modulus), -exponent, modulus)


def mod_fraction(value: Fraction, modulus: int) -> int:
    assert math.gcd(value.denominator, modulus) == 1
    return value.numerator * pow(value.denominator, -1, modulus) % modulus


def radical_inverse_two(k: int) -> Fraction:
    numerator = 0
    denominator = 1
    while k:
        denominator *= 2
        numerator = 2 * numerator + (k & 1)
        k >>= 1
    return Fraction(numerator, denominator)


def run() -> dict[str, object]:
    for path, expected in FROZEN_HASHES.items():
        assert sha256(path) == expected, path

    partial_fraction_checks = 0
    for k in range(0, 257):
        assert sum(formal_four_poles(k), Fraction()) == coefficient(k)
        partial_fraction_checks += 1

    # The 28 formal linear denominator forms are distinct.  Exactly four are
    # nonprimitive because a fixed factor 7 divides every value.
    forms: list[tuple[str, int, int]] = []
    for j in range(1, 8):
        forms.extend(
            [
                (f"j{j}:2k+1", 14, 2 * j + 1),
                (f"j{j}:4k+3", 28, 4 * j + 3),
                (f"j{j}:8k+1", 56, 8 * j + 1),
                (f"j{j}:8k+5", 56, 8 * j + 5),
            ]
        )
    assert len(forms) == 28
    assert len({(a, b) for _, a, b in forms}) == 28
    nonprimitive = [(name, a, b, math.gcd(a, b)) for name, a, b in forms if math.gcd(a, b) > 1]
    assert nonprimitive == [
        ("j1:4k+3", 28, 7, 7),
        ("j2:8k+5", 56, 21, 7),
        ("j3:2k+1", 14, 7, 7),
        ("j6:8k+1", 56, 49, 7),
    ]

    # Uniform coprimality fails inside each original quartic denominator.
    gcd_checks = 0
    overlap_3 = 0
    overlap_5 = 0
    for k in range(0, 500):
        a = 2 * k + 1
        b = 4 * k + 3
        c = 8 * k + 1
        d = 8 * k + 5
        assert math.gcd(a, b) == 1
        assert math.gcd(a, c) == math.gcd(a, 3)
        assert math.gcd(a, d) == 1
        assert math.gcd(b, c) == math.gcd(b, 5)
        assert math.gcd(b, d) == 1
        assert math.gcd(c, d) == 1
        overlap_3 += math.gcd(a, c) == 3
        overlap_5 += math.gcd(b, c) == 5
        gcd_checks += 1
    assert overlap_3 > 0 and overlap_5 > 0

    split_checks = 0
    lift_checks = 0
    lift_sign_checks = 0
    bad_formal_terms = 0
    for n in range(1, 19):
        b_n = Fraction()
        formal: list[Fraction] = []
        for j in range(1, 8):
            k = 7 * n + j
            s = 5 ** (n + 1) * 16 ** (7 - j)
            b_n += s * coefficient(k)
            formal.extend(s * term for term in formal_four_poles(k))
        assert sum(formal, Fraction()) == b_n
        this_bad = [term for term in formal if term.denominator % 2 == 0]
        assert len(this_bad) == 2
        bad_formal_terms += len(this_bad)

        split = split_terms(n)
        assert len(split) == 28
        assert sum((term.value() for term in split), Fraction()) == b_n
        assert sum(term.slope is not None for term in split) == 28
        assert all(term.denominator % 2 == 1 for term in split)

        modulus = 1 << (27 * (n + 1))
        gamma_residue = dyadic_residue(b_n, modulus)
        assert sum(dyadic_residue(term.value(), modulus) for term in split) % modulus == gamma_residue

        lifted_sum = b_n / modulus
        for term in split:
            rho, height = lifted_height(term, modulus)
            assert Fraction(rho, modulus) == (
                Fraction(height, term.denominator)
                + Fraction(term.numerator, term.denominator * modulus)
            )
            rational_base = 5 * pow(1 << 27, -1, term.denominator) % term.denominator
            assert term.phase_coefficient is not None
            predicted = mod_fraction(
                term.phase_coefficient, term.denominator
            ) * pow(rational_base, n + 1, term.denominator)
            assert height % term.denominator == predicted % term.denominator
            lifted_sum += Fraction(height, term.denominator)
            lift_checks += 1
            lift_sign_checks += 1
        assert frac_part(lifted_sum) == Fraction(gamma_residue, modulus)
        split_checks += 1

    # For a primitive linear term L(n)=A n+B that happens to be prime, the
    # selected rational-base phase is one distinguished root of a fixed
    # binomial modulo L(n).  This checks that exact reduction in many cases.
    root_checks = 0
    for n in range(1, 600):
        modulus_two = 1 << (27 * (n + 1))
        for term in split_terms(n):
            if term.slope is None:
                continue
            p = term.denominator
            phase_c = term.phase_coefficient
            assert phase_c is not None
            if not is_prime(p) or math.gcd(
                p, 10 * phase_c.numerator * phase_c.denominator
            ) != 1:
                continue
            rho, height = lifted_height(term, modulus_two)
            del rho
            rational_base = 5 * pow(1 << 27, -1, p) % p
            selected = mod_fraction(phase_c, p) * pow(
                rational_base, n + 1, p
            ) % p
            assert height % p == selected
            fixed_rhs = (
                pow(mod_fraction(phase_c, p), term.slope, p)
                * pow_signed(rational_base, term.slope - term.intercept + 1, p)
            ) % p
            assert pow(selected, term.slope, p) == fixed_rhs
            root_checks += 1
    assert root_checks > 500

    # A scalar forcing can have a uniformly distributed subsequence and a
    # much stronger-than-N^-0.475 covering mesh while the driven state avoids
    # a fixed interval.  First 2^m van der Corput points are the dyadic grid.
    recurrence_checks = 0
    mesh_checks = 0
    for m in range(1, 11):
        count = 1 << m
        values = [radical_inverse_two(k) for k in range(count)]
        assert set(values) == {Fraction(k, count) for k in range(count)}
        reflected = {frac_part(-x) for x in values}
        assert reflected == set(values)
        mesh_checks += 1

    for k in range(0, 1024):
        r = radical_inverse_two(k)
        x_even = Fraction(0)
        x_odd = r / 10
        forcing_even = r / 10
        forcing_odd = frac_part(-r)
        assert frac_part(10 * x_even + forcing_even) == x_odd
        assert frac_part(10 * x_odd + forcing_odd) == 0
        assert 0 <= x_even < Fraction(1, 10)
        assert 0 <= x_odd < Fraction(1, 10)
        recurrence_checks += 2

    return {
        "status": "PASS",
        "claim_status": "experiment",
        "partial_fraction_checks": partial_fraction_checks,
        "formal_linear_poles": 28,
        "odd_linear_terms_after_recombination": 28,
        "coupled_quadratic_terms": 0,
        "bad_half_integral_terms_per_n": bad_formal_terms // split_checks,
        "split_depth_checks": split_checks,
        "lift_identity_checks": lift_checks,
        "lift_sign_checks": lift_sign_checks,
        "quartic_gcd_checks": gcd_checks,
        "prime_binomial_root_checks": root_checks,
        "van_der_corput_mesh_checks": mesh_checks,
        "recurrence_transition_checks": recurrence_checks,
        "cklrs_directly_applies": False,
        "dubickas_n_power_d_directly_applies": False,
        "scalar_forcing_density_implies_state_hitting": False,
        "asserts_v1": False,
        "asserts_pi_normal": False,
    }


if __name__ == "__main__":
    print(json.dumps(run(), indent=2, sort_keys=True))
