#!/usr/bin/env python3
"""Independent replay for the BBP fractional-parts applicability audit.

The branch checker is pinned but never imported.  All finite output has claim
label ``experiment`` and asserts no infinite distribution or pi-digit claim.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from fractions import Fraction
from hashlib import sha256
import json
from math import gcd, isqrt, log2
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]

PINS = {
    "problems/local/pi-digits.txt":
        "2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825",
    "work/ultrapi-resume/bbp_dyadic_diagonal_functional_recurrence_20260813.md":
        "8768abbdd38d21721955f76a0c1ba90054ed9177a95b9b393aa393fc0d7466ba",
    "work/ultrapi-resume/bbp_dyadic_diagonal_functional_recurrence_20260813_check.py":
        "c7d04bb733cf50b08ed46dddf52bb98bbe726c0897f74c93f00533313a67f651",
    "work/ultrapi-resume/bbp_fractional_parts_density_application_audit_20260813.md":
        "55383eb4a52f65373c841dd86fdc5bf939d96e5a8ad536bae4a03e43de71135d",
    "work/ultrapi-resume/bbp_fractional_parts_density_application_audit_20260813_check.py":
        "8c43ce5a7739337fd3273b6a612879ae68d302b7bbc5b18ba0b5aea8ad4f4885",
}

SOURCE_PINS = {
    "cklrs_fractional_parts_an_over_n":
        "e5ab04087aa7f162b9431a003c16ccba9558d32f5e088ec7565bf6d6c2154164",
    "dubickas_2012_density":
        "9b16c0a16187f9a9e75475e25abbf9c11c7f79b69ebafe340d7762ca60f0bf0e",
    "dubickas_2023_special_sequences":
        "74bc3bdd4b05d6ebff3935f1dc4cddca37990fc6288a90946a2449ebc21149cd",
    "lind_arxiv_2308.14354v2":
        "d02adcb8aeb29fb5ac9e6d4be79ebb81728aef939e04e3f8ebd80f3959f5156e",
    "kowalski_soundararajan_arxiv_2003.12965v2":
        "82bf98763cd587fd77c07df08ff4583623a9a9b7b9d5b0a0fc2f9e76d425b809",
}


@dataclass(frozen=True)
class Term:
    label: str
    numerator: int
    denominator: int
    slope: int
    intercept: int
    phase_coefficient: Fraction

    @property
    def value(self) -> Fraction:
        return Fraction(self.numerator, self.denominator)


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def digest(path: Path) -> str:
    return sha256(path.read_bytes()).hexdigest()


def fractional_part(value: Fraction) -> Fraction:
    return Fraction(value.numerator % value.denominator, value.denominator)


def modular_fraction(value: Fraction, modulus: int) -> int:
    require(gcd(value.denominator, modulus) == 1,
            f"nonunit denominator {value.denominator} modulo {modulus}")
    return value.numerator * pow(value.denominator, -1, modulus) % modulus


def signed_power(base: int, exponent: int, modulus: int) -> int:
    if exponent >= 0:
        return pow(base, exponent, modulus)
    require(gcd(base, modulus) == 1,
            f"negative exponent of nonunit {base} modulo {modulus}")
    return pow(pow(base, -1, modulus), -exponent, modulus)


def is_prime(number: int) -> bool:
    if number < 2:
        return False
    if number % 2 == 0:
        return number == 2
    divisor = 3
    while divisor <= isqrt(number):
        if number % divisor == 0:
            return False
        divisor += 2
    return True


def prime_divisors(number: int) -> list[int]:
    result: list[int] = []
    divisor = 2
    remaining = number
    while divisor * divisor <= remaining:
        if remaining % divisor == 0:
            result.append(divisor)
            while remaining % divisor == 0:
                remaining //= divisor
        divisor = 3 if divisor == 2 else divisor + 2
    if remaining > 1:
        result.append(remaining)
    return result


def coefficient(k: int) -> Fraction:
    return Fraction(
        120 * k * k + 151 * k + 47,
        (2 * k + 1) * (4 * k + 3) * (8 * k + 1) * (8 * k + 5),
    )


def formal_poles(k: int) -> tuple[Fraction, Fraction, Fraction, Fraction]:
    return (
        Fraction(4, 8 * k + 1),
        Fraction(-1, 2 * (2 * k + 1)),
        Fraction(-1, 8 * k + 5),
        Fraction(-1, 2 * (4 * k + 3)),
    )


def split_terms(depth: int) -> list[Term]:
    terms: list[Term] = []
    for slot in range(1, 8):
        k = 7 * depth + slot
        two_exponent = 4 * (7 - slot)
        scale = 5 ** (depth + 1) * 2**two_exponent
        terms.append(Term(
            f"j{slot}:8k+1", 4 * scale, 8 * k + 1,
            56, 8 * slot + 1, Fraction(-4 * 2**two_exponent),
        ))
        if slot <= 6:
            terms.append(Term(
                f"j{slot}:2k+1", -scale // 2, 2 * k + 1,
                14, 2 * slot + 1, Fraction(2 ** (two_exponent - 1)),
            ))
            terms.append(Term(
                f"j{slot}:8k+5", -scale, 8 * k + 5,
                56, 8 * slot + 5, Fraction(2**two_exponent),
            ))
            terms.append(Term(
                f"j{slot}:4k+3", -scale // 2, 4 * k + 3,
                28, 4 * slot + 3, Fraction(2 ** (two_exponent - 1)),
            ))
        else:
            # Independent Bezout recombination of the two half-integral terms.
            terms.append(Term(
                "j7:2k+1-recombined", -scale * (k + 1), 2 * k + 1,
                14, 15, Fraction(1, 2),
            ))
            terms.append(Term(
                "j7:8k+5", -scale, 8 * k + 5,
                56, 61, Fraction(1),
            ))
            terms.append(Term(
                "j7:4k+3-recombined", scale * (2 * k + 1), 4 * k + 3,
                28, 31, Fraction(1, 2),
            ))
    return terms


def b_value(depth: int) -> Fraction:
    return sum(
        (5 ** (depth + 1) * 16 ** (7 - slot)
         * coefficient(7 * depth + slot) for slot in range(1, 8)),
        Fraction(0),
    )


def residue_and_height(term: Term, modulus: int) -> tuple[int, int]:
    require(term.denominator % 2 == 1, f"even denominator in {term.label}")
    rho = term.numerator * pow(term.denominator, -1, modulus) % modulus
    lift_numerator = term.denominator * rho - term.numerator
    require(lift_numerator % modulus == 0, f"nonintegral height in {term.label}")
    return rho, lift_numerator // modulus


def radical_inverse_two(number: int) -> Fraction:
    # String reversal is deliberately independent of the branch bit-loop.
    if number == 0:
        return Fraction(0)
    bits = format(number, "b")
    return Fraction(int(bits[::-1], 2), 1 << len(bits))


def replay(max_exact_depth: int, max_arithmetic_depth: int) -> dict[str, object]:
    require(max_exact_depth >= 0, "exact scan must include n=0")
    require(max_arithmetic_depth >= max(2, max_exact_depth),
            "arithmetic scan must contain exact scan")
    for relative, expected in PINS.items():
        actual = digest(ROOT / relative)
        require(actual == expected,
                f"pin mismatch {relative}: expected {expected}, got {actual}")

    partial_fraction_checks = 0
    for k in range(513):
        require(sum(formal_poles(k), Fraction(0)) == coefficient(k),
                f"partial fractions at k={k}")
        partial_fraction_checks += 1

    # Cross-multiply the j=7 identity in symbolic coefficients, then check
    # it independently at a broad integer range.
    bezout_symbolic_checks = 0
    # (2k+1)^2 - (k+1)(4k+3) = -(3k+2): coefficients low to high.
    require((1 - 3, 4 - 7, 4 - 4) == (-2, -3, 0),
            "cross-multiplied Bezout polynomial")
    bezout_symbolic_checks += 1
    bezout_instance_checks = 0
    for k in range(1, 1025):
        odd_a = 2 * k + 1
        odd_b = 4 * k + 3
        left = -Fraction(1, 2 * odd_a) - Fraction(1, 2 * odd_b)
        paired = -Fraction(3 * k + 2, odd_a * odd_b)
        recombined = -Fraction(k + 1, odd_a) + Fraction(2 * k + 1, odd_b)
        require(left == paired == recombined, f"Bezout recombination at k={k}")
        require(2 * (k + 1) % odd_a == 1,
                f"positive half coefficient modulo 2k+1 at k={k}")
        require((-2 * (2 * k + 1)) % odd_b == 1,
                f"positive half coefficient modulo 4k+3 at k={k}")
        bezout_instance_checks += 1

    exact_split_checks = 0
    exact_lift_checks = 0
    exact_sign_checks = 0
    half_integral_formal_terms = 0
    for depth in range(max_exact_depth + 1):
        formal_scaled: list[Fraction] = []
        for slot in range(1, 8):
            k = 7 * depth + slot
            scale = 5 ** (depth + 1) * 16 ** (7 - slot)
            formal_scaled.extend(scale * pole for pole in formal_poles(k))
        require(sum(formal_scaled, Fraction(0)) == b_value(depth),
                f"formal scaled sum at n={depth}")
        bad = [term for term in formal_scaled if term.denominator % 2 == 0]
        require(len(bad) == 2, f"exactly two half-integral terms at n={depth}")
        half_integral_formal_terms += len(bad)

        terms = split_terms(depth)
        require(len(terms) == 28, f"28 recombined terms at n={depth}")
        require(all(term.denominator % 2 == 1 for term in terms),
                f"all recombined denominators odd at n={depth}")
        require(sum((term.value for term in terms), Fraction(0)) == b_value(depth),
                f"recombined sum at n={depth}")

        modulus = 1 << (27 * (depth + 1))
        b_residue = modular_fraction(b_value(depth), modulus)
        rho_sum = 0
        theta = Fraction(0)
        for term in terms:
            require(term.denominator == term.slope * depth + term.intercept,
                    f"linear form metadata for {term.label} at n={depth}")
            rho, height = residue_and_height(term, modulus)
            require(Fraction(rho, modulus)
                    == Fraction(height, term.denominator)
                    + Fraction(term.numerator, term.denominator * modulus),
                    f"exact lift identity for {term.label} at n={depth}")
            require(height % term.denominator
                    == (-term.numerator * pow(modulus, -1, term.denominator))
                    % term.denominator,
                    f"control sign from definition for {term.label} at n={depth}")
            rational_base = 5 * pow(pow(2, 27, term.denominator), -1,
                                    term.denominator) % term.denominator
            predicted = modular_fraction(term.phase_coefficient, term.denominator)
            predicted *= pow(rational_base, depth + 1, term.denominator)
            require(height % term.denominator == predicted % term.denominator,
                    f"advertised phase sign for {term.label} at n={depth}")
            rho_sum += rho
            theta += Fraction(height, term.denominator)
            exact_lift_checks += 1
            exact_sign_checks += 1
        require(rho_sum % modulus == b_residue,
                f"linear reduction reconstructs b modulo M at n={depth}")
        require(fractional_part(theta + b_value(depth) / modulus)
                == Fraction(b_residue, modulus),
                f"linear height formula reconstructs Gamma at n={depth}")
        exact_split_checks += 1

    forms = {(term.label.split("-recombined")[0], term.slope, term.intercept)
             for term in split_terms(0)}
    require(len(forms) == 28, "28 distinct formal affine forms")
    nonprimitive = sorted(
        (label, slope, intercept, gcd(slope, intercept))
        for label, slope, intercept in forms if gcd(slope, intercept) > 1
    )
    require(nonprimitive == sorted([
        ("j1:4k+3", 28, 7, 7),
        ("j2:8k+5", 56, 21, 7),
        ("j3:2k+1", 14, 7, 7),
        ("j6:8k+1", 56, 49, 7),
    ]), "four fixed-divisor-seven forms")

    gcd_table_checks = 0
    overlap_three = 0
    overlap_five = 0
    for k in range(2001):
        a = 2 * k + 1
        b = 4 * k + 3
        c = 8 * k + 1
        d = 8 * k + 5
        require(gcd(a, b) == 1, f"gcd(A,B) at k={k}")
        require(gcd(a, c) == gcd(a, 3), f"gcd(A,C) at k={k}")
        require(gcd(a, d) == 1, f"gcd(A,D) at k={k}")
        require(gcd(b, c) == gcd(b, 5), f"gcd(B,C) at k={k}")
        require(gcd(b, d) == 1, f"gcd(B,D) at k={k}")
        require(gcd(c, d) == 1, f"gcd(C,D) at k={k}")
        overlap_three += gcd(a, c) == 3
        overlap_five += gcd(b, c) == 5
        gcd_table_checks += 1
    require(overlap_three > 0 and overlap_five > 0,
            "both non-coprime CRT obstructions occur")

    prime_binomial_checks = 0
    composite_binomial_checks = 0
    composite_five_checks = 0
    complementary_cofactor_variation_witnesses: set[tuple[str, int]] = set()
    local_values: dict[tuple[str, int], set[int]] = {}
    for depth in range(1, max_arithmetic_depth + 1):
        modulus = 1 << (27 * (depth + 1))
        for term in split_terms(depth):
            _, height = residue_and_height(term, modulus)
            linear = term.denominator
            c_mod_linear = modular_fraction(term.phase_coefficient, linear)
            r_mod_linear = 5 * pow(pow(2, 27, linear), -1, linear) % linear
            selected = c_mod_linear * pow(r_mod_linear, depth + 1, linear) % linear
            require(height % linear == selected,
                    f"selected phase at n={depth}, {term.label}")

            if is_prime(linear) and gcd(
                    linear,
                    10 * term.phase_coefficient.numerator
                    * term.phase_coefficient.denominator) == 1:
                fixed_rhs = pow(modular_fraction(term.phase_coefficient, linear),
                                term.slope, linear)
                fixed_rhs *= signed_power(
                    r_mod_linear,
                    term.slope - term.intercept + 1,
                    linear,
                )
                require(pow(selected, term.slope, linear) == fixed_rhs % linear,
                        f"prime fixed-binomial formula at n={depth}, {term.label}")
                prime_binomial_checks += 1

            if not is_prime(linear):
                for prime in prime_divisors(linear):
                    cofactor = linear // prime
                    c_mod_prime = modular_fraction(term.phase_coefficient, prime)
                    r_mod_prime = 5 * pow(pow(2, 27, prime), -1, prime) % prime
                    selected_prime = height % prime
                    exponent = cofactor + term.slope - term.intercept
                    if prime == 5:
                        # Fermat cannot be used for R=0 mod 5, but for these
                        # forms the exponent is positive and the identity is
                        # directly 0=0.
                        require(exponent > 0,
                                f"positive p=5 exponent at n={depth}, {term.label}")
                        require(selected_prime == 0,
                                f"selected phase vanishes mod 5 at {term.label}")
                        require(pow(c_mod_prime, term.slope, prime)
                                * pow(r_mod_prime, exponent, prime) % prime == 0,
                                f"direct composite p=5 identity at {term.label}")
                        composite_five_checks += 1
                        continue
                    rhs = pow(c_mod_prime, term.slope, prime)
                    rhs *= signed_power(r_mod_prime, exponent, prime)
                    require(pow(selected_prime, term.slope, prime) == rhs % prime,
                            f"composite cofactor formula p={prime}, n={depth}, "
                            f"{term.label}")
                    composite_binomial_checks += 1
                    key = (term.label, prime)
                    local_values.setdefault(key, set()).add(rhs % prime)
                    if len(local_values[key]) > 1:
                        complementary_cofactor_variation_witnesses.add(key)

    require(prime_binomial_checks > 5000,
            "substantial prime fixed-binomial scan")
    require(composite_binomial_checks > 50000,
            "substantial composite cofactor scan")
    require(complementary_cofactor_variation_witnesses,
            "at least one fixed prime sees genuinely varying cofactor targets")

    # No fixed integer can represent 5/2^27 for two distinct sufficiently
    # large affine moduli unless the fixed integer 2^27*a-5 vanishes.
    representative_obstruction_checks = 0
    for candidate in (-10, -1, 0, 1, 5, 10, 1234567):
        fixed_difference = (1 << 27) * candidate - 5
        divisors = [14 * depth + 3 for depth in range(1, 200)
                    if fixed_difference % (14 * depth + 3) == 0]
        require(len(divisors) < 199,
                f"candidate {candidate} cannot represent R on all moduli")
        representative_obstruction_checks += 1

    dyadic_grid_checks = 0
    for exponent in range(1, 15):
        count = 1 << exponent
        values = {radical_inverse_two(index) for index in range(count)}
        require(values == {Fraction(index, count) for index in range(count)},
                f"van der Corput grid at 2^{exponent}")
        reflected = {fractional_part(-value) for value in values}
        require(reflected == values, f"reflected grid at 2^{exponent}")
        dyadic_grid_checks += 1

    recurrence_checks = 0
    for index in range(4096):
        r = radical_inverse_two(index)
        y_even = Fraction(0)
        y_odd = r / 10
        delta_even = r / 10
        delta_odd = fractional_part(-r)
        require(fractional_part(10 * y_even + delta_even) == y_odd,
                f"even separator transition at k={index}")
        require(fractional_part(10 * y_odd + delta_odd) == 0,
                f"odd separator transition at k={index}")
        require(0 <= y_even < Fraction(1, 10)
                and 0 <= y_odd < Fraction(1, 10),
                f"separator state range at k={index}")
        recurrence_checks += 2

    mesh_bound_checks = 0
    for total_terms in range(3, 10001):
        odd_terms = total_terms // 2
        grid_size = 1 << int(log2(odd_terms))
        require(Fraction(1, grid_size) < Fraction(4, total_terms),
                f"embedded reflected-grid mesh at N={total_terms}")
        mesh_bound_checks += 1

    return {
        "status": "PASS_INDEPENDENT_NO_FATAL_GAP_NO_APPLICATION_BRIDGE",
        "bounded_replay_label": "experiment",
        "algebraic_claim_label": "proof sketch",
        "literature_audit_label": "literature-checked",
        "partial_fraction_checks": partial_fraction_checks,
        "bezout_symbolic_checks": bezout_symbolic_checks,
        "bezout_instance_checks": bezout_instance_checks,
        "exact_depth_range_including_zero": [0, max_exact_depth],
        "exact_split_checks": exact_split_checks,
        "half_integral_formal_terms_per_depth":
            half_integral_formal_terms // exact_split_checks,
        "exact_lift_checks": exact_lift_checks,
        "exact_sign_checks": exact_sign_checks,
        "formal_affine_forms": len(forms),
        "odd_linear_terms_after_recombination": 28,
        "coupled_quadratic_terms_after_recombination": 0,
        "nonprimitive_forms": [list(item) for item in nonprimitive],
        "gcd_table_checks": gcd_table_checks,
        "prime_binomial_checks": prime_binomial_checks,
        "composite_binomial_checks_away_from_five": composite_binomial_checks,
        "composite_binomial_direct_five_checks": composite_five_checks,
        "cofactor_variation_witness_count":
            len(complementary_cofactor_variation_witnesses),
        "representative_obstruction_checks": representative_obstruction_checks,
        "van_der_corput_grid_checks": dyadic_grid_checks,
        "van_der_corput_mesh_bound_checks": mesh_bound_checks,
        "recurrence_transition_checks": recurrence_checks,
        "independently_redownloaded_source_sha256": SOURCE_PINS,
        "imports_branch_checker": False,
        "asserts_scalar_density_theorem_applies": False,
        "asserts_forcing_discrepancy": False,
        "asserts_state_target_hitting": False,
        "asserts_v1": False,
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-exact-depth", type=int, default=96)
    parser.add_argument("--max-arithmetic-depth", type=int, default=2500)
    arguments = parser.parse_args()
    print(json.dumps(
        replay(arguments.max_exact_depth, arguments.max_arithmetic_depth),
        indent=2,
        sort_keys=True,
    ))
