#!/usr/bin/env python3
"""Independent exact replay for the 28-pole distinguished-root branch.

All bounded output has claim label ``experiment``.  The script checks the
exact doubled partial-fraction formula for the BBP dyadic forcing, the
distinguished-root identity at prime linear denominators, the unavoidable
root-selection ambiguity, and the elementary prime-tuple obstructions.  It
does not assert discrepancy for the forcing, target hitting for the moving
state, or canonical V1.
"""

from __future__ import annotations

import argparse
from fractions import Fraction
from hashlib import sha256
import json
from math import gcd, isqrt
from pathlib import Path

import sympy as sp


ROOT = Path(__file__).resolve().parents[2]

PINS = {
    "problems/local/pi-digits.txt":
        "2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825",
    "work/ultrapi-resume/bbp_dyadic_diagonal_functional_recurrence_20260813.md":
        "8768abbdd38d21721955f76a0c1ba90054ed9177a95b9b393aa393fc0d7466ba",
    "work/ultrapi-resume/bbp_dyadic_diagonal_functional_recurrence_20260813_check.py":
        "c7d04bb733cf50b08ed46dddf52bb98bbe726c0897f74c93f00533313a67f651",
}

# 2*a(k) = sum_s doubled_coefficient_s / (lambda_s*k + mu_s).
POLE_FAMILIES = (
    ("A", 8, 1, 8),
    ("B", 8, 5, -2),
    ("C", 4, 3, -1),
    ("D", 2, 1, -1),
)


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def digest(path: Path) -> str:
    return sha256(path.read_bytes()).hexdigest()


def frac(value: Fraction) -> Fraction:
    """Canonical fractional part of an exact rational."""
    return Fraction(value.numerator % value.denominator, value.denominator)


def rational_mod(value: Fraction, modulus: int) -> int:
    """Canonical residue of a rational whose denominator is a unit."""
    require(gcd(value.denominator, modulus) == 1,
            f"nonunit denominator {value.denominator} modulo {modulus}")
    return (value.numerator * pow(value.denominator, -1, modulus)) % modulus


def mod_power(base: int, exponent: int, modulus: int) -> int:
    if exponent >= 0:
        return pow(base, exponent, modulus)
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


def coefficient(k: int) -> Fraction:
    return Fraction(
        120 * k * k + 151 * k + 47,
        (2 * k + 1) * (4 * k + 3) * (8 * k + 1) * (8 * k + 5),
    )


def doubled_partial_fraction(k: int) -> Fraction:
    return sum(
        (Fraction(c, lam * k + mu) for _, lam, mu, c in POLE_FAMILIES),
        Fraction(0),
    )


def forms() -> list[dict[str, int | str]]:
    result: list[dict[str, int | str]] = []
    for name, lam, mu, doubled_coefficient in POLE_FAMILIES:
        for slot in range(1, 8):
            alpha = 7 * lam
            beta = lam * slot + mu
            result.append({
                "name": name,
                "slot": slot,
                "lambda": lam,
                "mu": mu,
                "alpha": alpha,
                "beta": beta,
                "doubled_coefficient": doubled_coefficient,
                "root_count": gcd(alpha, beta - 1),
            })
    return result


def linear_value(form: dict[str, int | str], depth: int) -> int:
    return int(form["alpha"]) * depth + int(form["beta"])


def scaled_coefficient(form: dict[str, int | str]) -> int:
    return int(form["doubled_coefficient"]) * 16 ** (7 - int(form["slot"]))


def direct_b(depth: int) -> Fraction:
    return 5 ** (depth + 1) * sum(
        (16 ** (7 - slot) * coefficient(7 * depth + slot)
         for slot in range(1, 8)),
        Fraction(0),
    )


def doubled_b_from_poles(depth: int, all_forms: list[dict[str, int | str]]) -> Fraction:
    return sum(
        (
            Fraction(
                5 ** (depth + 1) * scaled_coefficient(form),
                linear_value(form, depth),
            )
            for form in all_forms
        ),
        Fraction(0),
    )


def star_discrepancy(values: list[Fraction]) -> float:
    require(values, "star discrepancy needs at least one value")
    ordered = sorted(values)
    count = len(ordered)
    discrepancy = Fraction(0)
    for index, value in enumerate(ordered, start=1):
        discrepancy = max(
            discrepancy,
            Fraction(index, count) - value,
            value - Fraction(index - 1, count),
        )
    return float(discrepancy)


def symbolic_partial_fraction_check() -> None:
    variable = sp.symbols("k")
    numerator = 120 * variable**2 + 151 * variable + 47
    denominator = (
        (2 * variable + 1)
        * (4 * variable + 3)
        * (8 * variable + 1)
        * (8 * variable + 5)
    )
    rhs = sum(
        (sp.Rational(c, 1) / (lam * variable + mu)
         for _, lam, mu, c in POLE_FAMILIES),
        sp.Rational(0),
    )
    require(sp.cancel(2 * numerator / denominator - rhs) == 0,
            "symbolic 28-pole source identity")


def replay(exact_max_depth: int, prime_scan_max_depth: int) -> dict[str, object]:
    for relative, expected in PINS.items():
        actual = digest(ROOT / relative)
        require(actual == expected,
                f"pin mismatch {relative}: expected {expected}, got {actual}")

    require(exact_max_depth >= 1, "exact depth must be positive")
    require(prime_scan_max_depth >= exact_max_depth,
            "prime scan must contain exact scan")

    symbolic_partial_fraction_check()
    all_forms = forms()
    require(len(all_forms) == 28, "exactly 28 pole forms")

    fixed_composite = [
        (str(form["name"]), int(form["slot"]))
        for form in all_forms
        if gcd(int(form["alpha"]), int(form["beta"])) > 1
    ]
    require(fixed_composite == [("A", 6), ("B", 2), ("C", 1), ("D", 3)],
            "four permanently composite forms")
    for form in all_forms:
        common = gcd(int(form["alpha"]), int(form["beta"]))
        if common > 1:
            require(common == 7, "only fixed divisor seven")
            for depth in range(1, 10):
                value = linear_value(form, depth)
                require(value > 7 and value % 7 == 0,
                        "fixed-divisor form is composite")

    prime_capable = [
        form for form in all_forms
        if gcd(int(form["alpha"]), int(form["beta"])) == 1
    ]
    require(len(prime_capable) == 24, "24 primitive linear forms")

    mod_three_cover: dict[str, list[str]] = {}
    for residue in range(3):
        hits = [
            f"{form['name']}{form['slot']}"
            for form in prime_capable
            if linear_value(form, residue) % 3 == 0
        ]
        require(hits, f"mod-three cover at residue {residue}")
        mod_three_cover[str(residue)] = hits
    for depth in range(1, 100):
        require(any(
            linear_value(form, depth) > 3
            and linear_value(form, depth) % 3 == 0
            for form in prime_capable
        ), "remaining 24 forms cannot all be prime")

    reducible_root_polynomials = 0
    for form in all_forms:
        alpha = int(form["alpha"])
        beta = int(form["beta"])
        require(alpha % 2 == 0 and (beta - 1) % 2 == 0,
                "difference-of-squares exponents")
        # 5^(beta-1) X^alpha - 2^(27(beta-1)) = U^2 - V^2.
        require(5 ** (beta - 1) == (5 ** ((beta - 1) // 2)) ** 2,
                "left square coefficient")
        require(2 ** (27 * (beta - 1))
                == (2 ** (27 * (beta - 1) // 2)) ** 2,
                "right square coefficient")
        reducible_root_polynomials += 1

    exact_partial_fraction_checks = 0
    exact_gamma_checks = 0
    exact_lift_checks = 0
    exact_prime_root_checks = 0

    for depth in range(1, exact_max_depth + 1):
        for slot in range(1, 8):
            k = 7 * depth + slot
            require(doubled_partial_fraction(k) == 2 * coefficient(k),
                    f"partial fractions at k={k}")
            exact_partial_fraction_checks += 1

        b_value = direct_b(depth)
        two_b = doubled_b_from_poles(depth, all_forms)
        require(two_b == 2 * b_value, f"doubled b at n={depth}")

        modulus = 1 << (27 * (depth + 1))
        doubled_modulus = 2 * modulus
        b_residue = rational_mod(b_value, modulus)
        two_b_residue = rational_mod(two_b, doubled_modulus)
        require(two_b_residue == 2 * b_residue,
                f"safe doubled lift at n={depth}")

        rho_sum = 0
        theta = Fraction(0)
        for form in all_forms:
            denominator = linear_value(form, depth)
            coefficient_scale = scaled_coefficient(form)
            numerator = 5 ** (depth + 1) * coefficient_scale
            rho = (numerator * pow(denominator, -1, doubled_modulus)) % doubled_modulus
            lift_numerator = denominator * rho - numerator
            require(lift_numerator % doubled_modulus == 0,
                    f"integral lift n={depth}, form={form['name']}{form['slot']}")
            lift = lift_numerator // doubled_modulus
            require((lift - (-numerator * pow(doubled_modulus, -1, denominator)))
                    % denominator == 0,
                    f"lift congruence n={depth}, form={form['name']}{form['slot']}")
            rho_sum += rho
            theta += Fraction(lift, denominator)
            exact_lift_checks += 1

            if is_prime(denominator) and denominator not in (2, 5):
                prime = denominator
                base = (5 * pow(pow(2, 27, prime), -1, prime)) % prime
                root = pow(base, depth, prime)
                alpha = int(form["alpha"])
                beta = int(form["beta"])
                require(pow(root, alpha, prime)
                        == mod_power(base, 1 - beta, prime),
                        f"distinguished root n={depth},p={prime}")
                inv_two = pow(2, -1, prime)
                expected_lift = (
                    -coefficient_scale * inv_two
                    * pow(base, depth + 1, prime)
                ) % prime
                require(lift % prime == expected_lift,
                        f"scaled distinguished root n={depth},p={prime}")
                exact_prime_root_checks += 1

        require(rho_sum % doubled_modulus == two_b_residue,
                f"28 residues reconstruct 2b at n={depth}")
        epsilon = b_value / modulus
        gamma = Fraction(b_residue, modulus)
        require(frac(theta + epsilon) == gamma,
                f"exact 28-phase Gamma at n={depth}")
        exact_gamma_checks += 1

    prime_instances = 0
    root_identity_checks = 0
    root_multiplicity_checks = 0
    adversarial_complement_checks = 0
    family_prime_counts: dict[str, int] = {}
    family_discrepancies: dict[str, float] = {}

    for form in prime_capable:
        key = f"{form['name']}{form['slot']}"
        normalized_roots: list[Fraction] = []
        alpha = int(form["alpha"])
        beta = int(form["beta"])
        expected_root_count = int(form["root_count"])
        require(expected_root_count >= 2,
                f"selection is nontrivial for {key}")
        for depth in range(1, prime_scan_max_depth + 1):
            prime = linear_value(form, depth)
            if not is_prime(prime) or prime in (2, 5):
                continue
            base = (5 * pow(pow(2, 27, prime), -1, prime)) % prime
            root = pow(base, depth, prime)
            require(pow(root, alpha, prime)
                    == mod_power(base, 1 - beta, prime),
                    f"prime-scan root {key},n={depth}")
            require(gcd(alpha, prime - 1) == expected_root_count,
                    f"exact number of roots {key},n={depth}")
            require((-root) % prime != root,
                    f"opposite root differs {key},n={depth}")
            complement = Fraction((-root) % prime, prime)
            require(frac(Fraction(root, prime) + complement) == 0,
                    f"arbitrary complement cancels {key},n={depth}")
            normalized_roots.append(Fraction(root, prime))
            prime_instances += 1
            root_identity_checks += 1
            root_multiplicity_checks += 1
            adversarial_complement_checks += 1
        require(normalized_roots, f"prime scan found a prime for {key}")
        family_prime_counts[key] = len(normalized_roots)
        family_discrepancies[key] = star_discrepancy(normalized_roots)

    return {
        "status": "PASS_NO_APPLICABLE_ROOT_EQUIDISTRIBUTION_BRIDGE",
        "bounded_replay_label": "experiment",
        "analytic_claim_label": "proof sketch",
        "exact_depth_range": [1, exact_max_depth],
        "prime_scan_depth_range": [1, prime_scan_max_depth],
        "symbolic_partial_fraction_checks": 1,
        "pole_form_count": len(all_forms),
        "exact_partial_fraction_checks": exact_partial_fraction_checks,
        "exact_gamma_checks": exact_gamma_checks,
        "exact_lift_checks": exact_lift_checks,
        "exact_prime_root_checks": exact_prime_root_checks,
        "reducible_natural_root_polynomials": reducible_root_polynomials,
        "permanently_composite_forms": [f"{name}{slot}" for name, slot in fixed_composite],
        "prime_capable_form_count": len(prime_capable),
        "mod_three_cover": mod_three_cover,
        "prime_instances": prime_instances,
        "root_identity_checks": root_identity_checks,
        "root_multiplicity_checks": root_multiplicity_checks,
        "adversarial_complement_checks": adversarial_complement_checks,
        "minimum_roots_of_natural_congruence": min(
            int(form["root_count"]) for form in prime_capable
        ),
        "maximum_roots_of_natural_congruence": max(
            int(form["root_count"]) for form in prime_capable
        ),
        "minimum_family_prime_count": min(family_prime_counts.values()),
        "maximum_family_prime_count": max(family_prime_counts.values()),
        "minimum_observed_family_star_discrepancy": min(family_discrepancies.values()),
        "maximum_observed_family_star_discrepancy": max(family_discrepancies.values()),
        "wang_2108_05496_pdf_sha256_directly_inspected":
            "78565fd47fda2ec5060fe67b0bdf75ff552ecd891cdc2c5851f1d1d7124dbd26",
        "zehavi_2003_13100_pdf_sha256_directly_inspected":
            "82d654c51f7997269d013db30f3fcb03e40ef4c50083e790255cbdd9c11f0e18",
        "ngo_2107_13301_pdf_sha256_directly_inspected":
            "113f94cae375573f9ff9fe427e378ea01975befb42805ee54dcf79377108bc99",
        "foo_2010_prime_roots_pdf_sha256_directly_inspected":
            "72a3829132d72ee414dd3ed740eba390c36db4764f5023dc1d7bb58691edb831",
        "asserts_distinguished_root_equidistribution": False,
        "asserts_gamma_discrepancy": False,
        "asserts_x_target_hitting": False,
        "asserts_v1": False,
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--exact-max-depth", type=int, default=80)
    parser.add_argument("--prime-scan-max-depth", type=int, default=5000)
    args = parser.parse_args()
    print(json.dumps(
        replay(args.exact_max_depth, args.prime_scan_max_depth),
        indent=2,
        sort_keys=True,
    ))
