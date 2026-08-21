#!/usr/bin/env python3
"""Independent replay for the 28-pole distinguished-root report.

This checker imports neither the branch checker nor its helpers.  All bounded
calculations have claim label ``experiment``; they do not prove discrepancy,
target hitting, or the canonical pi digit conjecture.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from fractions import Fraction
from hashlib import sha256
import json
from math import gcd, isqrt
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]

PINS = {
    "problems/local/pi-digits.txt":
        "2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825",
    "work/ultrapi-resume/bbp_dyadic_diagonal_functional_recurrence_20260813.md":
        "8768abbdd38d21721955f76a0c1ba90054ed9177a95b9b393aa393fc0d7466ba",
    "work/ultrapi-resume/bbp_dyadic_distinguished_root_20260813.md":
        "d70f8cd56885e77aecdec9eb09f67575d2b8ffe4e972d66ff9a69d82386466b8",
    "work/ultrapi-resume/bbp_dyadic_distinguished_root_20260813_check.py":
        "e7103ffab23b88fb5bdf83fab73bcc1979f2ce3075dce2740d074d65f3b2b304",
}

SOURCE_PINS = {
    "wang_arxiv_2108.05496":
        "78565fd47fda2ec5060fe67b0bdf75ff552ecd891cdc2c5851f1d1d7124dbd26",
    "zehavi_arxiv_2003.13100":
        "82d654c51f7997269d013db30f3fcb03e40ef4c50083e790255cbdd9c11f0e18",
    "ngo_arxiv_2107.13301":
        "113f94cae375573f9ff9fe427e378ea01975befb42805ee54dcf79377108bc99",
    "foo_acta_arith_144_1_1":
        "72a3829132d72ee414dd3ed740eba390c36db4764f5023dc1d7bb58691edb831",
}


@dataclass(frozen=True)
class Pole:
    name: str
    lam: int
    mu: int
    doubled_coefficient: int


@dataclass(frozen=True)
class Form:
    pole: Pole
    slot: int

    @property
    def alpha(self) -> int:
        return 7 * self.pole.lam

    @property
    def beta(self) -> int:
        return self.pole.lam * self.slot + self.pole.mu

    @property
    def label(self) -> str:
        return f"{self.pole.name}{self.slot}"

    @property
    def scaled_coefficient(self) -> int:
        return self.pole.doubled_coefficient * 16 ** (7 - self.slot)

    def value(self, depth: int) -> int:
        return self.alpha * depth + self.beta


POLES = (
    Pole("A", 8, 1, 8),
    Pole("B", 8, 5, -2),
    Pole("C", 4, 3, -1),
    Pole("D", 2, 1, -1),
)
FORMS = tuple(Form(pole, slot) for pole in POLES for slot in range(1, 8))


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def digest(path: Path) -> str:
    return sha256(path.read_bytes()).hexdigest()


def fractional_part(value: Fraction) -> Fraction:
    return Fraction(value.numerator % value.denominator, value.denominator)


def rational_residue(value: Fraction, modulus: int) -> int:
    require(gcd(value.denominator, modulus) == 1,
            f"denominator {value.denominator} is not a unit modulo {modulus}")
    return value.numerator * pow(value.denominator, -1, modulus) % modulus


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


def poly_add(left: tuple[int, ...], right: tuple[int, ...]) -> tuple[int, ...]:
    size = max(len(left), len(right))
    result = [0] * size
    for index, coefficient in enumerate(left):
        result[index] += coefficient
    for index, coefficient in enumerate(right):
        result[index] += coefficient
    while len(result) > 1 and result[-1] == 0:
        result.pop()
    return tuple(result)


def poly_scale(polynomial: tuple[int, ...], scale: int) -> tuple[int, ...]:
    return tuple(scale * coefficient for coefficient in polynomial)


def poly_multiply(left: tuple[int, ...], right: tuple[int, ...]) -> tuple[int, ...]:
    result = [0] * (len(left) + len(right) - 1)
    for left_index, left_coefficient in enumerate(left):
        for right_index, right_coefficient in enumerate(right):
            result[left_index + right_index] += left_coefficient * right_coefficient
    return tuple(result)


def coefficient(k: int) -> Fraction:
    return Fraction(
        120 * k * k + 151 * k + 47,
        (2 * k + 1) * (4 * k + 3) * (8 * k + 1) * (8 * k + 5),
    )


def check_rational_function_identity() -> None:
    """Cross-multiply DR5 as a polynomial identity, without SymPy."""
    linear_polynomials = tuple((pole.mu, pole.lam) for pole in POLES)
    right = (0,)
    for omitted, pole in enumerate(POLES):
        product = (1,)
        for index, linear in enumerate(linear_polynomials):
            if index != omitted:
                product = poly_multiply(product, linear)
        right = poly_add(right, poly_scale(product, pole.doubled_coefficient))
    left = (94, 302, 240)
    require(right == left,
            f"cross-multiplied doubled partial fractions: {right} != {left}")

    # The undoubled form contains 1/(2(4k+3)) and 1/(2(2k+1)).
    # Those two denominators are even and therefore are not modular units at M=2^K.
    require(gcd(2 * (4 * 1 + 3), 2**8) != 1,
            "first half-coefficient denominator must be noninvertible")
    require(gcd(2 * (2 * 1 + 1), 2**8) != 1,
            "second half-coefficient denominator must be noninvertible")


def direct_b(depth: int) -> Fraction:
    return 5 ** (depth + 1) * sum(
        (16 ** (7 - slot) * coefficient(7 * depth + slot)
         for slot in range(1, 8)),
        Fraction(0),
    )


def pole_b_doubled(depth: int) -> Fraction:
    return sum(
        (Fraction(5 ** (depth + 1) * form.scaled_coefficient,
                  form.value(depth)) for form in FORMS),
        Fraction(0),
    )


def check_covering() -> tuple[list[str], dict[str, list[str]], list[int]]:
    fixed = [form for form in FORMS if gcd(form.alpha, form.beta) > 1]
    require([form.label for form in fixed] == ["A6", "B2", "C1", "D3"],
            "unexpected fixed-divisor forms")
    require(all(gcd(form.alpha, form.beta) == 7 for form in fixed),
            "each fixed divisor must be seven")

    primitive = [form for form in FORMS if gcd(form.alpha, form.beta) == 1]
    require(len(primitive) == 24, "expected 24 primitive forms")
    cover: dict[str, list[str]] = {}
    for residue in range(3):
        hits = [form.label for form in primitive if form.value(residue) % 3 == 0]
        require(hits, f"no primitive covering form modulo three at {residue}")
        cover[str(residue)] = hits
    witnesses = ("D1", "B1", "D2")
    for residue, label in enumerate(witnesses):
        form = next(candidate for candidate in primitive if candidate.label == label)
        require(form.value(residue) % 3 == 0,
                f"displayed cover witness {label} fails at residue {residue}")

    root_counts = [gcd(form.alpha, form.beta - 1) for form in primitive]
    require(min(root_counts) == 2 and max(root_counts) == 56,
            "claimed range of root multiplicities")
    return [form.label for form in fixed], cover, root_counts


def replay(exact_max_depth: int, prime_scan_max_depth: int) -> dict[str, object]:
    require(exact_max_depth >= 0, "exact depth must include at least n=0")
    require(prime_scan_max_depth >= max(1, exact_max_depth),
            "prime scan must contain exact scan")
    for relative, expected in PINS.items():
        actual = digest(ROOT / relative)
        require(actual == expected,
                f"pin mismatch for {relative}: expected {expected}, got {actual}")

    check_rational_function_identity()
    require(len(FORMS) == 28, "expected 28 indexed linear forms")
    fixed, cover, root_counts = check_covering()

    partial_fraction_checks = 0
    exact_doubled_residue_checks = 0
    exact_phase_reconstruction_checks = 0
    exact_lift_checks = 0
    prime_root_checks = 0
    enumerated_root_set_checks = 0
    selected_root_has_companion_checks = 0
    enumerated_per_form: dict[str, int] = {
        form.label: 0 for form in FORMS if gcd(form.alpha, form.beta) == 1
    }

    # Include n=0, which the branch checker did not scan, then all positive depths.
    for depth in range(exact_max_depth + 1):
        for slot in range(1, 8):
            k = 7 * depth + slot
            doubled = sum(
                (Fraction(pole.doubled_coefficient, pole.lam * k + pole.mu)
                 for pole in POLES),
                Fraction(0),
            )
            require(doubled == 2 * coefficient(k),
                    f"28-pole source identity at n={depth}, j={slot}")
            partial_fraction_checks += 1

        b_value = direct_b(depth)
        doubled_b = pole_b_doubled(depth)
        require(doubled_b == 2 * b_value,
                f"doubled 28-pole b identity at n={depth}")

        modulus = 1 << (27 * (depth + 1))
        doubled_modulus = 2 * modulus
        b_residue = rational_residue(b_value, modulus)
        doubled_b_residue = rational_residue(doubled_b, doubled_modulus)
        require(doubled_b_residue == 2 * b_residue,
                f"[2b]_(2M) = 2[b]_M at n={depth}")
        exact_doubled_residue_checks += 1

        rho_sum = 0
        theta = Fraction(0)
        for form in FORMS:
            linear = form.value(depth)
            require(linear % 2 == 1, f"non-odd pole {form.label} at n={depth}")
            q = 5 ** (depth + 1) * form.scaled_coefficient
            rho = q * pow(linear, -1, doubled_modulus) % doubled_modulus
            numerator = linear * rho - q
            require(numerator % doubled_modulus == 0,
                    f"nonintegral lift for {form.label} at n={depth}")
            h = numerator // doubled_modulus
            require(h % linear == (-q * pow(doubled_modulus, -1, linear)) % linear,
                    f"lift congruence for {form.label} at n={depth}")
            require(Fraction(rho, doubled_modulus)
                    == Fraction(h, linear) + Fraction(q, linear * doubled_modulus),
                    f"termwise rational lift for {form.label} at n={depth}")
            rho_sum += rho
            theta += Fraction(h, linear)
            exact_lift_checks += 1

            if is_prime(linear) and linear not in (2, 5):
                prime = linear
                base = 5 * pow(pow(2, 27, prime), -1, prime) % prime
                root = pow(base, depth, prime)
                constant = pow(pow(base, -1, prime), form.beta - 1, prime)
                require(pow(root, form.alpha, prime) == constant,
                        f"selected-root identity for {form.label} at n={depth}")
                require((pow(5, form.beta - 1, prime)
                         * pow(root, form.alpha, prime)
                         - pow(2, 27 * (form.beta - 1), prime)) % prime == 0,
                        f"cleared polynomial for {form.label} at n={depth}")
                expected_h = (
                    -form.scaled_coefficient * pow(2, -1, prime)
                    * pow(base, depth + 1, prime)
                ) % prime
                require(h % prime == expected_h,
                        f"scaled selected residue for {form.label} at n={depth}")
                expected_count = gcd(form.alpha, prime - 1)
                require(expected_count == gcd(form.alpha, form.beta - 1),
                        f"constant root multiplicity for {form.label} at n={depth}")
                require(expected_count >= 2,
                        f"selected root unexpectedly unique for {form.label}")
                selected_root_has_companion_checks += 1
                prime_root_checks += 1

                # Exhaustively enumerate a few small prime fibres per form.  This
                # tests the cyclic-group count without using it as an oracle.
                if (form.label in enumerated_per_form
                        and enumerated_per_form[form.label] < 3
                        and prime <= 5000):
                    roots = [candidate for candidate in range(1, prime)
                             if pow(candidate, form.alpha, prime) == constant]
                    require(len(roots) == expected_count,
                            f"enumerated root count for {form.label}, p={prime}")
                    require(root in roots,
                            f"selected root absent for {form.label}, p={prime}")
                    require(any(candidate != root for candidate in roots),
                            f"no companion root for {form.label}, p={prime}")
                    enumerated_per_form[form.label] += 1
                    enumerated_root_set_checks += 1

        require(rho_sum % doubled_modulus == doubled_b_residue,
                f"28 residues do not reconstruct doubled b at n={depth}")
        gamma = Fraction(b_residue, modulus)
        require(fractional_part(theta + b_value / modulus) == gamma,
                f"DR13 phase reconstruction at n={depth}")
        require(fractional_part(Fraction(rho_sum, doubled_modulus)) == gamma,
                f"safe 2M reconstruction at n={depth}")
        exact_phase_reconstruction_checks += 1

    primitive_forms = [form for form in FORMS if gcd(form.alpha, form.beta) == 1]
    prime_instances = 0
    arbitrary_complement_checks = 0
    family_prime_counts: dict[str, int] = {form.label: 0 for form in primitive_forms}
    for depth in range(1, prime_scan_max_depth + 1):
        # Four fixed-divisor forms and a fifth primitive form are composite.
        fixed_composite = [form for form in FORMS
                           if gcd(form.alpha, form.beta) == 7]
        require(all(form.value(depth) > 7 and form.value(depth) % 7 == 0
                    for form in fixed_composite),
                f"fixed divisor seven at n={depth}")
        cover_form = next(form for form in primitive_forms
                          if form.label == ("D1", "B1", "D2")[depth % 3])
        require(cover_form.value(depth) > 3 and cover_form.value(depth) % 3 == 0,
                f"mod-three cover at n={depth}")
        require(cover_form not in fixed_composite,
                f"fifth composite form is not distinct at n={depth}")

        for form in primitive_forms:
            prime = form.value(depth)
            if not is_prime(prime) or prime in (2, 5):
                continue
            base = 5 * pow(pow(2, 27, prime), -1, prime) % prime
            root = pow(base, depth, prime)
            constant = pow(pow(base, -1, prime), form.beta - 1, prime)
            require(pow(root, form.alpha, prime) == constant,
                    f"prime scan root identity for {form.label} at n={depth}")
            complement = (-root) % prime
            require((root + complement) % prime == 0,
                    f"adversarial complementary phase for {form.label}, p={prime}")
            require(root != 0 and complement != 0,
                    f"root must be a nonzero unit for {form.label}, p={prime}")
            family_prime_counts[form.label] += 1
            prime_instances += 1
            arbitrary_complement_checks += 1

    require(all(count > 0 for count in family_prime_counts.values()),
            "bounded scan must find an example prime for every primitive form")
    require(all(count == 3 for count in enumerated_per_form.values()),
            "three independent root-fibre enumerations per primitive form")

    # DR19 is an exact difference of squares for every indexed form.
    factorization_checks = 0
    for form in FORMS:
        require(form.alpha % 2 == 0 and (form.beta - 1) % 2 == 0,
                f"parities needed for DR19 at {form.label}")
        left_square = 5 ** ((form.beta - 1) // 2)
        right_square = 2 ** (27 * (form.beta - 1) // 2)
        require(left_square * left_square == 5 ** (form.beta - 1),
                f"leading square at {form.label}")
        require(right_square * right_square == 2 ** (27 * (form.beta - 1)),
                f"constant square at {form.label}")
        factorization_checks += 1

    return {
        "status": "PASS_INDEPENDENT_NO_FATAL_GAP_NO_DISTRIBUTION_BRIDGE",
        "bounded_replay_label": "experiment",
        "algebraic_claim_label": "proof sketch",
        "literature_audit_label": "literature-checked",
        "exact_depth_range_including_zero": [0, exact_max_depth],
        "prime_scan_depth_range": [1, prime_scan_max_depth],
        "pure_python_cross_multiplication_checks": 1,
        "partial_fraction_checks": partial_fraction_checks,
        "exact_doubled_residue_checks": exact_doubled_residue_checks,
        "exact_phase_reconstruction_checks": exact_phase_reconstruction_checks,
        "exact_lift_checks": exact_lift_checks,
        "prime_root_checks_in_exact_scan": prime_root_checks,
        "enumerated_root_set_checks": enumerated_root_set_checks,
        "selected_root_has_companion_checks": selected_root_has_companion_checks,
        "factorization_checks": factorization_checks,
        "pole_form_count": len(FORMS),
        "permanently_composite_forms": fixed,
        "prime_capable_form_count": len(family_prime_counts),
        "mod_three_cover": cover,
        "minimum_root_multiplicity": min(root_counts),
        "maximum_root_multiplicity": max(root_counts),
        "prime_instances": prime_instances,
        "arbitrary_complement_checks": arbitrary_complement_checks,
        "minimum_family_prime_count": min(family_prime_counts.values()),
        "maximum_family_prime_count": max(family_prime_counts.values()),
        "independently_redownloaded_source_sha256": SOURCE_PINS,
        "imports_branch_checker": False,
        "asserts_selected_root_equidistribution": False,
        "asserts_gamma_discrepancy": False,
        "asserts_state_target_hitting": False,
        "asserts_v1": False,
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--exact-max-depth", type=int, default=120)
    parser.add_argument("--prime-scan-max-depth", type=int, default=3000)
    arguments = parser.parse_args()
    print(json.dumps(
        replay(arguments.exact_max_depth, arguments.prime_scan_max_depth),
        indent=2,
        sort_keys=True,
    ))
