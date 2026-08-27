#!/usr/bin/env python3
"""Independent replay for the frozen even-depth BBP dyadic-mixing addendum.

This checker deliberately does not import the supplied checker.  Its main
modular evaluator starts from the frozen identity F(0)=0 and iterates
F(x+1)=16F(x)+a(x), rather than truncating the defining infinite series at
each requested value.  It also reconstructs the ordinary rational BBP
numerators and checks the complete (not merely prefixed) selected coordinate.

Every bounded result printed here has label ``experiment``.  The all-index
valuation theorem remains a ``proof sketch`` and no decimal return is asserted.
"""

from __future__ import annotations

from fractions import Fraction
from hashlib import sha256
import json
from math import gcd
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]

PINS = {
    "problems/local/pi-digits.txt":
        "2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825",
    "work/ultrapi-resume/bbp_all_depth_two_adic_attack.md":
        "9c1282724c7999fd67133a3f0e756015e564dc6b7a2a1ec44f2efe892b2653d9",
    "work/ultrapi-resume/bbp_high_dyadic_archimedean_separator_20260813.md":
        "d0d975ff9bab6ce456723085cb3e031a3be83a171fa6a94d8656d76d8b0457b3",
    "work/ultrapi-resume/bbp_high_dyadic_archimedean_separator_20260813_check.py":
        "69d07d421b215b85bd5e5f7a7d4036c9d38544a3a0a8fc7db4a6947687cb0ab8",
    "work/ultrapi-resume/bbp_even_depth_dyadic_mixing_20260813.md":
        "3d47a6a17e759d18b0aafb6215405226eadb99d1d83241a160dc93f6f8a3e623",
    "work/ultrapi-resume/bbp_even_depth_dyadic_mixing_20260813_check.py":
        "d05ed720b94c23d3d59c23b6bc300d46e6d88dc9f37d31ab5dddb604ce19a839",
}

MAX_F_ISOMETRY_PRECISION = 9
MAX_H_MIXING_PRECISION = 10
MAX_EXACT_M = 80
FULL_COORDINATE_RECURRENCE_M = 20


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def digest(path: Path) -> str:
    return sha256(path.read_bytes()).hexdigest()


def lcm(left: int, right: int) -> int:
    return left // gcd(left, right) * right


def v2(integer: int) -> int:
    require(integer != 0, "v2 requires a nonzero integer")
    integer = abs(integer)
    return (integer & -integer).bit_length() - 1


def v2_rational(value: Fraction) -> int:
    require(value != 0, "v2 requires a nonzero rational")
    return v2(value.numerator) - v2(value.denominator)


def compact_numerator(k: int) -> int:
    return 120 * k * k + 151 * k + 47


def compact_denominator(k: int) -> int:
    return (2 * k + 1) * (4 * k + 3) * (8 * k + 1) * (8 * k + 5)


def coefficient_compact(k: int) -> Fraction:
    return Fraction(compact_numerator(k), compact_denominator(k))


def coefficient_four_poles(k: int) -> Fraction:
    return (
        Fraction(4, 8 * k + 1)
        - Fraction(2, 8 * k + 4)
        - Fraction(1, 8 * k + 5)
        - Fraction(1, 8 * k + 6)
    )


def rational_mod(value: Fraction, bits: int) -> int:
    require(bits >= 1, "positive dyadic precision required")
    require(value.denominator % 2 == 1, "two-integral rational required")
    modulus = 1 << bits
    return value.numerator * pow(value.denominator, -1, modulus) % modulus


def coefficient_mod(k: int, bits: int) -> int:
    modulus = 1 << bits
    denominator = compact_denominator(k)
    require(denominator % 2 == 1, f"odd compact denominator at k={k}")
    return compact_numerator(k) * pow(denominator, -1, modulus) % modulus


def f_samples_by_recurrence(
    arguments: set[int], bits: int
) -> dict[int, int]:
    """Evaluate nonnegative integer values using only the F recurrence."""
    require(arguments and min(arguments) >= 0, "nonnegative arguments needed")
    modulus = 1 << bits
    requested = set(arguments)
    samples: dict[int, int] = {}
    current = 0
    if 0 in requested:
        samples[0] = current
    for k in range(max(requested)):
        current = (16 * current + coefficient_mod(k, bits)) % modulus
        if k + 1 in requested:
            samples[k + 1] = current
    require(samples.keys() == requested, "every requested F sample was produced")
    return samples


def h_from_f_residue(m: int, f_residue: int, bits: int) -> int:
    modulus = 1 << bits
    return pow(25, m, modulus) * f_residue % modulus


def f_zero_truncation(bits: int) -> int:
    """Directly replay F(0) modulo 2^bits from its reflected series."""
    modulus = 1 << bits
    total = 0
    for j in range((bits - 1) // 4 + 1):
        total += pow(16, j, modulus) * rational_mod(
            coefficient_compact(-1 - j), bits
        )
    return total % modulus


def build_exact_endpoints() -> tuple[dict[int, Fraction], dict[int, tuple[int, int]], int, int]:
    """Reconstruct F(14m+1)=A_(14m)/L_(14m) for 0 <= m <= 80."""
    common = 1
    scaled = 0
    exact_f = Fraction(0)
    f_at_m: dict[int, Fraction] = {}
    integers_at_m: dict[int, tuple[int, int]] = {}
    coefficient_checks = 0
    rational_identity_checks = 0

    for k in range(14 * MAX_EXACT_M + 1):
        compact = coefficient_compact(k)
        original = coefficient_four_poles(k)
        require(compact == original, f"four-pole coefficient at k={k}")
        coefficient_checks += 1

        denominator = compact_denominator(k)
        next_common = lcm(common, denominator)
        scaled = (
            16 * (next_common // common) * scaled
            + compact_numerator(k) * (next_common // denominator)
        )
        common = next_common
        exact_f = 16 * exact_f + original
        require(
            exact_f == Fraction(scaled, common),
            f"ordinary identity F(k+1)=A_k/L_k at k={k}",
        )
        rational_identity_checks += 1

        if k % 14 == 0:
            m = k // 14
            f_at_m[m] = exact_f
            integers_at_m[m] = (common, scaled)

    require(set(f_at_m) == set(range(MAX_EXACT_M + 1)),
            "all exact even-depth endpoints present")
    return (
        f_at_m,
        integers_at_m,
        coefficient_checks,
        rational_identity_checks,
    )


def replay() -> dict[str, object]:
    for relative, expected in PINS.items():
        path = ROOT / relative
        require(path.is_file(), f"missing pinned input: {relative}")
        require(digest(path) == expected, f"hash mismatch: {relative}")

    # This is only a finite consequence of the frozen analytic proof F(0)=0.
    f_zero_checks = 0
    reflected_coefficient_checks = 0
    for bits in range(1, 65):
        for j in range((bits - 1) // 4 + 1):
            require(
                coefficient_compact(-1 - j) == coefficient_four_poles(-1 - j),
                f"reflected four-pole coefficient at bits={bits}, j={j}",
            )
            reflected_coefficient_checks += 1
        require(f_zero_truncation(bits) == 0, f"F(0) modulo 2^{bits}")
        f_zero_checks += 1

    # Direct finite replay of the inherited pairwise F isometry.  The proof in
    # the audit uses F=X+2G; these rows merely try to falsify it.
    f_fixed_level_bijection_checks = 0
    f_isometry_pair_checks = 0
    for bits in range(1, MAX_F_ISOMETRY_PRECISION + 1):
        period = 1 << bits
        samples = f_samples_by_recurrence(set(range(period)), bits)
        require(set(samples.values()) == set(range(period)),
                f"F fixed-level bijection modulo 2^{bits}")
        f_fixed_level_bijection_checks += period
        for first in range(period):
            for second in range(first):
                difference = samples[first] - samples[second]
                require(difference != 0, f"F injectivity modulo 2^{bits}")
                require(
                    v2(difference) == v2(first - second),
                    f"F isometry modulo 2^{bits}, x={first}, y={second}",
                )
                f_isometry_pair_checks += 1

    # Test two arbitrary complete blocks at every level.  This checks both the
    # quotient statement and the report's "any complete block" quantifier.
    h_parity_checks = 0
    fixed_level_bijection_checks = 0
    fixed_level_pair_checks = 0
    quotient_periodicity_checks = 0
    s_one_edge_checks = 0
    blocks_per_precision = 2
    for bits in range(1, MAX_H_MIXING_PRECISION + 1):
        modulus = 1 << bits
        period = 1 << (bits - 1)
        starts = (0, 3 * period + 1)
        indices: set[int] = set()
        for start in starts:
            indices.update(range(start, start + period))
        indices.update(range(2 * period))
        arguments = {14 * m + 1 for m in indices}
        f_samples = f_samples_by_recurrence(arguments, bits)

        def h_mod(m: int) -> int:
            return h_from_f_residue(m, f_samples[14 * m + 1], bits)

        for start in starts:
            values = [h_mod(m) for m in range(start, start + period)]
            require(set(values) == set(range(1, modulus, 2)),
                    f"H odd-residue block at bits={bits}, start={start}")
            h_parity_checks += period
            fixed_level_bijection_checks += period
            for offset, first in enumerate(range(start, start + period)):
                for second in range(start, first):
                    difference = h_mod(first) - h_mod(second)
                    require(difference != 0,
                            f"H injectivity at bits={bits}, start={start}")
                    require(
                        v2(difference) == 1 + v2(first - second),
                        f"H scaled isometry at bits={bits}, m={first}, m'={second}",
                    )
                    fixed_level_pair_checks += 1

        for m in range(period):
            require(h_mod(m + period) == h_mod(m),
                    f"H quotient periodicity at bits={bits}, m={m}")
            quotient_periodicity_checks += 1

        if bits == 1:
            require(period == 1, "s=1 source is Z/1Z")
            require(h_mod(0) == 1 and h_mod(starts[1]) == 1,
                    "s=1 target is the singleton odd residue")
            s_one_edge_checks += 3

    (
        f_at_m,
        integers_at_m,
        coefficient_checks,
        rational_identity_checks,
    ) = build_exact_endpoints()

    endpoint_unit_checks = 0
    exact_scaled_isometry_checks = 0
    exact_two_term_decomposition_checks = 0
    exact_valuation_gap_checks = 0
    h_exact = {m: Fraction(25**m) * f_at_m[m]
               for m in range(MAX_EXACT_M + 1)}
    for m in range(MAX_EXACT_M + 1):
        require(v2_rational(f_at_m[m]) == 0,
                f"F(14m+1) is a unit at m={m}")
        require(v2_rational(h_exact[m]) == 0,
                f"H(m) is a unit at m={m}")
        endpoint_unit_checks += 2

    for m in range(1, MAX_EXACT_M + 1):
        for m_prime in range(m):
            distance = m - m_prime
            expected = 1 + v2(distance)
            first_term = Fraction(25**distance) * (
                f_at_m[m] - f_at_m[m_prime]
            )
            second_term = Fraction(25**distance - 1) * f_at_m[m_prime]
            reconstructed = Fraction(25**m_prime) * (first_term + second_term)
            require(reconstructed == h_exact[m] - h_exact[m_prime],
                    f"two-term H decomposition at m={m}, m'={m_prime}")
            exact_two_term_decomposition_checks += 1
            require(v2_rational(first_term) == expected,
                    f"first-term valuation at m={m}, m'={m_prime}")
            require(v2_rational(second_term) == expected + 2,
                    f"two-valuation gap at m={m}, m'={m_prime}")
            exact_valuation_gap_checks += 2
            require(v2_rational(h_exact[m] - h_exact[m_prime]) == expected,
                    f"exact scaled isometry at m={m}, m'={m_prime}")
            exact_scaled_isometry_checks += 1

    # Reconstruct the ordinary reduced fraction V/(2^(54m)L), check that its
    # dyadic denominator really has all 54m bits, and compare the complete
    # selected coordinate with H(m), not just a short prefix.
    exact_selected_coordinate_checks = 0
    complete_coordinate_recurrence_checks = 0
    for m in range(1, MAX_EXACT_M + 1):
        common, scaled = integers_at_m[m]
        require(common % 2 == 1, f"L_(14m) odd at m={m}")
        require(scaled % 2 == 1, f"A_(14m) odd at m={m}")
        bits = 54 * m
        selected_fraction = Fraction(
            25**m * scaled,
            (1 << bits) * common,
        )
        require(v2(selected_fraction.denominator) == bits,
                f"complete reduced dyadic denominator at m={m}")
        odd_denominator = selected_fraction.denominator >> bits
        direct_coordinate = (
            selected_fraction.numerator
            * pow(odd_denominator, -1, 1 << bits)
            % (1 << bits)
        )
        from_h = rational_mod(h_exact[m], bits)
        require(direct_coordinate == from_h,
                f"w_(2m) equals H(m) at all 54m bits, m={m}")
        exact_selected_coordinate_checks += 1

        if m <= FULL_COORDINATE_RECURRENCE_M:
            f_sample = f_samples_by_recurrence({14 * m + 1}, bits)[14 * m + 1]
            from_modular_recurrence = h_from_f_residue(m, f_sample, bits)
            require(from_modular_recurrence == direct_coordinate,
                    f"full-coordinate recurrence at m={m}")
            complete_coordinate_recurrence_checks += 1

    # Adversarial distances are evaluated by the recurrence at a precision
    # above the predicted valuation.  Modular LTE avoids constructing huge
    # integers and includes far offsets and both subtraction orientations.
    adversarial_scaled_isometry_checks = 0
    adversarial_lte_checks = 0
    for power in range(13):
        bits = power + 9
        modulus = 1 << bits
        pairs: list[tuple[int, int]] = []
        for base in (0, 2, 101, 4096):
            for odd in (1, 3, 5, 31):
                pairs.append((base + (odd << power), base))
        arguments = {14 * m + 1 for pair in pairs for m in pair}
        f_samples = f_samples_by_recurrence(arguments, bits)
        for first, second in pairs:
            distance = first - second
            expected = 1 + v2(distance)
            first_h = h_from_f_residue(
                first, f_samples[14 * first + 1], bits
            )
            second_h = h_from_f_residue(
                second, f_samples[14 * second + 1], bits
            )
            forward = first_h - second_h
            backward = second_h - first_h
            require(forward != 0 and backward != 0,
                    f"nonzero adversarial difference at m={first}, m'={second}")
            require(v2(forward) == expected and v2(backward) == expected,
                    f"oriented adversarial isometry at m={first}, m'={second}")
            adversarial_scaled_isometry_checks += 2

            lte_residue = (pow(25, distance, modulus) - 1) % modulus
            require(lte_residue != 0, f"nonzero LTE residue at d={distance}")
            require(v2(lte_residue) == 3 + v2(distance),
                    f"LTE valuation at d={distance}")
            adversarial_lte_checks += 1

    return {
        "status": "PASS",
        "finite_claim_label": "experiment",
        "audited_theorem_claim_label": "proof sketch",
        "maximum_F_isometry_precision": MAX_F_ISOMETRY_PRECISION,
        "maximum_H_mixing_precision": MAX_H_MIXING_PRECISION,
        "fixed_level_blocks_per_precision": blocks_per_precision,
        "maximum_exact_even_index_m": MAX_EXACT_M,
        "f_zero_checks": f_zero_checks,
        "reflected_coefficient_checks": reflected_coefficient_checks,
        "four_pole_coefficient_checks": coefficient_checks,
        "rational_identity_checks": rational_identity_checks,
        "f_fixed_level_bijection_checks": f_fixed_level_bijection_checks,
        "f_isometry_pair_checks": f_isometry_pair_checks,
        "h_parity_checks": h_parity_checks,
        "fixed_level_bijection_checks": fixed_level_bijection_checks,
        "fixed_level_pair_checks": fixed_level_pair_checks,
        "quotient_periodicity_checks": quotient_periodicity_checks,
        "s_one_edge_checks": s_one_edge_checks,
        "endpoint_unit_checks": endpoint_unit_checks,
        "exact_two_term_decomposition_checks": exact_two_term_decomposition_checks,
        "exact_valuation_gap_checks": exact_valuation_gap_checks,
        "exact_scaled_isometry_checks": exact_scaled_isometry_checks,
        "exact_selected_complete_coordinate_checks": exact_selected_coordinate_checks,
        "complete_coordinate_recurrence_checks": complete_coordinate_recurrence_checks,
        "adversarial_scaled_isometry_checks": adversarial_scaled_isometry_checks,
        "adversarial_two_adic_lifting_checks": adversarial_lte_checks,
        "full_diagonal_period_at_even_depth_m": "2^(54*m-1)",
        "asserts_diagonal_mixing": False,
        "asserts_colored_return": False,
        "asserts_v1": False,
    }


if __name__ == "__main__":
    print(json.dumps(replay(), indent=2, sort_keys=True))
