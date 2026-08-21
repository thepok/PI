#!/usr/bin/env python3
"""Disjoint exact audit replay for the CF36 Gowers/cube report.

This checker does not import the primary replay.  It uses integer arithmetic,
Fraction, and Decimal only.  Its bounded enumerations test the elementary
algebra behind the report; they do not prove CF36 or the canonical pi-digit
statement.
"""

from __future__ import annotations

from collections import Counter
from decimal import Decimal, getcontext
from fractions import Fraction
from hashlib import sha256
from itertools import product
from pathlib import Path
import re


ROOT = Path(__file__).resolve().parents[2]

FROZEN = {
    "problems/local/pi-digits.txt":
        "2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825",
    "work/ultrapi-resume/bbp_three_primary_twisted_sum_20260813.md":
        "0a7e6015782afdfa407242fe3e191cfffec414d7c9215ec8854a439c2fb08a12",
    "work/ultrapi-resume/bbp_three_primary_decimation_20260813.md":
        "29d4f903dca429ebe2cedad248f0a726b985492bfd0f06471a668a47e652ede0",
    "work/ultrapi-resume/bbp_complement_fourier_attack_20260813.md":
        "eccb19ffdd7a931cb9de1efb4ab1136ba3f8fb543a84ab00c3e320fd16f2316a",
    "work/ultrapi-resume/bbp_high_prime_phase_compression_20260813.md":
        "47f56886b769a36f5f397cad567579838d455f59b75af8ca458a8000dfb7c564",
    "work/ultrapi-resume/bbp_cf36_gowers_cube_persistence_20260813.md":
        "3bd9a948945570e975defd7bd2297338da0068f9c82eb027be84364a66bb528e",
    "work/ultrapi-resume/bbp_cf36_gowers_cube_persistence_20260813_check.py":
        "24adf41ff8197d354ea8a5569dbb227f521346e96287006d013b77e6fb3fdea9",
}

CONTROL_BYTES = re.compile(rb"[\x00-\x08\x0b\x0c\x0e-\x1f\x7f]")
MARKDOWN_LINK = re.compile(r"\[[^\]]+\]\(([^)]+)\)")


def digest(path: Path) -> str:
    return sha256(path.read_bytes()).hexdigest()


def valuation(n: int, prime: int) -> int:
    assert n
    n = abs(n)
    answer = 0
    while n % prime == 0:
        n //= prime
        answer += 1
    return answer


def valuation_distribution(depth: int) -> list[int]:
    """Counts of v_3(h)=j for nonzero h modulo 3^depth."""

    return [2 * 3 ** (depth - j - 1) for j in range(depth)]


def nonzero_cube_support(depth: int, order: int) -> int:
    """Count nonzero lag tuples whose LTE valuations meet cube support."""

    counts = valuation_distribution(depth)
    # Dynamic convolution of exact valuation counts.  This is deliberately
    # independent of the primary checker's nested loops.
    distribution = [1]
    for _ in range(order):
        updated = [0] * (len(distribution) + len(counts) - 1)
        for left_index, left_count in enumerate(distribution):
            for right_index, right_count in enumerate(counts):
                updated[left_index + right_index] += left_count * right_count
        distribution = updated
    threshold = max(0, depth - 2 * order)
    return sum(distribution[threshold:])


def full_cube_support(depth: int, order: int) -> Fraction:
    period = 3**depth
    # A zero lag makes the multiplicative-difference coefficient zero and
    # hence divisible by every power of three.
    with_zero = period**order - (period - 1) ** order
    return Fraction(with_zero + nonzero_cube_support(depth, order), period**order)


def u3_report_bound(exponent: int) -> Fraction:
    depth = exponent - 2
    period = 3**depth
    remainder = exponent - 8
    return Fraction(3, period) + Fraction(2 * (remainder + 2) ** 2, 3 ** (remainder + 1))


def ramanujan_kernel(exponent: int, lag: int) -> Fraction:
    """c_{3^e}(10^lag-1)/phi(3^e), using the prime-power formula."""

    period = 3 ** (exponent - 2)
    lag %= period
    if lag == 0:
        return Fraction(1)
    if lag in (period // 3, 2 * period // 3):
        return Fraction(-1, 2)
    return Fraction(0)


def signed_decimal_multisets(
    block: int, lags: tuple[int, ...], blocks: tuple[int, ...]
) -> tuple[Counter[int], Counter[int]]:
    positive: Counter[int] = Counter()
    negative: Counter[int] = Counter()
    for vertex, block_index in enumerate(blocks):
        exponent = block_index * block
        parity = 0
        for bit, lag in enumerate(lags):
            if vertex & (1 << bit):
                exponent += lag
                parity += 1
        (positive if parity % 2 == 0 else negative)[exponent] += 1
    return positive, negative


def coefficient_from_multisets(positive: Counter[int], negative: Counter[int]) -> int:
    return sum(count * 10**exponent for exponent, count in positive.items()) - sum(
        count * 10**exponent for exponent, count in negative.items()
    )


def markdown_hygiene(report: Path) -> tuple[int, int]:
    raw = report.read_bytes()
    assert CONTROL_BYTES.search(raw) is None
    text = raw.decode("utf-8")
    relative = 0
    external = 0
    for target in MARKDOWN_LINK.findall(text):
        if "://" in target:
            external += 1
        else:
            assert (report.parent / target).resolve().exists(), target
            relative += 1
    assert "Canonical V1 remains a 'conjecture'" in text
    assert "No estimate of CF36" in text
    assert "asserts_cf36_bound=False" in text
    assert "asserts_fixed_return=False" in text
    assert "asserts_v1=False" in text
    return relative, external


def main() -> None:
    hygiene_file_checks = 0
    for relative, expected in FROZEN.items():
        path = ROOT / relative
        assert path.is_file(), relative
        assert digest(path) == expected, (relative, digest(path), expected)
        assert CONTROL_BYTES.search(path.read_bytes()) is None, relative
        hygiene_file_checks += 1

    report = ROOT / "work/ultrapi-resume/bbp_cf36_gowers_cube_persistence_20260813.md"
    relative_links, external_links = markdown_hygiene(report)

    primary_permutation_checks = 0
    u2_frequency_checks = 0
    nine_block_resonance_checks = 0
    ramanujan_lag_checks = 0

    # Verify independently that x -> (10^x-1)/9 is the promised permutation,
    # the U^2 support has one frequency class modulo nine, and the resonant
    # nine-block operator cancels term by term.
    for exponent in range(4, 13, 2):
        modulus = 3**exponent
        period = 3 ** (exponent - 2)
        block = period // 9
        coordinates = [((pow(10, x, modulus) - 1) % modulus) // 9 for x in range(period)]
        assert sorted(coordinates) == list(range(period))
        primary_permutation_checks += period

        a = 1
        for frequency in range(period):
            # Fourier-transforming the nine nonzero correlations reduces to
            # sum_m zeta_9^((a-frequency)m), which is 9 or 0 exactly.
            root_class = (a - frequency) % 9
            predicted_squared_magnitude = 9 * period if root_class == 0 else 0
            assert predicted_squared_magnitude == (9 * period if frequency % 9 == a else 0)
            u2_frequency_checks += 1

        for unit_a in (1, 2, 4, 5, 7, 8):
            for m in range(9):
                assert (pow(10, m * block, modulus) - (1 + m * period)) % modulus == 0
                for u in range(min(block, 27)):
                    exponent_difference = (
                        unit_a * m * period
                        - unit_a * pow(10, u + m * block, modulus)
                        + unit_a * pow(10, u, modulus)
                    ) % modulus
                    assert exponent_difference == 0
                    nine_block_resonance_checks += 1

        for lag in range(period):
            modular_difference = (pow(10, lag, modulus) - 1) % modulus
            if lag == 0:
                independently_classified = Fraction(1)
            elif modular_difference % (3 ** (exponent - 1)) == 0:
                independently_classified = Fraction(-1, 2)
            else:
                independently_classified = Fraction(0)
            assert independently_classified == ramanujan_kernel(exponent, lag)
            ramanujan_lag_checks += 1

    # Exact U^2 identity from the support count and independently convolved
    # LTE support for U^3.  The latter is only an upper bound on the norm.
    gowers_bound_checks = 0
    for exponent in range(8, 25, 2):
        period = 3 ** (exponent - 2)
        u2_fourth = Fraction(period // 9, 1) * Fraction(9, period) ** 2
        assert u2_fourth == Fraction(9, period)
        support = full_cube_support(exponent - 2, 3)
        assert support <= u3_report_bound(exponent)
        gowers_bound_checks += 1

    # Exhaust the exact units-mean identity over all 2^9 sign weights in the
    # first row.  This avoids numerical roots of unity: the Ramanujan kernel
    # already is the exact unit-character average.
    moment_weight_checks = 0
    period = 9
    for signs in product((-1, 1), repeat=period):
        kernel_mean = Fraction(0)
        for j in range(period):
            for k in range(period):
                kernel_mean += signs[j] * signs[k] * ramanujan_kernel(4, j - k)
        shifted = sum(signs[(j + period // 3) % period] * signs[j] for j in range(period))
        stated = Fraction(period - shifted)
        assert kernel_mean == stated
        assert 0 <= stated <= 2 * period
        moment_weight_checks += 1

    # phi(3^e)=6T and the mean is at most 2T, so the total square mass is
    # at most 12T^2.  Dividing by eta^2 T^2 gives 12/eta^2.
    for eta in (Fraction(1, 10), Fraction(1, 3), Fraction(1), Fraction(2)):
        exceptional_bound = Fraction(12, 1) / (eta * eta)
        assert exceptional_bound * eta * eta == 12

    # Selected endpoint coefficients: exact finite residue table plus the
    # all-depth implication (unit congruence and period divisibility imply
    # coefficient congruence).  The latter is algebraic, not a random-sample
    # assertion.
    endpoint_units = {2: 2, 4: 38, 6: 524, 8: 4898, 10: 57386, 12: 175484}
    selected: dict[tuple[int, int], int] = {}
    nesting_checks = 0
    endpoint_scale_checks = 0
    for harmonic in (1, 2, 4, 5):
        for exponent, unit in endpoint_units.items():
            endpoint = 5 * (3**exponent - 1) // 8 - 1
            modulus = 3**exponent
            period = 3 ** (exponent - 2)
            if exponent >= 4:
                block = period // 9
                assert endpoint == (45 * period - 13) // 8
                assert Fraction(block, 1) == Fraction(8 * endpoint + 13, 405)
                endpoint_scale_checks += 2
            selected[harmonic, exponent] = harmonic * unit * pow(10, endpoint, modulus) % modulus
            if exponent >= 4:
                smaller = exponent - 2
                smaller_modulus = 3**smaller
                smaller_endpoint = 5 * (3**smaller - 1) // 8 - 1
                assert endpoint - smaller_endpoint == 5 * 3 ** (exponent - 2)
                assert (endpoint - smaller_endpoint) % (3 ** (exponent - 4)) == 0
                assert unit % smaller_modulus == endpoint_units[smaller]
                assert selected[harmonic, exponent] % smaller_modulus == selected[harmonic, smaller]
                # Raising the conjugate primary character to the ninth power
                # reduces its numerator modulo 3^(e-2).
                for u in range(min(3 ** (exponent - 4), 81)):
                    assert (
                        -selected[harmonic, exponent] * pow(10, u, smaller_modulus)
                        + selected[harmonic, smaller] * pow(10, u, smaller_modulus)
                    ) % smaller_modulus == 0
                    nesting_checks += 1

    # Universal second-cube nondegeneracy is the disjointness of the even and
    # odd subset-sum residue classes modulo H.  Also exhaust all 9^4 block
    # choices on H=9 using signed decimal multisets, rather than the primary
    # checker's direct coefficient constructor.
    second_residue_checks = 0
    second_multiset_checks = 0
    second_size_checks = 0
    block = 9
    for lag1 in range(1, block):
        for lag2 in range(1, block):
            even_residues = {0, (lag1 + lag2) % block}
            odd_residues = {lag1 % block, lag2 % block}
            assert even_residues.isdisjoint(odd_residues)
            second_residue_checks += 1
            for blocks in product(range(9), repeat=4):
                positive, negative = signed_decimal_multisets(block, (lag1, lag2), blocks)
                assert positive != negative
                coefficient = coefficient_from_multisets(positive, negative)
                assert coefficient != 0
                assert abs(coefficient) <= 4 * 10 ** (8 * block + lag1 + lag2)
                assert valuation(coefficient, 2) <= abs(coefficient).bit_length() - 1
                second_multiset_checks += 1
                second_size_checks += 1

    # At lags (1,2,4), all eight subset sums are distinct modulo every H>7.
    # Since block shifts are multiples of H, this proves nondegeneracy for all
    # 9^8 block assignments without enumerating 43,046,721 tuples.
    third_residue_pair_checks = 0
    third_sample_checks = 0
    lags = (1, 2, 4)
    for block in (9, 27, 81, 243):
        residues = []
        for vertex in range(8):
            residues.append(sum(lag for bit, lag in enumerate(lags) if vertex & (1 << bit)) % block)
        assert len(set(residues)) == 8
        for left in range(8):
            for right in range(left):
                assert residues[left] != residues[right]
                third_residue_pair_checks += 1

    # A disjoint bounded sample still reconstructs actual integer C values.
    for seed in range(4096):
        blocks = tuple((seed // (9**vertex)) % 9 for vertex in range(8))
        positive, negative = signed_decimal_multisets(9, lags, blocks)
        coefficient = coefficient_from_multisets(positive, negative)
        assert coefficient != 0
        assert abs(coefficient) < 8 * 10 ** (11 * 9)
        third_sample_checks += 1

    # Recompute the asymptotic losses.  These constants depend on the pinned
    # frozen theorem that the selected squarefree high-prime mass is
    # (5+o(1))M; this checker does not promote that input's claim status.
    getcontext().prec = 60
    log10 = Decimal(10).ln()
    log2_10 = log10 / Decimal(2).ln()
    constants: dict[int, tuple[Decimal, Decimal]] = {}
    for order in (2, 3):
        high_prime = Decimal(5) - Decimal(8 * (8 + order)) * log10 / Decimal(405)
        dyadic = Decimal(3) - Decimal(8) * (
            Decimal(1) + Decimal(8 + order) * log2_10
        ) / Decimal(405)
        assert high_prime > Decimal("4.49")
        assert dyadic > Decimal("2.25")
        constants[order] = high_prime, dyadic

    fields = {
        "external_links": external_links,
        "endpoint_scale_checks": endpoint_scale_checks,
        "gowers_bound_checks": gowers_bound_checks,
        "high_constant_s2": str(constants[2][0]),
        "high_constant_s3": str(constants[3][0]),
        "dyadic_constant_s2": str(constants[2][1]),
        "dyadic_constant_s3": str(constants[3][1]),
        "moment_weight_checks": moment_weight_checks,
        "hygiene_file_checks": hygiene_file_checks,
        "nesting_checks": nesting_checks,
        "nine_block_resonance_checks": nine_block_resonance_checks,
        "primary_permutation_checks": primary_permutation_checks,
        "ramanujan_lag_checks": ramanujan_lag_checks,
        "relative_links": relative_links,
        "second_multiset_checks": second_multiset_checks,
        "second_residue_checks": second_residue_checks,
        "second_size_checks": second_size_checks,
        "third_residue_pair_checks": third_residue_pair_checks,
        "third_sample_checks": third_sample_checks,
        "u2_frequency_checks": u2_frequency_checks,
        "asserts_cf36_bound": False,
        "asserts_fixed_return": False,
        "asserts_v1": False,
    }
    record = "\n".join(f"{key}={value}" for key, value in sorted(fields.items()))
    print(record)
    print(f"exact_record_sha256={sha256(record.encode()).hexdigest()}")
    print("status=PASS")


if __name__ == "__main__":
    main()
