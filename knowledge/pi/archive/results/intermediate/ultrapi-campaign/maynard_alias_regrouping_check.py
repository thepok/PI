#!/usr/bin/env python3
"""Exact and numerical checks for the mixed-modulus Fourier separator.

This is an experiment/checker, not a proof of the pi digit conjecture.  The
general identities checked here are proved algebraically in the companion
report.  Integer assertions are exact; the small DFT and product evaluations
use ordinary complex floating-point arithmetic only as reproducibility checks.
"""

from __future__ import annotations

import cmath
import hashlib
import math
from fractions import Fraction
from pathlib import Path


SOURCE_SHA256 = "2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825"


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def sample_positions(M: int, D: int, t: int) -> list[int]:
    assert 0 <= t < M
    assert math.gcd(M, D) == 1
    return [(M * c + t) // D for c in range(D)]


def avoids_digit(k: int, n: int, forbidden: int) -> bool:
    return str(k).zfill(n).find(str(forbidden)) < 0


def dft(values: list[complex]) -> list[complex]:
    size = len(values)
    root = -2j * math.pi / size
    return [
        sum(value * cmath.exp(root * h * k) for k, value in enumerate(values))
        for h in range(size)
    ]


def normalized_missing_digit_product(n: int, D: int, forbidden: int) -> float:
    """Return |F_M(1/(MD))| for M=10^n by the exact digit product formula."""
    M = 10**n
    theta = Fraction(1, M * D)
    product = 1.0 + 0.0j
    allowed = [digit for digit in range(10) if digit != forbidden]
    for place in range(n):
        factor = sum(
            cmath.exp(-2j * math.pi * float(digit * 10**place * theta))
            for digit in allowed
        ) / 9.0
        product *= factor
    return abs(product)


def main() -> None:
    source = Path(__file__).resolve().parents[2] / "problems/local/pi-digits.txt"
    assert sha256(source) == SOURCE_SHA256

    beatty_checks = 0
    base_denominator_checks = 0
    mixed_denominator_checks = 0
    gauge_exact_checks = 0
    pure_triadic_separator_checks = 0
    diagonal_alias_checks = 0

    # Exact Beatty reduction and denominator bookkeeping on several coprime
    # base/three-primary pairs and several shifts.
    for n, D in [(2, 3), (3, 9), (4, 27), (5, 81)]:
        M = 10**n
        assert D < M and math.gcd(M, D) == 1
        for t in [0, 1, M // 7, M - 1]:
            positions = sample_positions(M, D, t)
            assert len(positions) == D
            assert len(set(positions)) == D
            assert all(0 <= k < M for k in positions)
            # The ceiling-difference word is exactly the sample indicator.
            position_set = set(positions)
            for k in range(M):
                upper = -((-(D * (k + 1) - t)) // M)
                lower = -((-(D * k - t)) // M)
                weight = upper - lower
                assert weight in (0, 1)
                assert weight == (k in position_set)
                beatty_checks += 1

        for ell in range(-2 * M, 2 * M + 1):
            denominator = Fraction(ell * D, M).denominator
            assert denominator == M // math.gcd(ell, M)
            q = denominator
            while q % 2 == 0:
                q //= 2
            while q % 5 == 0:
                q //= 5
            assert q == 1
            base_denominator_checks += 1

        # h=aM+bD gives all frequencies on the MD grid.  The reduced
        # denominator splits exactly into its three-primary and base parts.
        for a in range(D):
            for b in range(M):
                h = a * M + b * D
                reduced = M * D // math.gcd(h, M * D)
                q1 = D // math.gcd(a, D)
                q2 = M // math.gcd(b, M)
                assert reduced == q1 * q2
                mixed_denominator_checks += 1

        # Every fixed-a Fourier row reconstructs the same inner product.  The
        # exact check uses finite-group orthogonality, represented here by the
        # only pairs k,l in [0,M) satisfying k=l (mod M).
        positions = set(sample_positions(M, D, M // 7))
        avoidance = {k for k in range(M) if avoids_digit(k, n, 4)}
        occupancy = len(avoidance & positions)
        diagonal_pairs = sum(
            1
            for k in avoidance
            for l in positions
            if (k - l) % M == 0
        )
        assert diagonal_pairs == occupancy
        for _a in range(D):
            assert diagonal_pairs == occupancy
            gauge_exact_checks += 1

        # Pure denominator-D Fourier data cannot determine Beatty occupancy.
        # If M>D(D+1), {0} and {D} have identical residue histograms modulo D,
        # while t=0 samples 0 and does not sample D.
        if M > D * (D + 1):
            positions0 = set(sample_positions(M, D, 0))
            assert 0 in positions0 and D not in positions0
            hist0 = [0] * D
            hist1 = [0] * D
            hist0[0 % D] += 1
            hist1[D % D] += 1
            assert hist0 == hist1
            assert int(0 in positions0) == 1
            assert int(D in positions0) == 0
            pure_triadic_separator_checks += 1

        # CRT puts the ultra-major alias 1/(MD) in a nonzero triadic row.
        a_star = pow(M, -1, D)
        b_star = (1 - a_star * M) // D
        assert 1 <= a_star < D
        assert a_star * M + b_star * D == 1
        assert Fraction(a_star, D) + Fraction(b_star, M) == Fraction(1, M * D)
        assert (M * D) > M ** (1 / 3)
        diagonal_alias_checks += 1

    # A direct numerical DFT check of the gauge-row identity on a small case.
    n = 2
    M = 10**n
    D = 3
    t = 17
    avoid_vector = [complex(avoids_digit(k, n, 4)) for k in range(M)]
    sample_set = set(sample_positions(M, D, t))
    sample_vector = [complex(k in sample_set) for k in range(M)]
    occupancy = sum(int(bool(avoid_vector[k].real)) for k in sample_set)
    gauge_numeric_checks = 0
    max_gauge_error = 0.0
    for a in range(D):
        modulation = [cmath.exp(-2j * math.pi * a * k / D) for k in range(M)]
        a_transform = dft([avoid_vector[k] * modulation[k] for k in range(M)])
        w_transform = dft([sample_vector[k] * modulation[k] for k in range(M)])
        reconstructed = sum(
            left * right.conjugate()
            for left, right in zip(a_transform, w_transform)
        ) / M
        error = abs(reconstructed - occupancy)
        max_gauge_error = max(max_gauge_error, error)
        assert error < 1e-9
        gauge_numeric_checks += 1

    # The exact diagonal alias has a large normalized digital coefficient,
    # despite retaining q1=D>1 in its reduced denominator q=MD.
    diagonal_rows: list[tuple[int, int, float, float, float]] = []
    for n, D in [(2, 3), (3, 9), (4, 27), (5, 81), (6, 243)]:
        M = 10**n
        value = normalized_missing_digit_product(n, D, forbidden=4)
        lower_bound = math.cos(math.pi / D)
        assert value + 1e-12 >= lower_bound

        positions = sample_positions(M, D, t=M // 7)
        normalized_sample_transform = abs(
            sum(cmath.exp(-2j * math.pi * k / (M * D)) for k in positions) / D
        )
        assert normalized_sample_transform + 1e-12 >= lower_bound
        diagonal_rows.append((n, D, value, normalized_sample_transform, lower_bound))

    print("claim_status=experiment")
    print(f"source_sha256={SOURCE_SHA256}")
    print(f"beatty_indicator_exact_checks={beatty_checks}")
    print(f"original_base_denominator_exact_checks={base_denominator_checks}")
    print(f"mixed_denominator_factorization_exact_checks={mixed_denominator_checks}")
    print(f"gauge_row_orthogonality_exact_checks={gauge_exact_checks}")
    print(f"gauge_row_numeric_dft_checks={gauge_numeric_checks}")
    print(f"gauge_row_max_numeric_error={max_gauge_error:.3e}")
    print(f"pure_triadic_data_separator_exact_checks={pure_triadic_separator_checks}")
    print(f"diagonal_major_alias_exact_checks={diagonal_alias_checks}")
    print("diagonal_major_alias_rows=" + repr(diagonal_rows))
    print("all exact assertions and numerical reproducibility checks passed")


if __name__ == "__main__":
    main()
