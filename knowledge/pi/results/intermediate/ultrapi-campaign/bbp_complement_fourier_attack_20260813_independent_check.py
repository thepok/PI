#!/usr/bin/env python3
"""Disjoint replay for the frozen BBP complement-Fourier audit.

All finite calculations have claim label ``experiment``.  The program uses
only the Python standard library, does not import NumPy, gmpy2, or any primary
branch checker, and checks the structural identities by integer arithmetic.
"""

from __future__ import annotations

import hashlib
import json
import math
from fractions import Fraction
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
FROZEN = {
    "source": (
        "problems/local/pi-digits.txt",
        "2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825",
    ),
    "primary_report": (
        "work/ultrapi-resume/bbp_complement_fourier_attack_20260813.md",
        "eccb19ffdd7a931cb9de1efb4ab1136ba3f8fb543a84ab00c3e320fd16f2316a",
    ),
    "primary_checker": (
        "work/ultrapi-resume/bbp_complement_fourier_attack_20260813_check.py",
        "4edba7339272813f152dbb9fb2a4af1ef8d8bd8ab76d4a28d45e1eee8494ff4c",
    ),
    "high_prime_report": (
        "work/ultrapi-resume/bbp_high_prime_phase_compression_20260813.md",
        "47f56886b769a36f5f397cad567579838d455f59b75af8ca458a8000dfb7c564",
    ),
    "large_sieve_report": (
        "work/ultrapi-resume/bbp_large_sieve_short_orbit_20260813.md",
        "23b3cba4c2b7c5846b4b18748994db8c9e897725612eaf80d08b32b3a97b781d",
    ),
    "bourgain_chang_pdf": (
        "work/theory/pi-lacunary-near-return-sparsity/library/t124/"
        "bourgain-chang-2006.pdf",
        "a4c130e401ff03a5b91fbd20339f06021f26bf871ca2bb375f2ce25e3ee5d1d7",
    ),
    "kerr_pdf": (
        "work/theory/pi-long-lag-block-collision-decay/library/t70/"
        "kerr-1302.4170v1.pdf",
        "9136dc3965da376942f653b2b06de8d92d7e5e997ee536e1257979698b73e4bd",
    ),
}


def file_sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def check_frozen() -> None:
    for name, (relative, expected) in FROZEN.items():
        actual = file_sha256(ROOT / relative)
        if actual != expected:
            raise AssertionError(("frozen input changed", name, expected, actual))


def primes_upto(limit: int) -> list[int]:
    sieve = bytearray(b"\x01") * (limit + 1)
    sieve[:2] = b"\x00\x00"
    for prime in range(2, math.isqrt(limit) + 1):
        if sieve[prime]:
            sieve[prime * prime : limit + 1 : prime] = b"\x00" * (
                (limit - prime * prime) // prime + 1
            )
    return [value for value in range(2, limit + 1) if sieve[value]]


def factor_with_bound(value: int, bound: int) -> dict[int, int]:
    remainder = value
    result: dict[int, int] = {}
    for prime in primes_upto(bound):
        exponent = 0
        while remainder % prime == 0:
            remainder //= prime
            exponent += 1
        if exponent:
            result[prime] = exponent
    if remainder != 1:
        raise AssertionError(("factorization remainder", remainder, bound))
    return result


def valuation(value: int, prime: int) -> int:
    if value == 0:
        raise ValueError("zero valuation is outside this replay")
    value = abs(value)
    result = 0
    while value % prime == 0:
        value //= prime
        result += 1
    return result


def bbp_partial_sum(depth: int) -> Fraction:
    total = Fraction(0)
    power16 = 1
    for index in range(depth + 1):
        pole = (
            Fraction(4, 8 * index + 1)
            - Fraction(1, 4 * index + 2)
            - Fraction(1, 8 * index + 5)
            - Fraction(1, 8 * index + 6)
        )
        total += pole / power16
        power16 *= 16
    return total


def high_coordinate(depth: int, prime: int) -> Fraction:
    """Six frozen localization rows, independently encoded with Fraction."""

    residue = prime % 4
    if residue not in (1, 3):
        raise AssertionError((depth, prime, residue))
    if 3 * prime > 8 * depth + 5:
        return Fraction(64 if residue == 1 else -32)
    if prime > 2 * depth + 1:
        return Fraction(64) if residue == 1 else Fraction(-128, 3)
    if 5 * prime > 8 * depth + 5:
        return Fraction(56) if residue == 1 else Fraction(-152, 3)
    if 3 * prime > 4 * depth + 3:
        return Fraction(264, 5) if residue == 1 else Fraction(-152, 3)
    if 7 * prime > 8 * depth + 5:
        return Fraction(752, 15) if residue == 1 else Fraction(-152, 3)
    return Fraction(752, 15) if residue == 1 else Fraction(-1040, 21)


def is_integer(value: Fraction) -> bool:
    return value.denominator == 1


def build_row(epoch: int, counters: dict[str, int]) -> dict[str, object]:
    period = 3 ** (epoch - 2)
    block = period // 9
    depth = (5 * (3**epoch - 1)) // 8 - 1
    partial = bbp_partial_sum(depth)
    numerator = partial.numerator
    denominator = partial.denominator
    factors = factor_with_bound(denominator, 8 * depth + 5)

    two_exponent = factors[2]
    assert two_exponent == 4 * depth - valuation(depth + 1, 2)
    assert factors[3] == epoch
    counters["denominator_factor_checks"] += len(factors)

    odd_denominator = denominator >> two_exponent
    dyadic_modulus = 1 << (two_exponent - 4)
    w = numerator * pow(odd_denominator, -1, dyadic_modulus) % dyadic_modulus
    c = (numerator - odd_denominator * w) // dyadic_modulus
    assert w % 2 == 1 and math.gcd(c, odd_denominator) == 1
    assert Fraction(16 * numerator, denominator) == (
        Fraction(w, dyadic_modulus) + Fraction(c, odd_denominator)
    )
    counters["sixteen_scaling_checks"] += 1

    q3 = 3**epoch
    v5 = factors[5]
    q5 = 5**v5
    high_primes = sorted(prime for prime in factors if prime > depth)
    high_product = math.prod(high_primes)
    assert all(factors[prime] == 1 for prime in high_primes)
    small = odd_denominator // (q3 * q5 * high_product)
    assert math.gcd(q3 * q5 * high_product, small) == 1

    beta3 = c * pow(odd_denominator // q3, -1, q3) % q3
    beta5 = c * pow(odd_denominator // q5, -1, q5) % q5
    beta0 = 0 if small == 1 else c * pow(odd_denominator // small, -1, small) % small
    assert beta3 % 3 and beta5 % 5
    assert small == 1 or math.gcd(beta0, small) == 1

    direct_high = Fraction(0)
    reciprocal_lift = Fraction(0)
    grid_numerator = 0
    for prime in high_primes:
        gamma = c * pow(odd_denominator // prime, -1, prime) % prime
        coordinate = high_coordinate(depth, prime)
        local_a = coordinate.numerator
        local_b = coordinate.denominator
        assert gamma == local_a * pow(local_b, -1, prime) % prime
        lift_digit = (-local_a * pow(prime, -1, local_b)) % local_b
        assert is_integer(
            Fraction(gamma, prime)
            - Fraction(lift_digit, local_b)
            - Fraction(local_a, local_b * prime)
        )
        direct_high += Fraction(gamma, prime)
        reciprocal_lift += coordinate / prime
        grid_numerator = (grid_numerator + 105 // local_b * lift_digit) % 105
        counters["local_lift_checks"] += 1

    assert is_integer(direct_high - Fraction(grid_numerator, 105) - reciprocal_lift)
    odd_crt_error = (
        Fraction(c, odd_denominator)
        - Fraction(beta3, q3)
        - Fraction(beta5, q5)
        - (Fraction(beta0, small) if small > 1 else 0)
        - direct_high
    )
    assert is_integer(odd_crt_error)
    counters["odd_crt_checks"] += 1

    # Reduction modulo each high prime proves that no such prime disappears
    # from the reciprocal lift's reduced denominator.
    for prime in high_primes:
        assert reciprocal_lift.denominator % prime == 0
        counters["reciprocal_denominator_checks"] += 1

    # CF12, including the factor 16 and the sign of the static 5-coordinate.
    offsets = sorted({0, 1, block - 1, block, 2 * block, period // 2, period - 1})
    for offset in offsets:
        exponent = depth + offset
        a_value = (10**exponent - 16) // 16
        assert a_value % q5 == q5 - 1
        error = (
            a_value * 16 * partial
            - Fraction(a_value * beta3, q3)
            - Fraction(a_value * w, dyadic_modulus)
            + Fraction(beta5, q5)
            - (Fraction(a_value * beta0, small) if small > 1 else 0)
            - Fraction(a_value * grid_numerator, 105)
            - a_value * reciprocal_lift
        )
        assert is_integer(error)
        counters["cf12_phase_checks"] += 1

    # CF18--CF23 without floating transforms.  The exact block relation fixes
    # the positive primary support class a, hence complement class -a.
    inv16 = pow(16, -1, q3)
    for harmonic in (-5, -2, 1, 4, 7):
        assert harmonic % 3
        support = harmonic * beta3 * inv16 * pow(10, depth, q3) % 9
        assert support in (1, 2, 4, 5, 7, 8)
        for u in range(block):
            base_a = ((pow(10, depth + u, q3) - 16) * inv16) % q3
            for block_index in range(9):
                shifted_a = (
                    (pow(10, depth + u + block_index * block, q3) - 16)
                    * inv16
                ) % q3
                assert (
                    harmonic * beta3 * (shifted_a - base_a)
                    - support * block_index * (q3 // 9)
                ) % q3 == 0
                counters["cf18_sign_checks"] += 1

        # Exact nine-character orthogonality: support is +a, not -a.
        for frequency in range(9):
            residue_counts = [0] * 9
            for block_index in range(9):
                residue_counts[((support - frequency) * block_index) % 9] += 1
            if frequency == support:
                assert residue_counts[0] == 9 and sum(residue_counts[1:]) == 0
            elif math.gcd((support - frequency) % 9, 9) == 1:
                assert residue_counts == [1] * 9
            else:
                assert all(
                    residue_counts[index] == (3 if index in (0, 3, 6) else 0)
                    for index in range(9)
                )
            counters["primary_support_class_checks"] += 1

        complement_class = (-support) % 9
        assert (-complement_class) % 9 == support
        # Coefficient kernels in CF22 agree exactly.  Orthogonality in the H
        # frequency variable kills unequal u; equal-u phases are -b(m-m').
        for m in range(9):
            for m_prime in range(9):
                left_exponent = (-complement_class * (m - m_prime)) % 9
                right_exponent = (support * (m - m_prime)) % 9
                assert left_exponent == right_exponent
                counters["cf22_kernel_sign_checks"] += 1

        support_count = period // 9
        assert support_count * (9 * period) == period * period
        diagonal_block_mass = 9 * block
        diagonal_energy = block * diagonal_block_mass
        assert diagonal_energy == period * period // 9
        counters["one_ninth_diagonal_checks"] += 1

    # CF28--CF29.  Compare both presentations after embedding them in the
    # original dyadic modulus; no roots of unity or floating point are used.
    dyadic_exponent = two_exponent - 4
    for harmonic in (-12, -1, 2, 20):
        h_v2 = valuation(harmonic, 2)
        odd_h = harmonic // (2**h_v2)
        for shift_blocks in range(1, 9):
            lag = shift_blocks * block
            repunit = 10**lag - 1
            for lower_block in range(9 - shift_blocks):
                start = depth + lower_block * block
                fixed_exponent = two_exponent - start - h_v2
                alpha = odd_h * w * 5**start * repunit
                assert alpha % 2
                for u in range(block):
                    n = start + u
                    original = (
                        harmonic
                        * w
                        * ((10 ** (n + lag) - 10**n) // 16)
                    ) % dyadic_modulus
                    embedded_fixed = (
                        alpha
                        * 10**u
                        * 2 ** (dyadic_exponent - fixed_exponent)
                    ) % dyadic_modulus
                    varying_exponent = fixed_exponent - u
                    embedded_varying = (
                        alpha
                        * 5**u
                        * 2 ** (dyadic_exponent - varying_exponent)
                    ) % dyadic_modulus
                    assert original == embedded_fixed == embedded_varying
                    assert lower_block * block + u <= 8 * block - 1
                    exact_lower = (
                        Fraction(1151 * depth, 405)
                        + Fraction(301, 405)
                        - valuation(depth + 1, 2)
                        - h_v2
                    )
                    assert varying_exponent >= exact_lower
                    counters["cf28_two_representation_checks"] += 1

    # CF30--CF31.  Annihilation is tested in the original CRT coordinates;
    # the rational lift alone can leave a denominator dividing 105, canceled
    # by the matching grid term.
    total_high_product = math.prod(high_primes)
    for shift_blocks in range(1, 9):
        lag = shift_blocks * block
        repunit = 10**lag - 1
        killed = [prime for prime in high_primes if repunit % prime == 0]
        active = [prime for prime in high_primes if repunit % prime]
        killed_product = math.prod(killed)
        active_product = math.prod(active)
        assert killed_product * active_product == total_high_product
        assert repunit % killed_product == 0
        assert killed_product <= repunit < 10**lag
        for harmonic in (-37, -1, 1, 20):
            assert depth > abs(harmonic)
            for prime in active:
                assert prime > depth > abs(harmonic)
                gamma = c * pow(odd_denominator // prime, -1, prime) % prime
                coefficient = (
                    harmonic
                    * gamma
                    * pow(10, depth, prime)
                    * (repunit % prime)
                    * pow(16, -1, prime)
                ) % prime
                assert coefficient
                counters["active_high_coordinate_checks"] += 1
            for prime in killed:
                gamma = c * pow(odd_denominator // prime, -1, prime) % prime
                # Original local phase coefficient is exactly zero modulo p.
                assert (
                    harmonic
                    * gamma
                    * pow(10, depth, prime)
                    * (repunit % prime)
                    * pow(16, -1, prime)
                ) % prime == 0
                counters["killed_high_coordinate_checks"] += 1
        counters["annihilation_product_checks"] += 1

    assert Fraction(3) - Fraction(64, 405) == Fraction(1151, 405)
    mass_constant = 5.0 - 64.0 * math.log(10.0) / 405.0
    assert abs(mass_constant - 4.6361347013540275) < 1e-15
    counters["constant_checks"] += 2

    return {
        "epoch": epoch,
        "depth": depth,
        "period": period,
        "block": block,
        "high_prime_count": len(high_primes),
        "high_product_bits": high_product.bit_length(),
        "grid_numerator_mod_105": grid_numerator,
        "cf29_coefficient": "1151/405",
        "cf31_mass_coefficient": f"{mass_constant:.15f}",
    }


def main() -> None:
    check_frozen()
    counters = {
        "denominator_factor_checks": 0,
        "sixteen_scaling_checks": 0,
        "local_lift_checks": 0,
        "odd_crt_checks": 0,
        "reciprocal_denominator_checks": 0,
        "cf12_phase_checks": 0,
        "cf18_sign_checks": 0,
        "primary_support_class_checks": 0,
        "cf22_kernel_sign_checks": 0,
        "one_ninth_diagonal_checks": 0,
        "cf28_two_representation_checks": 0,
        "active_high_coordinate_checks": 0,
        "killed_high_coordinate_checks": 0,
        "annihilation_product_checks": 0,
        "constant_checks": 0,
    }
    rows = [build_row(epoch, counters) for epoch in (4, 6)]
    record = {
        "rows": rows,
        "counters": counters,
        "uses_numpy": False,
        "uses_gmpy2": False,
        "imports_primary_checker": False,
        "asserts_selected_complement_bound": False,
        "asserts_full_phase_cancellation": False,
        "asserts_fixed_return": False,
        "asserts_v1": False,
    }
    encoded = json.dumps(record, sort_keys=True, separators=(",", ":")).encode()
    print("status=PASS")
    print("bounded_claim_label=experiment")
    print("analytic_claim_label=proof sketch")
    print("literature_claim_label=literature-checked")
    for name, count in counters.items():
        print(f"{name}={count}")
    for row in rows:
        print(
            f"epoch_{row['epoch']}=M{row['depth']},T{row['period']},"
            f"H{row['block']},high{row['high_prime_count']},"
            f"high_bits{row['high_product_bits']},J{row['grid_numerator_mod_105']}"
        )
    print(f"exact_record_sha256={hashlib.sha256(encoded).hexdigest()}")
    print("imports_primary_checker=false")
    print("asserts_selected_complement_bound=false")
    print("asserts_full_phase_cancellation=false")
    print("asserts_fixed_return=false")
    print("asserts_v1=false")


if __name__ == "__main__":
    main()
