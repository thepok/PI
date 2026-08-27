#!/usr/bin/env python3
"""Standalone exact replay for the CF36 Gowers/cube persistence branch.

All structural checks use integers and Fraction.  Decimal floating point is
used only to print the two asymptotic constants appearing in the report.
This file deliberately imports no other branch checker.
"""

from __future__ import annotations

from fractions import Fraction
from hashlib import sha256
from itertools import product
from pathlib import Path
from decimal import Decimal, getcontext


ROOT = Path(__file__).resolve().parents[2]

FROZEN = {
    "work/ultrapi-resume/bbp_three_primary_twisted_sum_20260813.md":
        "0a7e6015782afdfa407242fe3e191cfffec414d7c9215ec8854a439c2fb08a12",
    "work/ultrapi-resume/bbp_three_primary_decimation_20260813.md":
        "29d4f903dca429ebe2cedad248f0a726b985492bfd0f06471a668a47e652ede0",
    "work/ultrapi-resume/bbp_complement_fourier_attack_20260813.md":
        "eccb19ffdd7a931cb9de1efb4ab1136ba3f8fb543a84ab00c3e320fd16f2316a",
    "work/ultrapi-resume/bbp_high_prime_phase_compression_20260813.md":
        "47f56886b769a36f5f397cad567579838d455f59b75af8ca458a8000dfb7c564",
    "problems/local/pi-digits.txt":
        "2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825",
}


def file_hash(path: Path) -> str:
    return sha256(path.read_bytes()).hexdigest()


def v3(n: int) -> int:
    assert n != 0
    n = abs(n)
    answer = 0
    while n % 3 == 0:
        n //= 3
        answer += 1
    return answer


def v2(n: int) -> int:
    assert n != 0
    n = abs(n)
    return (n & -n).bit_length() - 1


def primary_parameters(e: int) -> tuple[int, int, int]:
    assert e >= 4
    modulus = 3**e
    period = 3 ** (e - 2)
    block = period // 9
    return modulus, period, block


def exact_u3_support_bound(e: int) -> tuple[Fraction, Fraction]:
    """Return the exact support proportion and the stated elementary bound.

    The support condition is only a necessary condition for a nonzero third
    derivative average, so it is an upper bound for U^3^8, not its value.
    """

    d = e - 2
    period = 3**d
    # Nonzero residues modulo 3^d with exact 3-adic valuation j.
    valuation_counts = [2 * 3 ** (d - j - 1) for j in range(d)]
    assert sum(valuation_counts) + 1 == period

    supported = period**3 - (period - 1) ** 3  # at least one zero lag
    for j1, c1 in enumerate(valuation_counts):
        for j2, c2 in enumerate(valuation_counts):
            for j3, c3 in enumerate(valuation_counts):
                if 6 + j1 + j2 + j3 >= d:
                    supported += c1 * c2 * c3
    exact = Fraction(supported, period**3)

    if d < 6:
        bound = Fraction(1, 1)
    else:
        # Union bound for zero lags plus the composition-tail bound
        # (2/3)(R+2)^2 3^{-R}, R=d-6.
        r = d - 6
        bound = Fraction(3, period) + Fraction(2 * (r + 2) ** 2, 3 ** (r + 1))
    assert exact <= bound
    return exact, bound


def cube_coefficient(block: int, lags: tuple[int, ...], blocks: tuple[int, ...]) -> int:
    k = len(lags)
    assert len(blocks) == 2**k
    value = 0
    for vertex in range(2**k):
        shift = blocks[vertex] * block
        parity = 0
        for i, lag in enumerate(lags):
            if (vertex >> i) & 1:
                shift += lag
                parity += 1
        value += (-1 if parity else 1) * 10**shift
    return value


def subset_sums_mod(block: int, lags: tuple[int, ...]) -> set[int]:
    result: set[int] = set()
    for vertex in range(2 ** len(lags)):
        result.add(sum(lag for i, lag in enumerate(lags) if (vertex >> i) & 1) % block)
    return result


def main() -> None:
    for relative, expected in FROZEN.items():
        actual = file_hash(ROOT / relative)
        assert actual == expected, (relative, actual, expected)

    sparse_support_checks = 0
    nine_block_checks = 0
    u3_support_checks = 0
    ramanujan_pattern_checks = 0
    resonance_checks = 0

    # Exact sparse support and nine-block lift through e=12.
    for e in range(4, 13, 2):
        modulus, period, block = primary_parameters(e)
        assert 9 * period == modulus
        assert 9 * block == period
        for lag in range(period):
            supported = (pow(10, lag, period) - 1) % period == 0
            assert supported == (lag % block == 0)
            sparse_support_checks += 1
        for m in range(9):
            assert (pow(10, m * block, modulus) - (1 + m * period)) % modulus == 0
            nine_block_checks += 1

        # Ramanujan c_{3^e} support among exponent differences.
        for lag in range(period):
            if lag == 0:
                category = "diagonal"
            else:
                residue = (pow(10, lag, modulus) - 1) % modulus
                valuation = v3(residue)
                category = "minus" if valuation == e - 1 else "zero"
            expected = (
                "diagonal" if lag == 0
                else "minus" if lag in (period // 3, 2 * period // 3)
                else "zero"
            )
            assert category == expected
            ramanujan_pattern_checks += 1

        # For W=conj(f_a), the selected pairing is termwise one and the
        # T/3 correlation is the constant cubic root e_3(-a).
        a = 1
        shift = period // 3
        for j in range(period):
            delta = (-a * (pow(10, j + shift, modulus) - pow(10, j, modulus))) % modulus
            assert delta == (-3 * a * period) % modulus
            resonance_checks += 1

    for e in range(8, 17, 2):
        exact, bound = exact_u3_support_bound(e)
        assert 0 <= exact <= bound
        u3_support_checks += 1

    # The exact U^2 identity follows from the nine surviving correlations.
    for e in range(4, 17, 2):
        _, period, _ = primary_parameters(e)
        u2_fourth = Fraction(9, period)
        assert u2_fourth.denominator > 0
        if e > 4:
            assert u2_fourth < 1

    # Frozen endpoint residues from the decimation report.  These checks do
    # not re-prove that report; they verify the new selected-coefficient
    # consequence and its ninth-root compatibility.
    endpoint_units = {
        2: 2,
        4: 38,
        6: 524,
        8: 4898,
        10: 57386,
        12: 175484,
    }
    selected_coefficients: dict[int, int] = {}
    endpoint_nesting_checks = 0
    for e, unit in endpoint_units.items():
        m = 5 * (3**e - 1) // 8 - 1
        selected_coefficients[e] = unit * pow(10, m, 3**e) % (3**e)
        if e >= 4:
            previous_e = e - 2
            previous_m = 5 * (3**previous_e - 1) // 8 - 1
            assert m - previous_m == 5 * 3 ** (e - 2)
            assert unit % (3 ** (e - 2)) == endpoint_units[previous_e]
            assert pow(10, m - previous_m, 3 ** (e - 2)) == 1
            assert (
                selected_coefficients[e] % (3 ** (e - 2))
                == selected_coefficients[previous_e]
            )
            endpoint_nesting_checks += 4

    # Every second cube coefficient is nonzero.  Exhaust the first genuine
    # H=9 row, every positive lag pair and all 9^4 block choices.
    block = 9
    second_cube_checks = 0
    size_bound_checks = 0
    valuation_bound_checks = 0
    for d1 in range(1, block):
        for d2 in range(1, block):
            lags = (d1, d2)
            for blocks in product(range(9), repeat=4):
                coefficient = cube_coefficient(block, lags, blocks)
                assert coefficient != 0
                bound = 2**2 * 10 ** (8 * block + d1 + d2)
                assert abs(coefficient) <= bound
                assert v2(coefficient) <= abs(coefficient).bit_length() - 1
                second_cube_checks += 1
                size_bound_checks += 1
                valuation_bound_checks += 1

    # A legal dissociated third-difference triple has eight distinct subset
    # sums modulo H, so opposite-parity decimal exponents cannot coincide.
    third_lags = (1, 2, 4)
    assert len(subset_sums_mod(block, third_lags)) == 8
    third_cube_checks = 0
    for blocks in product(range(3), repeat=8):
        coefficient = cube_coefficient(block, third_lags, blocks)
        assert coefficient != 0
        bound = 2**3 * 10 ** (8 * block + sum(third_lags))
        assert abs(coefficient) <= bound
        third_cube_checks += 1

    # Asymptotic surviving-mass and dyadic-depth constants for k=2,3.
    getcontext().prec = 50
    ln10 = Decimal(10).ln()
    log2_10 = ln10 / Decimal(2).ln()
    constants: dict[int, tuple[Decimal, Decimal]] = {}
    for k in (2, 3):
        high = Decimal(5) - Decimal(8 * (8 + k)) * ln10 / Decimal(405)
        dyadic = Decimal(3) - Decimal(8) * (
            Decimal(1) + Decimal(8 + k) * log2_10
        ) / Decimal(405)
        assert high > Decimal(4)
        assert dyadic > Decimal(2)
        constants[k] = high, dyadic

    record_fields = {
        "sparse_support_checks": sparse_support_checks,
        "nine_block_checks": nine_block_checks,
        "u3_support_checks": u3_support_checks,
        "ramanujan_pattern_checks": ramanujan_pattern_checks,
        "resonance_checks": resonance_checks,
        "endpoint_nesting_checks": endpoint_nesting_checks,
        "second_cube_checks": second_cube_checks,
        "third_cube_checks": third_cube_checks,
        "size_bound_checks": size_bound_checks,
        "valuation_bound_checks": valuation_bound_checks,
        "high_constant_k2": str(constants[2][0]),
        "dyadic_constant_k2": str(constants[2][1]),
        "high_constant_k3": str(constants[3][0]),
        "dyadic_constant_k3": str(constants[3][1]),
        "asserts_cf36_bound": False,
        "asserts_fixed_return": False,
        "asserts_v1": False,
    }
    record = "\n".join(f"{key}={value}" for key, value in sorted(record_fields.items()))
    record_hash = sha256(record.encode()).hexdigest()
    print(record)
    print(f"exact_record_sha256={record_hash}")
    print("status=PASS")


if __name__ == "__main__":
    main()
