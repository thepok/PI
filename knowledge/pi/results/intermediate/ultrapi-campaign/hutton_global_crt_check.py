#!/usr/bin/env python3
"""Exact replay for ``hutton_global_crt_attack.md``.

All asserted identities use Python integers or ``fractions.Fraction``.  The
printed orbit/cylinder data are finite experiments and make no assertion
about untested indices or about the digits of pi.
"""

from __future__ import annotations

import hashlib
import math
from fractions import Fraction
from pathlib import Path


SOURCE_SHA256 = "2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825"


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def valuation(value: int, prime: int) -> int:
    assert value > 0 and prime > 1
    result = 0
    while value % prime == 0:
        value //= prime
        result += 1
    return result


def floor_log(value: int, base: int) -> int:
    assert value >= 1 and base >= 2
    exponent = 0
    power = base
    while power <= value:
        exponent += 1
        power *= base
    return exponent


def primes_through(bound: int) -> list[int]:
    if bound < 2:
        return []
    sieve = bytearray(b"\x01") * (bound + 1)
    sieve[0:2] = b"\x00\x00"
    for prime in range(2, math.isqrt(bound) + 1):
        if sieve[prime]:
            count = (bound - prime * prime) // prime + 1
            sieve[prime * prime : bound + 1 : prime] = b"\x00" * count
    return [candidate for candidate in range(2, bound + 1) if sieve[candidate]]


def hutton_term(odd_exponent: int) -> Fraction:
    """Combined base-three/base-seven term at one odd exponent."""
    assert odd_exponent >= 1 and odd_exponent % 2 == 1
    sign = 1 if odd_exponent % 4 == 1 else -1
    numerator = 4 * sign * (2 * 7**odd_exponent + 3**odd_exponent)
    denominator = odd_exponent * 3**odd_exponent * 7**odd_exponent
    return Fraction(numerator, denominator)


def hutton_lower(index: int) -> Fraction:
    assert index >= 0
    radius = 4 * index + 3
    return sum(
        (hutton_term(exponent) for exponent in range(1, radius + 1, 2)),
        Fraction(),
    )


def hutton_width(index: int) -> Fraction:
    next_odd = 4 * index + 5
    return Fraction(8, next_odd * 3**next_odd) + Fraction(
        4, next_odd * 7**next_odd
    )


def safe_last_position(index: int, word_length: int) -> int:
    """Largest j with 10^j W_K < 1/(2*10^word_length), or -1."""
    threshold = Fraction(1, 2 * 10**word_length)
    width = hutton_width(index)
    position = -1
    decimal_power = 1
    while decimal_power * width < threshold:
        position += 1
        decimal_power *= 10
    return position


def upper_half_primes(index: int, primes: list[int]) -> list[int]:
    radius = 4 * index + 3
    return [
        prime
        for prime in primes
        if prime <= radius
        and radius < 2 * prime
        and prime > 7
        and prime != 17
    ]


def fractional_part(value: Fraction) -> Fraction:
    return Fraction(value.numerator % value.denominator, value.denominator)


def jacobi_symbol(value: int, odd_modulus: int) -> int:
    """Jacobi symbol (value / odd_modulus), for positive odd modulus."""
    assert odd_modulus >= 1 and odd_modulus % 2 == 1
    value %= odd_modulus
    result = 1
    while value:
        while value % 2 == 0:
            value //= 2
            if odd_modulus % 8 in (3, 5):
                result = -result
        value, odd_modulus = odd_modulus, value
        if value % 4 == 3 and odd_modulus % 4 == 3:
            result = -result
        value %= odd_modulus
    return result if odd_modulus == 1 else 0


def multiplicative_order_10(prime: int) -> int:
    assert prime > 5
    residue = 1
    for order in range(1, prime):
        residue = 10 * residue % prime
        if residue == 1:
            return order
    raise AssertionError("Fermat order bound failed")


def in_power_of_ten_subgroup(value: int, prime: int) -> bool:
    order = multiplicative_order_10(prime)
    return pow(value % prime, order, prime) == 1


def circle_grid_distance(numerator: int, denominator: int, grid: int) -> Fraction:
    point = Fraction(numerator % denominator, denominator)
    distances = []
    for branch in range(grid):
        raw = abs(point - Fraction(branch, grid))
        distances.append(min(raw, 1 - raw))
    return min(distances)


def selected_data(index: int, all_primes: list[int]) -> dict[str, object]:
    value = hutton_lower(index)
    numerator = value.numerator
    denominator = value.denominator
    radius = 4 * index + 3
    selected = upper_half_primes(index, all_primes)
    product = math.prod(selected)
    assert product > 1
    assert denominator % product == 0
    complement = denominator // product
    assert math.gcd(complement, product) == 1

    signed_sum = sum(
        (1 if prime % 4 == 1 else -1) * (product // prime)
        for prime in selected
    )
    assert math.gcd(signed_sum, product) == 1

    # Track Q/p exactly, rather than replacing it by an unspecified unit.
    for prime in selected:
        sign = 1 if prime % 4 == 1 else -1
        assert denominator // prime == complement * (product // prime)
        local = value * prime
        assert local.denominator % prime != 0
        local_residue = (
            local.numerator * pow(local.denominator, -1, prime)
        ) % prime
        expected_local = sign * 68 * pow(21, -1, prime) % prime
        assert local_residue == expected_local
        assert numerator % prime == (
            expected_local * (denominator // prime)
        ) % prime

    # Global selected-numerator congruence and its exact archimedean lift.
    assert (21 * numerator - 68 * complement * signed_sum) % product == 0
    quotient_numerator = (
        21 * numerator - 68 * complement * signed_sum
    ) // product
    assert value == Fraction(68 * signed_sum, 21 * product) + Fraction(
        quotient_numerator, 21 * complement
    )

    normalized = 68 * pow(21, -1, product) * signed_sum % product
    branch = (21 * normalized - 68 * signed_sum) // product
    assert Fraction(normalized, product) == Fraction(branch, 21) + Fraction(
        68 * signed_sum, 21 * product
    )

    # Reciprocity collapses every pairwise product to one Jacobi sign.
    number_three_mod_four = sum(prime % 4 == 3 for prime in selected)
    predicted_jacobi = (
        (-1) ** (number_three_mod_four * (number_three_mod_four + 1) // 2)
        * jacobi_symbol(357, product)
    )
    assert jacobi_symbol(normalized, product) == predicted_jacobi

    # The signed reciprocal sum has a direct exact upper bound.  PNT turns
    # the right side into O(1/log R); the checker uses no asymptotics.
    reciprocal_sum = Fraction(signed_sum, product)
    assert abs(reciprocal_sum) < Fraction(2 * len(selected), radius)

    # The five-adic transient is exact, not merely bounded above.
    transient = valuation(denominator, 5)
    assert transient == floor_log(radius, 5)
    modulus = denominator // 5**transient
    assert modulus % product == 0
    other_factor = modulus // product
    assert complement == 5**transient * other_factor
    state = pow(2, transient, modulus) * numerator % modulus
    assert math.gcd(state, modulus) == 1

    # Canonical additive CRT removes the complement from the G-coordinate.
    normalized_g_state = state * pow(other_factor, -1, product) % product
    assert normalized_g_state == pow(10, transient, product) * normalized % product
    if other_factor == 1:
        normalized_b_state = 0
    else:
        normalized_b_state = state * pow(product, -1, other_factor) % other_factor

    for offset in range(20):
        decimal_power = 10**offset
        actual_fraction = Fraction(state * decimal_power % modulus, modulus)
        g_fraction = Fraction(
            normalized_g_state * decimal_power % product, product
        )
        b_fraction = (
            Fraction(normalized_b_state * decimal_power % other_factor, other_factor)
            if other_factor > 1
            else Fraction()
        )
        assert actual_fraction == fractional_part(g_fraction + b_fraction)

        skeleton = Fraction(branch * 10 ** (transient + offset), 21) + Fraction(
            68 * signed_sum * 10 ** (transient + offset), 21 * product
        )
        assert g_fraction == fractional_part(skeleton)

    return {
        "K": index,
        "R": radius,
        "P": numerator,
        "Q": denominator,
        "primes": selected,
        "G": product,
        "C": complement,
        "S": signed_sum,
        "u": normalized,
        "branch": branch,
        "b": transient,
        "m": modulus,
        "B": other_factor,
        "a": state,
        "alpha": normalized_g_state,
        "jacobi": predicted_jacobi,
    }


def main() -> None:
    root = Path(__file__).resolve().parents[2]
    source = root / "problems/local/pi-digits.txt"
    assert sha256(source) == SOURCE_SHA256

    maximum_index = 250
    all_primes = primes_through(4 * maximum_index + 3)
    rows: dict[int, dict[str, object]] = {}
    local_checks = 0
    global_checks = 0
    skeleton_checks = 0

    for index in range(2, maximum_index + 1):
        data = selected_data(index, all_primes)
        rows[index] = data
        local_checks += len(data["primes"])
        global_checks += 7
        skeleton_checks += 20

    # Three deliberately false simplifications are rejected exactly.
    row3 = rows[3]
    assert row3["P"] % row3["G"] != row3["u"]
    assert row3["a"] % row3["G"] != row3["u"]
    multiplier3 = pow(10, row3["b"], row3["G"]) * row3["B"] % row3["G"]
    subgroup_failures3 = [
        prime
        for prime in row3["primes"]
        if not in_power_of_ten_subgroup(multiplier3, prime)
    ]
    assert subgroup_failures3 == [11, 13]
    assert multiplier3 % 11 == 3 and multiplier3 % 13 == 7

    # The CRT lift branch is not a function of the coarse endpoint class.
    assert rows[2]["R"] % 84 == rows[23]["R"] % 84 == 11
    assert rows[2]["branch"] % 21 == 10
    assert rows[23]["branch"] % 21 == 4

    # Even the sign of the signed prime-reciprocal sum changes.
    assert rows[10]["S"] < 0 < rows[12]["S"]

    # Independent direct checks of the residue formula for larger K values.
    display_indices = (3, 10, 12, 20, 40, 80, 120, 200)
    display_rows = []
    for index in display_indices:
        data = rows[index]
        raw_distance = circle_grid_distance(data["u"], data["G"], 21)
        shifted_distance = circle_grid_distance(data["alpha"], data["G"], 21)
        display_rows.append(
            (
                index,
                data["R"],
                len(data["primes"]),
                data["b"],
                data["branch"] % 21,
                float(Fraction(data["S"], data["G"])),
                float(raw_distance),
                float(shifted_distance),
                data["jacobi"],
            )
        )

    # G-factor coverage is printed only as an experiment.  It is not the
    # full CRT state and therefore cannot certify a decimal cylinder.
    coverage_rows = []
    for index in (20, 40, 80, 120, 200):
        data = rows[index]
        number = max(0, safe_last_position(index, 2) - data["b"] + 1)
        residue = data["alpha"]
        seen: set[int] = set()
        for _ in range(number):
            seen.add(100 * residue // data["G"])
            residue = 10 * residue % data["G"]
        coverage_rows.append((index, number, len(seen)))

    print(f"source sha256: {SOURCE_SHA256}")
    print(f"eligible local-prime congruences checked: {local_checks}")
    print(f"global/decomposition/reciprocity check groups: {global_checks}")
    print(f"exact CRT-skeleton phase checks: {skeleton_checks}")
    print("falsified naive formulas at K=3:")
    print(
        "  P mod G =", row3["P"] % row3["G"],
        "; a mod G =", row3["a"] % row3["G"],
        "; normalized u =", row3["u"],
    )
    print("  complement multiplier is outside <10> at primes:", subgroup_failures3)
    print("same R mod 84 but different lift branch:")
    print("  K=2 -> 10 mod 21; K=23 -> 4 mod 21")
    print(
        "sample rows: K R #P b branch delta dist(u,grid) "
        "dist(shifted,grid) Jacobi"
    )
    for row in display_rows:
        print(
            f"  {row[0]:3d} {row[1]:4d} {row[2]:3d} {row[3]:2d} "
            f"{row[4]:2d} {row[5]:+.8e} {row[6]:.8e} "
            f"{row[7]:.8e} {row[8]:+d}"
        )
    print("G-factor-only two-digit coverage: K starts distinct-cells")
    for row in coverage_rows:
        print("  " + " ".join(map(str, row)))
    print("all exact checks passed")


if __name__ == "__main__":
    main()
