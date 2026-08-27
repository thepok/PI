#!/usr/bin/env python3
"""Independent exact audit replay for the mixed BBP separator.

This script deliberately imports neither the primary replay nor any earlier
BBP checker.  Its finite output has claim label ``experiment``.  The script
checks exact identities and adversarial boundary cases; it does not assert a
return for pi or canonical V1.
"""

from __future__ import annotations

from fractions import Fraction
from hashlib import sha256
import json
from math import log
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
PINS = {
    "problems/local/pi-digits.txt":
        "2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825",
    "work/ultrapi-resume/bbp_mixed_coordinate_height_separator_20260813.md":
        "950b18b4ac30adc7d65a8a0d418f7fc4b7c5536d7b51d4f08b984f745d2c5820",
    "work/ultrapi-resume/bbp_mixed_coordinate_height_separator_20260813_check.py":
        "6549b99503cb34aaf757f0c428702b3797714144d0bc8e1f77a336fe965d6846",
    "work/ultrapi-resume/bbp_high_prime_coordinate_rigidity_20260813.md":
        "419158fe378aafdeb9ceef977b702e2409a81ddfbeca5e2fe43ec119b426cd42",
    "work/ultrapi-resume/bbp_high_dyadic_archimedean_separator_20260813.md":
        "d0d975ff9bab6ce456723085cb3e031a3be83a171fa6a94d8656d76d8b0457b3",
    "work/ultrapi-resume/bbp_high_dyadic_archimedean_separator_20260813_check.py":
        "69d07d421b215b85bd5e5f7a7d4036c9d38544a3a0a8fc7db4a6947687cb0ab8",
    "work/ultrapi-resume/bbp_actual_odd_quotient_attack.md":
        "d77e96b5bdce3bfd8278fa3b650d7a95d16bc86738c2af95a2d740919470c9fc",
}

FIRST_N = 18
LAST_N = 38
TAIL_N = 48
MAX_GENERIC_NESTING_DEPTH = 4000
PERIODS = tuple(range(1, 9))


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def gcd(a: int, b: int) -> int:
    while b:
        a, b = b, a % b
    return abs(a)


def lcm(a: int, b: int) -> int:
    return a // gcd(a, b) * b


def valuation_two(value: int) -> int:
    require(value != 0, "v2 is undefined at zero")
    value = abs(value)
    return (value & -value).bit_length() - 1


def nearest_half_up(value: Fraction) -> int:
    """The centered-cell convention floor(value + 1/2)."""
    return (2 * value.numerator + value.denominator) // (2 * value.denominator)


def closest_admissible_shift(target: Fraction, forbidden_modulus: int) -> int:
    """Find the closest integer not 0 mod C without trusting primary code."""
    require(forbidden_modulus > 1, "the forbidden class must be proper")
    center = nearest_half_up(target)
    candidates = range(center - 3, center + 4)
    admissible = [h for h in candidates if h % forbidden_modulus != 0]
    require(admissible, "local admissible search unexpectedly empty")
    # Tie-break by integer value; no correctness statement depends on the tie.
    return min(admissible, key=lambda h: (abs(Fraction(h) - target), h))


def coefficient_numerator(k: int) -> int:
    return 120 * k * k + 151 * k + 47


def coefficient_denominator(k: int) -> int:
    return (2 * k + 1) * (4 * k + 3) * (8 * k + 1) * (8 * k + 5)


def primes_up_to(limit: int) -> list[int]:
    sieve = bytearray(b"\x01") * (limit + 1)
    if limit >= 0:
        sieve[0] = 0
    if limit >= 1:
        sieve[1] = 0
    for p in range(2, int(limit**0.5) + 1):
        if sieve[p]:
            start = p * p
            sieve[start : limit + 1 : p] = b"\x00" * (
                (limit - start) // p + 1
            )
    return [p for p in range(2, limit + 1) if sieve[p]]


def in_first_band(depth: int, p: int) -> bool:
    return p > 4 * depth + 3 and (
        (p % 8 == 1 and p <= 8 * depth + 1)
        or (p % 8 == 5 and p <= 8 * depth + 5)
    )


def in_second_band(depth: int, p: int) -> bool:
    return 3 * p > 8 * depth + 5 and p <= 4 * depth + 3


def in_retained_band(depth: int, p: int) -> bool:
    return in_first_band(depth, p) or in_second_band(depth, p)


def retained_product(depth: int, primes: list[int]) -> tuple[int, tuple[int, ...]]:
    selected = tuple(p for p in primes if in_retained_band(depth, p))
    product = 1
    for p in selected:
        product *= p
    return product, selected


def large_integer_log(value: int) -> float:
    require(value > 0, "log input must be positive")
    shift = max(0, value.bit_length() - 52)
    return log(value >> shift) + shift * log(2)


def build_rows(max_depth: int) -> list[dict[str, int | Fraction]]:
    current_lcm = coefficient_denominator(0)
    current_scaled_numerator = coefficient_numerator(0)
    rows: list[dict[str, int | Fraction]] = [{
        "L": current_lcm,
        "A": current_scaled_numerator,
        "B": Fraction(current_scaled_numerator, current_lcm),
    }]
    for depth in range(1, max_depth + 1):
        denominator = coefficient_denominator(depth)
        next_lcm = lcm(current_lcm, denominator)
        current_scaled_numerator = (
            16 * (next_lcm // current_lcm) * current_scaled_numerator
            + coefficient_numerator(depth) * (next_lcm // denominator)
        )
        current_lcm = next_lcm
        rows.append({
            "L": current_lcm,
            "A": current_scaled_numerator,
            "B": Fraction(
                current_scaled_numerator,
                16**depth * current_lcm,
            ),
        })
    return rows


def odd_part(value: int) -> int:
    return value >> valuation_two(value)


def distinct_prime_divisors(value: int, primes: list[int]) -> tuple[int, ...]:
    value = abs(value)
    found: list[int] = []
    for p in primes:
        if p * p > value:
            break
        if value % p == 0:
            found.append(p)
            while value % p == 0:
                value //= p
        if value == 1:
            break
    if value > 1:
        found.append(value)
    return tuple(found)


def expected_clean_coordinate(p: int) -> int:
    return 64 % p if p % 4 == 1 else (-32) % p


def direct_additive_coordinate(row: dict[str, int | Fraction], p: int) -> int:
    """Compute c(R/p)^(-1) mod p directly from reduced B_M."""
    fraction = Fraction(row["B"])
    P = fraction.numerator
    K = valuation_two(fraction.denominator)
    R = fraction.denominator >> K
    require(R % p == 0 and (R // p) % p != 0,
            f"p={p} must occur exactly once in reduced odd denominator")
    D0 = 2 ** (K - 4)
    w = (P * pow(R, -1, D0)) % D0
    numerator = P - R * w
    require(numerator % D0 == 0, "odd quotient numerator is integral")
    c = numerator // D0
    return (c * pow(R // p, -1, p)) % p


def choose_mixed_state(
    n: int,
    row: dict[str, int | Fraction],
    reference: Fraction,
    primes: list[int],
) -> dict[str, object]:
    depth = 7 * n
    L = int(row["L"])
    A = int(row["A"])
    D = 2 ** (27 * n) * L
    V = 5**n * A
    Q, retained = retained_product(depth, primes)
    mixed_modulus = 2 ** (27 * n) * Q
    C = L // Q
    require(C > 1, f"free odd cofactor is nontrivial at n={n}")
    target = -10**n * (reference - Fraction(row["B"]))
    shift_target = Fraction(D * target - V, mixed_modulus)
    shift = closest_admissible_shift(shift_target, C)
    S = V + mixed_modulus * shift
    eta = Fraction(S, D) - target
    return {
        "n": n,
        "depth": depth,
        "L": L,
        "A": A,
        "D": D,
        "V": V,
        "Q": Q,
        "C": C,
        "retained": retained,
        "modulus": mixed_modulus,
        "target": target,
        "shift_target": shift_target,
        "shift": shift,
        "S": S,
        "eta": eta,
        "r": D + S,
    }


def run() -> dict[str, object]:
    for relative, expected in PINS.items():
        path = ROOT / relative
        require(path.is_file(), f"missing pinned input: {relative}")
        actual = sha256(path.read_bytes()).hexdigest()
        require(actual == expected, f"hash mismatch for {relative}: {actual}")

    # These two coefficient comparisons are the exact polynomial reductions
    # behind a(k) >= 1/(21 k^2) and a(k) <= 1/k^2 for every k >= 1.
    coefficient_bound_checks = 0
    for k in range(1, 10_001):
        numerator = coefficient_numerator(k)
        denominator = coefficient_denominator(k)
        lower_gap = 21 * k * k * numerator - denominator
        lower_polynomial = (
            2008 * k**4 + 2147 * k**3 + 275 * k**2 - 194 * k - 15
        )
        upper_gap = denominator - k * k * numerator
        upper_polynomial = (
            392 * k**4 + 873 * k**3 + 665 * k**2 + 194 * k + 15
        )
        require(lower_gap == lower_polynomial and lower_gap > 0,
                f"lower coefficient bound k={k}")
        require(upper_gap == upper_polynomial and upper_gap > 0,
                f"upper coefficient bound k={k}")
        coefficient_bound_checks += 2

    rows = build_rows(7 * TAIL_N)
    primes = primes_up_to(8 * max(7 * TAIL_N + 7, MAX_GENERIC_NESTING_DEPTH + 7) + 5)

    # Check the moving bands and their exact endpoint/residue alternatives far
    # beyond the separator replay.  A new retained prime must either remain in
    # the old retained set or occur in one of the seven newly added poles.
    band_disjointness_checks = 0
    band_nesting_checks = 0
    band_nesting_old_checks = 0
    band_nesting_new_pole_checks = 0
    for depth in range(8, MAX_GENERIC_NESTING_DEPTH + 1):
        upper = 8 * (depth + 7) + 5
        for p in primes:
            if p > upper:
                break
            require(not (in_first_band(depth, p) and in_second_band(depth, p)),
                    f"bands overlap at M={depth}, p={p}")
            band_disjointness_checks += 1
            if not in_retained_band(depth + 7, p):
                continue
            if in_retained_band(depth, p):
                band_nesting_old_checks += 1
            else:
                new_indices = [
                    k for k in range(depth + 1, depth + 8)
                    if coefficient_denominator(k) % p == 0
                ]
                require(new_indices,
                        f"new band prime has no new pole M={depth}, p={p}")
                # A genuinely new prime cannot already divide the old LCM.
                require(all(
                    coefficient_denominator(k) % p != 0
                    for k in range(depth + 1)
                ), f"new-pole alternative was already old M={depth}, p={p}")
                band_nesting_new_pole_checks += 1
            band_nesting_checks += 1

    # Experimental PNT/AP diagnostics.  The report's asymptotic derivation,
    # not these finite ratios, carries the proof-sketch label.
    band_mass_ratios: dict[str, float] = {}
    for depth in (1000, 2000, 4000):
        p1_log = sum(log(p) for p in primes if in_first_band(depth, p))
        p2_log = sum(log(p) for p in primes if in_second_band(depth, p))
        band_mass_ratios[str(depth)] = (p1_log + p2_log) / depth

    # Exhaust the forbidden-class selector, including half-integer ties,
    # negative targets, and the smallest possible modulus.
    selector_checks = 0
    offsets = (
        Fraction(-3, 2), Fraction(-1, 2), Fraction(-499, 1000),
        Fraction(-1, 3), Fraction(0), Fraction(1, 3),
        Fraction(499, 1000), Fraction(1, 2), Fraction(3, 2),
    )
    for C in range(2, 302):
        for multiple in range(-4, 5):
            for offset in offsets:
                target = C * multiple + offset
                chosen = closest_admissible_shift(target, C)
                require(chosen % C != 0,
                        f"selector entered forbidden class C={C}, x={target}")
                require(abs(Fraction(chosen) - target) <= Fraction(3, 2),
                        f"selector exceeded 3/2 C={C}, x={target}")
                brute = min(
                    abs(Fraction(h) - target)
                    for h in range(nearest_half_up(target) - 5,
                                   nearest_half_up(target) + 6)
                    if h % C != 0
                )
                require(abs(Fraction(chosen) - target) == brute,
                        f"selector is not closest admissible C={C}, x={target}")
                selector_checks += 3

    reference = Fraction(rows[7 * TAIL_N]["B"])
    states = {
        n: choose_mixed_state(n, rows[7 * n], reference, primes)
        for n in range(FIRST_N, LAST_N + 1)
    }

    exact_state_checks = 0
    local_coordinate_checks = 0
    gcd_equivalence_checks = 0
    max_state_relative_error = Fraction(0)
    free_mass_ratios: list[float] = []
    retained_mass_ratios: list[float] = []
    for n, state in states.items():
        depth = int(state["depth"])
        row = rows[depth]
        L = int(state["L"])
        D = int(state["D"])
        V = int(state["V"])
        Q = int(state["Q"])
        C = int(state["C"])
        mixed_modulus = int(state["modulus"])
        S = int(state["S"])
        r = int(state["r"])
        target = Fraction(state["target"])
        eta = Fraction(state["eta"])

        require(Fraction(V, D) == 10**n * Fraction(row["B"]),
                f"sevenfold rational identity n={n}")
        require(valuation_two(V) == valuation_two(depth + 1),
                f"selected valuation n={n}")
        require(gcd(mixed_modulus, L) == Q,
                f"mixed/full gcd n={n}")
        require(L == Q * C, f"cofactor decomposition n={n}")
        sampled_shifts = tuple(
            multiple * C + offset
            for multiple in range(-3, 4)
            for offset in (-2, -1, 0, 1, 2)
        ) + (10 * C + 1, -10 * C - 1)
        for h in sampled_shifts:
            left = (mixed_modulus * h) % L == 0
            right = h % C == 0
            require(left == right, f"gcd equivalence n={n}, h={h}")
            gcd_equivalence_checks += 1

        require((S - V) % mixed_modulus == 0,
                f"state mixed congruence n={n}")
        require((S - V) % L != 0 and S != V,
                f"state must change full odd class n={n}")
        require(abs(eta) <= Fraction(3 * Q, 2 * L),
                f"three-half mesh bound n={n}")
        require(valuation_two(S) == valuation_two(V),
                f"S preserves full dyadic coordinate n={n}")
        require(valuation_two(r) == valuation_two(V),
                f"r preserves full dyadic coordinate n={n}")
        require(Fraction(-1, 2) < Fraction(S, D) < 0,
                f"late centered state n={n}")
        require(0 < r < D, f"phase representative n={n}")
        exact_state_checks += 9

        reduced = Fraction(row["B"])
        reduced_R = odd_part(reduced.denominator)
        require(reduced_R % Q == 0,
                f"all retained primes survive reduction n={n}")
        for p in state["retained"]:
            p = int(p)
            require(p > depth, f"retained prime is not high n={n}, p={p}")
            require(L % p == 0 and L % (p * p) != 0,
                    f"retained exponent in L is not one n={n}, p={p}")
            require(reduced_R % p == 0 and reduced_R % (p * p) != 0,
                    f"retained exponent in R is not one n={n}, p={p}")
            gamma = direct_additive_coordinate(row, p)
            require(gamma == expected_clean_coordinate(p),
                    f"localized coordinate n={n}, p={p}, gamma={gamma}")
            ambient_factor = D // p
            actual_phase_coordinate = (V * pow(ambient_factor, -1, p)) % p
            shadow_phase_coordinate = (S * pow(ambient_factor, -1, p)) % p
            require(actual_phase_coordinate == shadow_phase_coordinate,
                    f"shadow local phase coordinate n={n}, p={p}")
            local_coordinate_checks += 5

        max_state_relative_error = max(
            max_state_relative_error, abs(eta / target)
        )
        retained_mass_ratios.append(large_integer_log(Q) / depth)
        free_mass_ratios.append(large_integer_log(C) / depth)

    transition_checks = 0
    color_carry_checks = 0
    max_forcing_relative_error = Fraction(0)
    for n in range(FIRST_N, LAST_N):
        current = states[n]
        following = states[n + 1]
        L = int(current["L"])
        L_next = int(following["L"])
        L_ratio = L_next // L
        Q = int(current["Q"])
        Q_next = int(following["Q"])
        D = int(current["D"])
        D_next = int(following["D"])
        dilation = D_next // D
        require(L_next % L == 0, f"LCM nesting n={n}")
        require(dilation == 2**27 * L_ratio,
                f"seven-depth denominator dilation n={n}")
        require((Q * L_ratio) % Q_next == 0,
                f"exact Q nesting n={n}")

        V = int(current["V"])
        V_next = int(following["V"])
        S = int(current["S"])
        S_next = int(following["S"])
        r = int(current["r"])
        r_next = int(following["r"])
        K = V_next - 10 * dilation * V
        K_shadow = S_next - 10 * dilation * S
        forcing = Fraction(K, D_next)
        shadow_forcing = Fraction(K_shadow, D_next)
        require(K > 0 and K_shadow > 0, f"positive forcing n={n}")
        require((K_shadow - K) % (2 ** (27 * (n + 1)) * Q_next) == 0,
                f"complete next mixed forcing class n={n}")
        require(Fraction(following["target"])
                == 10 * Fraction(current["target"]) + forcing,
                f"exact tail recurrence n={n}")
        require(shadow_forcing - forcing
                == Fraction(following["eta"]) - 10 * Fraction(current["eta"]),
                f"forcing coboundary n={n}")
        require(10 * dilation * r + K_shadow == 9 * D_next + r_next,
                f"phase quotient is exactly nine n={n}")
        transition_checks += 8
        max_forcing_relative_error = max(
            max_forcing_relative_error,
            abs((shadow_forcing - forcing) / forcing),
        )

        for period in PERIODS:
            q = 10**period - 1
            e = Fraction(S, D)
            e_next = Fraction(S_next, D_next)
            require(Fraction(-1, 2) < q * e < 0,
                    f"centered color cell n={n}, P={period}")
            require(Fraction(-1, 2) < q * e_next < 0,
                    f"next centered color cell n={n}, P={period}")
            color = nearest_half_up(Fraction(q * r, D))
            next_color = nearest_half_up(Fraction(q * r_next, D_next))
            carry = 9 * q + next_color - 10 * color
            require(color == q and next_color == q and carry == 0,
                    f"all-nine color/zero carry n={n}, P={period}")
            color_carry_checks += 5

    # Verify the determinant parity and every odd-prime equivalence directly
    # for generic (not sevenfold-only) rows.
    determinant_parity_checks = 0
    determinant_local_checks = 0
    max_cancelled_retained_log_fraction = 0.0
    factor_primes = primes_up_to(8 * 100 + 5)
    lambda_upper = log(16) / log(10)
    for depth in range(16, 101):
        reduced = Fraction(rows[depth]["B"])
        P = reduced.numerator
        K = valuation_two(reduced.denominator)
        R = reduced.denominator >> K
        require(P % 2 == 1 and R % 2 == 1 and gcd(P, R) == 1,
                f"reduced generic form M={depth}")
        D0 = 2 ** (K - 4)
        require(D0 % 2 == 0, f"return denominator must be even M={depth}")
        prime_divisors = distinct_prime_divisors(R, factor_primes)
        for m in range(5, int(lambda_upper * depth) + 1):
            A0 = (10**m - 16) // 16
            require(A0 % 2 == 1, f"return multiplier odd M={depth}, m={m}")
            value = Fraction(A0 * P, D0 * R)
            ell = nearest_half_up(value)
            E = A0 * P - ell * D0 * R
            require(E != 0 and E % 2 != 0,
                    f"return determinant is a nonzero 2-adic unit M={depth}, m={m}")
            determinant_parity_checks += 1
            cancelled_log = 0.0
            retained_log = 0.0
            for p in prime_divisors:
                equivalence = (E % p == 0) == ((pow(10, m, p) - 16) % p == 0)
                require(equivalence,
                        f"determinant local equivalence M={depth}, m={m}, p={p}")
                retained_log += log(p)
                if E % p == 0:
                    cancelled_log += log(p)
                determinant_local_checks += 1
            if retained_log:
                max_cancelled_retained_log_fraction = max(
                    max_cancelled_retained_log_fraction,
                    cancelled_log / retained_log,
                )

    # The exact numerical threshold follows solely from exponent comparison.
    tail_exponent = 27 * log(2) - log(5)
    rho_star = 6 - tail_exponent / 7
    clean_margin = 7 * (6 - Fraction(10, 3)) - tail_exponent
    require(Fraction(10, 3) < rho_star < Fraction(18, 5),
            "clean mass lies strictly below threshold")
    require(clean_margin > 0, "clean separator exponent margin")

    return {
        "status": "PASS",
        "bounded_claim_label": "experiment",
        "audited_construction_label": "proof sketch",
        "asserts_fixed_return": False,
        "asserts_all_color_return": False,
        "asserts_v1": False,
        "coefficient_bound_checks": coefficient_bound_checks,
        "band_disjointness_checks": band_disjointness_checks,
        "band_nesting_checks": band_nesting_checks,
        "band_nesting_old_checks": band_nesting_old_checks,
        "band_nesting_new_pole_checks": band_nesting_new_pole_checks,
        "band_mass_ratios": band_mass_ratios,
        "adversarial_selector_checks": selector_checks,
        "gcd_equivalence_checks": gcd_equivalence_checks,
        "exact_state_checks": exact_state_checks,
        "localized_coordinate_checks": local_coordinate_checks,
        "transition_checks": transition_checks,
        "color_and_zero_carry_checks": color_carry_checks,
        "determinant_parity_checks": determinant_parity_checks,
        "determinant_local_equivalence_checks": determinant_local_checks,
        "rho_star": rho_star,
        "clean_exponent_margin": float(clean_margin),
        "minimum_observed_retained_log_mass_over_depth": min(retained_mass_ratios),
        "minimum_observed_free_log_mass_over_depth": min(free_mass_ratios),
        "maximum_relative_state_error": float(max_state_relative_error),
        "maximum_relative_forcing_error": float(max_forcing_relative_error),
        "maximum_sampled_cancelled_odd_log_fraction":
            max_cancelled_retained_log_fraction,
        "resolved_primary_corrections": [
            "exact odd-prime determinant exception condition",
            "one-way worst-case mesh threshold wording",
            "actual odd-quotient dependency pin",
        ],
    }


if __name__ == "__main__":
    print(json.dumps(run(), indent=2, sort_keys=True))
