#!/usr/bin/env python3
"""Exact finite replay for the mixed dyadic/high-prime BBP separator.

The script is deliberately independent of the two frozen checkers.  It uses
only integer and Fraction arithmetic.  Every bounded result has label
``experiment`` and asserts neither a return for pi nor canonical V1.
"""

from __future__ import annotations

from fractions import Fraction
from hashlib import sha256
import json
from math import gcd, log
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
PINS = {
    "problems/local/pi-digits.txt":
        "2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825",
    "work/ultrapi-resume/bbp_high_prime_coordinate_rigidity_20260813.md":
        "419158fe378aafdeb9ceef977b702e2409a81ddfbeca5e2fe43ec119b426cd42",
    "work/ultrapi-resume/bbp_high_dyadic_archimedean_separator_20260813.md":
        "d0d975ff9bab6ce456723085cb3e031a3be83a171fa6a94d8656d76d8b0457b3",
    "work/ultrapi-resume/bbp_high_dyadic_archimedean_separator_20260813_check.py":
        "69d07d421b215b85bd5e5f7a7d4036c9d38544a3a0a8fc7db4a6947687cb0ab8",
    "work/ultrapi-resume/bbp_actual_odd_quotient_attack.md":
        "d77e96b5bdce3bfd8278fa3b650d7a95d16bc86738c2af95a2d740919470c9fc",
}

# The complete two explicit high-prime bands have logarithmic mass
# rho = 10/3 per BBP depth.  The exact odd-denominator asymptotic leaves
# mass 6-rho = 8/3, which exceeds the required log(2^27/5)/7.
RHO_NUMERATOR = 10
RHO_DENOMINATOR = 3
FIRST_N = 18
LAST_N = 42
TAIL_N = 56
PERIODS = (1, 2, 3, 4, 5)


def check(condition: bool, description: str) -> None:
    if not condition:
        raise AssertionError(description)


def coefficient_numerator(k: int) -> int:
    return 120 * k * k + 151 * k + 47


def coefficient_denominator(k: int) -> int:
    return (2 * k + 1) * (4 * k + 3) * (8 * k + 1) * (8 * k + 5)


def lcm(left: int, right: int) -> int:
    return left // gcd(left, right) * right


def v2(integer: int) -> int:
    check(integer != 0, "v2 at zero")
    integer = abs(integer)
    return (integer & -integer).bit_length() - 1


def nearest(value: Fraction) -> int:
    """Return floor(value + 1/2), also for negative values."""
    return (2 * value.numerator + value.denominator) // (2 * value.denominator)


def nearest_shift_changing_full_odd_class(
    target_shift: Fraction,
    remaining_odd_cofactor: int,
) -> int:
    """Choose the nearest mixed-grid shift outside the full odd BBP class.

    The progression is parameterized as ``V + mixed_modulus * h``.  Because
    ``gcd(mixed_modulus, L)`` is the retained squarefree odd product, full
    odd preservation occurs exactly in the forbidden class ``h = 0`` modulo
    the remaining odd cofactor.
    """
    cofactor = remaining_odd_cofactor
    check(cofactor > 1, "a nontrivial odd coordinate remains to be changed")

    closest = nearest(target_shift)
    if closest % cofactor != 0:
        return closest

    candidates = (closest - 1, closest + 1)
    chosen = min(candidates, key=lambda value: abs(Fraction(value) - target_shift))
    check(chosen % cofactor != 0,
          "adjacent shift avoids the unique forbidden class")
    return chosen


def primes_through(limit: int) -> list[int]:
    flags = bytearray(b"\x01") * (limit + 1)
    flags[:2] = b"\x00\x00"
    for candidate in range(2, int(limit**0.5) + 1):
        if flags[candidate]:
            first = candidate * candidate
            flags[first : limit + 1 : candidate] = b"\x00" * (
                (limit - first) // candidate + 1
            )
    return [candidate for candidate in range(2, limit + 1) if flags[candidate]]


def retained_primes(depth: int, primes: list[int]) -> tuple[int, tuple[int, ...]]:
    """The two disjoint explicit survivor bands of total mass (10/3)M."""
    chosen: list[int] = []
    for prime in primes:
        first_band = (
            prime > 4 * depth + 3
            and (
                (prime % 8 == 1 and prime <= 8 * depth + 1)
                or (prime % 8 == 5 and prime <= 8 * depth + 5)
            )
        )
        second_band = (
            3 * prime > 8 * depth + 5
            and prime <= 4 * depth + 3
        )
        if first_band or second_band:
            chosen.append(prime)
    product = 1
    for prime in chosen:
        product *= prime
    return product, tuple(chosen)


def in_retained_band(depth: int, prime: int) -> bool:
    first_band = (
        prime > 4 * depth + 3
        and (
            (prime % 8 == 1 and prime <= 8 * depth + 1)
            or (prime % 8 == 5 and prime <= 8 * depth + 5)
        )
    )
    second_band = (
        3 * prime > 8 * depth + 5
        and prime <= 4 * depth + 3
    )
    return first_band or second_band


def build_endpoints() -> list[dict[str, int | Fraction]]:
    running_lcm = coefficient_denominator(0)
    scaled_numerator = coefficient_numerator(0)
    rows: list[dict[str, int | Fraction]] = [
        {"n": 0, "L": running_lcm, "A": scaled_numerator,
         "B": Fraction(scaled_numerator, running_lcm)}
    ]

    for m in range(1, 7 * TAIL_N + 1):
        dk = coefficient_denominator(m)
        next_lcm = lcm(running_lcm, dk)
        scaled_numerator = (
            16 * (next_lcm // running_lcm) * scaled_numerator
            + coefficient_numerator(m) * (next_lcm // dk)
        )
        running_lcm = next_lcm
        if m % 7 == 0:
            n = m // 7
            rows.append({
                "n": n,
                "L": running_lcm,
                "A": scaled_numerator,
                "B": Fraction(scaled_numerator, 16**m * running_lcm),
            })
    check(len(rows) == TAIL_N + 1, "endpoint count")
    return rows


def choose_state(
    row: dict[str, int | Fraction], deep_bbp: Fraction, primes: list[int]
) -> dict[str, int | Fraction | tuple[int, ...]]:
    n = int(row["n"])
    depth = 7 * n
    odd_lcm = int(row["L"])
    D = 2 ** (27 * n) * odd_lcm
    V = 5**n * int(row["A"])
    Q, selected_primes = retained_primes(depth, primes)
    modulus = 2 ** (27 * n) * Q
    check(D % modulus == 0, f"mixed modulus divides D n={n}")

    target = -10**n * (deep_bbp - Fraction(row["B"]))
    target_shift = Fraction(D * target - V, modulus)
    shift = nearest_shift_changing_full_odd_class(
        target_shift, odd_lcm // Q
    )
    S = V + shift * modulus
    eta = Fraction(S, D) - target
    return {
        "n": n,
        "L": odd_lcm,
        "D": D,
        "V": V,
        "Q": Q,
        "primes": selected_primes,
        "modulus": modulus,
        "selected_shift": shift,
        "target": target,
        "S": S,
        "r": D + S,
        "eta": eta,
    }


def run() -> dict[str, object]:
    for relative, expected in PINS.items():
        path = ROOT / relative
        check(path.is_file(), f"missing pinned input {relative}")
        check(sha256(path.read_bytes()).hexdigest() == expected,
              f"hash mismatch {relative}")

    # The exact odd-denominator asymptotic is log R_M=(6+o(1))M.  After
    # retaining rho=10/3, the available logarithmic mesh exponent is 8/3.
    # The report proves the logarithmic comparison; the floating value here
    # is only a diagnostic replay of its positive margin.
    rho = Fraction(RHO_NUMERATOR, RHO_DENOMINATOR)
    certified_margin = Fraction(7) * (Fraction(6) - rho)
    analytic_exponent = 27 * log(2) - log(5)
    check(float(certified_margin) > analytic_exponent,
          "chosen retained-prime mass lies below the separator threshold")

    rows = build_endpoints()
    all_primes = primes_through(8 * 7 * TAIL_N + 5)

    # Broad boundary replay of the factor-by-factor proof of
    # Q_(M+7) | Q_M * (L_(M+7)/L_M).  It tests many generic M, separately
    # from the actual separator depths below.
    band_nesting_boundary_checks = 0
    boundary_primes = primes_through(8 * (600 + 7) + 5)
    for depth in range(8, 601):
        for prime in boundary_primes:
            if prime > 8 * (depth + 7) + 5:
                break
            if not in_retained_band(depth + 7, prime):
                continue
            old_band = in_retained_band(depth, prime)
            new_pole = any(
                coefficient_denominator(k) % prime == 0
                for k in range(depth + 1, depth + 8)
            )
            check(old_band or new_pole,
                  f"generic seven-depth band nesting M={depth}, p={prime}")
            band_nesting_boundary_checks += 1

    deep_bbp = Fraction(rows[TAIL_N]["B"])
    states = {
        n: choose_state(rows[n], deep_bbp, all_primes)
        for n in range(FIRST_N, LAST_N + 1)
    }

    endpoint_checks = 0
    adversarial_selector_checks = 0
    high_prime_checks = 0
    state_checks = 0
    transition_checks = 0
    color_checks = 0
    product_formula_checks = 0
    max_relative_state_error = Fraction(0)
    max_relative_forcing_error = Fraction(0)
    retained_log_mass_ratios: list[float] = []
    free_log_mass_ratios: list[float] = []

    for n, state in states.items():
        row = rows[n]
        depth = 7 * n
        L = int(state["L"])
        D = int(state["D"])
        V = int(state["V"])
        Q = int(state["Q"])
        modulus = int(state["modulus"])
        S = int(state["S"])
        r = int(state["r"])
        target = Fraction(state["target"])
        eta = Fraction(state["eta"])

        cofactor = L // Q
        check(gcd(modulus, L) == Q,
              f"mixed/full odd gcd is exactly retained product n={n}")
        for offset in (Fraction(0), Fraction(1, 3), Fraction(-1, 3)):
            selected = nearest_shift_changing_full_odd_class(
                Fraction(cofactor) + offset,
                cofactor,
            )
            check(selected % cofactor != 0,
                  f"adversarial full-odd avoidance n={n}")
            check(abs(Fraction(selected) - (Fraction(cofactor) + offset))
                  <= Fraction(3, 2),
                  f"adversarial three-half mesh bound n={n}")
            adversarial_selector_checks += 2

        check(Fraction(V, D) == 10**n * Fraction(row["B"]),
              f"selected rational identity n={n}")
        valuation = v2(7 * n + 1)
        check(v2(V) == valuation, f"exact selected valuation n={n}")
        reduced_dyadic_exponent = 27 * n - valuation
        reduced_coordinate = (
            (V >> valuation)
            * pow(L, -1, 2**reduced_dyadic_exponent)
        ) % 2**reduced_dyadic_exponent
        reflected_coordinate = (
            5**n * (int(row["A"]) >> valuation)
            * pow(L, -1, 2**reduced_dyadic_exponent)
        ) % 2**reduced_dyadic_exponent
        check(reduced_coordinate == reflected_coordinate,
              f"full F-derived dyadic coordinate n={n}")
        endpoint_checks += 3

        reduced_odd_denominator = Fraction(row["B"]).denominator
        reduced_odd_denominator >>= v2(reduced_odd_denominator)
        check(reduced_odd_denominator % Q == 0,
              f"retained high primes survive reduction n={n}")
        for prime in state["primes"]:
            prime = int(prime)
            check(prime > depth, f"prime is above BBP depth n={n}, p={prime}")
            check(L % (prime * prime) != 0,
                  f"selected high prime is squarefree in L n={n}, p={prime}")
            check(V % prime != 0, f"actual high-prime unit n={n}, p={prime}")
            check(S % prime == V % prime,
                  f"selected high-prime coordinate n={n}, p={prime}")
            high_prime_checks += 4

        check((S - V) % modulus == 0, f"mixed selected class n={n}")
        check((r - V) % modulus == 0, f"positive mixed class n={n}")
        check(v2(S) == v2(V) and v2(r) == v2(V),
              f"complete dyadic valuation n={n}")
        check(abs(eta) <= Fraction(3 * Q, 2 * L),
              f"admissible mixed mesh bound n={n}")
        check((S - V) % L != 0,
              f"full odd selected coordinate deliberately changes n={n}")
        check(Fraction(-1, 2) < Fraction(S, D) < 0,
              f"negative centered state n={n}")
        check(0 < r < D, f"positive phase numerator n={n}")
        state_checks += 7

        max_relative_state_error = max(max_relative_state_error, abs(eta / target))
        retained_log_mass_ratios.append(log(Q) / depth)
        free_log_mass_ratios.append(log(L // Q) / depth)

        difference = S - V
        check(difference != 0 and difference % modulus == 0,
              f"nonzero product-formula difference n={n}")
        check(abs(difference) >= modulus,
              f"ordinary height balances local divisibility n={n}")
        product_formula_checks += 2

        for period in PERIODS:
            repunit = 10**period - 1
            centered = Fraction(repunit * S, D)
            check(Fraction(-1, 2) < centered < 0,
                  f"period-centered cell n={n}, P={period}")
            split_color = nearest(Fraction(repunit * r, D))
            check(split_color == repunit,
                  f"all-nine color n={n}, P={period}")
            color_checks += 2

    for n in range(FIRST_N, LAST_N):
        current = states[n]
        following = states[n + 1]
        D = int(current["D"])
        D_next = int(following["D"])
        dilation = D_next // D
        L_ratio = int(following["L"]) // int(current["L"])
        check(dilation == 2**27 * L_ratio, f"sevenfold dilation n={n}")
        check((int(current["Q"]) * L_ratio) % int(following["Q"]) == 0,
              f"moving retained band nests through new L factors n={n}")

        V = int(current["V"])
        V_next = int(following["V"])
        S = int(current["S"])
        S_next = int(following["S"])
        r = int(current["r"])
        r_next = int(following["r"])
        K = V_next - 10 * dilation * V
        K_alt = S_next - 10 * dilation * S
        delta = Fraction(K, D_next)
        delta_alt = Fraction(K_alt, D_next)
        next_modulus = int(following["modulus"])

        check(K > 0 and K_alt > 0, f"positive forcing n={n}")
        check((K_alt - K) % next_modulus == 0,
              f"complete next mixed forcing class n={n}")
        check(Fraction(following["target"])
              == 10 * Fraction(current["target"]) + delta,
              f"exact tail recurrence n={n}")
        check(delta_alt - delta
              == Fraction(following["eta"]) - 10 * Fraction(current["eta"]),
              f"mixed forcing coboundary n={n}")
        check(10 * dilation * r + K_alt == 9 * D_next + r_next,
              f"alternative phase quotient nine n={n}")
        transition_checks += 7
        max_relative_forcing_error = max(
            max_relative_forcing_error, abs((delta_alt - delta) / delta)
        )

        for period in PERIODS:
            repunit = 10**period - 1
            c = nearest(Fraction(repunit * r, D))
            c_next = nearest(Fraction(repunit * r_next, D_next))
            gamma = 9 * repunit + c_next - 10 * c
            check(c == repunit and c_next == repunit and gamma == 0,
                  f"zero centered carry n={n}, P={period}")
            color_checks += 1

    return {
        "status": "PASS",
        "bounded_replay_label": "experiment",
        "construction_label": "proof sketch",
        "depth_range": [FIRST_N, LAST_N],
        "bbp_depth_range": [7 * FIRST_N, 7 * LAST_N],
        "rational_tail_cutoff": TAIL_N,
        "retained_prime_mass_rho": "10/3",
        "rho_star_from_log_R_equals_6M": 6 - analytic_exponent / 7,
        "positive_exponent_margin": float(certified_margin) - analytic_exponent,
        "endpoint_checks": endpoint_checks,
        "adversarial_selector_checks": adversarial_selector_checks,
        "band_nesting_boundary_checks": band_nesting_boundary_checks,
        "high_prime_coordinate_checks": high_prime_checks,
        "state_checks": state_checks,
        "transition_checks": transition_checks,
        "color_and_zero_carry_checks": color_checks,
        "product_formula_balance_checks": product_formula_checks,
        "minimum_observed_retained_log_mass_over_depth": min(retained_log_mass_ratios),
        "minimum_observed_free_log_mass_over_depth": min(free_log_mass_ratios),
        "maximum_relative_state_error": float(max_relative_state_error),
        "maximum_relative_forcing_error": float(max_relative_forcing_error),
        "preserves_complete_dyadic_coordinate": True,
        "preserves_positive_linear_high_prime_mass": True,
        "preserves_complete_next_mixed_forcing_class": True,
        "asserts_fixed_return": False,
        "asserts_all_color_return": False,
        "asserts_v1": False,
    }


if __name__ == "__main__":
    print(json.dumps(run(), indent=2, sort_keys=True))
