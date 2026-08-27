#!/usr/bin/env python3
"""Exact finite replay for the selected-numerator prefix separator.

The replay checks a bounded rational analogue of the infinite construction in
the companion report.  It preserves the complete odd BBP numerator class and
a growing dyadic prefix, but it deliberately changes the remaining selected
numerator bits.  It therefore does not prove anything about the digit
distribution of pi.
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
    "work/ultrapi-resume/bbp_colored_zero_carry_v1_20260813.md":
        "159ff0d1c94d9fb145790e0ca4f11db571d0af211ef2c588b094201122ff279a",
    "work/ultrapi-resume/bbp_centered_carry_recurrence_20260813.md":
        "3a357c5b1932b76357259613c338dc6ca49f4bf68baef96730ad31b2a13e69e6",
    "work/ultrapi-resume/bbp_all_depth_two_adic_attack.md":
        "9c1282724c7999fd67133a3f0e756015e564dc6b7a2a1ec44f2efe892b2653d9",
    "work/ultrapi-resume/bbp_rational_phase_density_separator_20260813.md":
        "1fa0054d89852630c573ad9eee5bd5ae59a442b34809343f7ca9bb7dc1fbc198",
    "work/theory/pi-digits/library/t6/bbp-1997-nasa.pdf":
        "e4e0b97fde01328ec41da5f2cd4d6ffc8bcd2b7bd7516b9d8afc320f6d1916c4",
    "work/theory/pi-lacunary-near-return-sparsity/library/t63/lagarias-math0101055v2.pdf":
        "a2a1171eb9c75c9fa3495ca3c3ceaa33c1d20b722bb56f82adb56d8c308209b9",
    "work/theory/pi-lacunary-near-return-sparsity/library/t63/bailey-crandall-2001-bcrandom.pdf":
        "701067697e8c1dace60cd8695ef509edae31f9da3bffd64b548624ccc2e4cfa8",
}

START_N = 100
MAX_N = 150
DEEP_N = 170
PERIODS = (1, 2, 3, 4)


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def digest(path: Path) -> str:
    return sha256(path.read_bytes()).hexdigest()


def coefficient_numerator(k: int) -> int:
    return 120 * k * k + 151 * k + 47


def coefficient_denominator(k: int) -> int:
    return (2 * k + 1) * (4 * k + 3) * (8 * k + 1) * (8 * k + 5)


def lcm(a: int, b: int) -> int:
    return a // gcd(a, b) * b


def valuation_two(value: int) -> int:
    require(value != 0, "two-adic valuation requires a nonzero integer")
    value = abs(value)
    return (value & -value).bit_length() - 1


def nearest_fraction(value: Fraction) -> int:
    """Return floor(value + 1/2), including for negative values."""
    return (2 * value.numerator + value.denominator) // (2 * value.denominator)


def nearest_ratio(numerator: int, denominator: int) -> int:
    require(denominator > 0, "nearest_ratio needs a positive denominator")
    return (2 * numerator + denominator) // (2 * denominator)


def build_endpoints() -> list[dict[str, int]]:
    """Build exact L_(7n), A_(7n), and seven-term increments."""
    common = coefficient_denominator(0)
    scaled = coefficient_numerator(0)
    endpoints = [{"n": 0, "L": common, "A": scaled, "R": 1, "H": 0}]

    for m in range(1, 7 * DEEP_N + 1):
        denominator = coefficient_denominator(m)
        next_common = lcm(common, denominator)
        scaled = (
            16 * (next_common // common) * scaled
            + coefficient_numerator(m) * (next_common // denominator)
        )
        common = next_common
        if m % 7 == 0:
            previous = endpoints[-1]
            ratio = common // previous["L"]
            forcing = sum(
                coefficient_numerator(k)
                * 16 ** (m - k)
                * (common // coefficient_denominator(k))
                for k in range(m - 6, m + 1)
            )
            require(
                scaled == 16**7 * ratio * previous["A"] + forcing,
                f"sevenfold endpoint recurrence at m={m}",
            )
            endpoints.append(
                {"n": m // 7, "L": common, "A": scaled,
                 "R": ratio, "H": forcing}
            )

    require(len(endpoints) == DEEP_N + 1, "endpoint count")
    return endpoints


def rational_bbp(endpoint: dict[str, int]) -> Fraction:
    n = endpoint["n"]
    return Fraction(endpoint["A"], 16 ** (7 * n) * endpoint["L"])


def selected_state(
    endpoint: dict[str, int], deep_bbp: Fraction
) -> dict[str, int | Fraction]:
    """Select the CRT-preserving representative nearest a rational tail."""
    n = endpoint["n"]
    odd = endpoint["L"]
    denominator = 2 ** (27 * n) * odd
    numerator = 5**n * endpoint["A"]
    kappa = 2 * n + 4
    modulus = 2**kappa * odd
    require(denominator % modulus == 0, "prefix modulus divides raw denominator")

    target = -10**n * (deep_bbp - rational_bbp(endpoint))
    residue = numerator % modulus
    shift = nearest_fraction((denominator * target - residue) / modulus)
    centered = residue + modulus * shift
    error = Fraction(centered, denominator) - target
    phase_numerator = denominator + centered

    return {
        "n": n,
        "D": denominator,
        "V": numerator,
        "L": odd,
        "kappa": kappa,
        "M": modulus,
        "target": target,
        "S_alt": centered,
        "eta": error,
        "r_alt": phase_numerator,
    }


def replay() -> dict[str, object]:
    for relative, expected in PINS.items():
        path = ROOT / relative
        require(path.is_file(), f"missing pinned input: {relative}")
        require(digest(path) == expected, f"hash mismatch: {relative}")

    endpoints = build_endpoints()
    deep_bbp = rational_bbp(endpoints[DEEP_N])
    states = {
        n: selected_state(endpoints[n], deep_bbp)
        for n in range(START_N, MAX_N + 1)
    }

    state_checks = 0
    denominator_checks = 0
    color_checks = 0
    transition_checks = 0
    maximum_relative_forcing_error = Fraction(0)
    maximum_relative_tail_error = Fraction(0)

    for n, state in states.items():
        denominator = int(state["D"])
        numerator = int(state["V"])
        odd = int(state["L"])
        kappa = int(state["kappa"])
        modulus = int(state["M"])
        centered = int(state["S_alt"])
        phase_numerator = int(state["r_alt"])
        target = Fraction(state["target"])
        error = Fraction(state["eta"])

        require(-denominator < 2 * centered < 0,
                f"negative centered representative at n={n}")
        require(0 < phase_numerator < denominator,
                f"fractional representative at n={n}")
        require((centered - numerator) % modulus == 0,
                f"selected numerator prefix at n={n}")
        require((phase_numerator - numerator) % modulus == 0,
                f"phase numerator prefix at n={n}")
        require(abs(error) <= Fraction(modulus, 2 * denominator),
                f"nearest-class error at n={n}")
        require(valuation_two(numerator) == valuation_two(7 * n + 1),
                f"actual two-adic identity at n={n}")
        require(kappa > valuation_two(numerator),
                f"dyadic prefix sees exact valuation at n={n}")
        require(valuation_two(phase_numerator) == valuation_two(numerator),
                f"alternative exact valuation at n={n}")
        state_checks += 8

        require(gcd(phase_numerator, denominator) == gcd(numerator, denominator),
                f"complete reduced denominator at n={n}")
        require(gcd(phase_numerator, odd) == gcd(numerator, odd),
                f"complete odd gcd at n={n}")
        denominator_checks += 2

        relative_tail_error = abs(error / target)
        maximum_relative_tail_error = max(
            maximum_relative_tail_error, relative_tail_error
        )

        for period in PERIODS:
            q = 10**period - 1
            q_error = Fraction(q * centered, denominator)
            require(Fraction(-1, 2) < q_error < 0,
                    f"fixed-period centered cell P={period}, n={n}")
            color = nearest_ratio(q * phase_numerator, denominator)
            require(color == q,
                    f"all-nine split color P={period}, n={n}")
            require(
                gcd(q * phase_numerator, denominator)
                == gcd(q * numerator, denominator),
                f"fixed-period reduced denominator P={period}, n={n}",
            )
            color_checks += 3

    for n in range(START_N, MAX_N):
        current = states[n]
        following = states[n + 1]
        endpoint = endpoints[n + 1]
        denominator = int(current["D"])
        next_denominator = int(following["D"])
        dilation = next_denominator // denominator
        require(dilation == 2**27 * endpoint["R"],
                f"denominator dilation at n={n}")

        actual_forcing = (
            int(following["V"]) - 10 * dilation * int(current["V"])
        )
        require(actual_forcing == 5 ** (n + 1) * endpoint["H"],
                f"actual selected forcing at n={n}")

        alternative_forcing = (
            int(following["S_alt"])
            - 10 * dilation * int(current["S_alt"])
        )
        require(alternative_forcing > 0,
                f"positive alternative forcing at n={n}")

        next_prefix_modulus = int(following["M"])
        require((alternative_forcing - actual_forcing) % next_prefix_modulus == 0,
                f"full odd/growing-dyadic forcing class at n={n}")

        delta = Fraction(actual_forcing, next_denominator)
        delta_alt = Fraction(alternative_forcing, next_denominator)
        target_identity = (
            Fraction(following["target"])
            - 10 * Fraction(current["target"])
        )
        require(target_identity == delta,
                f"common-cutoff zero solution at n={n}")
        require(
            delta_alt - delta
            == Fraction(following["eta"]) - 10 * Fraction(current["eta"]),
            f"forcing-error coboundary at n={n}",
        )
        maximum_relative_forcing_error = max(
            maximum_relative_forcing_error,
            abs((delta_alt - delta) / delta),
        )

        for period in PERIODS:
            q = 10**period - 1
            current_error = Fraction(q * int(current["S_alt"]), denominator)
            following_error = Fraction(
                q * int(following["S_alt"]), next_denominator
            )
            require(
                following_error
                == 10 * current_error + q * delta_alt,
                f"zero-carry recurrence P={period}, n={n}",
            )
            color_checks += 1
        transition_checks += 6

    return {
        "status": "PASS",
        "bounded_replay_label": "experiment",
        "construction_label": "proof sketch",
        "depth_range": [START_N, MAX_N],
        "rational_tail_cutoff": DEEP_N,
        "periods_checked": list(PERIODS),
        "state_identity_checks": state_checks,
        "complete_denominator_checks": denominator_checks,
        "color_and_zero_carry_checks": color_checks,
        "transition_identity_checks": transition_checks,
        "maximum_relative_tail_error": float(maximum_relative_tail_error),
        "maximum_relative_forcing_error": float(maximum_relative_forcing_error),
        "preserves_full_odd_selected_residue": True,
        "preserved_dyadic_bits": "2*n+4",
        "preserves_complete_reduced_denominator": True,
        "asserts_actual_bbp_carries_are_zero": False,
        "asserts_all_color_return": False,
        "asserts_v1": False,
    }


if __name__ == "__main__":
    print(json.dumps(replay(), indent=2, sort_keys=True))
