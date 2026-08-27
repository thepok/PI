#!/usr/bin/env python3
"""Exact replay for the colored zero-carry reformulation of decimal V1.

The integer checks below audit the sevenfold-BBP phase/color identities and
bounded counterexamples to fixed-modulus shortcuts.  They do not establish
the quantified colored recurrence for pi and therefore do not prove V1.
"""

from __future__ import annotations

from fractions import Fraction
from hashlib import sha256
import json
from math import factorial, gcd
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]

PINS = {
    "problems/local/pi-digits.txt":
        "2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825",
    "work/ultrapi-resume/bbp_fixed_period_carry_attack_20260813.md":
        "bdc77060ef42a15f8985d70b70cf9777c36070713c940a18e89e05b149734d55",
    "work/ultrapi-resume/bbp_centered_carry_recurrence_20260813.md":
        "3a357c5b1932b76357259613c338dc6ca49f4bf68baef96730ad31b2a13e69e6",
    "work/ultrapi-resume/bbp_centered_carry_recurrence_20260813_check.py":
        "b83276cc2aceb61e903e8764424e2a3b9dddec8a5ac16ffff4b8370200316fff",
    "work/theory/pi-lacunary-near-return-sparsity/library/t53/pi_digits.txt":
        "77eeccb0067283e14c460b33dc230de54ef15c2e825fc2a35c984fb6984bf684",
    "work/theory/pi-lacunary-near-return-sparsity/library/t53/T17_REPORT.md":
        "f566dd992fa7897797a83022741eec709978bb278c4f247d698d73348999719e",
}

MAX_N = 800
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


def nearest(numerator: int, denominator: int) -> int:
    """Return floor(numerator / denominator + 1/2), denominator positive."""
    require(denominator > 0, "nearest requires a positive denominator")
    return (2 * numerator + denominator) // (2 * denominator)


def build_endpoints() -> list[dict[str, int]]:
    """Build L_(7n), A_(7n), and each exact seven-term increment."""
    common = coefficient_denominator(0)
    scaled = coefficient_numerator(0)
    endpoints = [{"n": 0, "L": common, "A": scaled, "R": 1, "H": 0}]

    for m in range(1, 7 * MAX_N + 1):
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
                f"sevenfold A recurrence at m={m}",
            )
            endpoints.append(
                {"n": m // 7, "L": common, "A": scaled,
                 "R": ratio, "H": forcing}
            )

    require(len(endpoints) == MAX_N + 1, "endpoint count")
    return endpoints


def base_state(endpoint: dict[str, int]) -> dict[str, int]:
    n = endpoint["n"]
    denominator = 2 ** (27 * n) * endpoint["L"]
    numerator = 5**n * endpoint["A"]
    quotient, residue = divmod(numerator, denominator)
    return {"D": denominator, "V": numerator, "a": quotient, "r": residue}


def split_color(q: int, residue: int, denominator: int) -> int:
    """The nearest-q partition color in {0,...,q}; endpoints stay split."""
    return nearest(q * residue, denominator)


def check_periodic_words() -> int:
    checks = 0
    for period in PERIODS:
        q = 10**period - 1
        for k in range(1, q):
            current = k
            emitted: list[int] = []
            for _ in range(period):
                following = (10 * current) % q
                require(1 <= following < q, "interior color stays interior")
                digit, remainder = divmod(10 * current - following, q)
                require(remainder == 0 and 0 <= digit <= 9,
                        "periodic digit quotient")
                emitted.append(digit)
                current = following
            expected = [int(character) for character in f"{k:0{period}d}"]
            require(current == k, "period-P color return")
            require(emitted == expected, "residue/periodic-word correspondence")
            checks += 1
    return checks


def check_phase_recurrence(
    endpoints: list[dict[str, int]], states: list[dict[str, int]]
) -> tuple[int, dict[int, list[int]]]:
    checks = 0
    colors: dict[int, list[int]] = {period: [] for period in PERIODS}

    for state in states:
        for period in PERIODS:
            q = 10**period - 1
            color = split_color(q, state["r"], state["D"])
            rounded = nearest(q * state["V"], state["D"])
            require(0 <= color <= q, "split-color range")
            require(rounded == q * state["a"] + color,
                    "quotient/residue color decomposition")
            require(rounded % q == color % q, "ordinary residue color")
            colors[period].append(color)

    for n in range(MAX_N):
        current = states[n]
        following = states[n + 1]
        increment = endpoints[n + 1]
        dilation = 2**27 * increment["R"]
        forcing = 5 ** (n + 1) * increment["H"]
        require(following["D"] == dilation * current["D"],
                "denominator recurrence")
        require(following["V"] == 10 * dilation * current["V"] + forcing,
                "q-independent numerator recurrence")

        unwrapped = 10 * dilation * current["r"] + forcing
        ordinary_digit, next_residue = divmod(unwrapped, following["D"])
        require(next_residue == following["r"], "phase residue recurrence")
        require(following["a"] == 10 * current["a"] + ordinary_digit,
                "phase quotient recurrence")

        for period in PERIODS:
            q = 10**period - 1
            color = colors[period][n]
            next_color = colors[period][n + 1]
            rounded = q * current["a"] + color
            next_rounded = q * following["a"] + next_color
            carry = next_rounded - 10 * rounded
            require(
                carry == q * ordinary_digit + next_color - 10 * color,
                "colored carry factorization",
            )
            require(
                (carry == 0)
                == (q * ordinary_digit + next_color == 10 * color),
                "zero-carry color criterion",
            )
            require((next_color - 10 * color - carry) % q == 0,
                    "color recurrence modulo q")
            checks += 1

    return checks, colors


def check_fixed_modulus_failures(
    endpoints: list[dict[str, int]], states: list[dict[str, int]],
    colors: dict[int, list[int]],
) -> dict[str, object]:
    absorption: dict[str, int] = {}
    for period in PERIODS:
        q = 10**period - 1
        onset_bound = (q - 1 + 13) // 14
        require(onset_bound <= MAX_N, "configured absorption bound")
        witness_k = (q - 1) // 2
        require(2 * witness_k + 1 == q, "odd-factor witness")
        require(7 * onset_bound >= witness_k, "LCM witness is in range")
        require(coefficient_denominator(witness_k) % q == 0,
                "q occurs in a four-pole denominator")
        require(states[onset_bound]["D"] % q == 0,
                "fixed color modulus is absorbed by D_n")
        absorption[str(period)] = onset_bound

        for n in range(onset_bound, min(onset_bound + 8, MAX_N + 1)):
            q_rounded = nearest(q * states[n]["V"], states[n]["D"])
            centered = q * states[n]["V"] - states[n]["D"] * q_rounded
            require(states[n]["D"] % q == 0, "absorbed denominator persists")
            require(centered % q == 0, "centered residue also becomes zero")

    # At P=1 the congruence D*z = -S (mod 9) is 0=0 already at n=1,
    # while the exact colors at n=1 and n=2 differ.
    q = 9
    require(colors[1][1] % q == 4 and colors[1][2] % q == 1,
            "different colors behind the same vacuous mod-9 congruence")

    # A fixed residue r_n mod q also does not determine the Archimedean color.
    r2 = states[2]["r"]
    r4 = states[4]["r"]
    require(r2 % q == r4 % q == 3, "phase-residue collision")
    require(colors[1][2] % q == 1 and colors[1][4] % q == 8,
            "phase-residue collision has different colors")

    return {
        "coarse_q_divides_D_onset_bound": absorption,
        "vacuous_mod9_color_witness": {"indices": [1, 2], "colors": [4, 1]},
        "r_mod9_not_color_witness": {
            "indices": [2, 4], "common_r_mod9": 3, "colors": [1, 8]
        },
    }


def check_boundary_split(
    endpoints: list[dict[str, int]], states: list[dict[str, int]],
    colors: dict[int, list[int]],
) -> dict[str, object]:
    q = 9
    rational_carries: list[int] = []
    for n in range(761, 766):
        rounded = nearest(q * states[n]["V"], states[n]["D"])
        next_rounded = nearest(q * states[n + 1]["V"], states[n + 1]["D"])
        rational_carries.append(next_rounded - 10 * rounded)
    require(rational_carries == [0] * 5, "retained rational five-zero block")
    require(colors[1][761:767] == [9] * 6,
            "zero residue uses the upper split color in the five-zero block")

    digits = (
        ROOT
        / "work/theory/pi-lacunary-near-return-sparsity/library/t53/pi_digits.txt"
    ).read_text(encoding="ascii").strip()
    lookahead = 24
    scale = 10**lookahead
    true_colors: list[int] = []
    for n in range(761, 767):
        prefix = int(digits[n:n + lookahead])
        lower = nearest(q * prefix, scale)
        upper = nearest(q * (prefix + 1), scale)
        require(lower == upper, "certified true split-color enclosure")
        true_colors.append(lower)
    require(true_colors == [9] * 6, "certified upper boundary color")

    true_carries = [
        q * int(digits[n]) + true_colors[n - 760] - 10 * true_colors[n - 761]
        for n in range(761, 766)
    ]
    require(true_carries == [0] * 5, "certified true five-zero block")
    return {
        "positions": [761, 762, 763, 764, 765],
        "ordinary_residue": 0,
        "split_color": 9,
        "rational_carries": rational_carries,
        "certified_true_carries": true_carries,
        "claim_label": "experiment",
    }


def check_sparse_zero_counterexample_samples() -> list[dict[str, int]]:
    """Sample the exact tail bound for x=sum 10^(-j!), not its general proof."""
    samples: list[dict[str, int]] = []
    for period, height, minimum_n in ((1, 8, 10), (2, 20, 100), (4, 35, 1000)):
        q = 10**period - 1
        j = 2
        while True:
            n = factorial(j)
            gap = factorial(j + 1) - n
            tail_bound = Fraction(10, 9 * 10**gap)
            if n >= minimum_n and q * tail_bound < Fraction(1, 2 * 10**height):
                break
            j += 1
        require(gap > height, "sparse factorial gap dominates zero block")
        samples.append(
            {"period": period, "height": height, "minimum_n": minimum_n,
             "factorial_index": j, "n": n, "next_gap": gap}
        )
    return samples


def replay() -> dict[str, object]:
    for relative, expected in PINS.items():
        path = ROOT / relative
        require(path.is_file(), f"missing pinned input: {relative}")
        require(digest(path) == expected, f"hash mismatch: {relative}")

    endpoints = build_endpoints()
    states = [base_state(endpoint) for endpoint in endpoints]
    periodic_checks = check_periodic_words()
    phase_checks, colors = check_phase_recurrence(endpoints, states)
    fixed_modulus = check_fixed_modulus_failures(endpoints, states, colors)
    boundary = check_boundary_split(endpoints, states, colors)
    sparse_samples = check_sparse_zero_counterexample_samples()

    return {
        "status": "PASS",
        "maximum_sevenfold_depth": MAX_N,
        "periods_checked": list(PERIODS),
        "periodic_word_checks": periodic_checks,
        "phase_and_color_identity_checks": phase_checks,
        "fixed_modulus_failures": fixed_modulus,
        "zero_residue_boundary_split": boundary,
        "sparse_zero_counterexample_samples": sparse_samples,
        "exact_derivation_label": "proof sketch",
        "bounded_replay_label": "experiment",
        "asserts_colored_condition_for_pi": False,
        "asserts_v1": False,
    }


if __name__ == "__main__":
    print(json.dumps(replay(), indent=2, sort_keys=True, default=str))
