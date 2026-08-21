#!/usr/bin/env python3
"""Exact replay for the sevenfold BBP centered-carry recurrence.

Every structural assertion uses Python integers or ``fractions.Fraction``.
The certified-prefix and bounded BBP diagnostics are experiments, not an
asymptotic density proof.  This script asserts neither (40bl) nor V1.
"""

from __future__ import annotations

from fractions import Fraction
from hashlib import sha256
import json
from math import gcd
from math import prod
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]

PINS = {
    "problems/local/pi-digits.txt":
        "2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825",
    "work/ultrapi-resume/bbp_fixed_period_carry_attack_20260813.md":
        "bdc77060ef42a15f8985d70b70cf9777c36070713c940a18e89e05b149734d55",
    "work/ultrapi-resume/bbp_fixed_period_carry_attack_20260813_independent_audit.md":
        "ae7e6c84ca6ec253107c2fa48ed202c5ef4f3aadbee75cbd1bca3d2d03dafe91",
    "work/ultrapi-resume/bbp_all_depth_two_adic_attack.md":
        "9c1282724c7999fd67133a3f0e756015e564dc6b7a2a1ec44f2efe892b2653d9",
    "work/ultrapi-resume/bbp_all_depth_two_adic_independent_audit.md":
        "846268c0b45dd82b96c6112054e344669eca62fe9a4308a56e6026f131a25007",
    "work/theory/pi-digits/library/t6/bbp-1997-nasa.pdf":
        "e4e0b97fde01328ec41da5f2cd4d6ffc8bcd2b7bd7516b9d8afc320f6d1916c4",
    "work/theory/pi-positive-decimal-factor-entropy/library/t87/"
    "zeilberger-zudilin-2020.pdf":
        "3b11c4bf3e25927227ac8f7f4e49d7f1d3efeb42beecd7f3b8c64efb162d20b5",
    "work/theory/pi-lacunary-near-return-sparsity/library/t63/"
    "bailey-crandall-2001-bcrandom.pdf":
        "701067697e8c1dace60cd8695ef509edae31f9da3bffd64b548624ccc2e4cfa8",
    "work/theory/pi-lacunary-near-return-sparsity/library/t63/"
    "lagarias-math0101055v2.pdf":
        "a2a1171eb9c75c9fa3495ca3c3ceaa33c1d20b722bb56f82adb56d8c308209b9",
    "work/theory/pi-lacunary-near-return-sparsity/library/t53/pi_digits.txt":
        "77eeccb0067283e14c460b33dc230de54ef15c2e825fc2a35c984fb6984bf684",
    "work/theory/pi-lacunary-near-return-sparsity/library/t53/T17_REPORT.md":
        "f566dd992fa7897797a83022741eec709978bb278c4f247d698d73348999719e",
}

MAX_N = 1000
PERIODS = (1, 2, 4)


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def digest(path: Path) -> str:
    return sha256(path.read_bytes()).hexdigest()


def coefficient_numerator(k: int) -> int:
    return 120 * k * k + 151 * k + 47


def coefficient_denominator(k: int) -> int:
    return (2 * k + 1) * (4 * k + 3) * (8 * k + 1) * (8 * k + 5)


def coefficient(k: int) -> Fraction:
    return Fraction(coefficient_numerator(k), coefficient_denominator(k))


def lcm(a: int, b: int) -> int:
    return a // gcd(a, b) * b


def valuation_two(value: int) -> int:
    require(value != 0, "two-adic valuation of zero")
    value = abs(value)
    return (value & -value).bit_length() - 1


def nearest(numerator: int, denominator: int) -> int:
    """floor(numerator / denominator + 1/2), including negative inputs."""
    require(denominator > 0, "positive denominator")
    return (2 * numerator + denominator) // (2 * denominator)


def build_block_endpoints() -> list[dict[str, int]]:
    """Construct L_m,A_m at m=7n and verify every seven-term update."""
    common = coefficient_denominator(0)
    scaled = coefficient_numerator(0)
    endpoints: list[dict[str, int]] = [
        {"n": 0, "m": 0, "L": common, "A": scaled, "R": 1, "H": 0}
    ]

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
            new_denominator_product = prod(
                coefficient_denominator(k) for k in range(m - 6, m + 1)
            )
            require(new_denominator_product % ratio == 0,
                    f"odd LCM increment divides seven new denominators m={m}")
            forcing = sum(
                coefficient_numerator(k)
                * 16 ** (m - k)
                * (common // coefficient_denominator(k))
                for k in range(m - 6, m + 1)
            )
            require(
                scaled == 16**7 * ratio * previous["A"] + forcing,
                f"sevenfold numerator recurrence m={m}",
            )
            endpoints.append(
                {
                    "n": m // 7,
                    "m": m,
                    "L": common,
                    "A": scaled,
                    "R": ratio,
                    "H": forcing,
                }
            )

    require(len(endpoints) == MAX_N + 1, "endpoint count")
    return endpoints


def replay_period(
    period: int, endpoints: list[dict[str, int]]
) -> tuple[list[dict[str, int]], list[int]]:
    q = 10**period - 1
    states: list[dict[str, int]] = []
    carries: list[int] = []
    five_power = 1

    for endpoint in endpoints:
        n = endpoint["n"]
        common = endpoint["L"]
        scaled = endpoint["A"]
        denominator = 2 ** (27 * n) * common
        numerator = q * five_power * scaled
        rounded = nearest(numerator, denominator)
        centered = numerator - denominator * rounded

        require(-denominator <= 2 * centered < denominator,
                f"centered range P={period}, n={n}")
        if n >= 1:
            expected_v2 = valuation_two(7 * n + 1)
            require(valuation_two(scaled) == expected_v2,
                    f"v2(A_7n) P={period}, n={n}")
            require(valuation_two(numerator) == expected_v2,
                    f"v2(U) P={period}, n={n}")
            require(valuation_two(centered) == expected_v2,
                    f"v2(S) P={period}, n={n}")
            require((centered // 2**expected_v2) % 2 != 0,
                    f"odd centered numerator P={period}, n={n}")

        state = {
            "n": n,
            "D": denominator,
            "U": numerator,
            "z": rounded,
            "S": centered,
        }

        if n > 0:
            previous = states[-1]
            ratio = endpoint["R"]
            alpha = 2**27 * ratio
            forcing = q * five_power * endpoint["H"]
            require(denominator == alpha * previous["D"],
                    f"denominator recurrence P={period}, n={n - 1}")
            require(numerator == 10 * alpha * previous["U"] + forcing,
                    f"numerator recurrence P={period}, n={n - 1}")

            uncentered = 10 * alpha * previous["S"] + forcing
            carry = rounded - 10 * previous["z"]
            require(centered == uncentered - carry * denominator,
                    f"centered recurrence P={period}, n={n - 1}")
            require(carry == nearest(uncentered, denominator),
                    f"carry quotient P={period}, n={n - 1}")
            require(
                (carry == 0)
                == (-denominator <= 2 * uncentered < denominator),
                f"zero-carry interval P={period}, n={n - 1}",
            )
            carries.append(carry)

        states.append(state)
        five_power *= 5

    return states, carries


def check_h_step(
    states: list[dict[str, int]], carries: list[int], starts: tuple[tuple[int, int], ...]
) -> int:
    checks = 0
    for n, h in starts:
        start = states[n]
        finish = states[n + h]
        alpha = finish["D"] // start["D"]
        forcing = finish["U"] - 10**h * alpha * start["U"]
        aggregate = finish["z"] - 10**h * start["z"]
        weighted_carries = sum(
            10 ** (h - 1 - t) * carries[n + t] for t in range(h)
        )
        require(aggregate == weighted_carries,
                f"weighted carry identity n={n}, h={h}")
        require(
            finish["S"]
            == 10**h * alpha * start["S"]
            + forcing
            - aggregate * finish["D"],
            f"h-step centered recurrence n={n}, h={h}",
        )

        all_zero = all(carries[n + t] == 0 for t in range(h))
        interval_conditions = []
        for t in range(1, h + 1):
            current = states[n + t]
            alpha_t = current["D"] // start["D"]
            forcing_t = current["U"] - 10**t * alpha_t * start["U"]
            value_t = 10**t * alpha_t * start["S"] + forcing_t
            interval_conditions.append(
                -current["D"] <= 2 * value_t < current["D"]
            )
        require(all_zero == all(interval_conditions),
                f"exact null-block criterion n={n}, h={h}")
        checks += 1
    return checks


def find_context_conflicts(carries: list[int], maximum_order: int) -> dict[str, object]:
    result: dict[str, object] = {}
    for order in range(1, maximum_order + 1):
        seen: dict[tuple[int, ...], tuple[int, int]] = {}
        witness = None
        for index in range(max(20, order), len(carries)):
            context = tuple(carries[index - order:index])
            output = carries[index]
            if context in seen and seen[context][0] != output:
                old_output, old_index = seen[context]
                witness = {
                    "first_index": old_index,
                    "second_index": index,
                    "context": context,
                    "first_output": old_output,
                    "second_output": output,
                }
                break
            seen[context] = (output, index)
        require(witness is not None, f"finite context conflict order={order}")
        result[str(order)] = witness
    return result


def certified_prefix_experiment() -> dict[str, object]:
    """Compute P=1 true carries from the independently certified prefix."""
    digits = (
        ROOT
        / "work/theory/pi-lacunary-near-return-sparsity/library/t53/pi_digits.txt"
    ).read_text(encoding="ascii").strip()
    require(len(digits) == 1_048_596 and digits.isdigit(), "certified digit format")

    q = 9
    lookahead = 24
    scale = 10**lookahead
    rounded_fractional: list[int] = []
    for n in range(len(digits) - lookahead):
        prefix = int(digits[n:n + lookahead])
        lower = nearest(q * prefix, scale)
        upper = nearest(q * (prefix + 1), scale)
        require(lower == upper, f"rounding enclosure at decimal index {n}")
        rounded_fractional.append(lower)

    carries: list[int] = []
    for n in range(len(rounded_fractional) - 1):
        carries.append(
            q * int(digits[n])
            + rounded_fractional[n + 1]
            - 10 * rounded_fractional[n]
        )
    require(all(-5 <= carry <= 5 for carry in carries), "true carry range")

    longest = 0
    starts: list[int] = []
    current = 0
    for index, carry in enumerate(carries):
        if carry == 0:
            current += 1
            start = index - current + 1
            if current > longest:
                longest = current
                starts = [start]
            elif current == longest:
                starts.append(start)
        else:
            current = 0

    require(longest == 6 and starts == [710099], "certified longest P=1 zero run")
    require(sum(carry != 0 for carry in carries) == 943_633,
            "certified P=1 nonzero count")
    return {
        "available_carries": len(carries),
        "nonzero_carries": 943_633,
        "observed_nonzero_fraction": Fraction(943_633, len(carries)),
        "longest_zero_run": longest,
        "longest_zero_run_starts": starts,
        "claim_label": "experiment",
    }


def replay() -> dict[str, object]:
    for relative, expected in PINS.items():
        path = ROOT / relative
        require(path.is_file(), f"missing pinned input: {relative}")
        require(digest(path) == expected, f"hash mismatch: {relative}")

    # Directly verify the combined four-pole coefficient on a separate range.
    for k in range(256):
        direct = (
            Fraction(4, 8 * k + 1)
            - Fraction(2, 8 * k + 4)
            - Fraction(1, 8 * k + 5)
            - Fraction(1, 8 * k + 6)
        )
        require(direct == coefficient(k), f"four-pole coefficient k={k}")
        require(coefficient_denominator(k) % 2 == 1, f"odd d_k k={k}")

    endpoints = build_block_endpoints()
    period_results: dict[int, tuple[list[dict[str, int]], list[int]]] = {}
    for period in PERIODS:
        period_results[period] = replay_period(period, endpoints)

    states, carries = period_results[1]
    require(carries[761:766] == [0, 0, 0, 0, 0],
            "exact rational five-zero block")
    require(carries[755:772] ==
            [5, -1, 0, 2, 1, 5, 0, 0, 0, 0, 0, -1, -5, 4, -4, -3, -2],
            "exact rational local carry window")

    h_checks = check_h_step(
        states,
        carries,
        ((0, 1), (7, 3), (81, 9), (256, 17), (761, 5), (900, 31)),
    )
    context_conflicts = find_context_conflicts(carries, 6)

    # The BBP-tail upper allowance dominates the primitive lower grid bound
    # from v2(S) for n >= 8.  The proof in the report uses L_7n >= 1 and
    # 2^v2(7n+1) <= 7n+1; these exact checks replay its endpoint and growth.
    require(9 * 5**8 > 15 * (7 * 8 + 1) ** 3, "tail/grid dominance onset")
    for n in range(2, 1001):
        require(5 * (7 * n + 1) ** 3 > (7 * n + 8) ** 3,
                f"tail/grid dominance monotonicity n={n}")

    prefix = certified_prefix_experiment()
    prefix_digits = (
        ROOT
        / "work/theory/pi-lacunary-near-return-sparsity/library/t53/pi_digits.txt"
    ).read_text(encoding="ascii").strip()
    q = 9
    actual_window = []
    for n in range(755, 772):
        lookahead = 30
        scale = 10**lookahead
        first = int(prefix_digits[n:n + lookahead])
        second = int(prefix_digits[n + 1:n + 1 + lookahead])
        r0 = nearest(q * first, scale)
        r1 = nearest(q * second, scale)
        actual_window.append(q * int(prefix_digits[n]) + r1 - 10 * r0)
    require(actual_window == carries[755:772],
            "certified true/rational carry agreement in local window")

    fresh_odd_units: dict[str, object] = {}
    for n in range(761, 766):
        transition = endpoints[n + 1]
        ratio = transition["R"]
        forcing = 9 * 5 ** (n + 1) * transition["H"]
        require(carries[n] == 0, f"fresh-odd zero carry n={n}")
        require(ratio > 1, f"nontrivial fresh odd modulus n={n}")
        require(gcd(forcing, ratio) == 1, f"unit forcing modulo R_n n={n}")
        fresh_odd_units[str(n)] = {
            "carry": carries[n],
            "R_n": ratio,
            "R_n_bits": ratio.bit_length(),
            "gcd_J_R": gcd(forcing, ratio),
        }

    odd_growth = {
        "blocks": MAX_N,
        "blocks_with_no_odd_lcm_growth": sum(
            endpoint["R"] == 1 for endpoint in endpoints[1:]
        ),
        "maximum_increment_bits": max(
            endpoint["R"].bit_length() for endpoint in endpoints[1:]
        ),
    }

    return {
        "status": "PASS",
        "claim_label": "experiment",
        "pinned_inputs": len(PINS),
        "sevenfold_blocks": MAX_N,
        "periods": list(PERIODS),
        "one_step_recurrence_checks": MAX_N * len(PERIODS),
        "v2_centered_numerator_checks": MAX_N * len(PERIODS),
        "h_step_checks": h_checks,
        "exact_P1_zero_run": {"start": 761, "length": 5},
        "finite_context_conflicts": context_conflicts,
        "certified_prefix_P1": prefix,
        "odd_lcm_increment_diagnostic": odd_growth,
        "zero_carries_with_fresh_odd_unit_forcing": fresh_odd_units,
        "irrationality_exponent_used_in_report": "888/125",
        "linear_zero_run_slope": "763/125",
        "asserts_positive_carry_density": False,
        "asserts_sublinear_zero_run_bound": False,
        "asserts_finite_automaton": False,
        "asserts_v1": False,
    }


if __name__ == "__main__":
    print(json.dumps(replay(), indent=2, sort_keys=True, default=str))
