#!/usr/bin/env python3
"""Independent exact replay of the corrected high-dyadic BBP separator.

This checker intentionally does not import the primary checker.  It rebuilds
the BBP integers from the four original poles, compares them with the compact
coefficient, follows the raw-to-reduced dyadic normalization, and constructs
an odd-class-avoiding separator using a finite rational BBP tail.  All output
is finite ``experiment`` evidence; no decimal-distribution claim is made.
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
    "work/ultrapi-resume/bbp_all_depth_two_adic_attack.md":
        "9c1282724c7999fd67133a3f0e756015e564dc6b7a2a1ec44f2efe892b2653d9",
    "work/ultrapi-resume/bbp_centered_carry_recurrence_20260813.md":
        "3a357c5b1932b76357259613c338dc6ca49f4bf68baef96730ad31b2a13e69e6",
    "work/ultrapi-resume/bbp_actual_odd_quotient_attack.md":
        "d77e96b5bdce3bfd8278fa3b650d7a95d16bc86738c2af95a2d740919470c9fc",
    "work/ultrapi-resume/bbp_short_orbit_return_attack.md":
        "eed140ef58160c09ae65b2596105882ff7614440b36ce45a9c94185bcf881e7d",
    "work/ultrapi-resume/bbp_high_dyadic_archimedean_separator_20260813.md":
        "d0d975ff9bab6ce456723085cb3e031a3be83a171fa6a94d8656d76d8b0457b3",
    "work/ultrapi-resume/bbp_high_dyadic_archimedean_separator_20260813_check.py":
        "69d07d421b215b85bd5e5f7a7d4036c9d38544a3a0a8fc7db4a6947687cb0ab8",
}

DIAGONAL_MAX = 72
TAIL_CUTOFF = 96
SEPARATOR_FIRST = 36
SEPARATOR_LAST = 70
FIXED_LEVEL_MAX = 9
PERIODS = (1, 2, 3, 4)


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def digest(path: Path) -> str:
    return sha256(path.read_bytes()).hexdigest()


def lcm(left: int, right: int) -> int:
    return left // gcd(left, right) * right


def v2(integer: int) -> int:
    require(integer != 0, "v2 is used only on nonzero integers")
    integer = abs(integer)
    return (integer & -integer).bit_length() - 1


def compact_numerator(k: int) -> int:
    return 120 * k * k + 151 * k + 47


def compact_denominator(k: int) -> int:
    return (2 * k + 1) * (4 * k + 3) * (8 * k + 1) * (8 * k + 5)


def coefficient_compact(k: int) -> Fraction:
    return Fraction(compact_numerator(k), compact_denominator(k))


def coefficient_four_poles(k: int) -> Fraction:
    return (
        Fraction(4, 8 * k + 1)
        - Fraction(2, 8 * k + 4)
        - Fraction(1, 8 * k + 5)
        - Fraction(1, 8 * k + 6)
    )


def residue_two(value: Fraction, bits: int) -> int:
    require(bits > 0, "a positive dyadic precision is required")
    require(value.denominator % 2 == 1, "the rational must be two-integral")
    modulus = 1 << bits
    return value.numerator * pow(value.denominator, -1, modulus) % modulus


def nearest_integer(value: Fraction) -> int:
    """The exact half-up convention floor(value + 1/2)."""
    return (2 * value.numerator + value.denominator) // (2 * value.denominator)


def build_bbp_rows(max_k: int) -> list[dict[str, int | Fraction]]:
    """Build L_k and A_k once, while independently evolving the four-pole sum."""
    rows: list[dict[str, int | Fraction]] = []
    common = 1
    scaled = 0
    four_pole_sum = Fraction(0)

    for k in range(max_k + 1):
        compact = coefficient_compact(k)
        four_pole = coefficient_four_poles(k)
        require(compact == four_pole, f"four-pole combination at k={k}")
        require(compact > 0, f"positive BBP coefficient at k={k}")

        denominator = compact_denominator(k)
        next_common = lcm(common, denominator)
        scaled = (
            16 * (next_common // common) * scaled
            + compact_numerator(k) * (next_common // denominator)
        )
        common = next_common
        four_pole_sum = 16 * four_pole_sum + four_pole
        require(
            Fraction(scaled, common) == four_pole_sum,
            f"F(k+1)=A_k/L_k rational identity at k={k}",
        )
        rows.append({
            "k": k,
            "L": common,
            "A": scaled,
            "F": four_pole_sum,
            "B": Fraction(scaled, 16 ** k * common),
        })
    return rows


def f_values_modulo(max_x: int, bits: int) -> list[int]:
    """Use only F(0)=0 and F(x+1)=16F(x)+a(x), modulo 2^bits."""
    modulus = 1 << bits
    values = [0]
    current = 0
    for x in range(max_x):
        current = (
            16 * current + residue_two(coefficient_compact(x), bits)
        ) % modulus
        values.append(current)
    return values


def selected_state(row: dict[str, int | Fraction], n: int) -> dict[str, object]:
    l_value = int(row["L"])
    a_value = int(row["A"])
    f_value = Fraction(row["F"])
    raw_bits = 27 * n
    raw_modulus = 1 << raw_bits
    numerator = 5 ** n * a_value
    denominator = raw_modulus * l_value
    order = v2(7 * n + 1)
    reduced_bits = raw_bits - order
    require(v2(a_value) == order, f"r_n=v2(7n+1) at n={n}")
    require(v2(numerator) == order, f"v2(V_n)=r_n at n={n}")

    raw_f = residue_two(f_value, raw_bits)
    require(raw_f != 0 and v2(raw_f) == order,
            f"raw F residue has exact order at n={n}")
    from_raw = (5 ** n * (raw_f >> order)) % (1 << reduced_bits)
    from_formula = residue_two(
        Fraction(5 ** n) * f_value / (1 << order), reduced_bits
    )

    reduced = Fraction(numerator, denominator)
    require(v2(reduced.denominator) == reduced_bits,
            f"reduced dyadic denominator at n={n}")
    reduced_odd = reduced.denominator >> reduced_bits
    require(reduced_odd % 2 == 1, f"odd reduced denominator at n={n}")
    direct = (
        reduced.numerator
        * pow(reduced_odd, -1, 1 << reduced_bits)
        % (1 << reduced_bits)
    )
    require(from_raw == from_formula == direct,
            f"raw and reduced complete dyadic coordinates at n={n}")

    return {
        "n": n,
        "L": l_value,
        "A": a_value,
        "F": f_value,
        "M": raw_modulus,
        "D": denominator,
        "V": numerator,
        "r": order,
        "kappa": reduced_bits,
        "w": direct,
    }


def choose_odd_class_avoiding_state(
    target: Fraction, denominator: int, numerator: int, modulus: int, odd: int
) -> tuple[int, Fraction, int]:
    """Select S=V+modulus*j near denominator*target with j nonzero mod odd."""
    require(denominator == modulus * odd, "separator mesh factorization")
    require(odd > 1 and odd % 2 == 1, "nontrivial odd mesh")
    ideal_shift = Fraction(denominator * target - numerator, modulus)
    closest = nearest_integer(ideal_shift)
    if closest % odd == 0:
        candidates = (closest - 1, closest + 1)
        closest = min(
            candidates,
            key=lambda candidate: (
                abs(Fraction(candidate) - ideal_shift), candidate
            ),
        )
    require(closest % odd != 0, "the complete odd class must change")
    distance = abs(Fraction(closest) - ideal_shift)
    require(distance <= Fraction(3, 2), "three-half-mesh selector bound")
    selected = numerator + modulus * closest
    error = Fraction(selected, denominator) - target
    require(abs(error) <= Fraction(3, 2 * odd), "scaled selector bound")
    return selected, error, closest


def adversarial_selector_replay() -> int:
    checks = 0
    offsets = (
        Fraction(-3, 2), Fraction(-1, 2), Fraction(-1, 3), Fraction(0),
        Fraction(1, 3), Fraction(1, 2), Fraction(3, 2),
    )
    for odd in (3, 5, 15, 21, 35):
        for power in (1, 4, 9):
            modulus = 1 << power
            numerator = 2 * odd + 1
            denominator = modulus * odd
            for multiple in (-2, -1, 0, 1, 2):
                for offset in offsets:
                    ideal = odd * multiple + offset
                    target = Fraction(numerator, denominator) + ideal / odd
                    selected, error, shift = choose_odd_class_avoiding_state(
                        target, denominator, numerator, modulus, odd
                    )
                    require((selected - numerator) % modulus == 0,
                            "adversarial raw dyadic class")
                    require((selected - numerator) % odd != 0,
                            "adversarial odd-class exclusion")
                    require(shift % odd != 0, "adversarial shift exclusion")
                    require(abs(error) <= Fraction(3, 2 * odd),
                            "adversarial mesh error")
                    checks += 4
    return checks


def replay() -> dict[str, object]:
    for relative, expected in PINS.items():
        path = ROOT / relative
        require(path.is_file(), f"missing pinned input: {relative}")
        require(digest(path) == expected, f"hash mismatch: {relative}")

    rows = build_bbp_rows(7 * TAIL_CUTOFF)

    fixed_level_checks = 0
    for bits in range(1, FIXED_LEVEL_MAX + 1):
        period = 1 << bits
        values = f_values_modulo(7 * (period - 1) + 1, bits)
        image = [values[7 * n + 1] for n in range(period)]
        require(len(set(image)) == period,
                f"fixed-level F(7n+1) permutation modulo 2^{bits}")
        fixed_level_checks += period

    states = {
        n: selected_state(rows[7 * n], n)
        for n in range(1, DIAGONAL_MAX + 1)
    }

    recurrence_checks = 0
    odd_denominator_checks = 0
    for n, state in states.items():
        row = rows[7 * n]
        b_value = Fraction(row["B"])
        odd_reduced = b_value.denominator >> v2(b_value.denominator)
        require(int(row["L"]) % odd_reduced == 0,
                f"actual reduced odd denominator divides L at n={n}")
        odd_denominator_checks += 1

        if n == DIAGONAL_MAX:
            continue
        following = states[n + 1]
        block = sum(
            16 ** (7 - j) * coefficient_four_poles(7 * n + j)
            for j in range(1, 8)
        )
        require(
            Fraction(following["F"]) == 16 ** 7 * Fraction(state["F"]) + block,
            f"seven-step F recurrence at n={n}",
        )
        exponent = 27 * (n + 1)
        bracket = (
            residue_two(Fraction(5 ** (n + 1)) * block, exponent)
            + 5 * (1 << (28 + int(state["r"]))) * int(state["w"])
        ) % (1 << exponent)
        next_order = int(following["r"])
        require(bracket % (1 << next_order) == 0,
                f"next-order divisibility at n={n}")
        require(bracket >> next_order == int(following["w"]),
                f"28+r_n diagonal recurrence at n={n}")
        input_lift_change = 5 * (
            1 << (28 + int(state["r"]) + int(state["kappa"]))
        )
        require(input_lift_change % (1 << (exponent + 1)) == 0,
                f"old reduced precision suffices at n={n}")
        recurrence_checks += 4

    adversarial_checks = adversarial_selector_replay()
    deep_bbp = Fraction(rows[7 * TAIL_CUTOFF]["B"])
    separator: dict[int, dict[str, object]] = {}
    selector_checks = 0
    color_checks = 0
    product_formula_no_go_checks = 0
    lambda_value = Fraction(5, 1 << 27)

    for n in range(SEPARATOR_FIRST, SEPARATOR_LAST + 1):
        state = states[n]
        partial = Fraction(rows[7 * n]["B"])
        target = -(10 ** n) * (deep_bbp - partial)
        require(target < 0, f"negative finite-tail target at n={n}")
        lower = lambda_value ** n / (336 * (7 * n + 1) ** 2)
        upper = lambda_value ** n / (15 * (7 * n + 1) ** 2)
        require(lower <= abs(target) <= upper,
                f"first-term and geometric finite-tail bounds at n={n}")

        selected, error, shift = choose_odd_class_avoiding_state(
            target,
            int(state["D"]),
            int(state["V"]),
            int(state["M"]),
            int(state["L"]),
        )
        centered = Fraction(selected, int(state["D"]))
        phase_numerator = int(state["D"]) + selected
        require(Fraction(-1, 2) < centered < 0,
                f"eventual negative centered cell at n={n}")
        require((selected - int(state["V"])) % int(state["M"]) == 0,
                f"complete raw dyadic class at n={n}")
        require((selected - int(state["V"])) % int(state["L"]) != 0,
                f"complete odd class differs at n={n}")
        require(v2(selected) == int(state["r"]),
                f"alternative centered valuation at n={n}")
        require(v2(phase_numerator) == int(state["r"]),
                f"alternative phase valuation at n={n}")
        delta = selected - int(state["V"])
        require(delta == int(state["M"]) * shift and shift != 0,
                f"nonzero product-formula integer at n={n}")
        require(abs(delta) >= int(state["M"]),
                f"dyadic divisibility forces Archimedean height at n={n}")
        selector_checks += 8
        product_formula_no_go_checks += 2

        for period in PERIODS:
            q_value = 10 ** period - 1
            require(Fraction(-1, 2) < q_value * centered < 0,
                    f"fixed-period centered state P={period}, n={n}")
            color = nearest_integer(
                Fraction(q_value * phase_numerator, int(state["D"]))
            )
            require(color == q_value,
                    f"all-nine color P={period}, n={n}")
            color_checks += 2

        separator[n] = {
            **state,
            "target": target,
            "S": selected,
            "eta": error,
            "e": centered,
            "phase": phase_numerator,
        }

    forcing_checks = 0
    for n in range(SEPARATOR_FIRST, SEPARATOR_LAST):
        current = separator[n]
        following = separator[n + 1]
        dilation = int(following["D"]) // int(current["D"])
        require(dilation * int(current["D"]) == int(following["D"]),
                f"integer denominator dilation at n={n}")
        actual = int(following["V"]) - 10 * dilation * int(current["V"])
        alternative = int(following["S"]) - 10 * dilation * int(current["S"])
        require(actual > 0 and alternative > 0,
                f"positive actual and alternative forcing at n={n}")
        require((alternative - actual) % int(following["M"]) == 0,
                f"complete next-depth forcing class at n={n}")
        actual_normalized = Fraction(actual, int(following["D"]))
        alternative_normalized = Fraction(alternative, int(following["D"]))
        require(
            alternative_normalized - actual_normalized
            == Fraction(following["eta"]) - 10 * Fraction(current["eta"]),
            f"forcing-error coboundary at n={n}",
        )
        require(abs(alternative_normalized - actual_normalized) < actual_normalized,
                f"sampled relative forcing error below one at n={n}")

        phase_quotient = (
            10 * dilation * int(current["phase"])
            + alternative - int(following["phase"])
        ) // int(following["D"])
        require(phase_quotient == 9,
                f"alternative base-ten phase quotient at n={n}")
        for period in PERIODS:
            q_value = 10 ** period - 1
            current_color = nearest_integer(Fraction(
                q_value * int(current["phase"]), int(current["D"])
            ))
            next_color = nearest_integer(Fraction(
                q_value * int(following["phase"]), int(following["D"])
            ))
            carry = q_value * phase_quotient + next_color - 10 * current_color
            require(carry == 0, f"all-nine zero carry P={period}, n={n}")
            color_checks += 1
        forcing_checks += 5

    final_odd = Fraction(rows[7 * DIAGONAL_MAX]["B"]).denominator
    final_odd >>= v2(final_odd)
    return {
        "status": "PASS",
        "finite_claim_label": "experiment",
        "audited_report_claim_label": "proof sketch",
        "fixed_level_permutation_checks": fixed_level_checks,
        "rational_identity_rows": len(rows),
        "complete_diagonal_states": len(states),
        "raw_reduced_and_recurrence_checks": recurrence_checks,
        "actual_odd_denominator_divisibility_checks": odd_denominator_checks,
        "adversarial_selector_checks": adversarial_checks,
        "separator_state_checks": selector_checks,
        "forcing_and_next_class_checks": forcing_checks,
        "all_nine_and_zero_carry_checks": color_checks,
        "product_formula_no_go_checks": product_formula_no_go_checks,
        "separator_depth_range": [SEPARATOR_FIRST, SEPARATOR_LAST],
        "finite_tail_cutoff": TAIL_CUTOFF,
        "last_log_actual_odd_denominator_over_depth": (
            log(final_odd) / (7 * DIAGONAL_MAX)
        ),
        "preserves_complete_raw_and_reduced_dyadic_coordinate": True,
        "preserves_complete_next_dyadic_forcing_class": True,
        "forces_changed_complete_odd_class": True,
        "asserts_actual_bbp_carries_are_zero": False,
        "asserts_v1": False,
    }


if __name__ == "__main__":
    print(json.dumps(replay(), indent=2, sort_keys=True))
