#!/usr/bin/env python3
"""Independent exact replay of the selected-numerator prefix separator.

This checker intentionally does not import the primary checker.  It builds BBP
partial sums as ``Fraction`` objects, recovers the raw endpoint numerators from
those fractions, and then audits a different range and a broader collection of
repunit/determinant multipliers.  Its finite output has label ``experiment``;
it does not establish a statement about the decimal digits of pi.
"""

from __future__ import annotations

from fractions import Fraction
from hashlib import sha256
import json
from math import gcd
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
PRIMARY = ROOT / "work/ultrapi-resume/bbp_selected_numerator_prefix_separator_20260813.md"
PRIMARY_SHA256 = "5edd6bdacb3d0d9a6b12b4265da777891bdc22d2b95a1c75bc102e475280d0f6"

FIRST_N = 110
LAST_N = 145
TAIL_ENDPOINT = 170
PERIODS = (1, 2, 3, 5, 6)
EXTRA_MULTIPLIERS = (1, 2, 7, 11, 37, 101, 1009)
DETERMINANTS = (-10_001, -19, -1, 0, 1, 23, 99_991)


def check(condition: bool, description: str) -> None:
    if not condition:
        raise AssertionError(description)


def denominator(k: int) -> int:
    return (2 * k + 1) * (4 * k + 3) * (8 * k + 1) * (8 * k + 5)


def numerator(k: int) -> int:
    return 120 * k * k + 151 * k + 47


def lcm(left: int, right: int) -> int:
    return left // gcd(left, right) * right


def v2(value: int) -> int:
    check(value != 0, "v2 called at zero")
    value = abs(value)
    return (value & -value).bit_length() - 1


def round_nearest(value: Fraction) -> int:
    """floor(value + 1/2), valid for positive and negative values."""
    return (2 * value.numerator + value.denominator) // (2 * value.denominator)


def endpoint_table() -> list[dict[str, int | Fraction]]:
    """Build endpoints via rational summation, not the primary raw recurrence."""
    running_lcm = 1
    partial = Fraction(0)
    rows: list[dict[str, int | Fraction]] = []

    for k in range(7 * TAIL_ENDPOINT + 1):
        dk = denominator(k)
        running_lcm = lcm(running_lcm, dk)
        partial += Fraction(numerator(k), 16**k * dk)
        if k % 7 != 0:
            continue
        n = k // 7
        scaled = partial * 16 ** (7 * n) * running_lcm
        check(scaled.denominator == 1, f"raw endpoint integrality n={n}")
        rows.append(
            {
                "n": n,
                "L": running_lcm,
                "A": scaled.numerator,
                "B": partial,
            }
        )

    check(len(rows) == TAIL_ENDPOINT + 1, "endpoint table length")
    return rows


def select(row: dict[str, int | Fraction], target_pi: Fraction, kappa: int) -> dict[str, int | Fraction]:
    n = int(row["n"])
    odd = int(row["L"])
    raw_denominator = 2 ** (27 * n) * odd
    actual_numerator = 5**n * int(row["A"])
    modulus = 2**kappa * odd
    check(raw_denominator % modulus == 0, f"M divides D n={n}, kappa={kappa}")

    target = -10**n * (target_pi - Fraction(row["B"]))
    residue = actual_numerator % modulus
    grid_coordinate = Fraction(raw_denominator * target - residue, modulus)
    grid_shift = round_nearest(grid_coordinate)
    selected_centered = residue + modulus * grid_shift
    error = Fraction(selected_centered, raw_denominator) - target

    # The rational finite surrogate is not used to prove uniqueness, but it
    # also has no half-grid tie in the replayed rows.
    twice_grid = 2 * grid_coordinate
    rational_tie = twice_grid.denominator == 1 and twice_grid.numerator % 2 != 0
    check(not rational_tie, f"unexpected finite half-grid tie n={n}")

    return {
        "n": n,
        "L": odd,
        "D": raw_denominator,
        "V": actual_numerator,
        "M": modulus,
        "kappa": kappa,
        "t": target,
        "S": selected_centered,
        "r": raw_denominator + selected_centered,
        "eta": error,
    }


def run() -> dict[str, object]:
    check(PRIMARY.is_file(), "missing frozen primary report")
    check(sha256(PRIMARY.read_bytes()).hexdigest() == PRIMARY_SHA256,
          "frozen primary report hash mismatch")

    rows = endpoint_table()
    target_pi = Fraction(rows[TAIL_ENDPOINT]["B"])
    states = {
        n: select(rows[n], target_pi, 2 * n + 4)
        for n in range(FIRST_N, LAST_N + 1)
    }

    endpoint_checks = 0
    congruence_checks = 0
    gcd_checks = 0
    transition_checks = 0
    color_checks = 0
    max_relative_state_error = Fraction(0)
    max_relative_forcing_error = Fraction(0)

    for n in range(FIRST_N, LAST_N + 1):
        row = rows[n]
        state = states[n]
        D = int(state["D"])
        V = int(state["V"])
        L = int(state["L"])
        M = int(state["M"])
        S = int(state["S"])
        r = int(state["r"])
        eta = Fraction(state["eta"])
        t = Fraction(state["t"])

        # Re-derive the raw identities from the independently summed B_n.
        check(Fraction(V, D) == 10**n * Fraction(row["B"]),
              f"V/D identity n={n}")
        check(v2(V) == v2(7 * n + 1), f"two-adic identity n={n}")
        check(v2(V) < 2 * n + 4, f"prefix exposes valuation n={n}")
        endpoint_checks += 3

        check(S % M == V % M, f"centered selected class n={n}")
        check(r % M == V % M, f"positive selected class n={n}")
        check(abs(eta) <= Fraction(M, 2 * D), f"nearest-grid bound n={n}")
        check(Fraction(-1, 2) < Fraction(S, D) < 0,
              f"eventual centered sign/cell n={n}")
        check(0 < r < D, f"positive phase representative n={n}")
        check(v2(r) == v2(V), f"preserved exact v2 n={n}")
        congruence_checks += 6

        max_relative_state_error = max(max_relative_state_error, abs(eta / t))

        for q in EXTRA_MULTIPLIERS + tuple(10**p - 1 for p in PERIODS):
            check(gcd(q * r, D) == gcd(q * V, D),
                  f"multiplied reduced denominator n={n}, q={q}")
            for z in DETERMINANTS:
                check(gcd(q * r - z * D, D) == gcd(q * V, D),
                      f"determinant gcd n={n}, q={q}, z={z}")
                gcd_checks += 1
            gcd_checks += 1

        for p in PERIODS:
            q = 10**p - 1
            qe = Fraction(q * S, D)
            check(Fraction(-1, 2) < qe < 0,
                  f"q-centered cell n={n}, P={p}")
            split_color = round_nearest(Fraction(q * r, D))
            check(split_color == q, f"all-nine split color n={n}, P={p}")
            color_checks += 2

    for n in range(FIRST_N, LAST_N):
        current = states[n]
        following = states[n + 1]
        D = int(current["D"])
        D_next = int(following["D"])
        dilation = D_next // D
        check(D_next == dilation * D, f"integer dilation n={n}")
        check(dilation == 2**27 * (int(rows[n + 1]["L"]) // int(rows[n]["L"])),
              f"sevenfold dilation n={n}")

        V = int(current["V"])
        V_next = int(following["V"])
        S = int(current["S"])
        S_next = int(following["S"])
        r = int(current["r"])
        r_next = int(following["r"])
        K = V_next - 10 * dilation * V
        K_alt = S_next - 10 * dilation * S
        next_modulus = int(following["M"])

        check(K > 0, f"actual positive forcing n={n}")
        check(K_alt > 0, f"alternative positive forcing n={n}")
        check((K_alt - K) % next_modulus == 0,
              f"next full-odd/dyadic forcing class n={n}")
        delta = Fraction(K, D_next)
        delta_alt = Fraction(K_alt, D_next)
        check(Fraction(following["t"]) == 10 * Fraction(current["t"]) + delta,
              f"tail zero-orbit recurrence n={n}")
        check(delta_alt - delta
              == Fraction(following["eta"]) - 10 * Fraction(current["eta"]),
              f"coboundary identity n={n}")
        check(Fraction(S_next, D_next) == 10 * Fraction(S, D) + delta_alt,
              f"alternative centered recurrence n={n}")
        check(10 * dilation * r + K_alt == 9 * D_next + r_next,
              f"phase quotient b=9 n={n}")
        transition_checks += 9
        max_relative_forcing_error = max(
            max_relative_forcing_error, abs((delta_alt - delta) / delta)
        )

        for p in PERIODS:
            q = 10**p - 1
            c = round_nearest(Fraction(q * r, D))
            c_next = round_nearest(Fraction(q * r_next, D_next))
            gamma = q * 9 + c_next - 10 * c
            check(c == q and c_next == q and gamma == 0,
                  f"split-color carry factorization n={n}, P={p}")
            color_checks += 1

    # Audit the general-slope arithmetic separately.  The last rational slope
    # is 23/10 < log_2(5), certified without floating point by 2^23 < 5^10.
    slope_checks = 0
    for slope_num, slope_den in ((1, 2), (1, 1), (9, 5), (2, 1), (23, 10)):
        check(2**slope_num < 5**slope_den,
              f"slope {slope_num}/{slope_den} lies below log2(5)")
        for n in range(FIRST_N, LAST_N):
            kappa = slope_num * n // slope_den
            kappa_next = slope_num * (n + 1) // slope_den
            check(kappa > v2(7 * n + 1), f"slope sees v2 n={n}")
            check(0 <= kappa_next - kappa <= 3, f"slope increment n={n}")
            check(kappa_next <= kappa + 28,
                  f"transition promotes dyadic prefix n={n}")
            check(kappa <= 27 * n, f"slope modulus divides D n={n}")
            slope_checks += 4

    return {
        "status": "PASS",
        "bounded_replay_label": "experiment",
        "audited_construction_label": "proof sketch",
        "depth_range": [FIRST_N, LAST_N],
        "rational_tail_cutoff": TAIL_ENDPOINT,
        "periods_checked": list(PERIODS),
        "endpoint_checks": endpoint_checks,
        "congruence_and_cell_checks": congruence_checks,
        "determinant_gcd_checks": gcd_checks,
        "transition_checks": transition_checks,
        "split_color_carry_checks": color_checks,
        "general_slope_checks": slope_checks,
        "maximum_relative_state_error": float(max_relative_state_error),
        "maximum_relative_forcing_error": float(max_relative_forcing_error),
        "asserts_v1": False,
        "asserts_actual_pi_carry_return": False,
    }


if __name__ == "__main__":
    print(json.dumps(run(), indent=2, sort_keys=True))
