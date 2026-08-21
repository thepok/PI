#!/usr/bin/env python3
"""Exact checks for the Machin three-adic coarse/fine correlation.

All finite search output has claim status ``experiment``.  The algebraic
identities checked here use exact ``Fraction`` and modular integer arithmetic;
the script neither evaluates pi nor reads a decimal digit table.
"""

from __future__ import annotations

import argparse
import hashlib
from fractions import Fraction
from pathlib import Path

from actual_numerator_phase_experiment import machin_seed, valuation


SOURCE_SHA256 = (
    "2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825"
)


def source_path() -> Path:
    return Path(__file__).resolve().parents[2] / "problems/local/pi-digits.txt"


def chi4(odd: int) -> int:
    """The primitive character modulo four on a positive odd integer."""
    if odd <= 0 or odd % 2 == 0:
        raise ValueError("chi4 expects a positive odd integer")
    return 1 if odd % 4 == 1 else -1


def band_exponent(j: int) -> int:
    """Unique a with 3**a <= 12*j+3 < 3**(a+1)."""
    d = 12 * j + 3
    a = 0
    power = 1
    while 3 * power <= d:
        power *= 3
        a += 1
    if not power <= d < 3 * power:
        raise AssertionError((j, a, power, d))
    return a


def local_fraction_mod(value: Fraction, modulus: int) -> int:
    """Reduce a rational whose denominator is prime to ``modulus``."""
    if value.denominator % 3 == 0:
        raise ValueError("denominator is not a three-adic unit")
    return value.numerator * pow(value.denominator, -1, modulus) % modulus


def divided_cancellation_unit(u: int, modulus: int) -> int:
    """(4*239**u-5**u)/3 modulo a power-of-three modulus."""
    lifted = 3 * modulus
    numerator = (4 * pow(239, u, lifted) - pow(5, u, lifted)) % lifted
    if numerator % 3:
        raise AssertionError(("cancellation unit", u, modulus, numerator))
    return numerator // 3


def sparse_window_residue(j: int, k: int) -> int:
    """The exact surviving-exponent formula for D_j*y_j modulo 3**k."""
    a = band_exponent(j)
    if not 1 <= k <= a - 1:
        raise ValueError(("window range", j, a, k))
    modulus = 3**k
    scale = 3 ** (a - k + 1)
    h = (12 * j + 3) // scale
    total = 0
    for t in range(1, h + 1, 2):
        u = scale * t
        s = valuation(t, 3)
        unit_t = t // 3**s
        cancellation = divided_cancellation_unit(u, modulus)
        denominator_unit = pow(5, u, modulus) * pow(239, u, modulus) % modulus
        term = 4 * chi4(u) * 3 ** (k - 1 - s)
        term *= cancellation
        term *= pow(unit_t, -1, modulus)
        term *= pow(denominator_unit, -1, modulus)
        total = (total + term) % modulus
    return pow(10, j, modulus) * total % modulus


def harmonic_staircase(k: int, h: int) -> int:
    """Stable renormalized signed harmonic sum H_k(h)."""
    modulus = 3**k
    total = 0
    for t in range(1, h + 1, 2):
        s = valuation(t, 3)
        unit_t = t // 3**s
        term = chi4(t) * 3 ** (k - 1 - s) * pow(unit_t, -1, modulus)
        total = (total + term) % modulus
    return total


def stable_window_residue(j: int, k: int) -> int:
    """Collapsed fixed-k formula, valid when a_j >= 2*k-1."""
    a = band_exponent(j)
    if a < 2 * k - 1 or k > a - 1:
        raise ValueError(("stable range", j, a, k))
    modulus = 3**k
    scale = 3 ** (a - k + 1)
    h = (12 * j + 3) // scale
    parity = -1 if (a - k + 1) % 2 else 1
    return (
        -4
        * pow(10, j, modulus)
        * parity
        * harmonic_staircase(k, h)
    ) % modulus


def mod_nine_staircase(j: int) -> int:
    """The explicit three-zone residue for D_j*y_j modulo nine."""
    a = band_exponent(j)
    if a < 3:
        raise ValueError(("mod-nine stable range", j, a))
    d = 12 * j + 3
    d_over_D = d // 3 ** (a - 1)
    if d_over_D < 5:
        zone = 0
    elif d_over_D < 7:
        zone = 1
    else:
        zone = 2
    if a % 2:
        return 1 + 3 * zone
    return (8 - 3 * zone) % 9


def decimal(value: Fraction, places: int = 12) -> str:
    """Deterministic display helper; no proof uses the rounded value."""
    scale = 10**places
    rounded = (value.numerator * scale + value.denominator // 2) // value.denominator
    return f"{rounded // scale}.{rounded % scale:0{places}d}"


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-j", type=int, default=80)
    parser.add_argument("--max-k", type=int, default=5)
    args = parser.parse_args()
    if args.max_j < 2:
        raise SystemExit("--max-j must be at least two")
    if args.max_k < 1:
        raise SystemExit("--max-k must be positive")

    digest = hashlib.sha256(source_path().read_bytes()).hexdigest()
    if digest != SOURCE_SHA256:
        raise AssertionError(("target hash", digest))

    sparse_checks = 0
    stable_checks = 0
    coarse_selector_checks = 0
    pulse_selector_checks = 0
    mod_three_checks = 0
    mod_nine_checks = 0
    impulse_checks = 0
    zero_impulses = 0
    nonzero_impulses = 0
    prefix_checks = 0
    selected_relative_bound_violations = 0
    selected_last_survival: dict[str, int | None] = {
        str(digit): None for digit in range(10)
    }
    selected_largest_ratio = Fraction()
    selected_largest_events: list[tuple[int, str, int, int, Fraction, str]] = []

    first_coarse_residue: dict[int, int | None] = {r: None for r in range(9)}
    first_fine_residue: dict[int, int | None] = {r: None for r in range(9)}
    rows: list[dict[str, int | Fraction]] = []

    for j in range(1, args.max_j + 1):
        y = machin_seed(j)
        q = y.denominator
        b = y.numerator % q
        a = band_exponent(j)
        D = 3 ** (a - 1)
        if valuation(q, 3) != a - 1:
            raise AssertionError(("T52 denominator profile", j, q, a))
        F = q // D
        if F % 3 == 0:
            raise AssertionError(("coprime split", j))
        r = b % F
        c = b // F
        if b != F * c + r or not (0 <= c < D and 0 <= r < F):
            raise AssertionError(("Euclidean split", j))

        max_valid_k = min(args.max_k, a - 1)
        for k in range(1, max_valid_k + 1):
            modulus = 3**k
            actual = local_fraction_mod(D * y, modulus)
            sparse = sparse_window_residue(j, k)
            if sparse != actual:
                raise AssertionError(("sparse window", j, a, k, actual, sparse))
            sparse_checks += 1

            theta = r * pow(F, -1, modulus) % modulus
            if (c + theta) % modulus != actual:
                raise AssertionError(("coarse/fine selector", j, k))
            coarse_selector_checks += 1

            # The selector propagates through the ordinary decimal orbit of
            # this fixed rational seed.  This is the modular content of the
            # T53 fine/coarse carry recurrence.
            current = b
            multiplier = 1
            for step in range(21):
                pulse_r = current % F
                pulse_c = current // F
                pulse_theta = pulse_r * pow(F, -1, modulus) % modulus
                if (pulse_c + pulse_theta) % modulus != multiplier * actual % modulus:
                    raise AssertionError(("pulse selector", j, k, step))
                pulse_selector_checks += 1
                current = 10 * current % q
                multiplier = 10 * multiplier % modulus

            if a >= 2 * k - 1:
                stable = stable_window_residue(j, k)
                if stable != actual:
                    raise AssertionError(("stable window", j, a, k, actual, stable))
                stable_checks += 1

        actual_mod_three = local_fraction_mod(D * y, 3)
        expected_mod_three = 1 if a % 2 else 2
        if actual_mod_three != expected_mod_three:
            raise AssertionError(("mod three", j, a, actual_mod_three))
        mod_three_checks += 1

        theta_mod_nine = r * pow(F, -1, 9) % 9
        first_coarse_residue[c % 9] = first_coarse_residue[c % 9] or j
        first_fine_residue[theta_mod_nine] = first_fine_residue[theta_mod_nine] or j
        row = {
            "j": j,
            "a": a,
            "D": D,
            "c9": c % 9,
            "theta9": theta_mod_nine,
        }
        if a >= 3:
            actual_mod_nine = local_fraction_mod(D * y, 9)
            expected_mod_nine = mod_nine_staircase(j)
            if actual_mod_nine != expected_mod_nine:
                raise AssertionError(
                    ("mod nine staircase", j, a, actual_mod_nine, expected_mod_nine)
                )
            if c % 9 != (expected_mod_nine - theta_mod_nine) % 9:
                raise AssertionError(("mod nine selector", j))
            row["L9"] = actual_mod_nine
            mod_nine_checks += 1

            # Use the formula-derived selector, not the already-known c, to
            # retain one of the nine invariant coarse classes.
            selected_class = (expected_mod_nine - theta_mod_nine) % 9
            length = 2 * j
            decimal_modulus = 10**length
            fine_prefix = decimal_modulus * r // F
            words: list[str] = []
            for coarse in range(selected_class, D, 9):
                prefix = (decimal_modulus * coarse + fine_prefix) // D
                if not 0 <= prefix < decimal_modulus:
                    raise AssertionError(("selected prefix", j, coarse))
                words.append(f"{prefix:0{length}d}")
                prefix_checks += 1
            if c % 9 != selected_class:
                raise AssertionError(("actual class omitted", j))
            zero_mode = Fraction((D // 9) * 9**length, 10**length)
            for digit in selected_last_survival:
                count = sum(digit not in word for word in words)
                if count:
                    selected_last_survival[digit] = j
                discrepancy = abs(Fraction(count) - zero_mode)
                if discrepancy > zero_mode:
                    selected_relative_bound_violations += 1
                ratio = Fraction(count, 1) / zero_mode
                if ratio > selected_largest_ratio:
                    selected_largest_ratio = ratio
                    witnesses = [word for word in words if digit not in word]
                    selected_largest_events = [
                        (j, digit, D // 9, count, zero_mode, witnesses[0])
                    ]
                elif ratio == selected_largest_ratio and count:
                    selected_largest_events.append(
                        (j, digit, D // 9, count, zero_mode, "")
                    )
        rows.append(row)

    # Check the sparse impulse recurrence on consecutive indices that stay in
    # one a-band and lie in the stable range for k.
    for j in range(1, args.max_j):
        a = band_exponent(j)
        if band_exponent(j + 1) != a:
            continue
        for k in range(1, min(args.max_k, a - 1) + 1):
            if a < 2 * k - 1:
                continue
            modulus = 3**k
            scale = 3 ** (a - k + 1)
            h0 = (12 * j + 3) // scale
            h1 = (12 * (j + 1) + 3) // scale
            parity = -1 if (a - k + 1) % 2 else 1
            expected_impulse = (
                -4
                * parity
                * pow(10, j + 1, modulus)
                * (harmonic_staircase(k, h1) - harmonic_staircase(k, h0))
            ) % modulus
            D = 3 ** (a - 1)
            current = local_fraction_mod(D * machin_seed(j), modulus)
            following = local_fraction_mod(D * machin_seed(j + 1), modulus)
            actual_impulse = (following - 10 * current) % modulus
            if actual_impulse != expected_impulse:
                raise AssertionError(
                    ("impulse recurrence", j, a, k, actual_impulse, expected_impulse)
                )
            impulse_checks += 1
            if actual_impulse:
                nonzero_impulses += 1
            else:
                zero_impulses += 1

    # Exact counterexamples to tempting but false simplifications.
    same_band_coarse_change = None
    coarse_times_ten_failure = None
    leading_times_ten_failure = None
    same_leading_different_coarse = None
    for left, right in zip(rows, rows[1:]):
        if left["a"] != right["a"]:
            continue
        if same_band_coarse_change is None and left["c9"] != right["c9"]:
            same_band_coarse_change = (left["j"], right["j"], left["c9"], right["c9"])
        if coarse_times_ten_failure is None and right["c9"] != (10 * left["c9"]) % 9:
            coarse_times_ten_failure = (left["j"], right["j"], left["c9"], right["c9"])
        if (
            leading_times_ten_failure is None
            and "L9" in left
            and "L9" in right
            and right["L9"] != (10 * left["L9"]) % 9
        ):
            leading_times_ten_failure = (left["j"], right["j"], left["L9"], right["L9"])
    for i, left in enumerate(rows):
        if "L9" not in left:
            continue
        for right in rows[i + 1 :]:
            if (
                "L9" in right
                and left["L9"] == right["L9"]
                and left["c9"] != right["c9"]
            ):
                same_leading_different_coarse = (
                    left["j"], right["j"], left["L9"], left["c9"], right["c9"]
                )
                break
        if same_leading_different_coarse is not None:
            break

    print("claim_status=experiment")
    print(f"source_sha256={digest}")
    print(f"j_range=1..{args.max_j}")
    print(f"k_range=1..{args.max_k}_when_valid")
    print(f"sparse_leading_window_checks={sparse_checks}")
    print(f"stable_renormalization_checks={stable_checks}")
    print(f"coarse_fine_selector_checks={coarse_selector_checks}")
    print(f"fixed_seed_pulse_selector_checks={pulse_selector_checks}")
    print(f"mod_three_checks={mod_three_checks}")
    print(f"mod_nine_staircase_checks={mod_nine_checks}")
    print(f"cross_index_impulse_checks={impulse_checks}")
    print(f"zero_impulses={zero_impulses}")
    print(f"nonzero_impulses={nonzero_impulses}")
    print(f"first_j_by_coarse_residue_mod9={first_coarse_residue}")
    print(f"first_j_by_fine_phase_residue_mod9={first_fine_residue}")
    print(f"same_band_coarse_change={same_band_coarse_change}")
    print(f"coarse_times_ten_failure={coarse_times_ten_failure}")
    print(f"leading_unit_times_ten_impulse={leading_times_ten_failure}")
    print(f"same_leading_unit_different_coarse={same_leading_different_coarse}")
    print(f"selected_mod9_prefix_checks={prefix_checks}")
    print(f"selected_mod9_last_survival_by_digit={selected_last_survival}")
    print(
        "selected_mod9_naive_abs_discrepancy_le_zero_mode_violations="
        f"{selected_relative_bound_violations}"
    )
    for j, digit, size, count, zero_mode, witness in selected_largest_events:
        print(
            "selected_mod9_largest_resonance="
            f"j:{j},digit:{digit},grid_size:{size},N:{count},"
            f"zero_mode:{decimal(zero_mode)},"
            f"occupancy_over_zero_mode:{decimal(Fraction(count) / zero_mode)}"
        )
        if witness:
            print(f"selected_mod9_largest_witness_prefix={witness}")
    print("all exact checks passed")


if __name__ == "__main__":
    main()
