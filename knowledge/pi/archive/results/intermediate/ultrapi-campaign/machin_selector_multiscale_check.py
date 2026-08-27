#!/usr/bin/env python3
"""Exact finite checks for the balanced three-adic selector tower.

Every finite-search output has claim status ``experiment``.  The program uses
only integer arithmetic and ``Fraction``.  It neither evaluates pi nor reads a
decimal digit table.
"""

from __future__ import annotations

import argparse
import hashlib
from fractions import Fraction
from itertools import product
from pathlib import Path


SOURCE_SHA256 = (
    "2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825"
)
RHO = Fraction(10, 625**3)


def source_path() -> Path:
    return Path(__file__).resolve().parents[2] / "problems/local/pi-digits.txt"


def fract(value: Fraction) -> Fraction:
    return value - value.numerator // value.denominator


def valuation(value: int, prime: int) -> int:
    if value == 0:
        raise ValueError("valuation of zero")
    value = abs(value)
    exponent = 0
    while value % prime == 0:
        value //= prime
        exponent += 1
    return exponent


def band_exponent(j: int) -> int:
    """The unique a with 3**a <= 12*j+3 < 3**(a+1)."""
    d = 12 * j + 3
    a = 0
    power = 1
    while 3 * power <= d:
        power *= 3
        a += 1
    if not power <= d < 3 * power:
        raise AssertionError((j, a, d, power))
    return a


def balanced_depth(a: int) -> int:
    """A non-tautological growing selector depth, floor(a/2)."""
    return a // 2


def chi4(odd: int) -> int:
    if odd <= 0 or odd % 2 == 0:
        raise ValueError("chi4 expects a positive odd integer")
    return 1 if odd % 4 == 1 else -1


def harmonic_staircase(k: int, h: int) -> int:
    """The stable signed harmonic staircase H_k(h) modulo 3**k."""
    modulus = 3**k
    total = 0
    for t in range(1, h + 1, 2):
        s = valuation(t, 3)
        unit = t // 3**s
        total += chi4(t) * 3 ** (k - 1 - s) * pow(unit, -1, modulus)
    return total % modulus


def stable_leading_residue(j: int, k: int) -> int:
    """The stable formula for D_j*y_j modulo 3**k."""
    a = band_exponent(j)
    if not (1 <= k <= a - 1 and a >= 2 * k - 1):
        raise ValueError((j, a, k))
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


def local_fraction_mod(value: Fraction, modulus: int) -> int:
    if value.denominator % 3 == 0:
        raise ValueError("denominator is not a three-adic unit")
    return value.numerator * pow(value.denominator, -1, modulus) % modulus


def machin_seeds(max_j: int) -> list[Fraction | None]:
    """Construct all seeds incrementally, avoiding an O(max_j**2) rescan."""
    five_sum = Fraction()
    two_three_nine_sum = Fraction()
    five_count = 0
    two_three_nine_count = 0
    result: list[Fraction | None] = [None]
    for j in range(1, max_j + 1):
        next_five_count = 6 * j + 2
        for index in range(five_count, next_five_count):
            odd = 2 * index + 1
            five_sum += Fraction(-1 if index & 1 else 1, odd * 5**odd)
        five_count = next_five_count

        next_two_three_nine_count = 6 * j + 3
        for index in range(two_three_nine_count, next_two_three_nine_count):
            odd = 2 * index + 1
            two_three_nine_sum += Fraction(
                -1 if index & 1 else 1, odd * 239**odd
            )
        two_three_nine_count = next_two_three_nine_count
        result.append(10**j * (16 * five_sum - 4 * two_three_nine_sum))
    return result


def decimal_word(point: Fraction, length: int) -> str:
    scale = 10**length
    value = scale * point.numerator // point.denominator
    if not 0 <= value < scale:
        raise AssertionError((point, length, value))
    return f"{value:0{length}d}"


def avoidance_count(word: str, length: int) -> int:
    """Number of length-``length`` decimal strings avoiding ``word``."""
    m = len(word)
    if m == 0:
        return 0
    states = [0] * m
    states[0] = 1
    for _ in range(length):
        following = [0] * m
        for state, count in enumerate(states):
            if not count:
                continue
            prefix = word[:state]
            for digit in "0123456789":
                candidate = prefix + digit
                if candidate.endswith(word):
                    continue
                next_state = min(m - 1, len(candidate))
                while next_state and not candidate.endswith(word[:next_state]):
                    next_state -= 1
                following[next_state] += count
        states = following
    return sum(states)


def missing_words(text: str, length: int, universe: tuple[str, ...]) -> set[str]:
    present = {text[i : i + length] for i in range(len(text) - length + 1)}
    return set(universe).difference(present)


def decimal(value: Fraction, places: int = 12) -> str:
    scale = 10**places
    rounded = (value.numerator * scale + value.denominator // 2) // value.denominator
    return f"{rounded // scale}.{rounded % scale:0{places}d}"


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-j", type=int, default=240)
    args = parser.parse_args()
    if args.max_j < 20:
        raise SystemExit("--max-j must be at least 20")

    digest = hashlib.sha256(source_path().read_bytes()).hexdigest()
    if digest != SOURCE_SHA256:
        raise AssertionError(("target hash", digest))

    universes = {
        length: tuple("".join(chars) for chars in product("0123456789", repeat=length))
        for length in (1, 2)
    }
    avoid_counts: dict[tuple[str, int], int] = {}
    seeds = machin_seeds(args.max_j)

    data: list[dict[str, object] | None] = [None] * (args.max_j + 1)
    stable_checks = 0
    selector_checks = 0
    phase_recombination_checks = 0
    residual_integrality_checks = 0
    residual_depth_recurrence_checks = 0
    nested_phase_root_checks = 0
    actual_membership_checks = 0
    grid_partition_checks = 0
    prefix_checks = {1: 0, 2: 0}
    average_contraction_violations = {1: 0, 2: 0}
    full_concentrations = {1: 0, 2: 0}
    singleton_concentrations = {1: 0, 2: 0}
    first_full_concentrations: dict[int, list[tuple[int, str, int, int, int]]] = {
        1: [],
        2: [],
    }
    last_survival: dict[int, dict[str, int | None]] = {
        length: {word: None for word in universe}
        for length, universe in universes.items()
    }
    first_selected_resurrections: dict[int, list[tuple[int, str, int]]] = {
        1: [],
        2: [],
    }
    previous_selected: dict[int, dict[str, int]] = {1: {}, 2: {}}
    largest_occupancy_over_zero: dict[
        int, tuple[Fraction, int, str, int, int, Fraction] | None
    ] = {1: None, 2: None}

    # Start at j=2 (a_j=3).  At j=1 the nominal balanced choice has
    # k_1=a_1-1 and is the forbidden singleton/full-selector tautology.
    for j in range(2, args.max_j + 1):
        seed = seeds[j]
        assert seed is not None
        point = fract(seed)
        q_den = point.denominator
        b = point.numerator
        a = band_exponent(j)
        D = 3 ** (a - 1)
        k = balanced_depth(a)
        if not 1 <= k < a - 1:
            raise AssertionError(("non-tautological depth", j, a, k))
        p = 3**k
        E = D // p
        if D != p * E:
            raise AssertionError(("balanced factorization", j))
        if valuation(q_den, 3) != a - 1:
            raise AssertionError(("T52 denominator", j, q_den, a))
        F = q_den // D
        if F % 3 == 0:
            raise AssertionError(("coprime factor", j))
        r = b % F
        c = b // F
        if b != F * c + r or not (0 <= c < D and 0 <= r < F):
            raise AssertionError(("Euclidean split", j))
        theta = Fraction(r, F)

        tower: list[dict[str, int | Fraction] | None] = [None]
        previous_tower: dict[str, int | Fraction] | None = None
        for depth in range(1, k + 1):
            depth_modulus = 3**depth
            depth_grid_size = D // depth_modulus
            depth_L = stable_leading_residue(j, depth)
            actual_L = local_fraction_mod(D * seed, depth_modulus)
            if depth_L != actual_L:
                raise AssertionError(
                    ("stable staircase tower", j, a, depth, depth_L, actual_L)
                )
            stable_checks += 1
            depth_T = r * pow(F, -1, depth_modulus) % depth_modulus
            depth_C = (depth_L - depth_T) % depth_modulus
            if depth_C != c % depth_modulus:
                raise AssertionError(("coarse/fine selector tower", j, depth))
            selector_checks += 1

            residual_numerator = F * (depth_C - depth_L) + r
            if residual_numerator % depth_modulus:
                raise AssertionError(("residual integrality", j, depth))
            residual = residual_numerator // depth_modulus
            residual_integrality_checks += 1
            depth_beta = fract(depth_grid_size * point)
            recombined = Fraction(depth_L, depth_modulus) + Fraction(residual, F)
            if depth_beta != recombined:
                raise AssertionError(
                    ("leading/residual phase recombination", j, depth)
                )
            phase_recombination_checks += 1

            current_tower: dict[str, int | Fraction] = {
                "modulus": depth_modulus,
                "grid_size": depth_grid_size,
                "L": depth_L,
                "T": depth_T,
                "C": depth_C,
                "residual": residual,
                "beta": depth_beta,
            }
            if previous_tower is not None:
                old_modulus = int(previous_tower["modulus"])
                old_L = int(previous_tower["L"])
                old_C = int(previous_tower["C"])
                old_residual = int(previous_tower["residual"])
                old_beta = previous_tower["beta"]
                assert isinstance(old_beta, Fraction)
                c_lift = (depth_C - old_C) // old_modulus
                l_lift = (depth_L - old_L) // old_modulus
                if c_lift not in (0, 1, 2) or l_lift not in (0, 1, 2):
                    raise AssertionError(("ternary lift digits", j, depth))
                if 3 * residual != old_residual + F * (c_lift - l_lift):
                    raise AssertionError(("exact residual recurrence", j, depth))
                if residual % F != pow(3, -1, F) * old_residual % F:
                    raise AssertionError(("residual inverse-three recurrence", j, depth))
                residual_depth_recurrence_checks += 1
                if old_beta != fract(3 * depth_beta):
                    raise AssertionError(("nested phase cube root", j, depth))
                nested_phase_root_checks += 1
            tower.append(current_tower)
            previous_tower = current_tower

        balanced = tower[k]
        assert balanced is not None
        L = int(balanced["L"])
        T = int(balanced["T"])
        C = int(balanced["C"])
        beta = balanced["beta"]
        assert isinstance(beta, Fraction)

        parent_k = k - 1
        parent_p = 3**parent_k
        parent_E = D // parent_p
        parent_C = c % parent_p
        selector_digit = (C - parent_C) // parent_p
        if selector_digit not in (0, 1, 2) or C != parent_C + parent_p * selector_digit:
            raise AssertionError(("selector digit", j, C, parent_C, selector_digit))
        if parent_E != 3 * E:
            raise AssertionError(("parent/child sizes", j, parent_E, E))
        actual_index = (c - C) // p
        if not 0 <= actual_index < E:
            raise AssertionError(("actual selected membership", j, actual_index, E))
        actual_membership_checks += 1

        selected_counts_by_length: dict[int, dict[str, int]] = {}
        for word_length, universe in universes.items():
            prefix_length = 2 * j + word_length - 1
            alias_counts = [
                {word: 0 for word in universe}
                for _ in range(3)
            ]
            seen_parent = 0
            seen_selected = 0
            for parent_index in range(parent_E):
                coarse = parent_C + parent_p * parent_index
                if not 0 <= coarse < D:
                    raise AssertionError(("parent coarse range", j, coarse, D))
                value = Fraction(F * coarse + r, F * D)
                text_value = decimal_word(value, prefix_length)
                alias = parent_index % 3
                for word in missing_words(text_value, word_length, universe):
                    alias_counts[alias][word] += 1
                seen_parent += 1
                if alias == selector_digit:
                    selected_coarse = C + p * seen_selected
                    if coarse != selected_coarse:
                        raise AssertionError(
                            ("selected alias ordering", j, coarse, selected_coarse)
                        )
                    seen_selected += 1
            if seen_parent != parent_E or seen_selected != E:
                raise AssertionError(("alias cardinality", j, seen_parent, seen_selected))
            prefix_checks[word_length] += seen_parent
            grid_partition_checks += 1

            selected = alias_counts[selector_digit]
            selected_counts_by_length[word_length] = selected
            for word in universe:
                child_count = selected[word]
                parent_count = sum(alias[word] for alias in alias_counts)
                if not 0 <= child_count <= parent_count:
                    raise AssertionError(("occupancy nesting", j, word))
                if 3 * child_count > parent_count:
                    average_contraction_violations[word_length] += 1
                if child_count and child_count == parent_count:
                    full_concentrations[word_length] += 1
                    if len(first_full_concentrations[word_length]) < 12:
                        first_full_concentrations[word_length].append(
                            (j, word, parent_count, child_count, selector_digit)
                        )
                    if child_count == 1:
                        singleton_concentrations[word_length] += 1
                if child_count:
                    last_survival[word_length][word] = j

                key = (word, prefix_length)
                if key not in avoid_counts:
                    avoid_counts[key] = avoidance_count(word, prefix_length)
                zero_mode = Fraction(E * avoid_counts[key], 10**prefix_length)
                if child_count:
                    ratio = Fraction(child_count) / zero_mode
                    previous = largest_occupancy_over_zero[word_length]
                    if previous is None or ratio > previous[0]:
                        largest_occupancy_over_zero[word_length] = (
                            ratio,
                            j,
                            word,
                            E,
                            child_count,
                            zero_mode,
                        )

                before = previous_selected[word_length].get(word)
                if before == 0 and child_count > 0:
                    if len(first_selected_resurrections[word_length]) < 12:
                        first_selected_resurrections[word_length].append(
                            (j - 1, word, child_count)
                        )
            previous_selected[word_length] = selected.copy()

        data[j] = {
                "j": j,
                "seed": seed,
                "point": point,
                "a": a,
                "D": D,
                "k": k,
                "p": p,
                "E": E,
                "beta": beta,
                "tower": tower,
                "selected": selected_counts_by_length,
            }

    cross_index_checks = 0
    ordinary_geometry_steps = 0
    tripled_geometry_steps = 0
    selector_absorbed_thresholds = 0
    for j in range(2, args.max_j):
        left = data[j]
        right = data[j + 1]
        assert left is not None and right is not None
        E = int(left["E"])
        next_E = int(right["E"])
        sigma = next_E // E
        if sigma not in (1, 3) or next_E != sigma * E:
            raise AssertionError(("nested balanced geometry", j, E, next_E))
        seed = left["seed"]
        next_seed = right["seed"]
        assert isinstance(seed, Fraction) and isinstance(next_seed, Fraction)
        forcing = next_seed - 10 * seed
        if forcing <= 0:
            raise AssertionError(("positive actual forcing", j))
        beta = left["beta"]
        next_beta = right["beta"]
        assert isinstance(beta, Fraction) and isinstance(next_beta, Fraction)
        if next_beta != fract(10 * sigma * beta + next_E * forcing):
            raise AssertionError(("balanced frequency phase recurrence", j))
        cross_index_checks += 1
        if sigma == 3:
            tripled_geometry_steps += 1
        else:
            ordinary_geometry_steps += 1
            if int(right["D"]) == 3 * int(left["D"]):
                if int(right["p"]) != 3 * int(left["p"]):
                    raise AssertionError(("absorbed threshold selector", j))
                selector_absorbed_thresholds += 1

    # Separator: preserve the actual balanced stable residue L_j modulo p_j,
    # the D_j schedule, and a positive geometric coboundary, while forcing an
    # all-one prefix.  This deliberately changes the actual fine phase.
    separator: list[dict[str, object] | None] = [None] * (args.max_j + 1)
    separator_rows = 0
    separator_staircase_tower_checks = 0
    separator_prefix_checks = 0
    for j in range(2, args.max_j + 1):
        row = data[j]
        assert row is not None
        a = int(row["a"])
        if a < 5:
            continue
        D = int(row["D"])
        k = int(row["k"])
        p = int(row["p"])
        L = stable_leading_residue(j, k)
        if L % 3 == 0:
            raise AssertionError(("leading residue should be a unit", j, L))
        residue = (-pow(L, -1, p)) % p
        if residue % 3 == 0:
            raise AssertionError(("separator denominator residue", j, residue))
        sep_F = p * 10 ** (9 * j) + residue
        epsilon = Fraction(1, D * sep_F)
        point = Fraction(1, 9) - epsilon
        if point.denominator != D * sep_F:
            raise AssertionError(("separator reduced denominator", j))
        if valuation(point.denominator, 3) != a - 1:
            raise AssertionError(("separator complete three-primary part", j))
        for lower_k in range(1, k + 1):
            lower_p = 3**lower_k
            actual_lower = stable_leading_residue(j, lower_k)
            model_lower = local_fraction_mod(D * point, lower_p)
            if actual_lower != model_lower:
                raise AssertionError(
                    ("separator staircase tower", j, lower_k, actual_lower, model_lower)
                )
            separator_staircase_tower_checks += 1
        if not epsilon < RHO**j:
            raise AssertionError(("separator geometric size", j))
        if decimal_word(point, 2 * j) != "1" * (2 * j):
            raise AssertionError(("separator all-one prefix", j))
        separator_prefix_checks += 1
        separator_rows += 1
        separator[j] = {"epsilon": epsilon, "point": point}

    separator_recurrence_checks = 0
    separator_telescope_checks = 0
    for j in range(2, args.max_j):
        left = separator[j]
        right = separator[j + 1]
        if left is None or right is None:
            continue
        epsilon = left["epsilon"]
        next_epsilon = right["epsilon"]
        point = left["point"]
        next_point = right["point"]
        assert isinstance(epsilon, Fraction) and isinstance(next_epsilon, Fraction)
        assert isinstance(point, Fraction) and isinstance(next_point, Fraction)
        forcing = 10 * epsilon - next_epsilon
        if forcing <= 0 or next_point != fract(10 * point + forcing):
            raise AssertionError(("separator recurrence", j))
        separator_recurrence_checks += 1

        maximum_steps = min(2 * j, args.max_j - j)
        for steps in range(maximum_steps + 1):
            later = separator[j + steps]
            if later is None:
                break
            terminal_epsilon = later["epsilon"]
            assert isinstance(terminal_epsilon, Fraction)
            telescope = 10**steps * epsilon - terminal_epsilon
            if steps == 0:
                if telescope:
                    raise AssertionError(("separator zero telescope", j))
            elif not 0 < telescope < 10**steps * RHO**j:
                raise AssertionError(("separator telescope", j, steps))
            separator_telescope_checks += 1

    print("claim_status=experiment")
    print(f"source_sha256={digest}")
    print(f"j_range=2..{args.max_j}")
    print("selector_depth=k_j=floor(a_j/2)")
    print(f"balanced_stable_staircase_checks={stable_checks}")
    print(f"balanced_coarse_fine_selector_checks={selector_checks}")
    print(f"leading_fine_phase_recombination_checks={phase_recombination_checks}")
    print(f"selector_residual_integrality_checks={residual_integrality_checks}")
    print(f"selector_residual_inverse_three_checks={residual_depth_recurrence_checks}")
    print(f"nested_grid_phase_cube_root_checks={nested_phase_root_checks}")
    print(f"actual_selected_grid_membership_checks={actual_membership_checks}")
    print(f"ternary_grid_partition_checks={grid_partition_checks}")
    print(f"cross_index_balanced_phase_checks={cross_index_checks}")
    print(f"ordinary_or_selector_absorbed_geometry_steps={ordinary_geometry_steps}")
    print(f"tripled_geometry_steps={tripled_geometry_steps}")
    print(f"selector_absorbed_tripling_thresholds={selector_absorbed_thresholds}")
    for length in (1, 2):
        print(f"word_length_{length}_parent_prefix_checks={prefix_checks[length]}")
        print(
            f"word_length_{length}_selected_child_above_parent_average="
            f"{average_contraction_violations[length]}"
        )
        print(
            f"word_length_{length}_selected_child_full_concentrations="
            f"{full_concentrations[length]}"
        )
        print(
            f"word_length_{length}_selected_child_singleton_concentrations="
            f"{singleton_concentrations[length]}"
        )
        print(
            f"word_length_{length}_first_full_concentrations="
            f"{first_full_concentrations[length]}"
        )
        print(
            f"word_length_{length}_first_cross_j_resurrections="
            f"{first_selected_resurrections[length]}"
        )
        print(
            f"word_length_{length}_last_survival_in_range="
            f"{last_survival[length]}"
        )
        largest = largest_occupancy_over_zero[length]
        assert largest is not None
        ratio, j, word, E, count, zero_mode = largest
        print(
            f"word_length_{length}_largest_occupancy_over_zero_mode="
            f"j:{j},word:{word},grid_size:{E},N:{count},"
            f"zero_mode:{decimal(zero_mode)},ratio:{decimal(ratio)}"
        )
    print(f"separator_rows={separator_rows}")
    print(f"separator_actual_staircase_tower_checks={separator_staircase_tower_checks}")
    print(f"separator_all_one_prefix_checks={separator_prefix_checks}")
    print(f"separator_positive_recurrence_checks={separator_recurrence_checks}")
    print(f"separator_geometric_telescope_checks={separator_telescope_checks}")
    print("all exact checks passed")


if __name__ == "__main__":
    main()
