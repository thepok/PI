#!/usr/bin/env python3
"""Independent exact replay for the BBP scalar p-adic/Archimedean separator.

This checker deliberately imports no primary checker.  Every finite loop is
an experiment; the companion independent audit supplies the all-index
arguments and keeps canonical V1 at status ``conjecture``.
"""

from __future__ import annotations

import argparse
import hashlib
import math
from fractions import Fraction
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
REPORT = ROOT / "work/ultrapi-resume/bbp_scalar_padic_archimedean_separator_20260813.md"
PRIMARY_CHECKER = ROOT / "work/ultrapi-resume/bbp_scalar_padic_archimedean_separator_20260813_check.py"

PINNED = {
    "problems/local/pi-digits.txt":
        "2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825",
    "work/ultrapi-resume/bbp_scalar_padic_archimedean_separator_20260813.md":
        "ce581bf5bb9c1b95d2405c27839bd6e894e90dda8d0a8c1808e1b722e059a357",
    "work/ultrapi-resume/bbp_scalar_padic_archimedean_separator_20260813_check.py":
        "5c75450eda7f1998136a7e7583bb5c8925a791dfd8d1af4f76a57f94ec323350",
    "work/ultrapi-resume/bbp_character_breakthrough_attack_20260813.md":
        "5a0e3027eb2b6c38b48e2b3ae075b4175b586bbd54ec1de68e6621cb0e03c264",
    "work/ultrapi-resume/bbp_character_breakthrough_independent_audit_20260813.md":
        "c3d6f382972886e8c27d65159cc164ec55651ff353ac44f3300438033892304f",
    "work/ultrapi-resume/bbp_short_orbit_return_attack.md":
        "eed140ef58160c09ae65b2596105882ff7614440b36ce45a9c94185bcf881e7d",
    "work/ultrapi-resume/bbp_short_orbit_return_independent_audit.md":
        "49909a445f8748c4e3614537195072c94409c92e21100d2bf4593c4c8b4963f2",
    "work/ultrapi-resume/bbp_actual_odd_quotient_attack.md":
        "d77e96b5bdce3bfd8278fa3b650d7a95d16bc86738c2af95a2d740919470c9fc",
    "work/ultrapi-resume/bbp_actual_odd_quotient_independent_audit.md":
        "85f8e941bdb1d974d192e4f99f0aa1b10ea230b0b67c7a7fb5a067e1551f7c36",
    "work/ultrapi-resume/bbp_all_depth_two_adic_attack.md":
        "9c1282724c7999fd67133a3f0e756015e564dc6b7a2a1ec44f2efe892b2653d9",
    "work/ultrapi-resume/bbp_all_depth_two_adic_independent_audit.md":
        "846268c0b45dd82b96c6112054e344669eca62fe9a4308a56e6026f131a25007",
    "work/theory/pi-digits/library/t6/bbp-1997-nasa.pdf":
        "e4e0b97fde01328ec41da5f2cd4d6ffc8bcd2b7bd7516b9d8afc320f6d1916c4",
    "work/theory/pi-lacunary-near-return-sparsity/library/t63/lagarias-math0101055v2.pdf":
        "a2a1171eb9c75c9fa3495ca3c3ceaa33c1d20b722bb56f82adb56d8c308209b9",
    "work/theory/pi-lacunary-near-return-sparsity/library/t63/bailey-crandall-2001-bcrandom.pdf":
        "701067697e8c1dace60cd8695ef509edae31f9da3bffd64b548624ccc2e4cfa8",
}

RHO = Fraction(5, 8)
SIGMA = Fraction(1, 16)
H0 = Fraction(20048317, 16336320)
H1 = Fraction(258249, 17353600)


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1 << 20), b""):
            digest.update(chunk)
    return digest.hexdigest()


def v2_int(value: int) -> int:
    require(value != 0, "v2(0) is undefined here")
    value = abs(value)
    return (value & -value).bit_length() - 1


def v2_rat(value: Fraction) -> int:
    require(value != 0, "v2(0) is undefined here")
    return v2_int(value.numerator) - v2_int(value.denominator)


def circle_distance(value: Fraction) -> Fraction:
    residue = value.numerator % value.denominator
    return Fraction(min(residue, value.denominator - residue), value.denominator)


def pole_denominator(index: int) -> int:
    return (
        (2 * index + 1)
        * (4 * index + 3)
        * (8 * index + 1)
        * (8 * index + 5)
    )


def a(index: int) -> Fraction:
    return Fraction(
        120 * index * index + 151 * index + 47,
        pole_denominator(index),
    )


def b(index: int) -> Fraction:
    return a(index) / 16**index


def q(index: int) -> int:
    return 10**index - 16


def explicit_g(index: int) -> Fraction:
    return Fraction(
        15 * (index + 1) * (8 * index - 15),
        pole_denominator(index),
    )


def actual_h(index: int) -> Fraction:
    return q(index + 2) * b(index + 2) + (160 - 10 ** (index + 1)) * b(index + 1)


def epsilon_formula(index: int) -> Fraction:
    require(index >= 3, "the explicit proxy begins at depth three")
    return (RHO**index - 16 * SIGMA**index) * explicit_g(index) / 15


EPSILON_0 = Fraction(1, 3)
EPSILON_3 = epsilon_formula(3)
EPSILON_1 = (
    EPSILON_3 + H1 + 11 * (10 * EPSILON_0 + H0)
) / 111
EPSILON_2 = 11 * EPSILON_1 - 10 * EPSILON_0 - H0


def epsilon(index: int) -> Fraction:
    if index == 0:
        return EPSILON_0
    if index == 1:
        return EPSILON_1
    if index == 2:
        return EPSILON_2
    return epsilon_formula(index)


def shadow_phase(index: int) -> Fraction:
    return Fraction(q(index), 9) - epsilon(index)


def phase_forcing(values: list[Fraction], index: int) -> Fraction:
    return values[index + 2] - 11 * values[index + 1] + 10 * values[index]


def shadow_h(index: int) -> Fraction:
    return 11 * epsilon(index + 1) - 10 * epsilon(index) - epsilon(index + 2)


def poly_add(left: list[int], right: list[int]) -> list[int]:
    size = max(len(left), len(right))
    result = [0] * size
    for index in range(size):
        result[index] = (
            (left[index] if index < len(left) else 0)
            + (right[index] if index < len(right) else 0)
        )
    while len(result) > 1 and result[-1] == 0:
        result.pop()
    return result


def poly_scale(polynomial: list[int], scalar: int) -> list[int]:
    return [scalar * coefficient for coefficient in polynomial]


def poly_multiply(left: list[int], right: list[int]) -> list[int]:
    result = [0] * (len(left) + len(right) - 1)
    for i, x in enumerate(left):
        for j, y in enumerate(right):
            result[i + j] += x * y
    return result


def poly_shift(polynomial: list[int], shift: int) -> list[int]:
    """Ascending coefficients of p(n + shift)."""
    result = [0]
    for degree, coefficient in enumerate(polynomial):
        term = [
            coefficient * math.comb(degree, power) * shift ** (degree - power)
            for power in range(degree + 1)
        ]
        result = poly_add(result, term)
    return result


def denominator_polynomial() -> list[int]:
    result = [1]
    for factor in ([1, 2], [3, 4], [1, 8], [5, 8]):
        result = poly_multiply(result, list(factor))
    return result


def series_division(
    numerator: list[Fraction], denominator: list[Fraction], order: int
) -> list[Fraction]:
    require(denominator[0] != 0, "series denominator must be a unit")
    result = [Fraction(0) for _ in range(order)]
    for degree in range(order):
        value = numerator[degree] if degree < len(numerator) else Fraction(0)
        for prior in range(degree):
            remaining = degree - prior
            if remaining < len(denominator):
                value -= result[prior] * denominator[remaining]
        result[degree] = value / denominator[0]
    return result


def infinity_coefficients(
    numerator_ascending: list[int], denominator_ascending: list[int], order: int
) -> list[Fraction]:
    numerator_degree = len(numerator_ascending) - 1
    denominator_degree = len(denominator_ascending) - 1
    shift = denominator_degree - numerator_degree
    quotient = series_division(
        [Fraction(value) for value in reversed(numerator_ascending)],
        [Fraction(value) for value in reversed(denominator_ascending)],
        order,
    )
    result = [Fraction(0) for _ in range(order)]
    for degree, coefficient in enumerate(quotient):
        if degree + shift < order:
            result[degree + shift] = coefficient
    return result


def stirling_second(kind: int, parts: int) -> int:
    table = [[0] * (kind + 1) for _ in range(kind + 1)]
    table[0][0] = 1
    for n in range(1, kind + 1):
        for k in range(1, n + 1):
            table[n][k] = table[n - 1][k - 1] + k * table[n - 1][k]
    return table[kind][parts]


def geometric_moment(power: int) -> Fraction:
    """Return exactly 15 sum_{j >= 1} j^power / 16^j."""
    x = Fraction(1, 16)
    if power == 0:
        return 15 * x / (1 - x)
    total = Fraction(0)
    for falling_degree in range(1, power + 1):
        total += (
            stirling_second(power, falling_degree)
            * math.factorial(falling_degree)
            * x**falling_degree
            / (1 - x) ** (falling_degree + 1)
        )
    return 15 * total


def tail_coordinate_coefficients(order: int) -> list[Fraction]:
    """Laurent coefficients of G_n through n^{-(order-1)}."""
    denominator = denominator_polynomial()
    a_coefficients = infinity_coefficients([47, 151, 120], denominator, order)
    result = [Fraction(0) for _ in range(order)]
    for target_degree in range(2, order):
        coefficient = Fraction(0)
        for source_degree in range(2, target_degree + 1):
            moment_degree = target_degree - source_degree
            coefficient += (
                a_coefficients[source_degree]
                * (-1) ** moment_degree
                * math.comb(target_degree - 1, source_degree - 1)
                * geometric_moment(moment_degree)
            )
        result[target_degree] = coefficient
    return result


def laurent_proxy(index: int, jet_order: int, coefficients: list[Fraction]) -> Fraction:
    require(index >= 1 and jet_order >= 2, "valid Laurent proxy parameters")
    return sum(
        (coefficients[degree] / index**degree for degree in range(2, jet_order + 1)),
        Fraction(0),
    )


def scale_forcing_coefficients(
    coordinate: list[Fraction], jet_order: int, scale: Fraction, amplitude: Fraction
) -> list[Fraction]:
    """Coefficients of L(amplitude * scale^n * G_n) through a fixed jet."""
    result = [Fraction(0) for _ in range(jet_order + 1)]
    for target_degree in range(2, jet_order + 1):
        value = Fraction(0)
        for source_degree in range(2, target_degree + 1):
            expansion_degree = target_degree - source_degree
            binomial = (-1) ** expansion_degree * math.comb(
                target_degree - 1, source_degree - 1
            )
            shifted = (
                11 * scale * 1**expansion_degree
                - (scale**2) * 2**expansion_degree
            )
            if expansion_degree == 0:
                shifted -= 10
            value += coordinate[source_degree] * binomial * shifted
        result[target_degree] = amplitude * value
    return result


def nearest_integer(value: Fraction) -> int:
    floor = value.numerator // value.denominator
    return floor if value - floor <= Fraction(1, 2) else floor + 1


def prime_factors(value: int) -> set[int]:
    factors: set[int] = set()
    candidate = 2
    while candidate * candidate <= value:
        if value % candidate == 0:
            factors.add(candidate)
            while value % candidate == 0:
                value //= candidate
        candidate = 3 if candidate == 2 else candidate + 2
    if value > 1:
        factors.add(value)
    return factors


def independent_lift(actual: Fraction, target: Fraction, index: int) -> tuple[Fraction, int, int]:
    """Lift by changing the reduced numerator directly, not via the primary split."""
    exponent = v2_int(actual.denominator)
    require(exponent == 4 * index - v2_int(index + 1), "actual dyadic exponent")
    odd_denominator = actual.denominator >> exponent
    require(math.gcd(actual.numerator, 2 * odd_denominator) == 1, "actual reduced data")

    target_t = odd_denominator * (target - actual) / 16
    center = nearest_integer(target_t)
    step = 1 << (exponent + 4)
    chosen: int | None = None
    chosen_offset = 0
    for offset in range(100_001):
        candidates = [center] if offset == 0 else [center + offset, center - offset]
        for candidate in candidates:
            if math.gcd(actual.numerator + step * candidate, odd_denominator) == 1:
                chosen = candidate
                chosen_offset = candidate - center
                break
        if chosen is not None:
            break
    require(chosen is not None, "finite Kanold-style lift search")

    new_numerator = actual.numerator + step * chosen
    lifted = Fraction(new_numerator, actual.denominator)
    require(lifted.denominator == actual.denominator, "complete reduced denominator")
    require(lifted - actual == Fraction(16 * chosen, odd_denominator), "lift scaling")

    modulus = 1 << (exponent + 4)
    old_coordinate = actual.numerator * pow(odd_denominator, -1, modulus) % modulus
    new_coordinate = lifted.numerator * pow(odd_denominator, -1, modulus) % modulus
    require(old_coordinate == new_coordinate, "all derived two-adic bits")
    require(v2_rat(16**index * (lifted - actual)) >= 4 * (index + 1), "null congruence")
    return lifted, chosen_offset, len(prime_factors(odd_denominator))


def beta_for_jet(index: int, jet_order: int, coefficients: list[Fraction]) -> Fraction:
    proxy = laurent_proxy(index, jet_order, coefficients)
    bar_epsilon = (RHO**index - 16 * SIGMA**index) * proxy / 15
    return Fraction(1, 9) - bar_epsilon / q(index)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-depth", type=int, default=84)
    parser.add_argument("--lift-depth", type=int, default=58)
    parser.add_argument("--max-jet", type=int, default=8)
    args = parser.parse_args()
    require(args.max_depth >= 24, "max depth must be at least 24")
    require(16 <= args.lift_depth <= args.max_depth, "invalid lift depth")
    require(4 <= args.max_jet <= 12, "max jet must lie between 4 and 12")

    for relative, expected in PINNED.items():
        path = ROOT / relative
        require(path.is_file(), f"missing pinned artifact: {relative}")
        require(sha256(path) == expected, f"hash mismatch: {relative}")

    denominator = denominator_polynomial()
    a_coefficients = infinity_coefficients([47, 151, 120], denominator, args.max_jet + 3)
    g_coefficients = infinity_coefficients([-225, -105, 120], denominator, args.max_jet + 3)
    coordinate = tail_coordinate_coefficients(args.max_jet + 3)
    require(a_coefficients[2:4] == [Fraction(15, 64), Fraction(-89, 512)], "a Laurent jet")
    require(coordinate[2:4] == [Fraction(15, 64), Fraction(-345, 512)], "G Laurent jet")
    require(g_coefficients[2:4] == coordinate[2:4], "explicit proxy Laurent jet")
    require(geometric_moment(0) == 1, "geometric mass")
    require(geometric_moment(1) == Fraction(16, 15), "geometric first moment")

    # Derive the monotonicity polynomial and its positive shift exactly.
    g_numerator = [-225, -105, 120]
    d_shift = poly_shift(denominator, 1)
    g_shift = poly_shift(g_numerator, 1)
    difference_numerator = poly_add(
        poly_multiply(g_numerator, d_shift),
        poly_scale(poly_multiply(g_shift, denominator), -1),
    )
    require(all(value % 15 == 0 for value in difference_numerator), "factor 15")
    difference_quotient = [value // 15 for value in difference_numerator]
    require(
        difference_quotient
        == [-36645, -115688, -122248, -33792, 17920, 8192],
        "monotonicity numerator",
    )
    require(
        poly_shift(difference_quotient, 3)
        == [1045851, 3491560, 2753144, 918528, 140800, 8192],
        "positive shifted monotonicity polynomial",
    )
    proxy_bound_numerator = poly_add(
        denominator,
        poly_scale([0, 0, -225, -105, 120], -1),
    )
    require(
        proxy_bound_numerator == [15, 194, 937, 1129, 392],
        "all-positive proof of g(n) < n^-2",
    )
    a_numerator = [47, 151, 120]
    a_shift = poly_shift(a_numerator, 1)
    a_difference = poly_add(
        poly_multiply(a_numerator, d_shift),
        poly_scale(poly_multiply(a_shift, denominator), -1),
    )
    require(all(value % 3 == 0 for value in a_difference), "a difference factor 3")
    require(
        [value // 3 for value in a_difference]
        == [36903, 206712, 443480, 453632, 220672, 40960],
        "positive coefficient monotonicity for a",
    )

    require(actual_h(0) == H0 and actual_h(1) == H1, "actual endpoint forcing")
    require(EPSILON_1 == Fraction(3095504003, 6847215375), "epsilon one")
    require(EPSILON_2 == Fraction(25814204941, 62603112000), "epsilon two")
    require(shadow_phase(0) == -2, "integral anchor")
    require(shadow_h(0) == H0 and shadow_h(1) == H1, "endpoint forcing")
    require(shadow_h(2) == Fraction(-411876045113669, 99914566752000), "splice sign")
    for index in (1, 2):
        delta = epsilon(index) - Fraction(1, 3)
        require(Fraction(1, 16) < delta < Fraction(1, 2), "exceptional gap")

    rho_forcing = scale_forcing_coefficients(
        coordinate, args.max_jet, RHO, Fraction(1, 15)
    )
    sigma_forcing = scale_forcing_coefficients(
        coordinate, args.max_jet, SIGMA, Fraction(-16, 15)
    )
    require(rho_forcing[2] == Fraction(-225, 4096), "rho leading forcing")
    require(sigma_forcing[2] == Fraction(2385, 1024), "sigma leading forcing")

    partial = Fraction(0)
    actual_partials: list[Fraction] = []
    for index in range(args.max_depth + 3):
        partial += b(index)
        actual_partials.append(partial)
    exact_scalar_checks = 0
    valuation_checks = 0
    gap_checks = 0
    for index in range(args.max_depth + 1):
        if index >= 1:
            require(circle_distance(shadow_phase(index)) > Fraction(1, 16), "uniform shadow gap")
            gap_checks += 1
        if index >= 3:
            require(explicit_g(index) > 0, "positive explicit proxy")
            require(explicit_g(index) < Fraction(1, index * index), "explicit proxy upper bound")
            require(explicit_g(index + 1) < explicit_g(index), "explicit proxy decreases")
            require(epsilon(index + 1) / epsilon(index) < Fraction(10, 11), "epsilon ratio")
            require(shadow_h(index) < 0, "negative shadow forcing")
            actual_phase = q(index) * actual_partials[index]
            require(v2_rat(shadow_phase(index)) == v2_rat(actual_phase), "phase v2 equality")
            require(
                v2_rat(shadow_phase(index))
                == v2_int(q(index)) + v2_int(index + 1) - 4 * index,
                "closed phase v2 formula",
            )
            valuation_checks += 2
        if index >= 2:
            require(actual_h(index) < 0, "actual negative forcing")
        if index + 2 <= args.max_depth + 2:
            values = [shadow_phase(index + offset) for offset in range(3)]
            require(phase_forcing(values, 0) == shadow_h(index), "shadow recurrence")
            actual_values = [
                q(index + offset) * actual_partials[index + offset]
                for offset in range(3)
            ]
            require(phase_forcing(actual_values, 0) == actual_h(index), "actual recurrence")
            exact_scalar_checks += 1

    # Representative arbitrary-jet lifts, using the varying beta_n target.
    lift_checks = 0
    maximum_offset = 0
    minimum_gap = Fraction(1, 2)
    maximum_kanold_ratio = Fraction(0)
    chosen_jet = args.max_jet
    lifted_phases: dict[int, Fraction] = {}
    for jet_order in range(2, args.max_jet + 1):
        for index in range(8, args.lift_depth + 1):
            actual = actual_partials[index]
            target = beta_for_jet(index, jet_order, coordinate)
            lifted, offset, omega = independent_lift(actual, target, index)
            phase = q(index) * lifted
            target_phase = q(index) * target
            require(
                abs(phase - target_phase)
                <= abs(q(index)) * Fraction(16 * (abs(offset) + 1), actual.denominator >> v2_int(actual.denominator)),
                "lift phase error scaling",
            )
            require(circle_distance(phase) > Fraction(1, 5), "finite lifted nonreturn")
            require(abs(offset) <= 2**omega, "finite Kanold bound replay")
            if omega:
                maximum_kanold_ratio = max(maximum_kanold_ratio, Fraction(abs(offset), 2**omega))
            maximum_offset = max(maximum_offset, abs(offset))
            minimum_gap = min(minimum_gap, circle_distance(phase))
            lift_checks += 5
            if jet_order == chosen_jet:
                lifted_phases[index] = phase

    # One concrete finite splice: endpoint forcing is exact, straddling rows
    # are deliberately ignored, and the sufficiently deep lifted forcing is
    # checked to have the eventual negative sign.
    splice_depth = 16
    spliced: list[Fraction] = []
    for index in range(args.lift_depth + 1):
        if index < splice_depth:
            spliced.append(shadow_phase(index))
        else:
            spliced.append(lifted_phases[index])
    require(spliced[0].denominator == 1, "spliced integral anchor")
    require(phase_forcing(spliced, 0) == H0, "spliced h0")
    require(phase_forcing(spliced, 1) == H1, "spliced h1")
    eventual_negative = 0
    for index in range(splice_depth, args.lift_depth - 1):
        require(phase_forcing(spliced, index) < 0, "eventual lifted sign")
        eventual_negative += 1

    scanned = 0
    for path in [Path(__file__)] + [ROOT / relative for relative in PINNED if relative.endswith((".md", ".py", ".txt"))]:
        require(path.is_file(), f"missing C0 target: {path}")
        bad = [byte for byte in path.read_bytes() if byte < 32 and byte not in (9, 10, 13)]
        require(not bad, f"C0 control byte in {path}")
        scanned += 1

    print("status: PASS")
    print("claim_label: experiment")
    print(f"pinned_artifacts: {len(PINNED)}")
    print(f"c0_scanned_text_artifacts: {scanned}")
    print(f"generic_tail_jet_orders_checked: 2..{args.max_jet}")
    print(f"tail_jet_coefficients_through_{args.max_jet}: " + ",".join(str(coordinate[i]) for i in range(2, args.max_jet + 1)))
    print(f"exact_scalar_checks: {exact_scalar_checks}")
    print(f"valuation_checks: {valuation_checks}")
    print(f"uniform_gap_checks: {gap_checks}")
    print(f"varying_target_full_denominator_lift_checks: {lift_checks}")
    print(f"maximum_lift_center_offset: {maximum_offset}")
    print(f"maximum_finite_offset_over_2powomega: {float(maximum_kanold_ratio):.12f}")
    print(f"minimum_finite_lifted_circle_gap: {float(minimum_gap):.12f}")
    print(f"finite_splice_eventual_negative_rows: {eventual_negative}")
    print("matched_actual_endpoint_forcing: h_0,h_1")
    print("uniform_unlifted_gap_lower_bound: 1/16")
    print("asserts_fixed_return: false")
    print("asserts_v1: false")
    print("all independent exact finite checks passed")


if __name__ == "__main__":
    main()
