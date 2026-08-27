#!/usr/bin/env python3
"""Independent exact verifier for the T53 resource-frontier certificate."""

from __future__ import annotations

import argparse
import hashlib
import json
import math
from fractions import Fraction
from pathlib import Path


def file_hash(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1 << 20), b""):
            digest.update(block)
    return digest.hexdigest()


def down(x: Fraction) -> int:
    return x.numerator // x.denominator


def up(x: Fraction) -> int:
    return -down(-x)


def add(x: tuple[Fraction, Fraction], y: tuple[Fraction, Fraction]) -> tuple[Fraction, Fraction]:
    return x[0] + y[0], x[1] + y[1]


def neg(x: tuple[Fraction, Fraction]) -> tuple[Fraction, Fraction]:
    return -x[1], -x[0]


def mul(x: tuple[Fraction, Fraction], y: tuple[Fraction, Fraction]) -> tuple[Fraction, Fraction]:
    values = tuple(a * b for a in x for b in y)
    return min(values), max(values)


def scale(x: tuple[Fraction, Fraction], c: int | Fraction) -> tuple[Fraction, Fraction]:
    return mul(x, (Fraction(c), Fraction(c)))


def atan_bracket(q: int, tolerance: Fraction) -> tuple[tuple[Fraction, Fraction], int]:
    partial = Fraction(0)
    n = 0
    while True:
        term = Fraction(1, (2 * n + 1) * q ** (2 * n + 1))
        partial = partial + term if n % 2 == 0 else partial - term
        following = n + 1
        next_term = Fraction(1, (2 * following + 1) * q ** (2 * following + 1))
        adjacent = partial + next_term if following % 2 == 0 else partial - next_term
        if next_term < tolerance:
            return (min(partial, adjacent), max(partial, adjacent)), n + 1
        n += 1


def machin_bracket(bits: int) -> tuple[tuple[Fraction, Fraction], tuple[int, int]]:
    tolerance = Fraction(1, 2**bits)
    a, na = atan_bracket(5, tolerance / 32)
    b, nb = atan_bracket(239, tolerance / 8)
    return add(scale(a, 16), scale(b, -4)), (na, nb)


def base_trig(angle: tuple[Fraction, Fraction], terms: int) -> tuple[tuple[Fraction, Fraction], tuple[Fraction, Fraction]]:
    assert 0 <= angle[0] <= angle[1] <= 2
    sine = (Fraction(0), Fraction(0))
    cosine = (Fraction(0), Fraction(0))
    even_power = (Fraction(1), Fraction(1))
    angle_squared = mul(angle, angle)
    for k in range(terms + 1):
        cosine_term = scale(even_power, Fraction(1, math.factorial(2 * k)))
        sine_term = scale(mul(even_power, angle), Fraction(1, math.factorial(2 * k + 1)))
        cosine = add(cosine, cosine_term if k % 2 == 0 else neg(cosine_term))
        sine = add(sine, sine_term if k % 2 == 0 else neg(sine_term))
        even_power = mul(even_power, angle_squared)
    cosine_error = angle[1] ** (2 * terms + 1) / math.factorial(2 * terms + 1)
    sine_error = angle[1] ** (2 * terms + 2) / math.factorial(2 * terms + 2)
    return (
        (sine[0] - sine_error, sine[1] + sine_error),
        (cosine[0] - cosine_error, cosine[1] + cosine_error),
    )


def center_trig(
    turn: Fraction, pi: tuple[Fraction, Fraction], terms: int
) -> tuple[tuple[Fraction, Fraction], tuple[Fraction, Fraction]]:
    quadrant = down(4 * turn)
    remainder = turn - Fraction(quadrant, 4)
    sine, cosine = base_trig(scale(pi, 2 * remainder), terms)
    if quadrant == 0:
        return sine, cosine
    if quadrant == 1:
        return cosine, neg(sine)
    if quadrant == 2:
        return neg(sine), neg(cosine)
    return neg(cosine), sine


def independent_cells(config: dict) -> tuple[list[tuple[int, int]], list[tuple[int, int]], dict]:
    cert = config["certification"]
    pi, counts = machin_bracket(cert["trig_pi_target_bits"])
    assert 2 * pi[1] < 7
    expected_pi = {
        "method": "Machin_pi_equals_16_atan_1_over_5_minus_4_atan_1_over_239",
        "target_bits": cert["trig_pi_target_bits"],
        "atan_1_over_5_terms": counts[0],
        "atan_1_over_239_terms": counts[1],
        "endpoint_rationals": {
            "lo": [pi[0].numerator, pi[0].denominator],
            "hi": [pi[1].numerator, pi[1].denominator],
        },
    }
    bins = cert["turn_grid_bins"]
    fixed = cert["fixed_point_scale"]
    radius = Fraction(cert["derivative_upper_bound"], 2 * bins)
    sine_cells = []
    cosine_cells = []
    for index in range(bins):
        sine, cosine = center_trig(
            Fraction(2 * index + 1, 2 * bins), pi, cert["trig_taylor_terms"]
        )
        sine_cells.append((down((sine[0] - radius) * fixed), up((sine[1] + radius) * fixed)))
        cosine_cells.append((down((cosine[0] - radius) * fixed), up((cosine[1] + radius) * fixed)))
    return sine_cells, cosine_cells, expected_pi


def cells_for_phase(remainder: int, width: int, modulus: int, bins: int) -> list[int]:
    assert 0 <= remainder < modulus and 0 <= width < modulus
    endpoint = remainder + width
    first = remainder * bins // modulus
    if endpoint < modulus:
        last = min(bins - 1, endpoint * bins // modulus)
        return list(range(first, last + 1))
    wrapped_last = (endpoint - modulus) * bins // modulus
    return list(range(first, bins)) + list(range(min(bins - 1, wrapped_last) + 1))


def square_bounds(lo: int, hi: int) -> tuple[int, int]:
    if lo <= 0 <= hi:
        return 0, max(lo * lo, hi * hi)
    return min(lo * lo, hi * hi), max(lo * lo, hi * hi)


def coefficient(h: int, r: int) -> int:
    return h * (10**r - 1)


def assert_no_t50_recomputation(value: object) -> None:
    banned = {"apc_margin", "apc_status", "fsfs_margin", "fsfs_status", "primitive_classes", "controls"}
    if isinstance(value, dict):
        assert not (set(value) & banned)
        for child in value.values():
            assert_no_t50_recomputation(child)
    elif isinstance(value, list):
        for child in value:
            assert_no_t50_recomputation(child)


def verify(config_path: Path, output_path: Path, report_path: Path) -> None:
    root = config_path.parent
    config = json.loads(config_path.read_text(encoding="ascii"))
    output = json.loads(output_path.read_text(encoding="ascii"))
    report = report_path.read_text(encoding="ascii")
    assert config["format"] == "t53-resource-frontier-config-v1"
    for filename, expected in config["inputs"].items():
        assert file_hash(root / filename) == expected
    assert output["format"] == "t53-resource-frontier-output-v1"
    assert output["parameters"] == config
    assert output["input_hashes"] == config["inputs"]
    assert output["canonical_statement_sha256"] == config["inputs"]["canonical_statement.txt"]
    assert_no_t50_recomputation(output)

    t17 = json.loads((root / "T17_CERTIFICATE.json").read_text(encoding="ascii"))
    digits = (root / "pi_digits.txt").read_text(encoding="ascii")
    assert t17["decimal_prefix"]["file_sha256"] == file_hash(root / "pi_digits.txt")
    assert len(digits) == t17["decimal_prefix"]["file_bytes"]
    assert digits.endswith("\n") and digits[:-1].isdigit()
    prefix_length = config["certification"]["pi_decimal_prefix_digits_used"]
    prefix_bytes = ("3" + digits[:prefix_length]).encode("ascii")
    prefix_integer = int(prefix_bytes)
    modulus = 10**prefix_length
    pi_record = output["pi_certification"]
    assert pi_record["used_prefix_sha256"] == hashlib.sha256(prefix_bytes).hexdigest()
    assert pi_record["scaled_interval"] == {
        "scale_power": prefix_length,
        "lower_integer": str(prefix_integer),
        "upper_integer": str(prefix_integer + 1),
    }

    sine_cells, cosine_cells, expected_trig_pi = independent_cells(config)
    assert pi_record["trig_table_pi_certificate"] == expected_trig_pi
    search = config["search"]
    terminal_density = search["D"]
    for _ in range(search["depth"]):
        terminal_density = 8 * terminal_density * terminal_density
    request = 2 * terminal_density**2
    assert output["chain_length_decision"] == {
        "D": search["D"],
        "depth": search["depth"],
        "terminal_density_denominator": terminal_density,
        "chain_length_request": request,
        "K": search["K"],
        "chainLengthRequest_le_K": request <= search["K"],
    }

    min_M, max_M = search["M_inclusive"]
    min_r, max_r = search["r_inclusive"]
    min_h, max_h = search["h_inclusive"]
    min_shift, max_shift = search["shift_inclusive"]
    expected_tuples = []
    required = set()
    for M in range(min_M, max_M + 1):
        for r in range(min_r, max_r + 1):
            for h in range(min_h, max_h + 1):
                for shift in range(min_shift, max_shift + 1):
                    predicates = {
                        "chainLengthRequest_le_K": request <= search["K"],
                        "final_residual": search["K"] <= M - shift,
                        "length_eq_depth": search["depth"] == 1,
                        "nodup": True,
                        "shift_avoids_singleton_r": shift != r,
                        "shift_lower": search["B"] <= shift,
                    }
                    legal = all(predicates.values())
                    node_id = f"node0-M{M}-r{r}-h{h}" if legal else None
                    if legal:
                        required.add((M, r, h))
                    expected_tuples.append(
                        {
                            "id": f"pi-M{M}-D{search['D']}-r{r}-h{h}-s{shift}",
                            "M": M,
                            "D": search["D"],
                            "K": search["K"],
                            "r": r,
                            "h": h,
                            "shifts": [shift],
                            "chain_length_request": request,
                            "discrete_predicates": predicates,
                            "legal_for_resonance_test": legal,
                            "node0_decision_id": node_id,
                            "tested_nodes": [0] if legal else [],
                            "chain_status": (
                                "rejected_certified_node0_resonance" if legal else "rejected_discrete"
                            ),
                        }
                    )
    assert output["searched_tuples"] == expected_tuples

    records = output["certified_node_decisions"]
    assert len(records) == len(required)
    record_map = {(record["M"], record["r"], record["h"]): record for record in records}
    assert set(record_map) == required
    bins = config["certification"]["turn_grid_bins"]
    fixed = config["certification"]["fixed_point_scale"]
    fixed_sq = fixed * fixed
    checked_terms = 0
    for r in range(min_r, max_r + 1):
        for h in range(min_h, max_h + 1):
            q = coefficient(h, r)
            remainder = q * prefix_integer % modulus
            width = q
            real_lo = real_hi = imag_lo = imag_hi = 0
            for j in range(max_M):
                touched = cells_for_phase(remainder, width, modulus, bins)
                real_lo += min(cosine_cells[cell][0] for cell in touched)
                real_hi += max(cosine_cells[cell][1] for cell in touched)
                imag_lo += min(sine_cells[cell][0] for cell in touched)
                imag_hi += max(sine_cells[cell][1] for cell in touched)
                M = j + 1
                key = (M, r, h)
                if key in required:
                    record = record_map[key]
                    rsq = square_bounds(real_lo, real_hi)
                    isq = square_bounds(imag_lo, imag_hi)
                    norm_lo, norm_hi = rsq[0] + isq[0], rsq[1] + isq[1]
                    assert record == {
                        "id": f"node0-M{M}-r{r}-h{h}",
                        "M": M,
                        "r": r,
                        "h": h,
                        "k": 0,
                        "residual": M,
                        "density_denominator": search["D"],
                        "coefficient_multiplier_of_pi": q,
                        "phase_terms": M,
                        "real_sum_fixed_interval": [real_lo, real_hi, fixed],
                        "imag_sum_fixed_interval": [imag_lo, imag_hi, fixed],
                        "norm_squared_interval": {
                            "lo": [norm_lo, fixed_sq],
                            "hi": [norm_hi, fixed_sq],
                        },
                        "strict_resonance_threshold_squared": [M * M, search["D"] ** 2],
                        "strict_resonance_status": "false",
                        "certified_inequality": "norm_squared_upper_le_threshold_squared",
                    }
                    assert norm_hi * search["D"] ** 2 <= M * M * fixed_sq
                    checked_terms += M
                remainder = 10 * remainder % modulus
                width *= 10

    expected_targets = [
        "1_left_period_positive",
        "2_left_index_range",
        "3_right_period_positive",
        "4_right_index_range",
        "5_left_signed_error_bound",
        "6_right_signed_error_bound",
        "7_mixed_error_budget",
        "denominator_formulas_and_positivity",
        "coefficient_transport_Q0_a1_eq_U_Q1_a0",
        "literal_T28_compatibility",
    ]
    zero = {"false_negative": 0, "false_positive": 0, "true_negative": 0, "true_positive": 0}
    transitions = output["reduced_rational_transition_statistics"]
    assert transitions["eligible_adjacent_witness_pairs"] == 0
    assert transitions["records"] == []
    assert transitions["confusion_by_target"] == {target: zero for target in expected_targets}
    assert not transitions["coefficient_transport_is_literal_T28_conjunct"]
    assert output["genuine_chains"] == []
    assert output["t24_complete_witness_sets"] == []
    assert output["literal_t28_decisions"] == []
    assert output["resource_frontier"] == {
        "label": "RESOURCE FRONTIER",
        "exhausted": True,
        "bounds": {
            key: search[key]
            for key in ("M_inclusive", "r_inclusive", "h_inclusive", "shift_inclusive")
        },
        "first_unavailable_stage": "T24 complete witness enumeration",
        "reason": "every legal tuple fails certified node-0 T26 strict resonance",
    }
    legal_count = sum(item["legal_for_resonance_test"] for item in expected_tuples)
    assert output["summary"] == {
        "declared_tuple_count": len(expected_tuples),
        "legal_tuple_count": legal_count,
        "distinct_certified_node0_decision_count": len(required),
        "certified_node0_false_count": len(required),
        "genuine_chain_count": 0,
        "t24_node_count": 0,
        "t24_witness_count": 0,
        "literal_t28_decision_count": 0,
        "transition_pair_count": 0,
        "unresolved_decision_count": 0,
        "new_T50_APC_FSFS_or_control_computation": False,
    }
    assert output["claims"] == {
        "evidence_label": "experiment",
        "finite_heuristic_only": True,
        "proves_compatibility": False,
        "proves_C1": False,
        "proves_canonical_A1": False,
        "exhaustion_applies_only_to_declared_range": True,
    }
    for marker in (
        "finite heuristic evidence only",
        "All 65536 Cartesian tuples are recorded",
        "All 40320 legal tuples fail certified T26 node-0 resonance",
        "`RESOURCE FRONTIER`",
        "not an eighth literal conjunct",
        "Run `bash reproduce.sh`",
        "neither\nC1 nor canonical A1",
    ):
        assert marker in report
    print(
        "T53 verification passed: "
        f"{len(expected_tuples)} tuples, {legal_count} legal tuples, "
        f"{len(required)} certified node decisions, {checked_terms} reconstructed phase terms, "
        "and exact empty T24/T28/transition stages."
    )


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--config", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--report", type=Path, required=True)
    args = parser.parse_args()
    verify(args.config, args.output, args.report)


if __name__ == "__main__":
    main()
