#!/usr/bin/env python3
"""Certified bounded T53 fixed-pi T26 resource-frontier search."""

from __future__ import annotations

import argparse
import hashlib
import json
import math
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path


@dataclass(frozen=True)
class Interval:
    lo: Fraction
    hi: Fraction

    def __post_init__(self) -> None:
        if self.lo > self.hi:
            raise ValueError("reversed interval")

    @staticmethod
    def point(value: int | Fraction) -> "Interval":
        x = Fraction(value)
        return Interval(x, x)

    def __add__(self, other: "Interval") -> "Interval":
        return Interval(self.lo + other.lo, self.hi + other.hi)

    def __neg__(self) -> "Interval":
        return Interval(-self.hi, -self.lo)

    def __sub__(self, other: "Interval") -> "Interval":
        return self + (-other)

    def __mul__(self, other: "Interval") -> "Interval":
        products = (
            self.lo * other.lo,
            self.lo * other.hi,
            self.hi * other.lo,
            self.hi * other.hi,
        )
        return Interval(min(products), max(products))

    def scale(self, value: int | Fraction) -> "Interval":
        return self * Interval.point(value)


ZERO = Interval.point(0)
ONE = Interval.point(1)


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1 << 20), b""):
            digest.update(block)
    return digest.hexdigest()


def floor_fraction(x: Fraction) -> int:
    return x.numerator // x.denominator


def ceil_fraction(x: Fraction) -> int:
    return -floor_fraction(-x)


def fraction_pair(x: Fraction) -> list[int]:
    return [x.numerator, x.denominator]


def atan_reciprocal_interval(q: int, target: Fraction) -> tuple[Interval, int]:
    total = Fraction(0)
    k = 0
    while True:
        term = Fraction(1, (2 * k + 1) * q ** (2 * k + 1))
        total += term if k % 2 == 0 else -term
        next_k = k + 1
        next_term = Fraction(1, (2 * next_k + 1) * q ** (2 * next_k + 1))
        adjacent = total + (next_term if next_k % 2 == 0 else -next_term)
        if next_term < target:
            return Interval(min(total, adjacent), max(total, adjacent)), k + 1
        k += 1


def certify_pi(bits: int) -> tuple[Interval, dict]:
    target = Fraction(1, 2**bits)
    atan5, terms5 = atan_reciprocal_interval(5, target / 32)
    atan239, terms239 = atan_reciprocal_interval(239, target / 8)
    pi = atan5.scale(16) - atan239.scale(4)
    return pi, {
        "method": "Machin_pi_equals_16_atan_1_over_5_minus_4_atan_1_over_239",
        "target_bits": bits,
        "atan_1_over_5_terms": terms5,
        "atan_1_over_239_terms": terms239,
        "endpoint_rationals": {
            "lo": fraction_pair(pi.lo),
            "hi": fraction_pair(pi.hi),
        },
    }


def base_sin_cos(y: Interval, terms: int) -> tuple[Interval, Interval]:
    if y.lo < 0 or y.hi > 2:
        raise ValueError("base angle outside certified range")
    cosine = ZERO
    sine = ZERO
    power = ONE
    y_squared = y * y
    for k in range(terms + 1):
        cosine_term = power.scale(Fraction(1, math.factorial(2 * k)))
        sine_term = (power * y).scale(Fraction(1, math.factorial(2 * k + 1)))
        cosine = cosine + (cosine_term if k % 2 == 0 else -cosine_term)
        sine = sine + (sine_term if k % 2 == 0 else -sine_term)
        power = power * y_squared
    cosine_remainder = y.hi ** (2 * terms + 1) / math.factorial(2 * terms + 1)
    sine_remainder = y.hi ** (2 * terms + 2) / math.factorial(2 * terms + 2)
    return (
        Interval(sine.lo - sine_remainder, sine.hi + sine_remainder),
        Interval(cosine.lo - cosine_remainder, cosine.hi + cosine_remainder),
    )


def sin_cos_turn(turn: Fraction, pi: Interval, terms: int) -> tuple[Interval, Interval]:
    if not 0 <= turn < 1:
        raise ValueError("turn must lie in [0,1)")
    quadrant = floor_fraction(4 * turn)
    remainder = turn - Fraction(quadrant, 4)
    sine, cosine = base_sin_cos(pi.scale(2 * remainder), terms)
    if quadrant == 0:
        return sine, cosine
    if quadrant == 1:
        return cosine, -sine
    if quadrant == 2:
        return -sine, -cosine
    return -cosine, sine


def build_cell_table(config: dict, pi: Interval) -> tuple[list[tuple[int, int]], list[tuple[int, int]]]:
    cert = config["certification"]
    if 2 * pi.hi >= cert["derivative_upper_bound"]:
        raise ArithmeticError("configured trigonometric derivative bound is not certified")
    bins = cert["turn_grid_bins"]
    scale = cert["fixed_point_scale"]
    derivative_bound = cert["derivative_upper_bound"]
    radius = Fraction(derivative_bound, 2 * bins)
    sine_cells = []
    cosine_cells = []
    for cell in range(bins):
        center = Fraction(2 * cell + 1, 2 * bins)
        sine, cosine = sin_cos_turn(center, pi, cert["trig_taylor_terms"])
        for value, target in ((sine, sine_cells), (cosine, cosine_cells)):
            target.append(
                (
                    floor_fraction((value.lo - radius) * scale),
                    ceil_fraction((value.hi + radius) * scale),
                )
            )
    return sine_cells, cosine_cells


def touched_cells(remainder: int, width: int, denominator: int, bins: int) -> list[int]:
    if not 0 <= remainder < denominator or not 0 <= width < denominator:
        raise ValueError("phase enclosure is too wide")
    end = remainder + width
    first = (remainder * bins) // denominator
    if end < denominator:
        last = min(bins - 1, (end * bins) // denominator)
        return list(range(first, last + 1))
    last = ((end - denominator) * bins) // denominator
    return list(range(first, bins)) + list(range(0, min(bins - 1, last) + 1))


def square_interval_fixed(lo: int, hi: int) -> tuple[int, int]:
    if lo <= 0 <= hi:
        return 0, max(lo * lo, hi * hi)
    values = (lo * lo, hi * hi)
    return min(values), max(values)


def density_denominator(D: int, depth: int) -> int:
    value = D
    for _ in range(depth):
        value = 8 * value * value
    return value


def coefficient_multiplier(h: int, r: int) -> int:
    return h * (10**r - 1)


def decision_id(M: int, r: int, h: int) -> str:
    return f"node0-M{M}-r{r}-h{h}"


def certify_node_zero_family(
    config: dict,
    decimal_prefix_integer: int,
    decimal_scale: int,
    sine_cells: list[tuple[int, int]],
    cosine_cells: list[tuple[int, int]],
    required: set[tuple[int, int, int]],
) -> list[dict]:
    search = config["search"]
    cert = config["certification"]
    min_M, max_M = search["M_inclusive"]
    min_r, max_r = search["r_inclusive"]
    min_h, max_h = search["h_inclusive"]
    bins = cert["turn_grid_bins"]
    fixed_scale = cert["fixed_point_scale"]
    fixed_square = fixed_scale * fixed_scale
    decisions = []
    for r in range(min_r, max_r + 1):
        for h in range(min_h, max_h + 1):
            q = coefficient_multiplier(h, r)
            remainder = (q * decimal_prefix_integer) % decimal_scale
            width = q
            real_lo = real_hi = imag_lo = imag_hi = 0
            by_M = {}
            for j in range(max_M):
                cells = touched_cells(remainder, width, decimal_scale, bins)
                sin_lo = min(sine_cells[cell][0] for cell in cells)
                sin_hi = max(sine_cells[cell][1] for cell in cells)
                cos_lo = min(cosine_cells[cell][0] for cell in cells)
                cos_hi = max(cosine_cells[cell][1] for cell in cells)
                real_lo += cos_lo
                real_hi += cos_hi
                imag_lo += sin_lo
                imag_hi += sin_hi
                M = j + 1
                if min_M <= M <= max_M and (M, r, h) in required:
                    real_sq = square_interval_fixed(real_lo, real_hi)
                    imag_sq = square_interval_fixed(imag_lo, imag_hi)
                    norm_lo = real_sq[0] + imag_sq[0]
                    norm_hi = real_sq[1] + imag_sq[1]
                    threshold_num = M * M
                    threshold_den = search["D"] ** 2
                    false_certified = norm_hi * threshold_den <= threshold_num * fixed_square
                    true_certified = norm_lo * threshold_den > threshold_num * fixed_square
                    if not false_certified and not true_certified:
                        raise ArithmeticError(f"unresolved node-0 resonance for {(M, r, h)}")
                    status = "false" if false_certified else "true"
                    by_M[M] = {
                        "id": decision_id(M, r, h),
                        "M": M,
                        "r": r,
                        "h": h,
                        "k": 0,
                        "residual": M,
                        "density_denominator": search["D"],
                        "coefficient_multiplier_of_pi": q,
                        "phase_terms": M,
                        "real_sum_fixed_interval": [real_lo, real_hi, fixed_scale],
                        "imag_sum_fixed_interval": [imag_lo, imag_hi, fixed_scale],
                        "norm_squared_interval": {
                            "lo": [norm_lo, fixed_square],
                            "hi": [norm_hi, fixed_square],
                        },
                        "strict_resonance_threshold_squared": [threshold_num, threshold_den],
                        "strict_resonance_status": status,
                        "certified_inequality": (
                            "norm_squared_upper_le_threshold_squared"
                            if status == "false"
                            else "threshold_squared_lt_norm_squared_lower"
                        ),
                    }
                remainder = (10 * remainder) % decimal_scale
                width *= 10
            decisions.extend(by_M[M] for M in sorted(by_M))
    decisions.sort(key=lambda item: (item["M"], item["r"], item["h"]))
    if len(decisions) != len(required):
        raise AssertionError("did not produce every required node-0 decision")
    return decisions


def empty_confusion() -> dict[str, int]:
    return {"false_negative": 0, "false_positive": 0, "true_negative": 0, "true_positive": 0}


def make_report(result: dict) -> str:
    summary = result["summary"]
    frontier = result["resource_frontier"]
    return "\n".join(
        [
            "# T53 certified fixed-pi T26 resource frontier",
            "",
            "Status: `experiment` (finite heuristic evidence only).",
            "",
            "## Scope",
            "",
            "This is a bounded A14 sibling, not canonical A1 or C1. The canonical",
            "statement is vendored byte-for-byte and hash-pinned. The search concerns",
            "structural fixed-pi `GeometricResonanceChain` tuples; it does not claim the",
            "failure-derived provenance of T26. T50 APC/FSFS tables and controls are not",
            "recomputed.",
            "",
            "## Exact range",
            "",
            f"- `D=2`, depth `1`, `K=2048`, `B=1`.",
            f"- `M={frontier['bounds']['M_inclusive']}`, `r={frontier['bounds']['r_inclusive']}`, `h={frontier['bounds']['h_inclusive']}`, `shift={frontier['bounds']['shift_inclusive']}`.",
            f"- All {summary['declared_tuple_count']} Cartesian tuples are recorded; {summary['legal_tuple_count']} satisfy every exact discrete chain predicate.",
            "- `densityDenominator(2,1)=32`, hence `chainLengthRequest(2,1)=2*32^2=2048<=K`.",
            "",
            "## Certification",
            "",
            "The fixed-pi phase enclosure uses the hash-pinned T17 certified decimal",
            "prefix. Trigonometric grid centers are enclosed using T50/T51's exact Machin",
            "pi interval and rational Taylor bounds. The derivative bound `2*pi<7`, grid",
            "cell radius, and outward fixed-point rounding enclose every phase term.",
            "Each legal tuple is rejected only after its node-0 norm-squared upper bound",
            "is at most the literal squared threshold `M^2/D^2`. Any unresolved strict",
            "comparison aborts without publishing a frontier.",
            "",
            "## Result",
            "",
            f"All {summary['legal_tuple_count']} legal tuples fail certified T26 node-0 resonance.",
            f"There are {summary['genuine_chain_count']} genuine chains, {summary['t24_node_count']} tested T24 nodes, and {summary['transition_pair_count']} adjacent witness pairs.",
            "Therefore the exact exhausted range is a `RESOURCE FRONTIER`, not a positive",
            "chain corpus. Complete T24 sets, literal T28 decisions, and reduced-rational",
            "transition statistics are empty because no tuple reaches those stages.",
            "Coefficient transport is an exact diagnostic consequence associated with",
            "T28 compatibility, not an eighth literal conjunct of `AdjacentPairCompatible`.",
            "",
            "## Replay",
            "",
            "Run `bash reproduce.sh` in a directory containing only these artifacts.",
            "It checks every pinned hash, regenerates byte-identical JSON and this report,",
            "and independently verifies tuple coverage, interval inequalities, short-circuit",
            "decisions, empty downstream statistics, and the frontier conclusion.",
            "Budget: 300 seconds and 2048 MiB; no network or third-party package is used.",
            "",
            "## Required limitation",
            "",
            "Every conclusion is finite heuristic evidence. The exhausted range proves",
            "neither compatibility nor incompatibility outside the listed tuples, neither",
            "C1 nor canonical A1, and no asymptotic property of pi.",
            "",
        ]
    )


def run(config_path: Path, output_path: Path, report_path: Path) -> None:
    root = config_path.parent
    config = json.loads(config_path.read_text(encoding="ascii"))
    for filename, expected in config["inputs"].items():
        actual = sha256(root / filename)
        if actual != expected:
            raise AssertionError(f"input hash mismatch for {filename}: {actual}")
    t17 = json.loads((root / "T17_CERTIFICATE.json").read_text(encoding="ascii"))
    if t17["decimal_prefix"]["file_sha256"] != config["inputs"]["pi_digits.txt"]:
        raise AssertionError("T17 certificate does not pin the supplied digit file")
    digits = (root / "pi_digits.txt").read_text(encoding="ascii")
    if not digits.endswith("\n") or not digits[:-1].isdigit():
        raise AssertionError("invalid T17 digit-file encoding")
    prefix_length = config["certification"]["pi_decimal_prefix_digits_used"]
    fractional_prefix = digits[:prefix_length]
    prefix_payload = ("3" + fractional_prefix).encode("ascii")
    decimal_prefix_integer = int(prefix_payload)
    decimal_scale = 10**prefix_length
    max_phase_width = coefficient_multiplier(
        config["search"]["h_inclusive"][1], config["search"]["r_inclusive"][1]
    ) * 10 ** (config["search"]["M_inclusive"][1] - 1)
    if max_phase_width >= decimal_scale:
        raise AssertionError("decimal pi enclosure is too short for the search")

    trig_pi, trig_pi_certificate = certify_pi(config["certification"]["trig_pi_target_bits"])
    sine_cells, cosine_cells = build_cell_table(config, trig_pi)

    search = config["search"]
    min_M, max_M = search["M_inclusive"]
    min_r, max_r = search["r_inclusive"]
    min_h, max_h = search["h_inclusive"]
    min_shift, max_shift = search["shift_inclusive"]
    terminal_density = density_denominator(search["D"], search["depth"])
    length_request = 2 * terminal_density**2
    tuples = []
    required_decisions: set[tuple[int, int, int]] = set()
    for M in range(min_M, max_M + 1):
        for r in range(min_r, max_r + 1):
            for h in range(min_h, max_h + 1):
                for shift in range(min_shift, max_shift + 1):
                    discrete = {
                        "chainLengthRequest_le_K": length_request <= search["K"],
                        "final_residual": search["K"] <= M - shift,
                        "length_eq_depth": search["depth"] == 1,
                        "nodup": True,
                        "shift_avoids_singleton_r": shift != r,
                        "shift_lower": search["B"] <= shift,
                    }
                    legal = all(discrete.values())
                    if legal:
                        required_decisions.add((M, r, h))
                    tuples.append(
                        {
                            "id": f"pi-M{M}-D{search['D']}-r{r}-h{h}-s{shift}",
                            "M": M,
                            "D": search["D"],
                            "K": search["K"],
                            "r": r,
                            "h": h,
                            "shifts": [shift],
                            "chain_length_request": length_request,
                            "discrete_predicates": discrete,
                            "legal_for_resonance_test": legal,
                            "node0_decision_id": decision_id(M, r, h) if legal else None,
                            "tested_nodes": [0] if legal else [],
                            "chain_status": "pending_node0" if legal else "rejected_discrete",
                        }
                    )

    node_decisions = certify_node_zero_family(
        config,
        decimal_prefix_integer,
        decimal_scale,
        sine_cells,
        cosine_cells,
        required_decisions,
    )
    decision_map = {item["id"]: item for item in node_decisions}
    if any(item["strict_resonance_status"] != "false" for item in node_decisions):
        raise AssertionError("configured frontier unexpectedly contains a node-0 resonance")
    for candidate in tuples:
        if candidate["legal_for_resonance_test"]:
            decision = decision_map[candidate["node0_decision_id"]]
            if decision["strict_resonance_status"] != "false":
                raise AssertionError("non-false decision requires downstream chain processing")
            candidate["chain_status"] = "rejected_certified_node0_resonance"

    literal_clauses = [
        "1_left_period_positive",
        "2_left_index_range",
        "3_right_period_positive",
        "4_right_index_range",
        "5_left_signed_error_bound",
        "6_right_signed_error_bound",
        "7_mixed_error_budget",
    ]
    transition_targets = literal_clauses + [
        "denominator_formulas_and_positivity",
        "coefficient_transport_Q0_a1_eq_U_Q1_a0",
        "literal_T28_compatibility",
    ]
    transition_statistics = {
        "predictor": config["evaluation"]["transition_predictor"],
        "eligible_adjacent_witness_pairs": 0,
        "records": [],
        "confusion_by_target": {target: empty_confusion() for target in transition_targets},
        "interpretation": "zero-sample statistic because the certified chain corpus is empty",
        "coefficient_transport_is_literal_T28_conjunct": False,
    }
    legal_count = sum(candidate["legal_for_resonance_test"] for candidate in tuples)
    result = {
        "format": "t53-resource-frontier-output-v1",
        "canonical_statement_sha256": config["inputs"]["canonical_statement.txt"],
        "input_hashes": config["inputs"],
        "parameters": config,
        "pi_certification": {
            "phase_source": "T17 certified decimal prefix",
            "t17_certificate_sha256": config["inputs"]["T17_CERTIFICATE.json"],
            "full_digit_file_sha256": config["inputs"]["pi_digits.txt"],
            "fractional_prefix_digits_used": prefix_length,
            "used_prefix_sha256": hashlib.sha256(prefix_payload).hexdigest(),
            "scaled_interval": {
                "scale_power": prefix_length,
                "lower_integer": str(decimal_prefix_integer),
                "upper_integer": str(decimal_prefix_integer + 1),
            },
            "maximum_scaled_phase_interval_width": str(max_phase_width),
            "trig_table_pi_certificate": trig_pi_certificate,
            "trig_enclosure": {
                "grid_bins": config["certification"]["turn_grid_bins"],
                "derivative_bound": config["certification"]["derivative_upper_bound"],
                "fixed_point_scale": config["certification"]["fixed_point_scale"],
                "cell_rule": "center_Taylor_interval_plus_7_over_2B_then_outward_fixed_point_rounding",
            },
        },
        "chain_length_decision": {
            "D": search["D"],
            "depth": search["depth"],
            "terminal_density_denominator": terminal_density,
            "chain_length_request": length_request,
            "K": search["K"],
            "chainLengthRequest_le_K": length_request <= search["K"],
        },
        "searched_tuples": tuples,
        "certified_node_decisions": node_decisions,
        "genuine_chains": [],
        "t24_complete_witness_sets": [],
        "literal_t28_decisions": [],
        "reduced_rational_transition_statistics": transition_statistics,
        "resource_frontier": {
            "label": "RESOURCE FRONTIER",
            "exhausted": True,
            "bounds": {
                key: search[key]
                for key in ("M_inclusive", "r_inclusive", "h_inclusive", "shift_inclusive")
            },
            "first_unavailable_stage": "T24 complete witness enumeration",
            "reason": "every legal tuple fails certified node-0 T26 strict resonance",
        },
        "summary": {
            "declared_tuple_count": len(tuples),
            "legal_tuple_count": legal_count,
            "distinct_certified_node0_decision_count": len(node_decisions),
            "certified_node0_false_count": len(node_decisions),
            "genuine_chain_count": 0,
            "t24_node_count": 0,
            "t24_witness_count": 0,
            "literal_t28_decision_count": 0,
            "transition_pair_count": 0,
            "unresolved_decision_count": 0,
            "new_T50_APC_FSFS_or_control_computation": False,
        },
        "claims": {
            "evidence_label": "experiment",
            "finite_heuristic_only": True,
            "proves_compatibility": False,
            "proves_C1": False,
            "proves_canonical_A1": False,
            "exhaustion_applies_only_to_declared_range": True,
        },
    }
    output_path.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n", encoding="ascii")
    report_path.write_text(make_report(result), encoding="ascii")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--config", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--report", type=Path, required=True)
    args = parser.parse_args()
    run(args.config, args.output, args.report)


if __name__ == "__main__":
    main()
