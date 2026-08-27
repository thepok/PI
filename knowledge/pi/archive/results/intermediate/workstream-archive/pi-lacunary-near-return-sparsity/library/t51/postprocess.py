#!/usr/bin/env python3
"""Exact T24/T28 postprocessing of T50's pinned fixed-pi chain records."""

from __future__ import annotations

import argparse
import hashlib
import itertools
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


def outward_decimal(x: Fraction, places: int, upper: bool) -> str:
    scale = 10**places
    scaled = x * scale
    integer = ceil_fraction(scaled) if upper else floor_fraction(scaled)
    sign = "-" if integer < 0 else ""
    digits = str(abs(integer)).rjust(places + 1, "0")
    return f"{sign}{digits[:-places]}.{digits[-places:]}"


def interval_record(x: Interval, places: int) -> dict:
    return {
        "decimal": {
            "hi": outward_decimal(x.hi, places, True),
            "lo": outward_decimal(x.lo, places, False),
        },
        "rational": {
            "hi": fraction_pair(x.hi),
            "lo": fraction_pair(x.lo),
        },
    }


def interval_abs(x: Interval) -> Interval:
    if x.lo >= 0:
        return x
    if x.hi <= 0:
        return -x
    return Interval(Fraction(0), max(-x.lo, x.hi))


def classify_lt(left: Interval, right: Interval) -> str:
    if left.hi < right.lo:
        return "true"
    if left.lo >= right.hi:
        return "false"
    return "unresolved"


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
        "atan_1_over_239_terms": terms239,
        "atan_1_over_5_terms": terms5,
        "method": "Machin_pi_equals_16_atan_1_over_5_minus_4_atan_1_over_239",
        "target_bits": bits,
    }


def cos_turn_interval(turn: Fraction, pi: Interval, terms: int) -> Interval:
    if not 0 <= turn <= Fraction(1, 4):
        raise ValueError("cosine certifier expects a turn in [0,1/4]")
    angle = pi.scale(2 * turn)
    angle_squared = angle * angle
    power = ONE
    total = ZERO
    for k in range(terms + 1):
        term = power.scale(Fraction(1, math.factorial(2 * k)))
        total = total + (term if k % 2 == 0 else -term)
        power = power * angle_squared
    remainder = angle.hi ** (2 * terms + 1) / math.factorial(2 * terms + 1)
    return Interval(total.lo - remainder, total.hi + remainder)


def inverse_error_interval(
    tau: Fraction, pi: Interval, terms: int, bisections: int
) -> Interval:
    low = Fraction(0)
    high = Fraction(1, 4)
    target = Interval.point(tau)
    for _ in range(bisections):
        midpoint = (low + high) / 2
        cosine = cos_turn_interval(midpoint, pi, terms)
        relation = classify_lt(target, cosine)
        if relation == "true":
            low = midpoint
        elif relation == "false":
            high = midpoint
        else:
            raise ArithmeticError("inverse-error bisection unresolved")
    return Interval(low, high)


def density_denominator(D: int, k: int) -> int:
    value = D
    for _ in range(k):
        value = 8 * value * value
    return value


def decimal_denominator(j: int, s: int) -> int:
    return 10**j * (10**s - 1)


def multiplier(h: int, r: int, shifts: list[int], k: int) -> int:
    value = h * (10**r - 1)
    for shift in shifts[:k]:
        value *= 10**shift - 1
    return value


def complete_integer_bounds(x: Interval, radius: Interval) -> tuple[int, int]:
    # Any true witness must lie in the displayed open interval.
    return floor_fraction(x.lo - radius.hi) + 1, ceil_fraction(x.hi + radius.hi) - 1


def enumerate_node(
    chain_id: str,
    k: int,
    residual: int,
    density: int,
    coefficient: int,
    pi: Interval,
    inverse_error: Interval,
    places: int,
) -> dict:
    beta = pi.scale(coefficient)
    pair_records = []
    witnesses = []
    rejected = []
    for j in range(residual):
        for s in range(1, residual - j):
            Q = decimal_denominator(j, s)
            scaled = beta.scale(Q)
            first, last = complete_integer_bounds(scaled, inverse_error)
            candidates = []
            for a in range(first, last + 1):
                signed_error = scaled - Interval.point(a)
                absolute_error = interval_abs(signed_error)
                status = classify_lt(absolute_error, inverse_error)
                if status == "unresolved":
                    raise ArithmeticError(f"unresolved T24 decision at node {k}, {(j, s, a)}")
                witness_id = f"{chain_id}:k{k}:j{j}:s{s}:a{a}"
                record = {
                    "a": a,
                    "absolute_scaled_error": interval_record(absolute_error, places),
                    "id": witness_id,
                    "signed_scaled_error": interval_record(signed_error, places),
                    "strict_error_status": status,
                }
                candidates.append(record)
                if status == "true":
                    witness = {
                        "Q": Q,
                        "a": a,
                        "absolute_scaled_error": interval_record(absolute_error, places),
                        "id": witness_id,
                        "j": j,
                        "preperiod_class": "cycle" if j == 0 else "positive_preperiod",
                        "s": s,
                        "signed_scaled_error": interval_record(signed_error, places),
                    }
                    witnesses.append(witness)
                else:
                    rejected.append({"id": witness_id, "partition": "signed_error"})
            pair_records.append(
                {
                    "Q": Q,
                    "candidate_integer_bounds_inclusive": [first, last],
                    "candidates": candidates,
                    "denominator_positive": Q >= 1,
                    "failure_partition": None if any(
                        candidate["strict_error_status"] == "true" for candidate in candidates
                    ) else "signed_error",
                    "j": j,
                    "legal_preperiod_period_predicates": {
                        "j_nonnegative": j >= 0,
                        "j_plus_s_lt_residual": j + s < residual,
                        "s_positive": s >= 1,
                    },
                    "open_completeness_window": {
                        "lower": fraction_pair(scaled.lo - inverse_error.hi),
                        "upper": fraction_pair(scaled.hi + inverse_error.hi),
                    },
                    "s": s,
                    "witness_ids": [
                        candidate["id"]
                        for candidate in candidates
                        if candidate["strict_error_status"] == "true"
                    ],
                }
            )
    expected_pairs = residual * (residual - 1) // 2
    if len(pair_records) != expected_pairs:
        raise AssertionError("legal T24 pair enumeration is incomplete")
    return {
        "beta": interval_record(beta, places),
        "coefficient_multiplier_of_pi": coefficient,
        "density_denominator": density,
        "inverse_error": interval_record(inverse_error, places),
        "k": k,
        "legal_pair_count": len(pair_records),
        "pairs": pair_records,
        "rejected_candidate_partition": {
            "coefficient_transport": 0,
            "denominator": 0,
            "preperiod_period": 0,
            "signed_error": len(rejected) + sum(
                not pair["candidates"] and pair["failure_partition"] == "signed_error"
                for pair in pair_records
            ),
        },
        "residual": residual,
        "witness_count": len(witnesses),
        "witnesses": witnesses,
    }


def rational_interval(record: dict) -> Interval:
    raw = record["rational"]
    return Interval(Fraction(*raw["lo"]), Fraction(*raw["hi"]))


def maximum_matching(left: list[str], right: list[str], edges: list[list[str]]) -> list[list[str]]:
    adjacency = {vertex: [] for vertex in left}
    for source, target in edges:
        adjacency[source].append(target)
    for targets in adjacency.values():
        targets.sort()
    target_to_source: dict[str, str] = {}

    def augment(source: str, seen: set[str]) -> bool:
        for target in adjacency[source]:
            if target in seen:
                continue
            seen.add(target)
            if target not in target_to_source or augment(target_to_source[target], seen):
                target_to_source[target] = source
                return True
        return False

    for source in left:
        augment(source, set())
    return sorted([[source, target] for target, source in target_to_source.items()])


def hall_certificate(side: list[str], edges: list[list[str]], left_oriented: bool) -> dict:
    best_deficiency = -1
    best_subset: list[str] = []
    best_neighbors: list[str] = []
    for mask in range(1 << len(side)):
        subset = [vertex for index, vertex in enumerate(side) if mask & (1 << index)]
        if left_oriented:
            neighbors = sorted({target for source, target in edges if source in subset})
        else:
            neighbors = sorted({source for source, target in edges if target in subset})
        deficiency = len(subset) - len(neighbors)
        candidate = (deficiency, [-len(subset), subset])
        incumbent = (best_deficiency, [-len(best_subset), best_subset])
        if candidate > incumbent:
            best_deficiency = deficiency
            best_subset = subset
            best_neighbors = neighbors
    return {
        "deficiency": best_deficiency,
        "neighborhood": best_neighbors,
        "subset": best_subset,
    }


def build_adjacency(chain: dict, nodes: list[dict], shift: int, places: int) -> dict:
    U = 10**shift - 1
    left = nodes[0]["witnesses"]
    right = nodes[1]["witnesses"]
    edge_records = []
    edges = []
    partitions = {
        "coefficient_transport": 0,
        "denominator": 0,
        "mixed_error_budget_after_exact_transport": 0,
        "preperiod_period": 0,
        "signed_error": 0,
        "unresolved_interval": 0,
    }
    for v0, v1 in itertools.product(left, right):
        Q0 = v0["Q"]
        Q1 = v1["Q"]
        e0 = rational_interval(v0["absolute_scaled_error"])
        e1 = rational_interval(v1["absolute_scaled_error"])
        budget = e1.scale(Q0) + e0.scale(U * Q1)
        budget_status = classify_lt(budget, ONE)
        if budget_status == "unresolved":
            raise ArithmeticError("unresolved T28 mixed budget")
        cancellation_integer = Q0 * v1["a"] - U * Q1 * v0["a"]
        clauses = {
            "1_left_period_positive": v0["s"] >= 1,
            "2_left_index_range": v0["j"] + v0["s"] < nodes[0]["residual"],
            "3_right_period_positive": v1["s"] >= 1,
            "4_right_index_range": v1["j"] + v1["s"] < nodes[1]["residual"],
            "5_left_signed_error_bound": True,
            "6_right_signed_error_bound": True,
            "7_mixed_error_budget": budget_status == "true",
        }
        compatible = all(clauses.values())
        failure_partition = None
        if not compatible:
            if not all(list(clauses.values())[:4]):
                failure_partition = "preperiod_period"
            elif not clauses["5_left_signed_error_bound"] or not clauses["6_right_signed_error_bound"]:
                failure_partition = "signed_error"
            elif cancellation_integer != 0:
                failure_partition = "coefficient_transport"
            else:
                failure_partition = "mixed_error_budget_after_exact_transport"
            partitions[failure_partition] += 1
        if compatible:
            edges.append([v0["id"], v1["id"]])
        edge_records.append(
            {
                "Q0": Q0,
                "Q1": Q1,
                "cancellation_integer_Q0_a1_minus_U_Q1_a0": cancellation_integer,
                "compatible": compatible,
                "failure_partition": failure_partition,
                "left": v0["id"],
                "literal_T28_conjuncts": clauses,
                "mixed_error_budget": interval_record(budget, places),
                "right": v1["id"],
            }
        )
    left_ids = [vertex["id"] for vertex in left]
    right_ids = [vertex["id"] for vertex in right]
    matching = maximum_matching(left_ids, right_ids, edges)
    left_hall = hall_certificate(left_ids, edges, True)
    right_hall = hall_certificate(right_ids, edges, False)
    if left_hall["deficiency"] != len(left_ids) - len(matching):
        raise AssertionError("left Hall identity failed")
    if right_hall["deficiency"] != len(right_ids) - len(matching):
        raise AssertionError("right Hall identity failed")
    return {
        "U": U,
        "adjacent_nodes": [0, 1],
        "all_witness_pairs": edge_records,
        "compatible_edge_count": len(edges),
        "compatible_edge_exists": bool(edges),
        "edges": edges,
        "failure_partition": partitions,
        "hall": {"left": left_hall, "right": right_hall},
        "left_vertices": left_ids,
        "matching": matching,
        "maximum_matching_size": len(matching),
        "right_vertices": right_ids,
    }


def longest_layered_path(nodes: list[dict], adjacency: dict) -> dict:
    layers = [[witness["id"] for witness in node["witnesses"]] for node in nodes]
    predecessors: dict[str, tuple[int, list[str]]] = {}
    for vertex in layers[0]:
        predecessors[vertex] = (1, [vertex])
    edge_set = {tuple(edge) for edge in adjacency["edges"]}
    for layer_index in range(1, len(layers)):
        for vertex in layers[layer_index]:
            candidates = [
                predecessors[source]
                for source in layers[layer_index - 1]
                if (source, vertex) in edge_set and source in predecessors
            ]
            if candidates:
                length, path = max(candidates, key=lambda item: (item[0], item[1]))
                predecessors[vertex] = (length + 1, path + [vertex])
            else:
                predecessors[vertex] = (1, [vertex])
    if not predecessors:
        return {"edge_count": 0, "path": [], "spans_all_layers": False, "vertex_count": 0}
    vertex_count, path = max(predecessors.values(), key=lambda item: (item[0], item[1]))
    return {
        "edge_count": vertex_count - 1,
        "path": path,
        "spans_all_layers": vertex_count == len(nodes),
        "vertex_count": vertex_count,
    }


def make_report(result: dict) -> str:
    chains = result["chains"]
    lines = [
        "# T51 exact postprocessing of T50 fixed-pi chains",
        "",
        "Status: `experiment` (finite heuristic evidence only).",
        "",
        "## Scope",
        "",
        "This is the bounded A14 sibling, not canonical A1. The canonical statement is",
        "vendored byte-for-byte and hash-pinned. Only T50's fixed-pi structural",
        "`GeometricResonanceChain` records are consumed. T50's chain search, controls,",
        "APC, FSFS, primitive classes, and aggregate tables are not recomputed. No T50",
        "APC/FSFS computation is presented as new.",
        "",
        "## Literal predicates",
        "",
        "At node k, the complete legal T24 indices are s >= 1 and j+s < M_k, with",
        "Q=10^j(10^s-1). A triple (j,s,a) is retained exactly when the certified",
        "interval proves |Q beta_k-a| < inverseError(nodeTau(D,k)). Integer search",
        "bounds come from the enclosing open interval and therefore certify completeness.",
        "For every adjacent witness pair, edges use all seven conjuncts of kernel-checked",
        "T28 `AdjacentPairCompatible`; no equality of j, s, or Q is imposed.",
        "Preperiod ranges and denominator positivity/formulas are exact audits, not extra",
        "edge clauses; coefficient transport is diagnosed by Q0*a1-U*Q1*a0.",
        "",
        "## Results",
        "",
        "| chain | node witness counts | edges | matching | left/right Hall deficiency | longest path vertices |",
        "|---|---:|---:|---:|---:|---:|",
    ]
    for chain in chains:
        counts = "/".join(str(node["witness_count"]) for node in chain["nodes"])
        graph = chain["adjacencies"][0]
        longest = chain["longest_compatible_path"]
        lines.append(
            f"| {chain['id']} | {counts} | {graph['compatible_edge_count']} | "
            f"{graph['maximum_matching_size']} | {graph['hall']['left']['deficiency']}/"
            f"{graph['hall']['right']['deficiency']} | {longest['vertex_count']} |"
        )
    lines.extend(
        [
            "",
            "The sole selected chain has W_0={(j,s,a)=(0,1,2799)} and W_1 empty.",
            "Thus there is no literal T28 edge, the maximum matching has size 0, the",
            "left Hall deficiency is 1, and the longest path has one vertex.",
            "`raw_output.json` records every legal index, completeness window, interval",
            "decision, literal edge record, Hall witness, matching, and path certificate.",
            "",
            "## Premise audit and exact counterexample scope",
            "",
            "T26's nodewise inverse theorem requires `chainLengthRequest(D,d) <= K`.",
            "For the selected T50 chain this is 32768 <= 2, which is false. Therefore",
            "the empty terminal T24 set does not refute T28 `CoherentAdjacentSelection`,",
            "JWMO, compatibility on failure-derived chains, C1, or canonical A1. It only",
            "refutes the explicitly tested finite selection property that every",
            "T50-selected structural fixed-pi chain has a T24 witness at every node.",
            "The failure is partitioned as terminal-node signed-error exclusion; there",
            "are no witness pairs on which a coefficient-transport clause could fail.",
            "",
            "## Certification and replay",
            "",
            "Pi is enclosed by exact rational alternating-series bounds in Machin's",
            "formula. Inverse-error inequalities use rational cosine Taylor bounds and",
            "96 exact bisections. Discrete predicates and denominators use exact integers.",
            "T50 node-resonance intervals are pinned inherited inputs, not recomputed or",
            "presented as T51 results; every new T24/T28 phase decision is recertified.",
            "Any unresolved strict comparison aborts before graph statistics are emitted.",
            "Run `bash reproduce.sh` in a directory containing only these artifacts.",
            "It checks all pinned hashes, regenerates byte-identical output and report,",
            "then independently checks witness completeness, literal edges, and graph",
            "certificates. Budget: 300 seconds and 2048 MiB; no network is used.",
            "",
            "## Required limitation",
            "",
            "All positive observations are finite heuristic evidence. They prove neither",
            "compatibility nor canonical C1, neither canonical A1 nor any asymptotic",
            "property of pi. The finite missing-edge and Hall results apply only to the",
            "listed T50 structural chain and the explicitly stated selection property.",
        ]
    )
    return "\n".join(lines) + "\n"


def run(config_path: Path, output_path: Path, report_path: Path) -> None:
    root = config_path.parent
    config = json.loads(config_path.read_text(encoding="ascii"))
    for filename, expected in config["inputs"].items():
        actual = sha256(root / filename)
        if actual != expected:
            raise AssertionError(f"input hash mismatch for {filename}: {actual}")
    t50_config = json.loads((root / "t50_config.json").read_text(encoding="ascii"))
    t50 = json.loads((root / "t50_raw_output.json").read_text(encoding="ascii"))
    if t50["parameters"] != t50_config:
        raise AssertionError("T50 raw output does not embed the pinned T50 config")
    if t50["canonical_statement_sha256"] != config["inputs"]["canonical_statement.txt"]:
        raise AssertionError("canonical hash mismatch in T50 output")
    certification = config["certification"]
    places = certification["output_decimal_places"]
    pi, pi_method = certify_pi(certification["pi_target_bits"])
    selected_dataset = next(
        dataset for dataset in t50["datasets"] if dataset["name"] == config["selection"]["dataset"]
    )
    chains = []
    for candidate in selected_dataset["candidates"]:
        if not candidate["is_witness"]:
            continue
        M = candidate["M"]
        D = candidate["D"]
        K = t50_config["search"]["K"]
        h = candidate["h"]
        r = candidate["r"]
        shifts = candidate["shifts"]
        depth = len(shifts)
        if depth != 1:
            raise AssertionError("this T51 format currently requires T50 depth one")
        exact_discrete = {
            "final_residual": K <= M - sum(shifts),
            "length_eq_depth": len(shifts) == t50_config["search"]["depth"],
            "nodup": len(set(shifts)) == len(shifts),
            "shift_avoids_singleton_r": all(shift != r for shift in shifts),
            "shift_lower": all(t50_config["search"]["B"] <= shift for shift in shifts),
        }
        if exact_discrete != candidate["discrete_predicates"] or not all(exact_discrete.values()):
            raise AssertionError("pinned T50 discrete chain predicates failed")
        inherited_nodes = candidate["nodes"]
        if not all(node["strict_resonance"] == "true" for node in inherited_nodes):
            raise AssertionError("selected T50 candidate lacks a certified node resonance")
        inverse_errors = []
        nodes = []
        for k in range(depth + 1):
            Dk = density_denominator(D, k)
            tau = Fraction(1, 8 * Dk * Dk)
            epsilon = inverse_error_interval(
                tau, pi, certification["taylor_terms"], certification["inverse_error_bisections"]
            )
            inverse_errors.append(epsilon)
            residual = M - sum(shifts[:k])
            coefficient = multiplier(h, r, shifts, k)
            inherited = inherited_nodes[k]
            if (
                inherited["k"] != k
                or inherited["residual"] != residual
                or inherited["density_denominator"] != Dk
                or inherited["coefficient_multiplier_of_alpha"] != coefficient
            ):
                raise AssertionError("T50 node arithmetic mismatch")
            nodes.append(
                enumerate_node(
                    candidate["id"], k, residual, Dk, coefficient, pi, epsilon, places
                )
            )
        adjacency = build_adjacency(candidate, nodes, shifts[0], places)
        terminal_density = density_denominator(D, depth)
        length_request = 2 * terminal_density**2
        chain = {
            "adjacencies": [adjacency],
            "chain_length_request": length_request,
            "discrete_chain_predicates": exact_discrete,
            "id": candidate["id"],
            "inherited_T50_node_resonance_certificates": inherited_nodes,
            "longest_compatible_path": longest_layered_path(nodes, adjacency),
            "nodewise_T24_theorem_premise": {
                "K": K,
                "chainLengthRequest_le_K": length_request <= K,
                "chain_length_request": length_request,
            },
            "nodes": nodes,
            "parameters": {"D": D, "K": K, "M": M, "h": h, "r": r, "shifts": shifts},
            "tested_selection_property": {
                "counterexample": any(node["witness_count"] == 0 for node in nodes),
                "property": "every selected T50 fixed-pi structural chain has at least one T24 witness at every node",
                "scope_limitation": "not T28 CoherentAdjacentSelection because chainLengthRequest_le_K is false",
            },
        }
        chains.append(chain)
    if not chains:
        raise AssertionError("no T50 fixed-pi structural chain selected")
    result = {
        "canonical_statement_sha256": config["inputs"]["canonical_statement.txt"],
        "chains": chains,
        "claims": {
            "counterexample_scope": "finite tested T50 structural-chain nodewise-witness selection property only",
            "evidence_label": "experiment",
            "finite_heuristic_only": True,
            "new_T50_APC_or_FSFS_computation": False,
            "proves_C1": False,
            "proves_canonical_A1": False,
            "proves_compatibility": False,
            "refutes_T28_CoherentAdjacentSelection": False,
        },
        "format": "t51-exact-postprocessing-output-v1",
        "input_hashes": config["inputs"],
        "interval_encoding": f"exact rational endpoints plus {places}-place outward decimals",
        "pi_certificate": {"interval": interval_record(pi, places), **pi_method},
        "scope": config["selection"],
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
