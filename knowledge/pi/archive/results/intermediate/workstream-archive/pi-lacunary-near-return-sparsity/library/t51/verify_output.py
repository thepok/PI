#!/usr/bin/env python3
"""Independent exact verifier for T51 witness and graph certificates."""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
import math
from fractions import Fraction
from pathlib import Path


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1 << 20), b""):
            digest.update(block)
    return digest.hexdigest()


def frac(pair: list[int]) -> Fraction:
    return Fraction(pair[0], pair[1])


def interval(record: dict) -> tuple[Fraction, Fraction]:
    lo = frac(record["rational"]["lo"])
    hi = frac(record["rational"]["hi"])
    assert lo <= hi
    assert Fraction(record["decimal"]["lo"]) <= lo
    assert hi <= Fraction(record["decimal"]["hi"])
    return lo, hi


def interval_add(
    left: tuple[Fraction, Fraction], right: tuple[Fraction, Fraction]
) -> tuple[Fraction, Fraction]:
    return left[0] + right[0], left[1] + right[1]


def interval_scale(
    value: tuple[Fraction, Fraction], scalar: int | Fraction
) -> tuple[Fraction, Fraction]:
    products = (value[0] * scalar, value[1] * scalar)
    return min(products), max(products)


def interval_mul(
    left: tuple[Fraction, Fraction], right: tuple[Fraction, Fraction]
) -> tuple[Fraction, Fraction]:
    products = tuple(x * y for x in left for y in right)
    return min(products), max(products)


def interval_abs(value: tuple[Fraction, Fraction]) -> tuple[Fraction, Fraction]:
    lo, hi = value
    if lo >= 0:
        return value
    if hi <= 0:
        return -hi, -lo
    return Fraction(0), max(-lo, hi)


def classify_lt(
    left: tuple[Fraction, Fraction], right: tuple[Fraction, Fraction]
) -> str:
    if left[1] < right[0]:
        return "true"
    if left[0] >= right[1]:
        return "false"
    return "unresolved"


def floor_fraction(x: Fraction) -> int:
    return x.numerator // x.denominator


def ceil_fraction(x: Fraction) -> int:
    return -floor_fraction(-x)


def alternating_atan(q: int, tolerance: Fraction) -> tuple[tuple[Fraction, Fraction], int]:
    partial = Fraction(0)
    n = 0
    while True:
        term = Fraction(1, (2 * n + 1) * q ** (2 * n + 1))
        partial = partial + term if n % 2 == 0 else partial - term
        following = n + 1
        next_term = Fraction(1, (2 * following + 1) * q ** (2 * following + 1))
        next_partial = partial + next_term if following % 2 == 0 else partial - next_term
        if next_term < tolerance:
            return (min(partial, next_partial), max(partial, next_partial)), n + 1
        n += 1


def independent_pi(bits: int) -> tuple[tuple[Fraction, Fraction], tuple[int, int]]:
    target = Fraction(1, 2**bits)
    atan5, terms5 = alternating_atan(5, target / 32)
    atan239, terms239 = alternating_atan(239, target / 8)
    first = interval_scale(atan5, 16)
    second = interval_scale(atan239, -4)
    return interval_add(first, second), (terms5, terms239)


def independent_cos_turn(
    turn: Fraction, pi: tuple[Fraction, Fraction], terms: int
) -> tuple[Fraction, Fraction]:
    angle = interval_scale(pi, 2 * turn)
    angle_squared = interval_mul(angle, angle)
    power = (Fraction(1), Fraction(1))
    total = (Fraction(0), Fraction(0))
    for k in range(terms + 1):
        term = interval_scale(power, Fraction(1, math.factorial(2 * k)))
        total = interval_add(total, term if k % 2 == 0 else interval_scale(term, -1))
        power = interval_mul(power, angle_squared)
    remainder = angle[1] ** (2 * terms + 1) / math.factorial(2 * terms + 1)
    return total[0] - remainder, total[1] + remainder


def independent_inverse_error(
    tau: Fraction,
    pi: tuple[Fraction, Fraction],
    terms: int,
    bisections: int,
) -> tuple[Fraction, Fraction]:
    low = Fraction(0)
    high = Fraction(1, 4)
    for _ in range(bisections):
        midpoint = (low + high) / 2
        cosine = independent_cos_turn(midpoint, pi, terms)
        status = classify_lt((tau, tau), cosine)
        if status == "true":
            low = midpoint
        elif status == "false":
            high = midpoint
        else:
            raise AssertionError("independent inverse-error decision unresolved")
    return low, high


def density(D: int, k: int) -> int:
    value = D
    for _ in range(k):
        value = 8 * value * value
    return value


def coefficient(h: int, r: int, shifts: list[int], k: int) -> int:
    value = h * (10**r - 1)
    for shift in shifts[:k]:
        value *= 10**shift - 1
    return value


def maximum_matching_size(left: list[str], right: list[str], edges: set[tuple[str, str]]) -> int:
    best = 0
    for size in range(1, min(len(left), len(right)) + 1):
        for left_subset in itertools.combinations(left, size):
            for right_subset in itertools.combinations(right, size):
                for permutation in itertools.permutations(right_subset):
                    if all((source, target) in edges for source, target in zip(left_subset, permutation)):
                        best = size
                        break
    return best


def hall_max(side: list[str], edges: set[tuple[str, str]], left_side: bool) -> int:
    best = 0
    for size in range(len(side) + 1):
        for subset_tuple in itertools.combinations(side, size):
            subset = set(subset_tuple)
            if left_side:
                neighbors = {target for source, target in edges if source in subset}
            else:
                neighbors = {source for source, target in edges if target in subset}
            best = max(best, len(subset) - len(neighbors))
    return best


def longest_path_size(layers: list[list[str]], edges: set[tuple[str, str]]) -> int:
    lengths: dict[str, int] = {}
    best = 0
    for layer_index, layer in enumerate(layers):
        previous = layers[layer_index - 1] if layer_index else []
        for vertex in layer:
            predecessors = [lengths[source] for source in previous if (source, vertex) in edges]
            lengths[vertex] = 1 + max(predecessors, default=0)
            best = max(best, lengths[vertex])
    return best


def assert_no_repeated_t50_tables(value: object) -> None:
    banned_keys = {"apc_margin", "apc_status", "fsfs_margin", "fsfs_status", "strata", "primitive_classes"}
    if isinstance(value, dict):
        assert not (set(value) & banned_keys), "T51 output repeats a T50 APC/FSFS table"
        for child in value.values():
            assert_no_repeated_t50_tables(child)
    elif isinstance(value, list):
        for child in value:
            assert_no_repeated_t50_tables(child)


def verify(config_path: Path, output_path: Path, report_path: Path) -> None:
    root = config_path.parent
    config = json.loads(config_path.read_text(encoding="ascii"))
    output = json.loads(output_path.read_text(encoding="ascii"))
    report = report_path.read_text(encoding="ascii")
    assert config["format"] == "t51-exact-postprocessing-config-v1"
    for filename, expected in config["inputs"].items():
        assert sha256(root / filename) == expected
    assert output["format"] == "t51-exact-postprocessing-output-v1"
    assert output["input_hashes"] == config["inputs"]
    assert output["canonical_statement_sha256"] == config["inputs"]["canonical_statement.txt"]
    assert output["claims"] == {
        "counterexample_scope": "finite tested T50 structural-chain nodewise-witness selection property only",
        "evidence_label": "experiment",
        "finite_heuristic_only": True,
        "new_T50_APC_or_FSFS_computation": False,
        "proves_C1": False,
        "proves_canonical_A1": False,
        "proves_compatibility": False,
        "refutes_T28_CoherentAdjacentSelection": False,
    }
    assert_no_repeated_t50_tables(output)

    cert = config["certification"]
    pi, term_counts = independent_pi(cert["pi_target_bits"])
    assert interval(output["pi_certificate"]["interval"]) == pi
    assert term_counts == (
        output["pi_certificate"]["atan_1_over_5_terms"],
        output["pi_certificate"]["atan_1_over_239_terms"],
    )
    t50 = json.loads((root / "t50_raw_output.json").read_text(encoding="ascii"))
    selected = next(dataset for dataset in t50["datasets"] if dataset["name"] == "pi")
    expected_chains = [candidate for candidate in selected["candidates"] if candidate["is_witness"]]
    assert [chain["id"] for chain in output["chains"]] == [candidate["id"] for candidate in expected_chains]

    checked_pairs = 0
    checked_vertices = 0
    checked_edges = 0
    for chain, inherited_candidate in zip(output["chains"], expected_chains):
        params = chain["parameters"]
        M, D, K = params["M"], params["D"], params["K"]
        h, r, shifts = params["h"], params["r"], params["shifts"]
        assert chain["inherited_T50_node_resonance_certificates"] == inherited_candidate["nodes"]
        terminal_density = density(D, len(shifts))
        request = 2 * terminal_density**2
        assert chain["chain_length_request"] == request
        assert chain["nodewise_T24_theorem_premise"] == {
            "K": K,
            "chainLengthRequest_le_K": request <= K,
            "chain_length_request": request,
        }
        reconstructed_layers: list[list[dict]] = []
        for k, node in enumerate(chain["nodes"]):
            residual = M - sum(shifts[:k])
            Dk = density(D, k)
            Ck = coefficient(h, r, shifts, k)
            assert node["k"] == k
            assert node["residual"] == residual
            assert node["density_denominator"] == Dk
            assert node["coefficient_multiplier_of_pi"] == Ck
            assert interval(node["beta"]) == interval_scale(pi, Ck)
            epsilon = independent_inverse_error(
                Fraction(1, 8 * Dk * Dk), pi, cert["taylor_terms"], cert["inverse_error_bisections"]
            )
            assert interval(node["inverse_error"]) == epsilon
            expected_indices = [(j, s) for j in range(residual) for s in range(1, residual - j)]
            assert [(pair["j"], pair["s"]) for pair in node["pairs"]] == expected_indices
            assert node["legal_pair_count"] == len(expected_indices)
            reconstructed = []
            signed_failure_count = 0
            for pair in node["pairs"]:
                checked_pairs += 1
                j, s = pair["j"], pair["s"]
                Q = 10**j * (10**s - 1)
                assert pair["Q"] == Q and pair["denominator_positive"]
                assert all(pair["legal_preperiod_period_predicates"].values())
                scaled = interval_scale(pi, Ck * Q)
                first = floor_fraction(scaled[0] - epsilon[1]) + 1
                last = ceil_fraction(scaled[1] + epsilon[1]) - 1
                assert pair["candidate_integer_bounds_inclusive"] == [first, last]
                assert frac(pair["open_completeness_window"]["lower"]) == scaled[0] - epsilon[1]
                assert frac(pair["open_completeness_window"]["upper"]) == scaled[1] + epsilon[1]
                assert [candidate["a"] for candidate in pair["candidates"]] == list(range(first, last + 1))
                pair_witnesses = []
                for candidate in pair["candidates"]:
                    a = candidate["a"]
                    signed = (scaled[0] - a, scaled[1] - a)
                    absolute = interval_abs(signed)
                    status = classify_lt(absolute, epsilon)
                    assert status != "unresolved"
                    assert candidate["strict_error_status"] == status
                    assert interval(candidate["signed_scaled_error"]) == signed
                    assert interval(candidate["absolute_scaled_error"]) == absolute
                    if status == "true":
                        pair_witnesses.append(candidate["id"])
                        reconstructed.append(
                            {
                                "Q": Q,
                                "a": a,
                                "absolute_scaled_error": candidate["absolute_scaled_error"],
                                "id": candidate["id"],
                                "j": j,
                                "preperiod_class": "cycle" if j == 0 else "positive_preperiod",
                                "s": s,
                                "signed_scaled_error": candidate["signed_scaled_error"],
                            }
                        )
                assert pair["witness_ids"] == pair_witnesses
                expected_failure = None if pair_witnesses else "signed_error"
                assert pair["failure_partition"] == expected_failure
                signed_failure_count += expected_failure == "signed_error"
            assert node["witnesses"] == reconstructed
            assert node["witness_count"] == len(reconstructed)
            assert node["rejected_candidate_partition"]["signed_error"] == signed_failure_count
            assert node["rejected_candidate_partition"]["preperiod_period"] == 0
            assert node["rejected_candidate_partition"]["denominator"] == 0
            assert node["rejected_candidate_partition"]["coefficient_transport"] == 0
            checked_vertices += len(reconstructed)
            reconstructed_layers.append(reconstructed)

        for layer_index, graph in enumerate(chain["adjacencies"]):
            U = 10**shifts[layer_index] - 1
            left, right = reconstructed_layers[layer_index : layer_index + 2]
            expected_records = []
            expected_edges: set[tuple[str, str]] = set()
            partitions = {
                "coefficient_transport": 0,
                "denominator": 0,
                "mixed_error_budget_after_exact_transport": 0,
                "preperiod_period": 0,
                "signed_error": 0,
                "unresolved_interval": 0,
            }
            for v0, v1 in itertools.product(left, right):
                e0 = interval(v0["absolute_scaled_error"])
                e1 = interval(v1["absolute_scaled_error"])
                budget = interval_add(interval_scale(e1, v0["Q"]), interval_scale(e0, U * v1["Q"]))
                status = classify_lt(budget, (Fraction(1), Fraction(1)))
                assert status != "unresolved"
                z = v0["Q"] * v1["a"] - U * v1["Q"] * v0["a"]
                clauses = {
                    "1_left_period_positive": v0["s"] >= 1,
                    "2_left_index_range": v0["j"] + v0["s"] < chain["nodes"][layer_index]["residual"],
                    "3_right_period_positive": v1["s"] >= 1,
                    "4_right_index_range": v1["j"] + v1["s"] < chain["nodes"][layer_index + 1]["residual"],
                    "5_left_signed_error_bound": True,
                    "6_right_signed_error_bound": True,
                    "7_mixed_error_budget": status == "true",
                }
                compatible = all(clauses.values())
                partition = None
                if not compatible:
                    partition = "coefficient_transport" if z != 0 else "mixed_error_budget_after_exact_transport"
                    partitions[partition] += 1
                if compatible:
                    expected_edges.add((v0["id"], v1["id"]))
                expected_records.append(
                    {
                        "Q0": v0["Q"],
                        "Q1": v1["Q"],
                        "cancellation_integer_Q0_a1_minus_U_Q1_a0": z,
                        "compatible": compatible,
                        "failure_partition": partition,
                        "left": v0["id"],
                        "literal_T28_conjuncts": clauses,
                        "mixed_error_budget": graph["all_witness_pairs"][len(expected_records)]["mixed_error_budget"],
                        "right": v1["id"],
                    }
                )
                assert interval(expected_records[-1]["mixed_error_budget"]) == budget
            assert graph["all_witness_pairs"] == expected_records
            assert {tuple(edge) for edge in graph["edges"]} == expected_edges
            assert graph["failure_partition"] == partitions
            assert graph["compatible_edge_count"] == len(expected_edges)
            assert graph["compatible_edge_exists"] == bool(expected_edges)
            left_ids = [vertex["id"] for vertex in left]
            right_ids = [vertex["id"] for vertex in right]
            matching_size = maximum_matching_size(left_ids, right_ids, expected_edges)
            assert graph["maximum_matching_size"] == matching_size
            assert len(graph["matching"]) == matching_size
            assert all(tuple(edge) in expected_edges for edge in graph["matching"])
            assert len({edge[0] for edge in graph["matching"]}) == matching_size
            assert len({edge[1] for edge in graph["matching"]}) == matching_size
            assert hall_max(left_ids, expected_edges, True) == graph["hall"]["left"]["deficiency"]
            assert hall_max(right_ids, expected_edges, False) == graph["hall"]["right"]["deficiency"]
            for orientation, side, left_side in (
                ("left", left_ids, True), ("right", right_ids, False)
            ):
                certificate = graph["hall"][orientation]
                subset = set(certificate["subset"])
                assert subset <= set(side)
                neighbors = (
                    {target for source, target in expected_edges if source in subset}
                    if left_side
                    else {source for source, target in expected_edges if target in subset}
                )
                assert certificate["neighborhood"] == sorted(neighbors)
                assert certificate["deficiency"] == len(subset) - len(neighbors)
            checked_edges += len(expected_edges)

        longest = chain["longest_compatible_path"]
        path = longest["path"]
        all_edges = {tuple(edge) for graph in chain["adjacencies"] for edge in graph["edges"]}
        assert all((path[i], path[i + 1]) in all_edges for i in range(len(path) - 1))
        assert longest["vertex_count"] == len(path)
        assert longest["edge_count"] == max(0, len(path) - 1)
        assert longest["spans_all_layers"] == (len(path) == len(chain["nodes"]))
        assert longest["vertex_count"] == longest_path_size(
            [[vertex["id"] for vertex in layer] for layer in reconstructed_layers], all_edges
        )

    for marker in (
        "finite heuristic evidence only",
        "No T50\nAPC/FSFS computation is presented as new",
        "32768 <= 2, which is false",
        "does not refute T28 `CoherentAdjacentSelection`",
        "Run `bash reproduce.sh`",
        "prove neither\ncompatibility nor canonical C1",
    ):
        assert marker in report
    print(
        "T51 verification passed: "
        f"{len(output['chains'])} chain, {checked_pairs} legal T24 index pairs, "
        f"{checked_vertices} witnesses, and {checked_edges} literal T28 edges."
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
