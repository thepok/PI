#!/usr/bin/env python3
"""Replay T65's terminality-dropped criterion on finite T48 graphs.

All classifications produced here are finite experimental evidence only.
They do not prove the uniform linear-depth hypothesis, C6, or C1.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import itertools
import json
import signal
import shutil
import sys
import tempfile
from pathlib import Path

sys.dont_write_bytecode = True

import t52_experiment as t52


FORMAT_VERSION = 1
STATEMENT_SHA256 = "a70dd741b27595aeb3dfc902b5e201579fed6bae24e2191f58c5ac64a22939e6"
GENERATED_FILES = ("results.json", "instance_table.csv")
BASELINE = [
    (str(digit), 0) for digit in range(10)
] + [("0", 1), ("00", 1), ("01", 1), ("010", 1), ("0", 2), ("010", 2)]
EXTENSION = [
    (str(digit), depth)
    for digit in range(10)
    for depth in range(1, 4)
    if (str(digit), depth) not in BASELINE
]
FINITE_ONLY = (
    "finite experimental evidence only; no bounded classification proves the "
    "uniform linear-depth hypothesis, C6, or C1"
)


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1 << 20), b""):
            digest.update(block)
    return digest.hexdigest()


def canonical_json(value) -> bytes:
    return (json.dumps(value, indent=2, sort_keys=True) + "\n").encode("ascii")


def records_hash(records) -> str:
    return hashlib.sha256(canonical_json(records)).hexdigest()


def label_key(edge):
    return edge[2], edge[3], edge[4]


def labelled_target_records(edge_ids, edges):
    records = []
    for edge_id in edge_ids:
        edge = edges[edge_id]
        records.append({
            "edge_id": edge_id,
            "label_kind": edge[2],
            "initial_carry": list(edge[3]),
            "digits": list(edge[4]),
            "dst_id": edge[1],
        })
    return records


def serialized_edge(edge_id, graph):
    value = t52.edge_json(graph["edges"][edge_id], graph["states"])
    value["edge_id"] = edge_id
    return value


def serialized_path(edge_ids, graph):
    return [serialized_edge(edge_id, graph) for edge_id in edge_ids]


def continuation_to_cycle(start, live, components, component_of, graph):
    path, cycle_vertex = t52.path_to_cycle(
        start, live, components, graph["edges"], graph["outgoing"])
    cycle_component = components[component_of[cycle_vertex]]
    cycle = t52.closed_cycle(
        cycle_vertex, cycle_component, graph["edges"], graph["outgoing"])
    return {
        "path_to_cycle": serialized_path(path, graph),
        "closed_cycle": serialized_path(cycle, graph),
    }


def build_internal_failure(component, source, internal, graph):
    if len(internal) < 2:
        raise AssertionError("a vertex in a cyclic SCC has an internal edge")
    component_set = set(component)
    closed_walks = []
    for edge_id in internal[:2]:
        target = graph["edges"][edge_id][1]
        return_path = t52.bfs_edge_path(
            target, source, graph["edges"], graph["outgoing"], component_set)
        if return_path is None:
            raise AssertionError("SCC return path missing")
        closed_walks.append(serialized_path([edge_id] + return_path, graph))
    return {
        "classification": "internal_cycle_violation",
        "violated_condition": (
            "T65 SimpleDirectedCycleSCC: the branch state has more than one "
            "reachable-live edge staying in its recurrent SCC"
        ),
        "scc_representative_state_id": component[0],
        "scc_state_ids": component,
        "branch_state_id": source,
        "all_internal_edge_ids": internal,
        "start_to_branch_path": serialized_path(
            t52.bfs_edge_path(0, source, graph["edges"], graph["outgoing"]), graph),
        "first_closed_walk": closed_walks[0],
        "second_closed_walk": closed_walks[1],
    }


def build_projected_failure(
        component, source, first, second, live, components, component_of, graph):
    first_target = graph["edges"][first][1]
    second_target = graph["edges"][second][1]
    return {
        "classification": "projected_determinism_violation",
        "violated_condition": (
            "T65 projected determinism: equal labels from one reachable-live "
            "source have different targets"
        ),
        "scc_representative_state_id": component[0],
        "scc_state_ids": component,
        "source_state_id": source,
        "start_to_source_path": serialized_path(
            t52.bfs_edge_path(0, source, graph["edges"], graph["outgoing"]), graph),
        "first_edge": serialized_edge(first, graph),
        "second_edge": serialized_edge(second, graph),
        "first_target_recurrence": continuation_to_cycle(
            first_target, live, components, component_of, graph),
        "second_target_recurrence": continuation_to_cycle(
            second_target, live, components, component_of, graph),
    }


def analyze_relaxed_t65(graph):
    states = graph["states"]
    edges = graph["edges"]
    outgoing = graph["outgoing"]
    components = t52.tarjan_scc(len(states), edges, outgoing)
    component_of = {}
    for component_id, component in enumerate(components):
        for state_id in component:
            component_of[state_id] = component_id
    live = t52.live_vertices(len(states), edges, outgoing)
    cyclic_live_components = [
        component for component in components
        if component[0] in live and t52.cyclic_component(component, edges, outgoing)
    ]

    failure = None
    checks = []
    total_internal_state_checks = 0
    total_projected_label_checks = 0
    for component in cyclic_live_components:
        component_set = set(component)
        state_records = []
        component_internal_ok = True
        component_projected_ok = True
        for source in component:
            live_outgoing = [
                edge_id for edge_id in outgoing[source]
                if edges[edge_id][1] in live
            ]
            internal = [
                edge_id for edge_id in live_outgoing
                if edges[edge_id][1] in component_set
            ]
            total_internal_state_checks += 1
            internal_ok = len(internal) == 1
            component_internal_ok &= internal_ok
            if failure is None and not internal_ok:
                failure = build_internal_failure(component, source, internal, graph)

            seen_labels = {}
            projected_ok = True
            conflict = None
            for edge_id in live_outgoing:
                key = label_key(edges[edge_id])
                total_projected_label_checks += 1
                if key in seen_labels:
                    prior = seen_labels[key]
                    if edges[prior][1] != edges[edge_id][1]:
                        projected_ok = False
                        conflict = (prior, edge_id)
                        break
                else:
                    seen_labels[key] = edge_id
            component_projected_ok &= projected_ok
            if failure is None and conflict is not None:
                failure = build_projected_failure(
                    component, source, conflict[0], conflict[1], live,
                    components, component_of, graph)
            state_records.append({
                "state_id": source,
                "internal_reachable_live_edge_count": len(internal),
                "internal_edge_ids": internal,
                "internal_unique": internal_ok,
                "reachable_live_outgoing_edge_count": len(live_outgoing),
                "projected_label_deterministic": projected_ok,
                "labelled_targets_sha256": records_hash(
                    labelled_target_records(live_outgoing, edges)),
            })
        checks.append({
            "representative_state_id": component[0],
            "state_ids": component,
            "size": len(component),
            "recurrent": True,
            "internal_simple_cycle_condition": component_internal_ok,
            "projected_label_determinism": component_projected_ok,
            "state_checks_sha256": records_hash(state_records),
            "state_checks": state_records,
        })

    criterion = failure is None
    certificate = {
        "certificate_kind": (
            "replay-checked T65 terminality-dropped reachable-live SCC certificate"
        ),
        "criterion": criterion,
        "reachable_state_count": len(states),
        "reachable_state_ids_sha256": t52.table_hash(range(len(states))),
        "reachable_live_state_count": len(live),
        "reachable_live_state_ids_sha256": t52.table_hash(live),
        "reachable_live_scc_partition_sha256": records_hash([
            component for component in components if component[0] in live
        ]),
        "cyclic_reachable_live_scc_count": len(cyclic_live_components),
        "internal_state_checks": total_internal_state_checks,
        "projected_label_checks": total_projected_label_checks,
        "cyclic_reachable_live_scc_checks": checks,
        "terminality_checked": False,
        "terminality_required": False,
    }
    validate_failure_witness(failure, graph, live, components)
    return certificate, failure, live


def validate_serialized_path(path, graph, expected_start, expected_end, allowed=None):
    edge_ids = []
    for item in path:
        edge_id = item["edge_id"]
        assert item == serialized_edge(edge_id, graph)
        edge_ids.append(edge_id)
    if not edge_ids:
        assert expected_start == expected_end
        return
    assert graph["edges"][edge_ids[0]][0] == expected_start
    assert graph["edges"][edge_ids[-1]][1] == expected_end
    for first, second in itertools.pairwise(edge_ids):
        assert graph["edges"][first][1] == graph["edges"][second][0]
    if allowed is not None:
        allowed = set(allowed)
        assert all(
            graph["edges"][edge_id][0] in allowed
            and graph["edges"][edge_id][1] in allowed
            for edge_id in edge_ids)


def validate_recurrence(payload, target, graph, live):
    path = payload["path_to_cycle"]
    cycle = payload["closed_cycle"]
    cycle_start = path[-1]["dst_id"] if path else target
    validate_serialized_path(path, graph, target, cycle_start)
    assert cycle
    validate_serialized_path(cycle, graph, cycle_start, cycle_start)
    assert all(item["src_id"] in live and item["dst_id"] in live
               for item in path + cycle)


def validate_failure_witness(witness, graph, live, components):
    if witness is None:
        return
    edges = graph["edges"]
    outgoing = graph["outgoing"]
    component_of = {}
    for component_id, component in enumerate(components):
        for state_id in component:
            component_of[state_id] = component_id
    component = witness["scc_state_ids"]
    representative = witness["scc_representative_state_id"]
    assert component == components[component_of[representative]]
    assert t52.cyclic_component(component, edges, outgoing)
    assert all(state_id in live for state_id in component)

    if witness["classification"] == "internal_cycle_violation":
        source = witness["branch_state_id"]
        internal = [
            edge_id for edge_id in outgoing[source]
            if edges[edge_id][1] in set(component) and edges[edge_id][1] in live
        ]
        assert internal == witness["all_internal_edge_ids"]
        assert len(internal) != 1 and len(internal) >= 2
        validate_serialized_path(witness["start_to_branch_path"], graph, 0, source)
        for walk in (witness["first_closed_walk"], witness["second_closed_walk"]):
            assert walk
            validate_serialized_path(walk, graph, source, source, component)
        assert witness["first_closed_walk"][0]["edge_id"] != \
            witness["second_closed_walk"][0]["edge_id"]
    else:
        assert witness["classification"] == "projected_determinism_violation"
        source = witness["source_state_id"]
        validate_serialized_path(witness["start_to_source_path"], graph, 0, source)
        first = witness["first_edge"]["edge_id"]
        second = witness["second_edge"]["edge_id"]
        assert witness["first_edge"] == serialized_edge(first, graph)
        assert witness["second_edge"] == serialized_edge(second, graph)
        assert edges[first][0] == source == edges[second][0]
        assert label_key(edges[first]) == label_key(edges[second])
        assert edges[first][1] != edges[second][1]
        assert edges[first][1] in live and edges[second][1] in live
        validate_recurrence(
            witness["first_target_recurrence"], edges[first][1], graph, live)
        validate_recurrence(
            witness["second_target_recurrence"], edges[second][1], graph, live)


def frontier_row(spec, caps, reason, graph=None):
    word = spec["word"]
    depth = spec["depth"]
    return {
        "instance_order": spec["instance_order"],
        "cohort": spec["cohort"],
        "word": word,
        "word_length": len(word),
        "depth_R": depth,
        "declared_state_count_including_root": 1 + len(word) ** (depth + 1) * 18 ** depth,
        "caps": caps,
        "status": "resource_frontier",
        "resource_stop_reason": reason,
        "discovered_state_count_including_root": (
            None if graph is None else len(graph["states"])),
        "generated_edge_count": None if graph is None else len(graph["edges"]),
        "reachable_state_count": None,
        "reachable_live_state_count": None,
        "t65_relaxed_certificate": None,
        "violating_recurrent_scc_witness": None,
        "finite_experimental_verdict": None,
        "evidence_scope": FINITE_ONLY,
    }


def _evaluate_instance(spec, caps):
    word = spec["word"]
    depth = spec["depth"]
    graph = t52.build_reachable(
        word, depth, caps["state_cap"], caps["time_cap_seconds"])
    if not graph["complete"]:
        return frontier_row(spec, caps, graph["stop_reason"], graph)

    table = t52.kmp_data(word)["transition_table_rows_state_columns_digit_0_to_9"]
    for edge in graph["edges"]:
        t52.validate_edge(edge, graph["states"], word, depth, table)
    certificate, witness, live = analyze_relaxed_t65(graph)
    criterion = certificate["criterion"]
    return {
        "instance_order": spec["instance_order"],
        "cohort": spec["cohort"],
        "word": word,
        "word_length": len(word),
        "depth_R": depth,
        "declared_state_count_including_root": 1 + len(word) ** (depth + 1) * 18 ** depth,
        "caps": caps,
        "status": "completed",
        "resource_stop_reason": None,
        "discovered_state_count_including_root": len(graph["states"]),
        "generated_edge_count": len(graph["edges"]),
        "reachable_state_count": len(graph["states"]),
        "reachable_live_state_count": len(live),
        "t65_relaxed_certificate": certificate,
        "violating_recurrent_scc_witness": witness,
        "finite_experimental_verdict": (
            "t65_relaxed_criterion_pass" if criterion
            else "t65_relaxed_criterion_failure"
        ),
        "evidence_scope": FINITE_ONLY,
    }


def evaluate_instance(spec, caps):
    def timeout_handler(_signum, _frame):
        raise t52.ResourceStop("time_cap")

    old_handler = signal.getsignal(signal.SIGALRM)
    signal.signal(signal.SIGALRM, timeout_handler)
    try:
        signal.setitimer(signal.ITIMER_REAL, caps["time_cap_seconds"])
        return _evaluate_instance(spec, caps)
    except t52.ResourceStop as stop:
        if stop.reason != "time_cap":
            raise
        return frontier_row(spec, caps, "time_cap")
    finally:
        signal.setitimer(signal.ITIMER_REAL, 0)
        signal.signal(signal.SIGALRM, old_handler)


def load_and_validate_config(directory):
    assert sha256(directory / "pi-positive-decimal-factor-entropy.txt") == STATEMENT_SHA256
    config = json.loads((directory / "instances.json").read_text(encoding="ascii"))
    assert config["format_version"] == FORMAT_VERSION
    for source in config["source_dependencies"]:
        assert sha256(directory / source["file"]) == source["sha256"]
    actual_baseline = [
        (row["word"], row["depth"])
        for row in config["instances"] if row["cohort"] == "t52_completed_baseline"
    ]
    actual_extension = [
        (row["word"], row["depth"])
        for row in config["instances"] if row["cohort"] == "deterministic_extension"
    ]
    assert actual_baseline == BASELINE
    assert actual_extension == EXTENSION
    assert len(set(actual_baseline + actual_extension)) == len(actual_baseline + actual_extension)
    assert config["caps"]["state_cap"] > 0
    assert config["caps"]["time_cap_seconds"] > 0
    return config


def evaluate_manifest(config):
    instances = []
    for order, raw_spec in enumerate(config["instances"]):
        spec = dict(raw_spec)
        spec["instance_order"] = order
        instances.append(evaluate_instance(spec, config["caps"]))
    return instances


def summarize(instances):
    summary = {
        "baseline_completed": 0,
        "baseline_pass": 0,
        "baseline_failure": 0,
        "baseline_resource_frontier": 0,
        "extension_completed": 0,
        "extension_pass": 0,
        "extension_failure": 0,
        "extension_resource_frontier": 0,
    }
    for row in instances:
        prefix = "baseline" if row["cohort"] == "t52_completed_baseline" else "extension"
        if row["status"] == "resource_frontier":
            summary[f"{prefix}_resource_frontier"] += 1
        else:
            summary[f"{prefix}_completed"] += 1
            verdict = row["finite_experimental_verdict"].removeprefix(
                "t65_relaxed_criterion_")
            summary[f"{prefix}_{verdict}"] += 1
    return summary


def write_table(directory, instances):
    fields = [
        "instance_order", "cohort", "word", "word_length", "depth_R", "status",
        "declared_state_count_including_root", "reachable_state_count",
        "reachable_live_state_count", "generated_edge_count",
        "finite_experimental_verdict", "resource_stop_reason",
    ]
    with (directory / "instance_table.csv").open("w", newline="", encoding="ascii") as handle:
        writer = csv.DictWriter(handle, fieldnames=fields)
        writer.writeheader()
        for row in instances:
            writer.writerow({field: row.get(field) for field in fields})


def generate(directory):
    config = load_and_validate_config(directory)
    instances = evaluate_manifest(config)
    result = {
        "format_version": FORMAT_VERSION,
        "item": "T66",
        "status": "experiment",
        "canonical_statement_sha256": STATEMENT_SHA256,
        "graph_convention": "kernel-checked T48 endpoint-complete carry/KMP graph",
        "predicate_convention": (
            "kernel-checked T65 RelaxedLiveSCCCriterion: T46 terminality omitted; "
            "internal simple-cycle uniqueness retained; projected determinism replayed"
        ),
        "caps": config["caps"],
        "baseline_definition": config["baseline_definition"],
        "extension_order_rule": config["extension_order_rule"],
        "source_dependencies": config["source_dependencies"],
        "summary": summarize(instances),
        "instances": instances,
        "claim_label": "experiment",
        "universal_nonclaim": FINITE_ONLY,
    }
    (directory / "results.json").write_bytes(canonical_json(result))
    write_table(directory, instances)


def verify(directory):
    config = load_and_validate_config(directory)
    result = json.loads((directory / "results.json").read_text(encoding="ascii"))
    assert result["item"] == "T66" and result["claim_label"] == "experiment"
    assert result["universal_nonclaim"] == FINITE_ONLY
    expected_instances = evaluate_manifest(config)
    assert result["instances"] == expected_instances
    assert result["summary"] == summarize(expected_instances)
    for row in result["instances"]:
        if row["status"] == "resource_frontier":
            assert row["reachable_state_count"] is None
            assert row["reachable_live_state_count"] is None
            assert row["t65_relaxed_certificate"] is None
            assert row["violating_recurrent_scc_witness"] is None
            assert row["finite_experimental_verdict"] is None
        else:
            certificate = row["t65_relaxed_certificate"]
            assert row["reachable_state_count"] == certificate["reachable_state_count"]
            assert row["reachable_live_state_count"] == certificate["reachable_live_state_count"]
            if certificate["criterion"]:
                assert row["finite_experimental_verdict"] == "t65_relaxed_criterion_pass"
                assert row["violating_recurrent_scc_witness"] is None
                assert all(
                    check["internal_simple_cycle_condition"]
                    and check["projected_label_determinism"]
                    for check in certificate["cyclic_reachable_live_scc_checks"])
            else:
                assert row["finite_experimental_verdict"] == "t65_relaxed_criterion_failure"
                assert row["violating_recurrent_scc_witness"] is not None
    timeout_spec = {
        "instance_order": 0,
        "cohort": "deterministic_extension",
        "word": "010",
        "depth": 3,
    }
    timeout_probe = evaluate_instance(
        timeout_spec, {"state_cap": 1_000_000, "time_cap_seconds": 0.000001})
    assert timeout_probe["status"] == "resource_frontier"
    assert timeout_probe["resource_stop_reason"] == "time_cap"
    assert timeout_probe["finite_experimental_verdict"] is None
    summary = result["summary"]
    print(f"verified baseline completed: {summary['baseline_completed']}")
    print(f"verified baseline T65 passes: {summary['baseline_pass']}")
    print(f"verified baseline T65 failures: {summary['baseline_failure']}")
    print(f"verified extension completed: {summary['extension_completed']}")
    print(f"verified extension T65 passes: {summary['extension_pass']}")
    print(f"verified extension T65 failures: {summary['extension_failure']}")
    print(f"verified extension resource frontiers: {summary['extension_resource_frontier']}")
    print("verified every pass certificate and every failure recurrent-SCC witness")
    print("verified capped rows carry no mathematical classification")
    print("ALL T66 CHECKS PASSED -- FINITE EXPERIMENTAL EVIDENCE ONLY")


def replay(directory):
    with tempfile.TemporaryDirectory(prefix="t66-replay-") as temporary:
        target = Path(temporary)
        inputs = (
            "t66_experiment.py", "t52_experiment.py", "instances.json",
            "pi-positive-decimal-factor-entropy.txt", "T46T46LiveSCC.lean",
            "T48EndpointCarryKMP.lean", "T65RationalCoreCertificate.lean",
        )
        for name in inputs:
            shutil.copy2(directory / name, target / name)
        generate(target)
        for name in GENERATED_FILES:
            if (target / name).read_bytes() != (directory / name).read_bytes():
                raise AssertionError(f"regenerated artifact differs: {name}")
        verify(target)
    print("artifact-only regeneration matched byte-for-byte")


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("mode", choices=("generate", "verify", "replay"))
    parser.add_argument("--directory", type=Path, default=Path(__file__).resolve().parent)
    arguments = parser.parse_args()
    if arguments.mode == "generate":
        generate(arguments.directory)
    elif arguments.mode == "verify":
        verify(arguments.directory)
    else:
        replay(arguments.directory)


if __name__ == "__main__":
    main()
