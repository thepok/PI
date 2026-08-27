#!/usr/bin/env python3
"""Decide T68's projected primitive-phase criterion on finite T48 graphs.

Every generated classification is finite experimental evidence only.  In
particular, this program does not prove a uniform depth hypothesis, C6, C1,
or any new statement about pi.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
import shutil
import sys
import tempfile
from collections import deque
from pathlib import Path

sys.dont_write_bytecode = True

import t52_experiment as t52


FORMAT_VERSION = 1
STATEMENT_SHA256 = "a70dd741b27595aeb3dfc902b5e201579fed6bae24e2191f58c5ac64a22939e6"
SOURCE_HASHES = {
    "T46T46LiveSCC.lean": "9e35511d20b9997e7fd98eaf54bfb3eb3b2e53f42b720d962b671b128bf61ec8",
    "T48EndpointCarryKMP.lean": "cbe1652c833fb21ae2618aedbc3040a2f29a7db5b310a9f3873536c888c4b211",
    "T65RationalCoreCertificate.lean": "6ee5b2a7e35405340fc82e4232582c743b820b89b9c5c73a9598e485b48bcba8",
    "t52_experiment.py": "5b5d790f623b2e51fa9b6babf48c483bc4e633afafdf1047aaa84e468054e0a0",
    "t66_instance_table.csv": "ed3529167b13d291161a9eae1ff38f6125f992ebb6baf2fc734920b9b1b70fe1",
}
GENERATED_FILES = ("results.json", "instance_table.csv")
FINITE_ONLY = (
    "experiment: 34 replayed finite T48 instances only; no bounded census "
    "proves a uniform linear-depth hypothesis, C6, C1, or a fact about pi"
)


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1 << 20), b""):
            digest.update(block)
    return digest.hexdigest()


def canonical_json(value) -> bytes:
    return (json.dumps(value, indent=2, sort_keys=True) + "\n").encode("ascii")


def records_hash(value) -> str:
    return hashlib.sha256(canonical_json(value)).hexdigest()


def projected_digit(edge) -> int:
    """T48/T65 projection: coordinate zero of Label.digits."""
    digits = edge[4]
    assert digits
    return digits[0]


def divisors(n: int) -> list[int]:
    assert n > 0
    return [value for value in range(1, n + 1) if n % value == 0]


def least_word_period(word: list[int]) -> int:
    assert word
    for period in divisors(len(word)):
        if all(word[index] == word[index % period] for index in range(len(word))):
            return period
    raise AssertionError("the full word is always a period")


def validate_edge_path(path, graph, start, end, allowed=None):
    edges = graph["edges"]
    allowed_set = None if allowed is None else set(allowed)
    if not path:
        assert start == end
        return
    assert edges[path[0]][0] == start
    assert edges[path[-1]][1] == end
    for first, second in zip(path, path[1:]):
        assert edges[first][1] == edges[second][0]
    if allowed_set is not None:
        assert all(
            edges[edge_id][0] in allowed_set and edges[edge_id][1] in allowed_set
            for edge_id in path
        )


def internal_edge_ids(component, graph):
    component_set = set(component)
    return [
        edge_id
        for source in component
        for edge_id in graph["outgoing"][source]
        if graph["edges"][edge_id][1] in component_set
    ]


def forced_phases(component, graph, period):
    """Propagate phase(dst)=phase(src)+1 mod period from phase(root)=0."""
    root = component[0]
    component_set = set(component)
    phase = {root: 0}
    path = {root: []}
    queue = deque([root])
    while queue:
        source = queue.popleft()
        for edge_id in graph["outgoing"][source]:
            target = graph["edges"][edge_id][1]
            if target not in component_set:
                continue
            expected = (phase[source] + 1) % period
            proposed_path = path[source] + [edge_id]
            if target not in phase:
                phase[target] = expected
                path[target] = proposed_path
                queue.append(target)
            elif phase[target] != expected:
                return None, None, {
                    "kind": "phase_advance_conflict",
                    "period": period,
                    "endpoint_state_id": target,
                    "first_path_edge_ids": path[target],
                    "first_path_length_mod_period": len(path[target]) % period,
                    "second_path_edge_ids": proposed_path,
                    "second_path_length_mod_period": len(proposed_path) % period,
                }
    assert set(phase) == component_set
    return phase, path, None


def check_period(component, graph, period):
    phase, paths, conflict = forced_phases(component, graph, period)
    if conflict is not None:
        return None, conflict

    symbols = [None] * period
    symbol_edge = [None] * period
    symbol_source = [None] * period
    for edge_id in internal_edge_ids(component, graph):
        edge = graph["edges"][edge_id]
        source = edge[0]
        residue = phase[source]
        digit = projected_digit(edge)
        if symbols[residue] is None:
            symbols[residue] = digit
            symbol_edge[residue] = edge_id
            symbol_source[residue] = source
        elif symbols[residue] != digit:
            first_source = symbol_source[residue]
            return None, {
                "kind": "projected_digit_conflict",
                "period": period,
                "phase": residue,
                "first_source_state_id": first_source,
                "first_source_path_edge_ids": paths[first_source],
                "first_edge_id": symbol_edge[residue],
                "first_projected_digit": symbols[residue],
                "second_source_state_id": source,
                "second_source_path_edge_ids": paths[source],
                "second_edge_id": edge_id,
                "second_projected_digit": digit,
            }

    # A positive closed walk has length divisible by period and visits every
    # residue, so a successful phase propagation cannot leave a symbol unseen.
    assert all(symbol is not None for symbol in symbols)
    primitive_period = least_word_period(symbols)
    if primitive_period != period:
        return None, {
            "kind": "nonprimitive_forced_word",
            "period": period,
            "forced_word": "".join(map(str, symbols)),
            "proper_period": primitive_period,
            "primitive_root": "".join(map(str, symbols[:primitive_period])),
        }

    certificate = {
        "period": period,
        "primitive_word": "".join(map(str, symbols)),
        "phase_by_state": [
            {"state_id": state, "phase": phase[state]} for state in component
        ],
        "internal_edge_count": len(internal_edge_ids(component, graph)),
        "internal_edges_sha256": records_hash([
            {
                "edge_id": edge_id,
                "src": graph["edges"][edge_id][0],
                "dst": graph["edges"][edge_id][1],
                "projected_digit": projected_digit(graph["edges"][edge_id]),
            }
            for edge_id in internal_edge_ids(component, graph)
        ]),
    }
    return certificate, None


def analyze_component(component, graph):
    root = component[0]
    anchor = t52.closed_cycle(
        root, component, graph["edges"], graph["outgoing"]
    )
    validate_edge_path(anchor, graph, root, root, component)
    rejections = []
    for period in divisors(len(anchor)):
        certificate, rejection = check_period(component, graph, period)
        if certificate is not None:
            return {
                "state_ids": component,
                "criterion": True,
                "anchor_closed_walk_edge_ids": anchor,
                "anchor_projected_word": "".join(
                    str(projected_digit(graph["edges"][edge_id])) for edge_id in anchor
                ),
                "certificate": certificate,
                "period_rejections": rejections,
            }
        rejections.append(rejection)
    return {
        "state_ids": component,
        "criterion": False,
        "anchor_closed_walk_edge_ids": anchor,
        "anchor_projected_word": "".join(
            str(projected_digit(graph["edges"][edge_id])) for edge_id in anchor
        ),
        "certificate": None,
        "period_rejections": rejections,
    }


def validate_rejection(rejection, component, graph):
    period = rejection["period"]
    root = component[0]
    if rejection["kind"] == "phase_advance_conflict":
        first = rejection["first_path_edge_ids"]
        second = rejection["second_path_edge_ids"]
        endpoint = rejection["endpoint_state_id"]
        validate_edge_path(first, graph, root, endpoint, component)
        validate_edge_path(second, graph, root, endpoint, component)
        assert len(first) % period == rejection["first_path_length_mod_period"]
        assert len(second) % period == rejection["second_path_length_mod_period"]
        assert len(first) % period != len(second) % period
    elif rejection["kind"] == "projected_digit_conflict":
        first_source = rejection["first_source_state_id"]
        second_source = rejection["second_source_state_id"]
        validate_edge_path(
            rejection["first_source_path_edge_ids"], graph, root, first_source, component
        )
        validate_edge_path(
            rejection["second_source_path_edge_ids"], graph, root, second_source, component
        )
        assert len(rejection["first_source_path_edge_ids"]) % period == rejection["phase"]
        assert len(rejection["second_source_path_edge_ids"]) % period == rejection["phase"]
        first_edge = graph["edges"][rejection["first_edge_id"]]
        second_edge = graph["edges"][rejection["second_edge_id"]]
        assert first_edge[0] == first_source and second_edge[0] == second_source
        assert first_edge[1] in component and second_edge[1] in component
        assert projected_digit(first_edge) == rejection["first_projected_digit"]
        assert projected_digit(second_edge) == rejection["second_projected_digit"]
        assert rejection["first_projected_digit"] != rejection["second_projected_digit"]
    else:
        assert rejection["kind"] == "nonprimitive_forced_word"
        word = [int(digit) for digit in rejection["forced_word"]]
        assert len(word) == period
        proper = rejection["proper_period"]
        assert 0 < proper < period and period % proper == 0
        assert least_word_period(word) == proper
        assert rejection["primitive_root"] == "".join(map(str, word[:proper]))


def validate_component_result(result, component, graph):
    assert result["state_ids"] == component
    anchor = result["anchor_closed_walk_edge_ids"]
    validate_edge_path(anchor, graph, component[0], component[0], component)
    assert result["anchor_projected_word"] == "".join(
        str(projected_digit(graph["edges"][edge_id])) for edge_id in anchor
    )
    candidate_periods = divisors(len(anchor))
    for rejection in result["period_rejections"]:
        assert rejection["period"] in candidate_periods
        validate_rejection(rejection, component, graph)
    if result["criterion"]:
        certificate = result["certificate"]
        assert certificate is not None
        assert candidate_periods[len(result["period_rejections"])] == certificate["period"]
        rebuilt, rejection = check_period(component, graph, certificate["period"])
        assert rejection is None and rebuilt == certificate
    else:
        assert result["certificate"] is None
        assert [entry["period"] for entry in result["period_rejections"]] == candidate_periods


def analyze_graph(graph):
    components = t52.tarjan_scc(
        len(graph["states"]), graph["edges"], graph["outgoing"]
    )
    live = t52.live_vertices(
        len(graph["states"]), graph["edges"], graph["outgoing"]
    )
    recurrent = [
        component
        for component in components
        if component[0] in live
        and t52.cyclic_component(component, graph["edges"], graph["outgoing"])
    ]
    checks = [analyze_component(component, graph) for component in recurrent]
    for result, component in zip(checks, recurrent):
        validate_component_result(result, component, graph)
    criterion = all(check["criterion"] for check in checks)
    failure = None
    if not criterion:
        failed = next(check for check in checks if not check["criterion"])
        failure = {
            "kind": "projected_phase_incompatibility",
            "explanation": (
                "the anchor closed-walk length restricts the primitive period to its "
                "positive divisors; every divisor has the replayed finite rejection below"
            ),
            "scc_state_ids": failed["state_ids"],
            "anchor_closed_walk_edge_ids": failed["anchor_closed_walk_edge_ids"],
            "anchor_projected_word": failed["anchor_projected_word"],
            "period_rejections": failed["period_rejections"],
        }
    return {
        "criterion": criterion,
        "reachable_live_state_count": len(live),
        "reachable_live_state_ids_sha256": t52.table_hash(live),
        "cyclic_reachable_live_scc_count": len(recurrent),
        "component_checks": checks,
    }, failure


def load_t66_rows(directory):
    assert sha256(directory / "pi-positive-decimal-factor-entropy.txt") == STATEMENT_SHA256
    for name, expected in SOURCE_HASHES.items():
        assert sha256(directory / name) == expected
    with (directory / "t66_instance_table.csv").open(newline="", encoding="ascii") as handle:
        rows = list(csv.DictReader(handle))
    assert len(rows) == 44
    assert [int(row["instance_order"]) for row in rows] == list(range(44))
    completed = [row for row in rows if row["status"] == "completed"]
    frontiers = [row for row in rows if row["status"] == "resource_frontier"]
    assert len(completed) == 34 and len(frontiers) == 10
    assert all(row["finite_experimental_verdict"] == "" for row in frontiers)
    assert all(row["resource_stop_reason"] == "state_cap" for row in frontiers)
    return rows, completed, frontiers


def evaluate_row(raw):
    word = raw["word"]
    depth = int(raw["depth_R"])
    declared = int(raw["declared_state_count_including_root"])
    graph = t52.build_reachable(word, depth, declared + 1, 120)
    assert graph["complete"]
    table = t52.kmp_data(word)["transition_table_rows_state_columns_digit_0_to_9"]
    for edge in graph["edges"]:
        t52.validate_edge(edge, graph["states"], word, depth, table)
    assert len(graph["states"]) == int(raw["reachable_state_count"])
    assert len(graph["edges"]) == int(raw["generated_edge_count"])
    analysis, failure = analyze_graph(graph)
    assert analysis["reachable_live_state_count"] == int(raw["reachable_live_state_count"])
    return {
        "t66_instance_order": int(raw["instance_order"]),
        "cohort": raw["cohort"],
        "word": word,
        "word_length": len(word),
        "depth_R": depth,
        "reachable_state_count": len(graph["states"]),
        "reachable_live_state_count": analysis["reachable_live_state_count"],
        "generated_edge_count": len(graph["edges"]),
        "projected_phase_certificate": analysis,
        "failure_witness": failure,
        "finite_experimental_verdict": (
            "projected_primitive_phase_pass"
            if analysis["criterion"]
            else "projected_primitive_phase_failure"
        ),
        "evidence_scope": FINITE_ONLY,
    }


def summarize(instances):
    return {
        "completed_replayed": len(instances),
        "projected_primitive_phase_pass": sum(
            row["projected_phase_certificate"]["criterion"] for row in instances
        ),
        "projected_primitive_phase_failure": sum(
            not row["projected_phase_certificate"]["criterion"] for row in instances
        ),
        "t66_resource_frontiers_not_classified": 10,
    }


def verify_hidden_branching_probe():
    """A strongly connected branch passes because only its projection matters."""
    graph = {
        "states": ["phase0", "phase1-left", "phase1-right"],
        "edges": [
            (0, 1, "next", (), (0,)),
            (0, 2, "next", (), (0,)),
            (1, 0, "next", (), (1,)),
            (2, 0, "next", (), (1,)),
        ],
        "outgoing": [[0, 1], [2], [3]],
    }
    analysis, failure = analyze_graph(graph)
    assert failure is None and analysis["criterion"]
    checks = analysis["component_checks"]
    assert len(checks) == 1
    certificate = checks[0]["certificate"]
    assert certificate["period"] == 2
    assert certificate["primitive_word"] == "01"


def write_table(directory, instances):
    fields = [
        "t66_instance_order", "cohort", "word", "word_length", "depth_R",
        "reachable_state_count", "reachable_live_state_count", "generated_edge_count",
        "cyclic_reachable_live_scc_count", "finite_experimental_verdict",
        "failure_witness_kind",
    ]
    with (directory / "instance_table.csv").open("w", newline="", encoding="ascii") as handle:
        writer = csv.DictWriter(handle, fieldnames=fields)
        writer.writeheader()
        for row in instances:
            writer.writerow({
                **{field: row.get(field) for field in fields},
                "cyclic_reachable_live_scc_count": row["projected_phase_certificate"][
                    "cyclic_reachable_live_scc_count"
                ],
                "failure_witness_kind": (
                    "" if row["failure_witness"] is None else row["failure_witness"]["kind"]
                ),
            })


def generate(directory):
    _rows, completed, _frontiers = load_t66_rows(directory)
    instances = [evaluate_row(row) for row in completed]
    result = {
        "format_version": FORMAT_VERSION,
        "item": "T68",
        "claim_label": "experiment",
        "canonical_statement_sha256": STATEMENT_SHA256,
        "graph_convention": "byte-exact kernel-checked T48 endpoint carry/KMP source",
        "projection_convention": (
            "coordinate zero of T48 Label.digits, exactly as T48 graphEvaluation and "
            "T65 graphEvaluation_exists_rational_real_of_eventuallyPeriodic"
        ),
        "criterion": (
            "each reachable-live cyclic SCC admits a primitive projected word and a "
            "vertex phase such that every internal edge emits its source-phase digit "
            "and advances phase by one"
        ),
        "source_dependencies": [
            {"file": name, "sha256": digest} for name, digest in SOURCE_HASHES.items()
        ],
        "summary": summarize(instances),
        "instances": instances,
        "universal_nonclaim": FINITE_ONLY,
    }
    (directory / "results.json").write_bytes(canonical_json(result))
    write_table(directory, instances)


def replay(directory):
    inputs = (
        "t68_projection.py", "t52_experiment.py", "t66_instance_table.csv",
        "pi-positive-decimal-factor-entropy.txt", "T46T46LiveSCC.lean",
        "T48EndpointCarryKMP.lean", "T65RationalCoreCertificate.lean",
    )
    with tempfile.TemporaryDirectory(prefix="t68-replay-") as temporary:
        target = Path(temporary)
        for name in inputs:
            shutil.copy2(directory / name, target / name)
        generate(target)
        for name in GENERATED_FILES:
            if (target / name).read_bytes() != (directory / name).read_bytes():
                raise AssertionError(f"regenerated artifact differs: {name}")
        result = json.loads((target / "results.json").read_text(encoding="ascii"))
    verify_hidden_branching_probe()
    summary = result["summary"]
    print("verified projected criterion accepts a three-state hidden-branching probe")
    print(f"verified completed T66 instances replayed: {summary['completed_replayed']}")
    print(f"verified projected primitive-phase passes: {summary['projected_primitive_phase_pass']}")
    print(f"verified projected primitive-phase failures: {summary['projected_primitive_phase_failure']}")
    print("verified a finite projected phase-incompatibility witness for every failure")
    print("verified 10 T66 resource-frontier rows remain unclassified")
    print("artifact-only regeneration matched byte-for-byte")
    print("ALL T68 CHECKS PASSED -- FINITE EXPERIMENTAL EVIDENCE ONLY")


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("mode", choices=("generate", "replay"))
    parser.add_argument("--directory", type=Path, default=Path(__file__).resolve().parent)
    arguments = parser.parse_args()
    if arguments.mode == "generate":
        generate(arguments.directory)
    else:
        replay(arguments.directory)


if __name__ == "__main__":
    main()
