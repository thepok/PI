#!/usr/bin/env python3
"""Replay T53 depth truncation and strict one-step witness lift checks.

Only exact integer operations and Python's standard library are used.  T44,
T46, and T48 are pinned machine-checked dependencies.  T52 supplies only the
finite witness instances regenerated and checked here.
"""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import shutil
import tempfile
from collections import deque
from pathlib import Path


HERE = Path(__file__).resolve().parent
EXPECTED_HASHES = {
    "pi-positive-decimal-factor-entropy.txt": "a70dd741b27595aeb3dfc902b5e201579fed6bae24e2191f58c5ac64a22939e6",
    "t52_experiment.py": "5b5d790f623b2e51fa9b6babf48c483bc4e633afafdf1047aaa84e468054e0a0",
    "t52_results.json": "b7b3757c0450c31eb41c29545cfaee47477348342b9435d493821c74ec8411f1",
    "T44EndpointSafeInvariantCore.lean": "0157022e5125d130a8e12d1e40e97ee9e3df10fb3aa179c8a1cacbdaace59083",
    "T46T46LiveSCC.lean": "9e35511d20b9997e7fd98eaf54bfb3eb3b2e53f42b720d962b671b128bf61ec8",
    "T48EndpointCarryKMP.lean": "cbe1652c833fb21ae2618aedbc3040a2f29a7db5b310a9f3873536c888c4b211",
}


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1 << 20), b""):
            digest.update(block)
    return digest.hexdigest()


def canonical_bytes(value) -> bytes:
    return (json.dumps(value, indent=2, sort_keys=True) + "\n").encode("ascii")


def value_hash(values) -> str:
    return hashlib.sha256(json.dumps(values, sort_keys=True, separators=(",", ":")).encode("ascii")).hexdigest()


def load_t52(directory: Path):
    spec = importlib.util.spec_from_file_location("t53_vendored_t52", directory / "t52_experiment.py")
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def fibers(word: str):
    return tuple((kmp, carry) for kmp in range(len(word)) for carry in range(-1, 17))


def edge_payload(t52, graph, edge_id: int):
    return t52.edge_json(graph["edges"][edge_id], graph["states"])


def serialized_edge_key(edge) -> str:
    return json.dumps(edge, sort_keys=True, separators=(",", ":"))


def witness_paths(witness):
    if witness["classification"] == "branching_cyclic_scc":
        return {
            "start_to_branch_path": witness["start_to_branch_path"],
            "first_closed_walk": witness["first_closed_walk"],
            "second_closed_walk": witness["second_closed_walk"],
        }
    return {
        "start_to_exit_source_path": witness["start_to_exit_source_path"],
        "exit_edge": [witness["exit_edge"]],
        "target_to_cycle_path": witness["target_to_cycle_path"],
        "target_continuation_cycle": witness["target_continuation_cycle"],
    }


def validate_source_witness(t52, instance, graph):
    witness = instance["bad_scc_witness"]
    lookup = {serialized_edge_key(edge_payload(t52, graph, edge_id)): edge_id
              for edge_id in range(len(graph["edges"]))}
    paths = witness_paths(witness)
    for path in paths.values():
        t52.validate_path(path)
        for edge in path:
            key = serialized_edge_key(edge)
            assert key in lookup
            assert edge_payload(t52, graph, lookup[key]) == edge
    certificate, regenerated, live, components = t52.analyze_complete(graph)
    assert certificate == instance["t48_t46_boolean_certificate"]
    assert regenerated == witness
    t52.validate_witness(witness, graph, live, components)
    return lookup, live, components


def initial_choices(word, table, final_digit, target_fiber):
    target_kmp, target_carry = target_fiber
    result = []
    for initial_carry in range(-1, 17):
        for added_digit in range(10):
            if table[0][added_digit] == len(word):
                continue
            if (table[0][added_digit], added_digit + 10 * initial_carry - 16 * final_digit) == target_fiber:
                result.append((initial_carry, added_digit))
    return tuple(result)


def next_added_digit(word, table, final_digit, source_fiber, target_fiber):
    source_kmp, source_carry = source_fiber
    target_kmp, target_carry = target_fiber
    result = []
    for added_digit in range(10):
        if table[source_kmp][added_digit] == len(word):
            continue
        if table[source_kmp][added_digit] == target_kmp and \
                added_digit + 10 * source_carry - 16 * final_digit == target_carry:
            result.append(added_digit)
    assert len(result) <= 1
    return None if not result else result[0]


def build_constraints(t52, word, graph, witness, lookup):
    table = t52.kmp_data(word)["transition_table_rows_state_columns_digit_0_to_9"]
    fiber_values = fibers(word)
    variables = sorted({edge[key]["kind"] == "raw" and edge[f"{key}_id"] or None
                        for path in witness_paths(witness).values()
                        for edge in path for key in ("src", "dst")} - {None})
    constraints = []
    seen = {}
    for path_name, path in witness_paths(witness).items():
        for occurrence, serialized in enumerate(path):
            key = serialized_edge_key(serialized)
            edge_id = lookup[key]
            if edge_id in seen:
                constraints[seen[edge_id]]["occurrences"].append([path_name, occurrence])
                continue
            source, target, kind, _carry, digits = graph["edges"][edge_id]
            constraint = {
                "id": len(constraints),
                "base_edge_id": edge_id,
                "kind": kind,
                "src": source,
                "dst": target,
                "final_retained_digit": digits[-1],
                "occurrences": [[path_name, occurrence]],
            }
            if kind == "initial":
                choices = {index: initial_choices(word, table, digits[-1], fiber)
                           for index, fiber in enumerate(fiber_values)}
                constraint["allowed"] = {index for index, options in choices.items() if options}
                constraint["choices"] = choices
            else:
                pairs = set()
                choices = {}
                for source_index, source_fiber in enumerate(fiber_values):
                    for target_index, target_fiber in enumerate(fiber_values):
                        added = next_added_digit(
                            word, table, digits[-1], source_fiber, target_fiber)
                        if added is not None:
                            pairs.add((source_index, target_index))
                            choices[(source_index, target_index)] = added
                constraint["pairs"] = pairs
                constraint["choices"] = choices
            seen[edge_id] = len(constraints)
            constraints.append(constraint)
    return variables, fiber_values, constraints


def product_cyclic_data(t52, word, graph, source_id, target_id, fiber_values):
    components = t52.tarjan_scc(len(graph["states"]), graph["edges"], graph["outgoing"])
    component_of = {state: index for index, component in enumerate(components) for state in component}
    assert component_of[source_id] != component_of[target_id]
    base_component = components[component_of[source_id]]
    base_set = set(base_component)
    table = t52.kmp_data(word)["transition_table_rows_state_columns_digit_0_to_9"]
    fiber_index = {fiber: index for index, fiber in enumerate(fiber_values)}
    nodes = [(state, index) for state in base_component for index in range(len(fiber_values))]
    node_index = {node: index for index, node in enumerate(nodes)}
    product_edges = []
    outgoing = [[] for _ in nodes]
    attempts = 0
    for base_source in base_component:
        for source_fiber_id, source_fiber in enumerate(fiber_values):
            product_source = node_index[(base_source, source_fiber_id)]
            for base_edge_id in graph["outgoing"][base_source]:
                base_edge = graph["edges"][base_edge_id]
                if base_edge[1] not in base_set:
                    continue
                final_digit = base_edge[4][-1]
                for added_digit in range(10):
                    attempts += 1
                    target_kmp = table[source_fiber[0]][added_digit]
                    target_carry = added_digit + 10 * source_fiber[1] - 16 * final_digit
                    if target_kmp == len(word) or not -1 <= target_carry <= 16:
                        continue
                    target_fiber = (target_kmp, target_carry)
                    product_target = node_index[(base_edge[1], fiber_index[target_fiber])]
                    edge_id = len(product_edges)
                    product_edges.append((product_source, product_target, base_edge_id, added_digit))
                    outgoing[product_source].append(edge_id)
    product_components = t52.tarjan_scc(len(nodes), product_edges, outgoing)
    cyclic_components = [component for component in product_components
                         if t52.cyclic_component(component, product_edges, outgoing)]
    cyclic_nodes = {node for component in cyclic_components for node in component}
    allowed = {fiber_id for fiber_id in range(len(fiber_values))
               if node_index[(source_id, fiber_id)] in cyclic_nodes}
    component_of_product = {node: component for component in cyclic_components for node in component}
    return {
        "allowed": allowed,
        "base_scc_size": len(base_component),
        "product_vertex_count": len(nodes),
        "product_edge_count": len(product_edges),
        "transition_attempts": attempts,
        "nodes": nodes,
        "node_index": node_index,
        "edges": product_edges,
        "outgoing": outgoing,
        "cyclic_component_of": component_of_product,
    }


def constraint_summary(constraint):
    base = {
        "id": constraint["id"],
        "base_edge_id": constraint["base_edge_id"],
        "kind": constraint["kind"],
        "src": constraint["src"],
        "dst": constraint["dst"],
        "final_retained_digit": constraint["final_retained_digit"],
        "occurrences": constraint["occurrences"],
    }
    if constraint["kind"] == "initial":
        values = sorted(constraint["allowed"])
        base.update({"allowed_count": len(values), "allowed_sha256": value_hash(values)})
    else:
        values = [list(pair) for pair in sorted(constraint["pairs"])]
        base.update({"pair_count": len(values), "pairs_sha256": value_hash(values)})
    return base


def propagate(domains, constraints, unary, trace):
    domains = {variable: set(values) for variable, values in domains.items()}
    while True:
        changed = False
        for name, variable, allowed in unary:
            before = set(domains[variable])
            domains[variable].intersection_update(allowed)
            if domains[variable] != before:
                trace.append({
                    "constraint": name,
                    "variable": variable,
                    "before_count": len(before),
                    "after": sorted(domains[variable]),
                })
                changed = True
        for constraint in constraints:
            if constraint["kind"] == "initial":
                continue
            source = constraint["src"]
            target = constraint["dst"]
            pairs = constraint["pairs"]
            if source == target:
                allowed = {value for value in domains[source] if (value, value) in pairs}
                before = set(domains[source])
                domains[source].intersection_update(allowed)
                if domains[source] != before:
                    trace.append({
                        "constraint": f"edge:{constraint['id']}:loop",
                        "variable": source,
                        "before_count": len(before),
                        "after": sorted(domains[source]),
                    })
                    changed = True
                continue
            source_allowed = {a for a in domains[source]
                              if any((a, b) in pairs for b in domains[target])}
            before_source = set(domains[source])
            domains[source].intersection_update(source_allowed)
            if domains[source] != before_source:
                trace.append({
                    "constraint": f"edge:{constraint['id']}:forward",
                    "variable": source,
                    "before_count": len(before_source),
                    "after": sorted(domains[source]),
                })
                changed = True
            target_allowed = {b for b in domains[target]
                              if any((a, b) in pairs for a in domains[source])}
            before_target = set(domains[target])
            domains[target].intersection_update(target_allowed)
            if domains[target] != before_target:
                trace.append({
                    "constraint": f"edge:{constraint['id']}:backward",
                    "variable": target,
                    "before_count": len(before_target),
                    "after": sorted(domains[target]),
                })
                changed = True
        if any(not values for values in domains.values()) or not changed:
            return domains


def solve(domains, constraints, unary, statistics):
    trace = []
    reduced = propagate(domains, constraints, unary, trace)
    statistics["propagation_steps"] += len(trace)
    if any(not values for values in reduced.values()):
        statistics["failed_nodes"] += 1
        return None, reduced, trace
    if all(len(values) == 1 for values in reduced.values()):
        return {variable: next(iter(values)) for variable, values in reduced.items()}, reduced, trace
    variable = min((variable for variable in reduced if len(reduced[variable]) > 1),
                   key=lambda item: (len(reduced[item]), item))
    combined_trace = list(trace)
    for value in sorted(reduced[variable]):
        statistics["search_nodes"] += 1
        branch = {item: set(values) for item, values in reduced.items()}
        branch[variable] = {value}
        assignment, final_domains, branch_trace = solve(branch, constraints, unary, statistics)
        combined_trace.extend(branch_trace)
        if assignment is not None:
            return assignment, final_domains, combined_trace
    return None, reduced, combined_trace


def lifted_state(graph, state_id, fiber_values, fiber_id):
    state = graph["states"][state_id]
    assert state is not None
    hidden_kmp, hidden_carry = fiber_values[fiber_id]
    return {"kind": "raw", "kmp": list(state[0]) + [hidden_kmp],
            "carry": list(state[1]) + [hidden_carry]}


def lifted_edge(t52, graph, constraint, assignment, fiber_values, forced_added=None):
    base_edge = graph["edges"][constraint["base_edge_id"]]
    source, target, kind, initial_carries, digits = base_edge
    target_fiber_id = assignment[target]
    if kind == "initial":
        initial_carry, added_digit = min(constraint["choices"][target_fiber_id])
        source_payload = {"kind": "synthetic_root"}
        carries = list(initial_carries) + [initial_carry]
    else:
        source_fiber_id = assignment[source]
        added_digit = constraint["choices"][(source_fiber_id, target_fiber_id)]
        source_payload = lifted_state(graph, source, fiber_values, source_fiber_id)
        carries = []
    if forced_added is not None:
        assert forced_added == added_digit
    label = {"kind": kind, "digits": list(digits) + [added_digit]}
    if kind == "initial":
        label["carry"] = carries
    return {
        "src": source_payload,
        "dst": lifted_state(graph, target, fiber_values, target_fiber_id),
        "label": label,
        "projects_to_base_edge_id": constraint["base_edge_id"],
    }


def validate_lifted_edge(t52, word, depth, lifted, base_serialized):
    assert lifted["src"]["kind"] == base_serialized["src"]["kind"]
    assert lifted["dst"]["kmp"][:-1] == base_serialized["dst"]["kmp"]
    assert lifted["dst"]["carry"][:-1] == base_serialized["dst"]["carry"]
    assert lifted["label"]["digits"][:-1] == base_serialized["label"]["digits"]
    assert lifted["label"]["kind"] == base_serialized["label"]["kind"]
    if lifted["label"]["kind"] == "initial":
        assert lifted["label"]["carry"][:-1] == base_serialized["label"]["carry"]
        source = t52.raw_state((0,) * (depth + 2), tuple(lifted["label"]["carry"]))
    else:
        assert lifted["src"]["kmp"][:-1] == base_serialized["src"]["kmp"]
        assert lifted["src"]["carry"][:-1] == base_serialized["src"]["carry"]
        source = t52.raw_state(tuple(lifted["src"]["kmp"]), tuple(lifted["src"]["carry"]))
    target = t52.raw_state(tuple(lifted["dst"]["kmp"]), tuple(lifted["dst"]["carry"]))
    table = t52.kmp_data(word)["transition_table_rows_state_columns_digit_0_to_9"]
    assert t52.next_raw(word, table, source, tuple(lifted["label"]["digits"])) == target


def product_cycle(product, start_node):
    component = set(product["cyclic_component_of"][start_node])
    edges = product["edges"]
    outgoing = product["outgoing"]
    for first in outgoing[start_node]:
        target = edges[first][1]
        if target not in component:
            continue
        if target == start_node:
            return [first]
        queue = deque([target])
        previous = {target: None}
        while queue and start_node not in previous:
            vertex = queue.popleft()
            for edge_id in outgoing[vertex]:
                next_vertex = edges[edge_id][1]
                if next_vertex in component and next_vertex not in previous:
                    previous[next_vertex] = edge_id
                    queue.append(next_vertex)
        if start_node in previous:
            path = []
            vertex = start_node
            while vertex != target:
                edge_id = previous[vertex]
                path.append(edge_id)
                vertex = edges[edge_id][0]
            path.reverse()
            return [first] + path
    raise AssertionError("cyclic product state has no closed walk")


def serialize_product_cycle(t52, graph, product, cycle, fiber_values):
    result = []
    for product_edge_id in cycle:
        source_node, target_node, base_edge_id, added_digit = product["edges"][product_edge_id]
        source_state, source_fiber = product["nodes"][source_node]
        target_state, target_fiber = product["nodes"][target_node]
        base_edge = graph["edges"][base_edge_id]
        assert base_edge[0] == source_state and base_edge[1] == target_state
        result.append({
            "src": lifted_state(graph, source_state, fiber_values, source_fiber),
            "dst": lifted_state(graph, target_state, fiber_values, target_fiber),
            "label": {"kind": "next", "digits": list(base_edge[4]) + [added_digit]},
            "projects_to_base_edge_id": base_edge_id,
        })
    assert result and result[0]["src"] == result[-1]["dst"]
    return result


def check_instance(t52, instance):
    word = instance["word"]
    depth = instance["depth_R"]
    graph = t52.build_reachable(word, depth, 2500, float("inf"))
    assert graph["complete"] and len(graph["states"]) == instance["reachable_state_count"]
    lookup, _live, _components = validate_source_witness(t52, instance, graph)
    witness = instance["bad_scc_witness"]
    variables, fiber_values, constraints = build_constraints(t52, word, graph, witness, lookup)
    domains = {variable: set(range(len(fiber_values))) for variable in variables}
    unary = []
    for constraint in constraints:
        if constraint["kind"] == "initial":
            unary.append((f"edge:{constraint['id']}:initial", constraint["dst"], constraint["allowed"]))
    product = None
    if witness["classification"] == "nonterminal_delay_corridor":
        source_id = witness["exit_edge"]["src_id"]
        target_id = witness["exit_edge"]["dst_id"]
        product = product_cyclic_data(t52, word, graph, source_id, target_id, fiber_values)
        unary.append(("source_product_cyclicity", source_id, product["allowed"]))
    statistics = {"search_nodes": 0, "failed_nodes": 0, "propagation_steps": 0}
    initial_trace = []
    ac_domains = propagate(domains, constraints, unary, initial_trace)
    assignment, final_domains, search_trace = solve(domains, constraints, unary, statistics)
    base = {
        "instance_order": instance["instance_order"],
        "word": word,
        "from_depth": depth,
        "to_depth": depth + 1,
        "source_witness_classification": witness["classification"],
        "fiber_order": "lexicographic (hidden_kmp, hidden_carry), carry -1 through 16",
        "fiber_values": [list(value) for value in fiber_values],
        "variables_base_state_ids": variables,
        "constraints": [constraint_summary(constraint) for constraint in constraints],
        "arc_consistency_trace": initial_trace,
        "arc_consistency_final_domains": {str(key): sorted(value) for key, value in ac_domains.items()},
        "search_statistics": statistics,
        "strict_lift_meaning": (
            "one global hidden state per state in the stored T52 paths; all stored joins and "
            "closed walks preserved; corridor source cyclicity is an independent high closed walk "
            "based at the assigned exit source"),
    }
    if product is not None:
        base["source_cyclicity_product"] = {
            "base_scc_size": product["base_scc_size"],
            "product_vertex_count": product["product_vertex_count"],
            "product_edge_count": product["product_edge_count"],
            "transition_attempts": product["transition_attempts"],
            "allowed_source_fibers": sorted(product["allowed"]),
            "allowed_source_fibers_sha256": value_hash(sorted(product["allowed"])),
        }
    if assignment is None:
        assert any(not values for values in ac_domains.values())
        base.update({
            "result": "death",
            "death_scope": "this selected finite witness diagram only",
            "exhaustive_reason": "sound arc-consistency reached an empty finite fiber domain",
            "empty_base_state_ids": sorted(key for key, values in ac_domains.items() if not values),
            "alternative_next_depth_witnesses_excluded": False,
        })
        return base
    assignment_json = {str(variable): list(fiber_values[fiber_id])
                       for variable, fiber_id in sorted(assignment.items())}
    lifted_paths = {}
    constraint_by_edge = {constraint["base_edge_id"]: constraint for constraint in constraints}
    for name, path in witness_paths(witness).items():
        lifted_paths[name] = [lifted_edge(t52, graph, constraint_by_edge[lookup[serialized_edge_key(edge)]],
                                                assignment, fiber_values)
                              for edge in path]
        for lifted, base_edge in zip(lifted_paths[name], path):
            validate_lifted_edge(t52, word, depth, lifted, base_edge)
    base.update({
        "result": "lift",
        "assignment_hidden_kmp_carry": assignment_json,
        "lifted_paths": lifted_paths,
        "next_depth_graph_classified": False,
        "infinite_tower_claimed": False,
    })
    if product is not None:
        source_id = witness["exit_edge"]["src_id"]
        start_node = product["node_index"][(source_id, assignment[source_id])]
        cycle = product_cycle(product, start_node)
        base["lifted_source_closed_walk"] = serialize_product_cycle(
            t52, graph, product, cycle, fiber_values)
        for lifted in base["lifted_source_closed_walk"]:
            base_edge = edge_payload(t52, graph, lifted["projects_to_base_edge_id"])
            validate_lifted_edge(t52, word, depth, lifted, base_edge)
    return base


def endpoint_checks():
    valid = []
    minus = []
    plus = []
    for current in range(-1, 17):
        for left in range(10):
            for right in range(10):
                for target in range(-1, 17):
                    if 16 * left + target == right + 10 * current:
                        valid.append((current, left, right, target))
                        if current == -1:
                            minus.append((current, left, right, target))
                        if current == 16:
                            plus.append((current, left, right, target))
    assert minus == [(-1, 0, 9, -1)]
    assert plus == [(16, 9, 0, 16)]
    assert (7, 5, 9, -1) in valid
    assert (8, 4, 0, 16) in valid
    return {
        "valid_digit_carry_quadruples": len(valid),
        "current_minus_one_solutions": [list(value) for value in minus],
        "current_sixteen_solutions": [list(value) for value in plus],
        "backward_absorption_counterexamples": [[7, 5, 9, -1], [8, 4, 0, 16]],
    }


def finite_projection_counterexamples(t52):
    table0 = t52.kmp_data("0")["transition_table_rows_state_columns_digit_0_to_9"]
    current = {(0, carry) for carry in range(-1, 17)}
    corridor_sizes = []
    corridor_values = []
    for retained_digit in (1, 3, 1, 3):
        following = set()
        for source in current:
            for added_digit in range(1, 10):
                target = (table0[source[0]][added_digit],
                          added_digit + 10 * source[1] - 16 * retained_digit)
                if target[0] < 1 and -1 <= target[1] <= 16:
                    following.add(target)
        current = following
        corridor_sizes.append(len(current))
        corridor_values.append([list(value) for value in sorted(current)])
    assert corridor_sizes == [16, 13, 2, 0]

    def run(word, state, columns):
        table = t52.kmp_data(word)["transition_table_rows_state_columns_digit_0_to_9"]
        result = state
        for column in columns:
            result = t52.next_raw(word, table, result, tuple(column))
            assert result is not None
        return result

    branch_state = t52.raw_state((0, 0, 0), (5, 5))
    assert run("0", t52.raw_state((0, 0, 0), (2, 2)), [(1, 1, 1)]) == branch_state
    first_walk = [(3, 3, 1), (3, 2, 5), (2, 2, 4), (6, 1, 1)]
    second_walk = [(3, 3, 2), (3, 2, 1), (2, 5, 5), (8, 9, 5), (7, 7, 7)]
    assert run("0", branch_state, first_walk) == branch_state
    assert run("0", branch_state, second_walk) == branch_state
    first_target = run("0", branch_state, first_walk[:1])
    second_target = run("0", branch_state, second_walk[:1])
    assert first_walk[0][:-1] == second_walk[0][:-1]
    assert first_target[0][:-1] == second_target[0][:-1]
    assert first_target[1][:-1] == second_target[1][:-1]

    corridor_source = t52.raw_state((1, 1, 0), (0, 1))
    source_loop = [(0, 0, 0), (0, 6, 2), (4, 4, 4), (0, 0, 1)]
    assert run("010", corridor_source, source_loop) == corridor_source
    corridor_target = run("010", corridor_source, [(0, 0, 6)])
    assert corridor_target == t52.raw_state((1, 1, 0), (0, 16))
    cycle_state = run("010", corridor_target, [(0, 9, 0), (6, 9, 0), (2, 9, 0), (4, 9, 0)])
    assert cycle_state == t52.raw_state((0, 0, 1), (15, 16))
    assert run("010", cycle_state, [(9, 9, 0)]) == cycle_state
    assert corridor_source[0][:-1] == corridor_target[0][:-1]
    assert corridor_source[1][:-1] == corridor_target[1][:-1]

    graph = t52.build_reachable("0", 1, 100, float("inf"))
    assert graph["complete"]
    live = t52.live_vertices(len(graph["states"]), graph["edges"], graph["outgoing"])
    dead_endpoints = []
    for carry in (-1, 16):
        state = t52.raw_state((0, 0), (carry,))
        state_id = graph["states"].index(state)
        assert state_id not in live
        dead_endpoints.append(state_id)
    low_graph = t52.build_reachable("0", 0, 20, float("inf"))
    assert low_graph["complete"]
    low_state = t52.raw_state((0,), ())
    low_state_id = low_graph["states"].index(low_state)
    low_live = t52.live_vertices(
        len(low_graph["states"]), low_graph["edges"], low_graph["outgoing"])
    low_components = t52.tarjan_scc(
        len(low_graph["states"]), low_graph["edges"], low_graph["outgoing"])
    low_component = next(component for component in low_components if low_state_id in component)
    assert low_state_id in low_live
    assert t52.cyclic_component(low_component, low_graph["edges"], low_graph["outgoing"])

    merge_graph = t52.build_reachable("01", 1, 200, float("inf"))
    assert merge_graph["complete"]
    q_a = t52.raw_state((0, 1), (16,))
    q_b = t52.raw_state((0, 0), (5,))
    q_a_id = merge_graph["states"].index(q_a)
    q_b_id = merge_graph["states"].index(q_b)
    components = t52.tarjan_scc(len(merge_graph["states"]), merge_graph["edges"], merge_graph["outgoing"])
    component_of = {state: index for index, component in enumerate(components) for state in component}
    assert component_of[q_a_id] != component_of[q_b_id]
    assert q_a[0][:-1] == q_b[0][:-1]
    assert run("01", q_a, [(9, 0)]) == q_a
    assert run("01", q_b, [(3, 3)]) == q_b

    reach_graph = t52.build_reachable("00", 1, 200, float("inf"))
    assert reach_graph["complete"]
    unreachable_high = t52.raw_state((0, 1), (-1,))
    assert unreachable_high not in reach_graph["states"]
    reach_graph_low = t52.build_reachable("00", 0, 20, float("inf"))
    assert reach_graph_low["complete"]
    projected_low = t52.raw_state((0,), ())
    assert projected_low in reach_graph_low["states"]

    corridor_graph = t52.build_reachable("010", 2, 2500, float("inf"))
    assert corridor_graph["complete"]
    corridor_source_id = corridor_graph["states"].index(corridor_source)
    corridor_target_id = corridor_graph["states"].index(corridor_target)
    corridor_live = t52.live_vertices(
        len(corridor_graph["states"]), corridor_graph["edges"], corridor_graph["outgoing"])
    corridor_components = t52.tarjan_scc(
        len(corridor_graph["states"]), corridor_graph["edges"], corridor_graph["outgoing"])
    corridor_component_of = {
        state: index for index, component in enumerate(corridor_components) for state in component}
    source_component = corridor_components[corridor_component_of[corridor_source_id]]
    assert corridor_target_id in corridor_live
    assert t52.cyclic_component(
        source_component, corridor_graph["edges"], corridor_graph["outgoing"])
    assert corridor_component_of[corridor_source_id] != corridor_component_of[corridor_target_id]
    exit_edges = [edge_id for edge_id in corridor_graph["outgoing"][corridor_source_id]
                  if corridor_graph["edges"][edge_id][1] == corridor_target_id
                  and corridor_graph["edges"][edge_id][4] == (0, 0, 6)]
    assert len(exit_edges) == 1
    projected_source = t52.raw_state((1, 1), (0,))
    table010 = t52.kmp_data("010")["transition_table_rows_state_columns_digit_0_to_9"]
    assert t52.next_raw("010", table010, projected_source, (0, 0)) == projected_source

    return {
        "low_path_without_any_prescribed_fiber_lift": {
            "word": "0", "from_depth": 0, "retained_digits": [1, 3, 1, 3],
            "successive_fiber_counts": corridor_sizes,
            "successive_fibers": corridor_values,
        },
        "reachability_does_not_reflect_to_every_fiber": {
            "word": "00", "from_depth": 1,
            "unreachable_high_raw_state": [[0, 1], [-1]],
            "reachable_projected_depth_zero_raw_state": [[0], []],
        },
        "branch_first_edges_collapse": {
            "word": "0", "from_depth": 2, "source": [[0, 0, 0], [5, 5]],
            "first_columns": [list(first_walk[0]), list(second_walk[0])],
            "projected_column": [3, 3],
        },
        "corridor_exit_collapses_to_loop": {
            "word": "010", "from_depth": 2,
            "source": [[1, 1, 0], [0, 1]],
            "target": [[1, 1, 0], [0, 16]],
            "exit_column": [0, 0, 6], "projected_exit_column": [0, 0],
            "source_state_id": corridor_source_id,
            "target_state_id": corridor_target_id,
            "source_scc_id": corridor_component_of[corridor_source_id],
            "target_scc_id": corridor_component_of[corridor_target_id],
            "target_live": True,
            "source_scc_cyclic": True,
            "projected_exit_is_self_loop": True,
        },
        "liveness_and_cyclicity_do_not_reflect_to_every_fiber": {
            "word": "0", "from_depth": 1, "reachable_dead_endpoint_state_ids": dead_endpoints,
            "projected_depth_zero_raw_state_id": low_state_id,
            "projected_depth_zero_raw_state_is_live": True,
            "projected_depth_zero_raw_state_is_cyclic": True,
        },
        "distinct_high_sccs_merge_under_projection": {
            "word": "01", "from_depth": 1, "state_ids": [q_a_id, q_b_id],
            "high_scc_ids": [component_of[q_a_id], component_of[q_b_id]],
            "common_projected_raw_state": [[0], []],
        },
    }


def generate(directory: Path):
    for name, expected in EXPECTED_HASHES.items():
        assert sha256(directory / name) == expected, name
    t52 = load_t52(directory)
    source = json.loads((directory / "t52_results.json").read_text(encoding="ascii"))
    completed = [instance for instance in source["instances"] if instance["status"] == "completed"]
    assert len(completed) == 16 and all(not instance["criterion_boolean"] for instance in completed)
    checks = [check_instance(t52, instance) for instance in completed]
    lifts = [check for check in checks if check["result"] == "lift"]
    deaths = [check for check in checks if check["result"] == "death"]
    assert [check["instance_order"] for check in lifts] == [12, 13, 15]
    assert len(deaths) == 13
    result = {
        "format_version": 1,
        "item": "T53",
        "claim_label": "experiment",
        "canonical_statement_sha256": EXPECTED_HASHES["pi-positive-decimal-factor-entropy.txt"],
        "dependency_hashes": EXPECTED_HASHES,
        "truncation": "drop final KMP, carry, digit, and initial-carry coordinates; preserve synthetic root",
        "endpoint_checks": endpoint_checks(),
        "explicit_projection_counterexamples": finite_projection_counterexamples(t52),
        "completed_T52_witness_checks": checks,
        "summary": {
            "completed_witnesses_checked": len(checks),
            "strict_one_step_lifts": len(lifts),
            "strict_one_step_deaths": len(deaths),
            "lift_instance_orders": [check["instance_order"] for check in lifts],
            "death_instance_orders": [check["instance_order"] for check in deaths],
        },
        "scope": {
            "death": "no lift of the selected finite diagram, not absence of every next-depth obstruction",
            "lift": "one finite next-depth diagram, not a complete next-depth graph verdict",
            "tower": "no finite lift is reported as an infinite compatible tower",
            "nonclaims": ["universal extinction", "C6", "C1", "decimal disjunctivity"],
        },
    }
    (directory / "t53_certificates.json").write_bytes(canonical_bytes(result))


def verify(directory: Path):
    with tempfile.TemporaryDirectory(prefix="t53-regenerate-") as temporary:
        target = Path(temporary)
        for name in EXPECTED_HASHES:
            shutil.copy2(directory / name, target / name)
        shutil.copy2(directory / "t53_lift_check.py", target / "t53_lift_check.py")
        generate(target)
        expected = (directory / "t53_certificates.json").read_bytes()
        actual = (target / "t53_certificates.json").read_bytes()
        assert actual == expected
        parsed = json.loads(actual.decode("ascii"))
        assert parsed["summary"] == {
            "completed_witnesses_checked": 16,
            "death_instance_orders": [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 14],
            "lift_instance_orders": [12, 13, 15],
            "strict_one_step_deaths": 13,
            "strict_one_step_lifts": 3,
        }
    print("verified canonical statement and T44/T46/T48/T52 source hashes")
    print("verified depth-truncation endpoint and counterexample checks")
    print("verified completed T52 witness diagrams: 16")
    print("verified strict one-step lifts: 3 (instances 12, 13, 15)")
    print("verified exhaustive selected-diagram deaths: 13")
    print("verified no finite lift is labeled an infinite obstruction tower")
    print("ALL T53 CHECKS PASSED")


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("mode", choices=("generate", "verify"))
    parser.add_argument("--directory", type=Path, default=HERE)
    args = parser.parse_args()
    if args.mode == "generate":
        generate(args.directory)
    else:
        verify(args.directory)


if __name__ == "__main__":
    main()
