#!/usr/bin/env python3
"""Replay T48's endpoint-complete carry/KMP graph on bounded instances.

The program uses only exact integer operations and Python's standard library.
Finite computations are experiments; T48 supplies the kernel-checked semantic
bridge between its graph criterion and finiteness of one fixed core.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import importlib.util
import itertools
import json
import signal
import shutil
import sys
import tempfile
import time
from collections import deque
from pathlib import Path


sys.dont_write_bytecode = True

DIGITS = tuple(range(10))
CARRIES = tuple(range(-1, 17))
INTERIOR_CARRIES = tuple(range(16))
STATEMENT_SHA256 = "a70dd741b27595aeb3dfc902b5e201579fed6bae24e2191f58c5ac64a22939e6"
FORMAT_VERSION = 1
GENERATED_FILES = ("results.json", "instance_table.csv", "t38_overlap.json")


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1 << 20), b""):
            digest.update(block)
    return digest.hexdigest()


def canonical_json(value) -> bytes:
    return (json.dumps(value, indent=2, sort_keys=True) + "\n").encode("ascii")


def kmp_transition(word: str, state: int, digit: int) -> int:
    candidate = word[:state] + str(digit)
    for length in range(min(len(word), len(candidate)), -1, -1):
        if candidate.endswith(word[:length]):
            return length
    raise AssertionError("unreachable KMP fallback")


def kmp_data(word: str):
    table = [[kmp_transition(word, state, digit) for digit in DIGITS]
             for state in range(len(word))]
    borders = [length for length in range(1, len(word))
               if word.startswith(word[-length:])]
    failure = [0] * len(word)
    for index in range(1, len(word)):
        fallback = failure[index - 1]
        while fallback and word[index] != word[fallback]:
            fallback = failure[fallback - 1]
        if word[index] == word[fallback]:
            fallback += 1
        failure[index] = fallback
    return {
        "active_state_meaning": "state k is the proper prefix word[:k]",
        "border_lengths": borders,
        "failure_function": failure,
        "rejection_sentinel": len(word),
        "transition_table_rows_state_columns_digit_0_to_9": table,
    }


def raw_state(kmp, carry):
    return (tuple(kmp), tuple(carry))


def state_json(state):
    if state is None:
        return {"kind": "synthetic_root"}
    return {"kind": "raw", "kmp": list(state[0]), "carry": list(state[1])}


def label_json(kind, digits, carry=()):
    value = {"kind": kind, "digits": list(digits)}
    if kind == "initial":
        value["carry"] = list(carry)
    return value


def edge_json(edge, states):
    src, dst, kind, carry, digits = edge
    value = {
        "src_id": src,
        "dst_id": dst,
        "src": state_json(states[src]),
        "dst": state_json(states[dst]),
        "label": label_json(kind, digits, carry),
    }
    return value


def next_raw(word: str, table, state, digits):
    kmp, carry = state
    next_kmp = []
    for coordinate, digit in enumerate(digits):
        target = table[kmp[coordinate]][digit]
        if target == len(word):
            return None
        next_kmp.append(target)
    next_carry = []
    for coordinate, current in enumerate(carry):
        target = digits[coordinate + 1] + 10 * current - 16 * digits[coordinate]
        if target < -1 or target > 16:
            return None
        next_carry.append(target)
    return raw_state(next_kmp, next_carry)


def initial_edges(word: str, depth: int, table):
    """Generate root edges without scanning all 18^R carry tuples."""
    initial_kmp = (0,) * (depth + 1)
    for digits in itertools.product(DIGITS, repeat=depth + 1):
        next_kmp = tuple(table[0][digit] for digit in digits)
        if any(target == len(word) for target in next_kmp):
            continue
        choices = []
        for coordinate in range(depth):
            pairs = []
            for current in CARRIES:
                target = (digits[coordinate + 1] + 10 * current
                          - 16 * digits[coordinate])
                if -1 <= target <= 16:
                    pairs.append((current, target))
            choices.append(tuple(pairs))
        for selected in itertools.product(*choices):
            current = tuple(pair[0] for pair in selected)
            target = tuple(pair[1] for pair in selected)
            yield current, digits, raw_state(next_kmp, target)
    assert len(initial_kmp) == depth + 1


class ResourceStop(Exception):
    def __init__(self, reason: str):
        super().__init__(reason)
        self.reason = reason


def build_reachable(word: str, depth: int, state_cap: int, time_cap: float):
    table = kmp_data(word)["transition_table_rows_state_columns_digit_0_to_9"]
    states = [None]
    state_ids = {None: 0}
    edges = []
    outgoing = [[]]
    queue = deque([0])
    processed = 0
    transition_attempts = 0
    deadline = time.monotonic() + time_cap

    def check_time():
        if time.monotonic() > deadline:
            raise ResourceStop("time_cap")

    def intern(state):
        if state in state_ids:
            return state_ids[state]
        if len(states) >= state_cap:
            raise ResourceStop("state_cap")
        identifier = len(states)
        state_ids[state] = identifier
        states.append(state)
        outgoing.append([])
        queue.append(identifier)
        return identifier

    try:
        while queue:
            check_time()
            src = queue.popleft()
            state = states[src]
            if state is None:
                iterator = (("initial", carry, digits, target)
                            for carry, digits, target in initial_edges(word, depth, table))
            else:
                def raw_iterator():
                    nonlocal transition_attempts
                    for number, digits in enumerate(
                            itertools.product(DIGITS, repeat=depth + 1), 1):
                        transition_attempts += 1
                        if number % 4096 == 0:
                            check_time()
                        target = next_raw(word, table, state, digits)
                        if target is not None:
                            yield "next", (), digits, target
                iterator = raw_iterator()
            for kind, carry, digits, target in iterator:
                transition_attempts += state is None
                dst = intern(target)
                edge_id = len(edges)
                edge = (src, dst, kind, tuple(carry), tuple(digits))
                edges.append(edge)
                outgoing[src].append(edge_id)
            processed += 1
    except ResourceStop as stop:
        return {
            "complete": False,
            "stop_reason": stop.reason,
            "states": states,
            "edges": edges,
            "outgoing": outgoing,
            "processed_states": processed,
            "transition_attempts": transition_attempts,
        }
    return {
        "complete": True,
        "stop_reason": None,
        "states": states,
        "edges": edges,
        "outgoing": outgoing,
        "processed_states": processed,
        "transition_attempts": transition_attempts,
    }


def tarjan_scc(vertex_count, edges, outgoing, allowed=None):
    if allowed is None:
        allowed = set(range(vertex_count))
    else:
        allowed = set(allowed)
    sys.setrecursionlimit(max(sys.getrecursionlimit(), 2 * vertex_count + 100))
    counter = 0
    stack = []
    on_stack = set()
    indices = {}
    low = {}
    components = []

    def visit(vertex):
        nonlocal counter
        indices[vertex] = low[vertex] = counter
        counter += 1
        stack.append(vertex)
        on_stack.add(vertex)
        for edge_id in outgoing[vertex]:
            target = edges[edge_id][1]
            if target not in allowed:
                continue
            if target not in indices:
                visit(target)
                low[vertex] = min(low[vertex], low[target])
            elif target in on_stack:
                low[vertex] = min(low[vertex], indices[target])
        if low[vertex] == indices[vertex]:
            component = []
            while True:
                member = stack.pop()
                on_stack.remove(member)
                component.append(member)
                if member == vertex:
                    break
            components.append(sorted(component))

    for vertex in sorted(allowed):
        if vertex not in indices:
            visit(vertex)
    return sorted(components, key=lambda component: (component[0], len(component), component))


def cyclic_component(component, edges, outgoing):
    if len(component) > 1:
        return True
    vertex = component[0]
    return any(edges[edge_id][1] == vertex for edge_id in outgoing[vertex])


def reverse_adjacency(vertex_count, edges):
    reverse = [[] for _ in range(vertex_count)]
    for edge_id, edge in enumerate(edges):
        reverse[edge[1]].append((edge[0], edge_id))
    return reverse


def live_vertices(vertex_count, edges, outgoing):
    components = tarjan_scc(vertex_count, edges, outgoing)
    cyclic = set()
    for component in components:
        if cyclic_component(component, edges, outgoing):
            cyclic.update(component)
    reverse = reverse_adjacency(vertex_count, edges)
    live = set(cyclic)
    queue = deque(sorted(cyclic))
    while queue:
        target = queue.popleft()
        for source, _ in reverse[target]:
            if source not in live:
                live.add(source)
                queue.append(source)
    return live


def bfs_edge_path(start, goal, edges, outgoing, allowed=None):
    allowed_set = None if allowed is None else set(allowed)
    queue = deque([start])
    previous = {start: None}
    while queue:
        vertex = queue.popleft()
        if vertex == goal:
            break
        for edge_id in outgoing[vertex]:
            target = edges[edge_id][1]
            if allowed_set is not None and target not in allowed_set:
                continue
            if target not in previous:
                previous[target] = edge_id
                queue.append(target)
    if goal not in previous:
        return None
    path = []
    vertex = goal
    while previous[vertex] is not None:
        edge_id = previous[vertex]
        path.append(edge_id)
        vertex = edges[edge_id][0]
    path.reverse()
    return path


def path_json(path, edges, states):
    return [edge_json(edges[edge_id], states) for edge_id in path]


def path_to_cycle(start, live, components, edges, outgoing):
    cyclic_vertices = set()
    for component in components:
        if cyclic_component(component, edges, outgoing):
            cyclic_vertices.update(component)
    queue = deque([start])
    previous = {start: None}
    goal = None
    while queue:
        vertex = queue.popleft()
        if vertex in cyclic_vertices:
            goal = vertex
            break
        for edge_id in outgoing[vertex]:
            target = edges[edge_id][1]
            if target in live and target not in previous:
                previous[target] = edge_id
                queue.append(target)
    if goal is None:
        raise AssertionError("live state has no path to a cycle")
    path = []
    vertex = goal
    while previous[vertex] is not None:
        edge_id = previous[vertex]
        path.append(edge_id)
        vertex = edges[edge_id][0]
    path.reverse()
    return path, goal


def closed_cycle(vertex, component, edges, outgoing):
    component_set = set(component)
    for edge_id in outgoing[vertex]:
        target = edges[edge_id][1]
        if target not in component_set:
            continue
        if target == vertex:
            return [edge_id]
        rest = bfs_edge_path(target, vertex, edges, outgoing, component_set)
        if rest is not None:
            return [edge_id] + rest
    raise AssertionError("cyclic SCC vertex lacks a closed walk")


def table_hash(true_ids):
    payload = ",".join(map(str, sorted(true_ids))).encode("ascii")
    return hashlib.sha256(payload).hexdigest()


def analyze_complete(graph):
    states = graph["states"]
    edges = graph["edges"]
    outgoing = graph["outgoing"]
    count = len(states)
    components = tarjan_scc(count, edges, outgoing)
    component_of = {}
    for component_id, component in enumerate(components):
        for vertex in component:
            component_of[vertex] = component_id
    live = live_vertices(count, edges, outgoing)
    cyclic_ids = {vertex for component in components
                  if cyclic_component(component, edges, outgoing)
                  for vertex in component}
    live_components = [component for component in components
                       if component[0] in live]
    cyclic_live_components = [component for component in live_components
                              if cyclic_component(component, edges, outgoing)]
    bad = None
    component_rows = []
    for component in cyclic_live_components:
        component_set = set(component)
        exit_edges = [edge_id for source in component for edge_id in outgoing[source]
                      if edges[edge_id][1] in live
                      and edges[edge_id][1] not in component_set]
        branching = []
        for source in component:
            internal = [edge_id for edge_id in outgoing[source]
                        if edges[edge_id][1] in component_set]
            if len(internal) != 1:
                branching.append((source, internal))
        component_rows.append({
            "representative_state_id": component[0],
            "size": len(component),
            "terminal_in_reachable_live": not exit_edges,
            "simple_directed_cycle_scc": not branching,
        })
        if bad is None and exit_edges:
            bad = ("nonterminal_delay_corridor", component, exit_edges[0])
        if bad is None and branching:
            bad = ("branching_cyclic_scc", component, branching[0])
    criterion = bad is None
    certificate = {
        "certificate_kind": "exact replayed T46 Boolean criterion tables on the complete reachable subgraph of the T48 graph",
        "reachable_true_count": count,
        "reachable_true_ids_sha256": table_hash(range(count)),
        "live_true_count": len(live),
        "live_true_ids_sha256": table_hash(live),
        "cyclic_true_count": len(cyclic_ids),
        "cyclic_true_ids_sha256": table_hash(cyclic_ids),
        "same_scc_partition": components,
        "cyclic_reachable_live_scc_checks": component_rows,
        "criterion": criterion,
    }
    witness = None
    if bad is not None:
        kind, component, detail = bad
        component_set = set(component)
        if kind == "branching_cyclic_scc":
            source, internal = detail
            if len(internal) < 2:
                raise AssertionError("cyclic SCC cannot have zero internal exits")
            selected = internal[:2]
            returns = []
            for edge_id in selected:
                target = edges[edge_id][1]
                rest = bfs_edge_path(target, source, edges, outgoing, component_set)
                if rest is None:
                    raise AssertionError("SCC return path missing")
                returns.append([edge_id] + rest)
            witness = {
                "classification": kind,
                "violated_T46_clause": "SimpleDirectedCycleSCC: two distinct labelled internal live edges",
                "scc_representative_state_id": component[0],
                "scc_size": len(component),
                "branch_state_id": source,
                "start_to_branch_path": path_json(
                    bfs_edge_path(0, source, edges, outgoing), edges, states),
                "first_closed_walk": path_json(returns[0], edges, states),
                "second_closed_walk": path_json(returns[1], edges, states),
            }
        else:
            edge_id = detail
            source, target = edges[edge_id][:2]
            continuation, cycle_vertex = path_to_cycle(
                target, live, components, edges, outgoing)
            cycle_component = components[component_of[cycle_vertex]]
            cycle = closed_cycle(cycle_vertex, cycle_component, edges, outgoing)
            witness = {
                "classification": kind,
                "violated_T46_clause": "TerminalInReachableLive: live edge exits a cyclic SCC",
                "scc_representative_state_id": component[0],
                "scc_size": len(component),
                "start_to_exit_source_path": path_json(
                    bfs_edge_path(0, source, edges, outgoing), edges, states),
                "exit_edge": edge_json(edges[edge_id], states),
                "target_to_cycle_path": path_json(continuation, edges, states),
                "target_continuation_cycle": path_json(cycle, edges, states),
            }
    return certificate, witness, live, components


def carry_ranges(states, subset):
    raw = [states[index] for index in sorted(subset) if states[index] is not None]
    if not raw or not raw[0][1]:
        return []
    return [{"coordinate": coordinate,
             "minimum": min(state[1][coordinate] for state in raw),
             "maximum": max(state[1][coordinate] for state in raw)}
            for coordinate in range(len(raw[0][1]))]


def validate_edge(edge, states, word, depth, table):
    src, dst, kind, carry, digits = edge
    assert len(digits) == depth + 1
    assert all(digit in DIGITS for digit in digits)
    assert states[dst] is not None
    if kind == "initial":
        assert states[src] is None and len(carry) == depth
        source_state = raw_state((0,) * (depth + 1), carry)
    else:
        assert kind == "next" and states[src] is not None and carry == ()
        source_state = states[src]
    assert next_raw(word, table, source_state, digits) == states[dst]


def edge_key(edge, states):
    src, dst, kind, carry, digits = edge
    return (states[src], states[dst], kind, carry, digits)


def validate_path(path, expected_start=None, expected_end=None):
    if not path:
        if expected_start is not None and expected_end is not None:
            assert expected_start == expected_end
        return
    if expected_start is not None:
        assert path[0]["src_id"] == expected_start
    for first, second in zip(path, path[1:]):
        assert first["dst_id"] == second["src_id"]
    if expected_end is not None:
        assert path[-1]["dst_id"] == expected_end


def validate_witness(witness, graph, live, components):
    if witness is None:
        return
    edges = graph["edges"]
    states = graph["states"]
    outgoing = graph["outgoing"]
    edge_lookup = {json.dumps(edge_json(edge, states), sort_keys=True): edge_id
                   for edge_id, edge in enumerate(edges)}
    component_of = {}
    for identifier, component in enumerate(components):
        for vertex in component:
            component_of[vertex] = identifier

    def check_serialized_path(path):
        for serialized in path:
            assert json.dumps(serialized, sort_keys=True) in edge_lookup

    representative = witness["scc_representative_state_id"]
    source_component = components[component_of[representative]]
    assert len(source_component) == witness["scc_size"]
    assert cyclic_component(source_component, edges, outgoing)
    assert all(vertex in live for vertex in source_component)
    if witness["classification"] == "branching_cyclic_scc":
        source = witness["branch_state_id"]
        walks = (witness["first_closed_walk"], witness["second_closed_walk"])
        assert source in source_component
        validate_path(witness["start_to_branch_path"], 0, source)
        check_serialized_path(witness["start_to_branch_path"])
        for walk in walks:
            assert walk
            validate_path(walk, source, source)
            check_serialized_path(walk)
            assert all(edge["src_id"] in live and edge["dst_id"] in live for edge in walk)
            assert all(edge["src_id"] in source_component and edge["dst_id"] in source_component
                       for edge in walk)
        first = json.dumps(walks[0][0], sort_keys=True)
        second = json.dumps(walks[1][0], sort_keys=True)
        assert first != second and first in edge_lookup and second in edge_lookup
        assert component_of[walks[0][0]["dst_id"]] == component_of[source]
        assert component_of[walks[1][0]["dst_id"]] == component_of[source]
    else:
        source = witness["exit_edge"]["src_id"]
        target = witness["exit_edge"]["dst_id"]
        assert source in source_component
        validate_path(witness["start_to_exit_source_path"], 0, source)
        check_serialized_path(witness["start_to_exit_source_path"])
        assert json.dumps(witness["exit_edge"], sort_keys=True) in edge_lookup
        assert target in live and component_of[source] != component_of[target]
        continuation = witness["target_to_cycle_path"]
        cycle = witness["target_continuation_cycle"]
        cycle_start = continuation[-1]["dst_id"] if continuation else target
        validate_path(continuation, target, cycle_start)
        check_serialized_path(continuation)
        assert cycle
        validate_path(cycle, cycle_start, cycle_start)
        check_serialized_path(cycle)
        target_component = components[component_of[cycle_start]]
        assert cyclic_component(target_component, edges, outgoing)
        assert all(edge["src_id"] in live and edge["dst_id"] in live
                   for edge in continuation + cycle)


def _evaluate_instance(spec, caps):
    word = spec["word"]
    depth = spec["depth"]
    assert word and all(character in "0123456789" for character in word)
    declared = 1 + len(word) ** (depth + 1) * 18 ** depth
    graph = build_reachable(word, depth, caps["state_cap"], caps["time_cap_seconds"])
    base = {
        "phase": spec["phase"],
        "word": word,
        "word_length": len(word),
        "depth_R": depth,
        "instance_order": spec["instance_order"],
        "declared_state_count_including_root": declared,
        "endpoint_carry_convention": [-1, 16],
        "kmp": kmp_data(word),
        "caps": caps,
        "discovered_state_count_including_root": len(graph["states"]),
        "generated_edge_count": len(graph["edges"]),
        "processed_reachable_state_count": graph["processed_states"],
        "transition_attempts": graph["transition_attempts"],
    }
    if not graph["complete"]:
        base.update({
            "status": "resource_frontier",
            "resource_stop_reason": graph["stop_reason"],
            "mathematical_verdict": None,
            "reachable_state_count": None,
            "reachable_live_state_count": None,
            "criterion_boolean": None,
            "bad_scc_witness": None,
            "extrapolation": "heuristic only: partial growth is not a graph or core verdict",
        })
        return base
    table = base["kmp"]["transition_table_rows_state_columns_digit_0_to_9"]
    for edge in graph["edges"]:
        validate_edge(edge, graph["states"], word, depth, table)
    certificate, witness, live, components = analyze_complete(graph)
    validate_witness(witness, graph, live, components)
    criterion = certificate["criterion"]
    base.update({
        "status": "completed",
        "resource_stop_reason": None,
        "reachable_state_count": len(graph["states"]),
        "reachable_live_state_count": len(live),
        "reachable_carry_ranges": carry_ranges(graph["states"], range(len(graph["states"]))),
        "reachable_live_carry_ranges": carry_ranges(graph["states"], live),
        "criterion_boolean": criterion,
        "t48_t46_boolean_certificate": certificate,
        "bad_scc_witness": witness,
        "mathematical_verdict": (
            "fixed_core_finite_via_T48_equivalence" if criterion
            else "fixed_core_infinite_via_T48_equivalence"),
        "claim_label": "experiment",
        "formal_basis": "machine-checked T48 core_finite_iff_liveSCCCriterion",
        "extrapolation": "none; this fixed-instance result is not a uniform extinction claim",
    })
    if not criterion:
        assert witness is not None
    return base


def time_frontier_instance(spec, caps):
    word = spec["word"]
    depth = spec["depth"]
    return {
        "phase": spec["phase"],
        "word": word,
        "word_length": len(word),
        "depth_R": depth,
        "instance_order": spec["instance_order"],
        "declared_state_count_including_root": 1 + len(word) ** (depth + 1) * 18 ** depth,
        "endpoint_carry_convention": [-1, 16],
        "kmp": kmp_data(word),
        "caps": caps,
        "status": "resource_frontier",
        "resource_stop_reason": "time_cap",
        "discovered_state_count_including_root": None,
        "generated_edge_count": None,
        "processed_reachable_state_count": None,
        "transition_attempts": None,
        "mathematical_verdict": None,
        "reachable_state_count": None,
        "reachable_live_state_count": None,
        "criterion_boolean": None,
        "bad_scc_witness": None,
        "extrapolation": "heuristic only: timed computation is not a graph or core verdict",
    }


def evaluate_instance(spec, caps):
    """Apply one hard wall-clock cap to construction and certificate analysis."""
    def timeout_handler(_signum, _frame):
        raise ResourceStop("time_cap")

    old_handler = signal.getsignal(signal.SIGALRM)
    signal.signal(signal.SIGALRM, timeout_handler)
    signal.setitimer(signal.ITIMER_REAL, caps["time_cap_seconds"])
    try:
        return _evaluate_instance(spec, caps)
    except ResourceStop as stop:
        if stop.reason != "time_cap":
            raise
        return time_frontier_instance(spec, caps)
    finally:
        signal.setitimer(signal.ITIMER_REAL, 0)
        signal.signal(signal.SIGALRM, old_handler)


def load_vendored_t38(directory: Path, expected_hash: str):
    source = directory / "t38_experiment.py"
    assert sha256(source) == expected_hash
    spec = importlib.util.spec_from_file_location("vendored_t38_experiment", source)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def reachable_from_starts(edges, starts):
    seen = set(starts)
    queue = deque(starts)
    while queue:
        source = queue.popleft()
        for edge in edges[source]:
            target = edge[0]
            if target not in seen:
                seen.add(target)
                queue.append(target)
    return seen


def live_reference(edges):
    converted = []
    outgoing = [[] for _ in edges]
    for source, row in enumerate(edges):
        for target, left_digit, right_digit in row:
            edge_id = len(converted)
            converted.append((source, target, "next", (), (left_digit, right_digit)))
            outgoing[source].append(edge_id)
    return live_vertices(len(edges), converted, outgoing), converted, outgoing


def t48_restricted_edge_set(word: str):
    table = kmp_data(word)["transition_table_rows_state_columns_digit_0_to_9"]
    result = set()
    for carry in INTERIOR_CARRIES:
        for left in range(len(word)):
            for right in range(len(word)):
                source = raw_state((left, right), (carry,))
                for digits in itertools.product(DIGITS, repeat=2):
                    target = next_raw(word, table, source, digits)
                    if target is not None and target[1][0] in INTERIOR_CARRIES:
                        result.add(((carry, left, right),
                                    (target[1][0], target[0][0], target[0][1]),
                                    digits[0], digits[1]))
    return result


def generate_t38_overlap(config, directory: Path):
    t38 = load_vendored_t38(
        directory, config["t38_source_hashes"]["t38_experiment.py"])
    rows = []
    for fixture in config["t38_overlap_fixtures"]:
        word = fixture["word"]
        states, edges, starts = t38.product_graph(word, 16)
        reference_edges = {
            (states[source], states[target], left_digit, right_digit)
            for source, row in enumerate(edges)
            for target, left_digit, right_digit in row
        }
        restricted_edges = t48_restricted_edge_set(word)
        assert reference_edges == restricted_edges
        reachable = t38.reachable(edges, starts)
        live, converted, outgoing = live_reference(edges)
        reachable_live = reachable & live
        components = tarjan_scc(len(states), converted, outgoing, live)
        cyclic_sizes = sorted(len(component) for component in components
                              if cyclic_component(component, converted, outgoing))
        rows.append({
            "word": word,
            "q": 16,
            "mapping": "(carry,leftKMP,rightKMP) <-> T48 R=1 raw state; label (a,b) <-> digit column",
            "restriction": "T48 raw induced subgraph on carries 0..15; synthetic root omitted",
            "t38_state_count": len(states),
            "t38_labelled_edge_count": len(reference_edges),
            "t38_start_count": len(starts),
            "t38_reachable_count": len(reachable),
            "t38_live_count_all_declared_raw_states": len(live),
            "t38_reachable_live_count": len(reachable_live),
            "t38_cyclic_scc_sizes": cyclic_sizes,
            "restricted_T48_edge_set_equal": True,
            "vendored_T38_code_replay_agrees": True,
        })
    return {
        "format_version": FORMAT_VERSION,
        "source": "T38 replayed experiment bundle, structural fields only",
        "source_t38_experiment_sha256": config["t38_source_hashes"]["t38_experiment.py"],
        "source_entropy_certificates_sha256": config["t38_source_hashes"]["entropy_certificates.json.gz"],
        "convention_warning": (
            "T38 uses carries 0..15 and no endpoint claim. Full T48 uses -1..16, "
            "has a synthetic root, and can have additional endpoint-live SCCs."),
        "nonclaim": "No T38 entropy-gap table or tau table is reproduced.",
        "rows": rows,
    }


def self_checks():
    checks = {"kmp_cases": 0, "carry_equations": 0}
    for word in ("0", "00", "01", "010", "999"):
        table = kmp_data(word)["transition_table_rows_state_columns_digit_0_to_9"]
        for length in range(5):
            for digits in itertools.product(DIGITS, repeat=length):
                state = 0
                accepted = True
                text = ""
                for digit in digits:
                    text += str(digit)
                    state = table[state][digit]
                    if state == len(word):
                        accepted = False
                        break
                assert accepted == (word not in text)
                checks["kmp_cases"] += 1
    for left_digit, right_digit, current, target in itertools.product(
            DIGITS, DIGITS, CARRIES, CARRIES):
        if 16 * left_digit + target == right_digit + 10 * current:
            assert target == right_digit + 10 * current - 16 * left_digit
            checks["carry_equations"] += 1
    return checks


def load_config(directory: Path):
    return json.loads((directory / "instances.json").read_text(encoding="ascii"))


def generate(directory: Path):
    if sha256(directory / "pi-positive-decimal-factor-entropy.txt") != STATEMENT_SHA256:
        raise SystemExit("canonical statement hash mismatch")
    config = load_config(directory)
    assert config["format_version"] == FORMAT_VERSION
    for dependency in config["formal_dependencies"]:
        assert sha256(directory / dependency["file"]) == dependency["sha256"]
    instances = []
    for order, raw_spec in enumerate(config["instances"]):
        spec = dict(raw_spec)
        spec["instance_order"] = order
        instances.append(evaluate_instance(spec, config["caps"]))
    result = {
        "format_version": FORMAT_VERSION,
        "item": "T52",
        "status": "experiment",
        "canonical_statement_sha256": STATEMENT_SHA256,
        "graph": "T48 endpoint-complete carry/KMP graph",
        "criterion": "T46 reachable-live terminal simple-directed-cycle SCC criterion",
        "instance_order_rule": "manifest order: complete baseline, then progressive extension, then frontier",
        "caps": config["caps"],
        "formal_dependencies": config["formal_dependencies"],
        "lean_gate_receipt": config["lean_gate_receipt"],
        "self_checks": self_checks(),
        "instances": instances,
        "universal_nonclaim": (
            "No bounded result proves the universal linear finite-core hypothesis, C6, "
            "positive decimal factor entropy for pi, or decimal disjunctivity."),
        "heuristic_extrapolation": (
            "State-growth observations beyond completed instances are heuristic only."),
    }
    (directory / "results.json").write_bytes(canonical_json(result))
    fields = [
        "instance_order", "phase", "word", "word_length", "depth_R", "status",
        "declared_state_count_including_root", "reachable_state_count",
        "reachable_live_state_count", "generated_edge_count", "criterion_boolean",
        "mathematical_verdict", "resource_stop_reason",
    ]
    with (directory / "instance_table.csv").open("w", newline="", encoding="ascii") as handle:
        writer = csv.DictWriter(handle, fieldnames=fields)
        writer.writeheader()
        for instance in instances:
            writer.writerow({field: instance.get(field) for field in fields})
    overlap = generate_t38_overlap(config, directory)
    (directory / "t38_overlap.json").write_bytes(canonical_json(overlap))


def verify(directory: Path):
    assert sha256(directory / "pi-positive-decimal-factor-entropy.txt") == STATEMENT_SHA256
    config = load_config(directory)
    result = json.loads((directory / "results.json").read_text(encoding="ascii"))
    assert result["format_version"] == FORMAT_VERSION
    assert result["self_checks"] == self_checks()
    expected_order = [(entry["word"], entry["depth"]) for entry in config["instances"]]
    actual_order = [(entry["word"], entry["depth_R"]) for entry in result["instances"]]
    assert actual_order == expected_order
    completed = 0
    negative = 0
    positive = 0
    frontier = 0
    for instance in result["instances"]:
        if instance["status"] == "completed":
            completed += 1
            assert instance["reachable_state_count"] == instance["discovered_state_count_including_root"]
            assert instance["criterion_boolean"] is instance["t48_t46_boolean_certificate"]["criterion"]
            if instance["criterion_boolean"]:
                positive += 1
                assert instance["bad_scc_witness"] is None
            else:
                negative += 1
                assert instance["bad_scc_witness"] is not None
                assert instance["bad_scc_witness"]["classification"] in (
                    "branching_cyclic_scc", "nonterminal_delay_corridor")
        else:
            frontier += 1
            assert instance["status"] == "resource_frontier"
            assert instance["criterion_boolean"] is None
            assert instance["mathematical_verdict"] is None
            assert instance["bad_scc_witness"] is None
    overlap = json.loads((directory / "t38_overlap.json").read_text(encoding="ascii"))
    for dependency in config["formal_dependencies"]:
        assert sha256(directory / dependency["file"]) == dependency["sha256"]
    assert sha256(directory / "t38_experiment.py") == config["t38_source_hashes"]["t38_experiment.py"]
    assert all(row["restricted_T48_edge_set_equal"] and row["vendored_T38_code_replay_agrees"]
               for row in overlap["rows"])
    timeout_probe = evaluate_instance(
        {"phase": "timeout_self_check", "word": "010", "depth": 3, "instance_order": 0},
        {"state_cap": 1_000_000, "time_cap_seconds": 0.001})
    assert timeout_probe["status"] == "resource_frontier"
    assert timeout_probe["resource_stop_reason"] == "time_cap"
    assert timeout_probe["criterion_boolean"] is None
    print(f"verified completed instances: {completed}")
    print(f"verified positive certificates: {positive}")
    print(f"verified negative bad-SCC witnesses: {negative}")
    print(f"verified resource-frontier cases without verdict: {frontier}")
    print(f"verified T38 structural overlaps: {len(overlap['rows'])}")
    print("ALL T52 CHECKS PASSED")


def replay(directory: Path):
    with tempfile.TemporaryDirectory(prefix="t52-replay-") as temporary:
        target = Path(temporary)
        for name in ("t52_experiment.py", "instances.json",
                     "pi-positive-decimal-factor-entropy.txt", "t38_experiment.py",
                     "T46T46LiveSCC.lean", "T48EndpointCarryKMP.lean"):
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
