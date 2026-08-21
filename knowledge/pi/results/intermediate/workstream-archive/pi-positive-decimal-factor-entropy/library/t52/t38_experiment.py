#!/usr/bin/env python3
"""Generate and verify the finite T38 experiment artifacts.

Only Python's standard library is required.  All certificate checks use exact
integer or Fraction arithmetic; floating point is used only to choose compact
positive Collatz-Wielandt test vectors, which are then checked exactly.
"""

from __future__ import annotations

import argparse
import csv
import gzip
import hashlib
import itertools
import json
import shutil
import sys
import tempfile
from collections import defaultdict, deque
from fractions import Fraction
from pathlib import Path


DIGITS = tuple(range(10))
MULTIPLIERS = (9, 11, 16)
STATEMENT_SHA256 = "a70dd741b27595aeb3dfc902b5e201579fed6bae24e2191f58c5ac64a22939e6"
FORMAT_VERSION = 1
FRONTIER_CANDIDATE_BUDGET = 500_000


def sha256(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for block in iter(lambda: f.read(1 << 20), b""):
            h.update(block)
    return h.hexdigest()


def words():
    for length in (1, 2, 3):
        for digits in itertools.product(DIGITS, repeat=length):
            yield "".join(map(str, digits))


def kmp_transition(word: str, state: int, digit: int) -> int:
    candidate = word[:state] + str(digit)
    for length in range(min(len(word), len(candidate)), -1, -1):
        if candidate.endswith(word[:length]):
            return length
    raise AssertionError("unreachable KMP state")


def kmp_table(word: str):
    return [[kmp_transition(word, state, digit) for digit in DIGITS]
            for state in range(len(word))]


def baseline_graph(word: str):
    table = kmp_table(word)
    edges = [[] for _ in word]
    for state in range(len(word)):
        for digit in DIGITS:
            target = table[state][digit]
            if target < len(word):
                edges[state].append((target, digit, digit))
    return edges, [0]


def product_graph(word: str, q: int):
    """Most-significant-first graph for q*a_j+c_{j+1}=b_j+10*c_j."""
    m = len(word)
    table = kmp_table(word)
    states = [(carry, left, right)
              for carry in range(q) for left in range(m) for right in range(m)]
    index = {state: i for i, state in enumerate(states)}
    edges = [[] for _ in states]
    for carry_right in range(q):
        for a in DIGITS:
            value = q * a + carry_right
            carry_left, b = divmod(value, 10)
            for left in range(m):
                next_left = table[left][a]
                if next_left == m:
                    continue
                for right in range(m):
                    next_right = table[right][b]
                    if next_right == m:
                        continue
                    source = index[(carry_left, left, right)]
                    target = index[(carry_right, next_left, next_right)]
                    edges[source].append((target, a, b))
    starts = [index[(carry, 0, 0)] for carry in range(q)]
    return states, edges, starts


def reachable(edges, starts):
    seen = set(starts)
    queue = deque(starts)
    while queue:
        source = queue.popleft()
        for target, _, _ in edges[source]:
            if target not in seen:
                seen.add(target)
                queue.append(target)
    return seen


def tarjan_scc(edges, allowed):
    counter = 0
    stack = []
    on_stack = set()
    indices = {}
    low = {}
    result = []

    def visit(v):
        nonlocal counter
        indices[v] = low[v] = counter
        counter += 1
        stack.append(v)
        on_stack.add(v)
        for target, _, _ in edges[v]:
            if target not in allowed:
                continue
            if target not in indices:
                visit(target)
                low[v] = min(low[v], low[target])
            elif target in on_stack:
                low[v] = min(low[v], indices[target])
        if low[v] == indices[v]:
            component = []
            while True:
                x = stack.pop()
                on_stack.remove(x)
                component.append(x)
                if x == v:
                    break
            result.append(sorted(component))

    for vertex in sorted(allowed):
        if vertex not in indices:
            visit(vertex)
    return sorted(result, key=lambda c: (c[0], len(c), c))


def component_matrix(edges, component):
    local = {vertex: i for i, vertex in enumerate(component)}
    rows = [defaultdict(int) for _ in component]
    for source in component:
        for target, _, _ in edges[source]:
            if target in local:
                rows[local[source]][local[target]] += 1
    return [dict(sorted(row.items())) for row in rows]


def is_cyclic(rows):
    return len(rows) > 1 or (len(rows) == 1 and rows[0].get(0, 0) > 0)


def matvec(rows, vector, add_identity=False):
    result = []
    for i, row in enumerate(rows):
        value = sum(weight * vector[j] for j, weight in row.items())
        if add_identity:
            value += vector[i]
        result.append(value)
    return result


def choose_vector(rows, iterations=350, scale=10**15):
    """Floating-point guidance only; returned vector is checked exactly."""
    vector = [1.0] * len(rows)
    for _ in range(iterations):
        nxt = []
        for i, row in enumerate(rows):
            nxt.append(vector[i] + sum(weight * vector[j]
                                        for j, weight in row.items()))
        maximum = max(nxt)
        vector = [x / maximum for x in nxt]
    positive = [x for x in vector if x > 0.0]
    minimum = min(positive, default=1.0)
    if minimum * scale < 10:
        scale = min(10**120, max(scale, int(100 / minimum)))
    return [max(1, int(round(x * scale))) for x in vector]


def fraction_pair(value: Fraction):
    return [str(value.numerator), str(value.denominator)]


def parse_fraction(pair):
    return Fraction(int(pair[0]), int(pair[1]))


def collatz_bounds(rows, vector):
    assert vector and all(isinstance(x, int) and x > 0 for x in vector)
    image = matvec(rows, vector)
    ratios = [Fraction(image[i], vector[i]) for i in range(len(vector))]
    return min(ratios), max(ratios)


def graph_certificate(edges, starts):
    allowed = reachable(edges, starts)
    components = tarjan_scc(edges, allowed)
    certs = []
    for component in components:
        rows = component_matrix(edges, component)
        if not is_cyclic(rows):
            continue
        vector = choose_vector(rows)
        lower, upper = collatz_bounds(rows, vector)
        certs.append({
            "nodes": component,
            "vector": [str(x) for x in vector],
            "lower": fraction_pair(lower),
            "upper": fraction_pair(upper),
        })
    if not certs:
        return {"components": [], "lower": ["0", "1"], "upper": ["0", "1"]}
    lower = max(parse_fraction(c["lower"]) for c in certs)
    upper = max(parse_fraction(c["upper"]) for c in certs)
    return {"components": certs, "lower": fraction_pair(lower), "upper": fraction_pair(upper)}


def certify_case(word: str, q: int):
    base_edges, base_starts = baseline_graph(word)
    states, product_edges, product_starts = product_graph(word, q)
    base = graph_certificate(base_edges, base_starts)
    product = graph_certificate(product_edges, product_starts)
    base_l = parse_fraction(base["lower"])
    base_u = parse_fraction(base["upper"])
    prod_l = parse_fraction(product["lower"])
    prod_u = parse_fraction(product["upper"])
    if prod_l <= 0:
        ratio_upper = None
    else:
        ratio_upper = base_u / prod_l
    ratio_lower = base_l / prod_u if prod_u > 0 else Fraction(10**100, 1)
    return {
        "word": word,
        "q": q,
        "state_count": len(states),
        "reachable_count": len(reachable(product_edges, product_starts)),
        "base": base,
        "product": product,
        "ratio_lower": fraction_pair(ratio_lower),
        "ratio_upper": fraction_pair(ratio_upper) if ratio_upper is not None else None,
    }


def decimal_log_bound(value: Fraction, lower: bool):
    if value <= 0:
        return "-inf"
    if value < 1:
        raise ValueError("the certified log display is implemented for ratios >= 1")
    if value == 1:
        return "0.000000000000000000"
    # log(x)=2*sum z^(2k+1)/(2k+1), z=(x-1)/(x+1).  Everything here is
    # Fraction arithmetic.  The geometric tail majorant makes the decimal
    # endpoints certificates rather than floating-point approximations.
    z = (value - 1) / (value + 1)
    z_squared = z * z
    total = Fraction(0)
    power = z
    k = 0
    target = Fraction(1, 10**24)
    while True:
        total += power / (2 * k + 1)
        k += 1
        power *= z_squared
        remainder = 2 * power / ((2 * k + 1) * (1 - z_squared))
        if remainder < target:
            break
    lower_value = 2 * total
    upper_value = lower_value + remainder
    places = 18
    scale = 10**places
    endpoint = lower_value if lower else upper_value
    scaled = endpoint.numerator * scale
    integer = (scaled // endpoint.denominator if lower else
               -(-scaled // endpoint.denominator))
    whole, fractional = divmod(integer, scale)
    return f"{whole}.{fractional:0{places}d}"


def write_gzip_json(path: Path, value):
    payload = json.dumps(value, sort_keys=True, separators=(",", ":")).encode() + b"\n"
    with path.open("wb") as raw:
        with gzip.GzipFile(filename="", mode="wb", fileobj=raw, mtime=0) as out:
            out.write(payload)


def read_gzip_json(path: Path):
    with gzip.open(path, "rt", encoding="utf-8") as f:
        return json.load(f)


def live_input_graph(word: str, multiplier: int):
    """Explicit carry/KMP graph used by the exact tau computation."""
    m = len(word)
    table = kmp_table(word)
    edges = [[] for _ in range(multiplier * m)]
    for carry_left in range(multiplier):
        for state in range(m):
            source = carry_left * m + state
            for a in DIGITS:
                target_state = table[state][a]
                if target_state == m:
                    continue
                for b in DIGITS:
                    carry_right = b + 10 * carry_left - multiplier * a
                    if 0 <= carry_right < multiplier:
                        edges[source].append((carry_right * m + target_state, a, b))
    return edges


def live_vertices(edges):
    """Vertices that can reach a directed cycle."""
    allowed = set(range(len(edges)))
    old_recursion_limit = sys.getrecursionlimit()
    sys.setrecursionlimit(max(old_recursion_limit, 2 * len(edges) + 100))
    try:
        components = tarjan_scc(edges, allowed)
    finally:
        sys.setrecursionlimit(old_recursion_limit)
    cyclic = set()
    for component in components:
        rows = component_matrix(edges, component)
        if is_cyclic(rows):
            cyclic.update(component)
    reverse = [[] for _ in edges]
    for source, outgoing in enumerate(edges):
        for target, _, _ in outgoing:
            reverse[target].append(source)
    live = set(cyclic)
    queue = deque(cyclic)
    while queue:
        target = queue.popleft()
        for source in reverse[target]:
            if source not in live:
                live.add(source)
                queue.append(source)
    return live


def live_input_states(word: str, multiplier: int):
    """States (carry,KMP) admitting an infinite symbolic continuation."""
    return live_vertices(live_input_graph(word, multiplier))


def prefix_is_covered(word: str, q_power: int, output_word: str, live=None):
    """Exact symbolic membership in the prefix language of T_{q_power}(K_w)."""
    m = len(word)
    table = kmp_table(word)
    if live is None:
        live = live_input_states(word, q_power)
    current = {(carry, 0) for carry in range(q_power)}
    for char in output_word:
        b = int(char)
        nxt = set()
        for carry_left, state in current:
            for a in DIGITS:
                target_state = table[state][a]
                if target_state == m:
                    continue
                carry_right = b + 10 * carry_left - q_power * a
                if 0 <= carry_right < q_power:
                    nxt.add((carry_right, target_state))
        current = nxt
        if not current:
            return False
    return any(carry * m + state in live for carry, state in current)


def exact_tau(word: str, q: int, ell: int, max_m: int):
    targets = ["".join(map(str, d)) for d in itertools.product(DIGITS, repeat=ell)]
    uncovered = set(targets)
    frontier = []
    for exponent in range(max_m + 1):
        multiplier = q ** exponent
        live = live_input_states(word, multiplier)
        before = len(uncovered)
        uncovered = {target for target in uncovered
                     if not prefix_is_covered(word, multiplier, target, live)}
        frontier.append({
            "exponent": exponent,
            "multiplier": multiplier,
            "carry_kmp_states": multiplier * len(word),
            "live_states": len(live),
            "uncovered_before": before,
            "uncovered_after": len(uncovered),
        })
        if not uncovered:
            return exponent, frontier, []
    return None, frontier, sorted(uncovered)


def transducer_self_checks():
    checks = {"carry_edges": 0, "integer_paths": 0, "kmp_cases": 0,
              "baseline_counts": 0, "product_edges": 0,
              "product_path_counts": 0}
    for q in MULTIPLIERS:
        for carry_right in range(q):
            for a in DIGITS:
                value = q * a + carry_right
                carry_left, b = divmod(value, 10)
                assert 0 <= carry_left < q and 0 <= b < 10
                assert q * a + carry_right == b + 10 * carry_left
                checks["carry_edges"] += 1
        for n in (1, 2, 3):
            power = 10 ** n
            for a_integer in range(power):
                for carry_right in range(q):
                    value = q * a_integer + carry_right
                    carry_left, b_integer = divmod(value, power)
                    assert value == b_integer + carry_left * power
                    assert 0 <= carry_left < q
                    checks["integer_paths"] += 1
    test_words = ("0", "7", "00", "09", "11", "000", "010", "999")
    for word in test_words:
        table = kmp_table(word)
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
    for word in test_words:
        edges, starts = baseline_graph(word)
        counts = [1 if i in starts else 0 for i in range(len(edges))]
        for length in range(1, 5):
            nxt = [0] * len(edges)
            for source, count in enumerate(counts):
                for target, _, _ in edges[source]:
                    nxt[target] += count
            counts = nxt
            brute = sum(word not in "".join(map(str, digits))
                        for digits in itertools.product(DIGITS, repeat=length))
            assert sum(counts) == brute
            checks["baseline_counts"] += 1
    for word in ("0", "00", "010"):
        table = kmp_table(word)
        for q in MULTIPLIERS:
            states, edges, starts = product_graph(word, q)
            for source, outgoing in enumerate(edges):
                carry_left, left, right = states[source]
                for target, a, b in outgoing:
                    carry_right, next_left, next_right = states[target]
                    assert q * a + carry_right == b + 10 * carry_left
                    assert next_left == table[left][a] < len(word)
                    assert next_right == table[right][b] < len(word)
                    checks["product_edges"] += 1
            counts = [1 if i in starts else 0 for i in range(len(edges))]
            for length in range(1, 4):
                nxt = [0] * len(edges)
                for source, count in enumerate(counts):
                    for target, _, _ in edges[source]:
                        nxt[target] += count
                counts = nxt
                power = 10 ** length
                brute = 0
                for a_integer in range(power):
                    a_text = str(a_integer).zfill(length)
                    if word in a_text:
                        continue
                    for terminal_carry in range(q):
                        value = q * a_integer + terminal_carry
                        _, b_integer = divmod(value, power)
                        b_text = str(b_integer).zfill(length)
                        if word not in b_text:
                            brute += 1
                assert sum(counts) == brute
                checks["product_path_counts"] += 1
    return checks


def generate_feasibility_frontier():
    """Build explicit graphs up to a deterministic candidate-transition cap."""
    word = "0"
    q = 16
    rows = []
    exponent = 0
    while True:
        multiplier = q ** exponent
        state_count = multiplier * len(word)
        candidate_count = state_count * len(DIGITS) * len(DIGITS)
        row = {
            "exponent": exponent,
            "multiplier": multiplier,
            "carry_kmp_states": state_count,
            "transition_candidates": candidate_count,
        }
        if candidate_count > FRONTIER_CANDIDATE_BUDGET:
            row.update({
                "directed_edges": None,
                "live_states": None,
                "status": "deterministic-budget-stop",
            })
            rows.append(row)
            break
        edges = live_input_graph(word, multiplier)
        row.update({
            "directed_edges": sum(len(outgoing) for outgoing in edges),
            "live_states": len(live_vertices(edges)),
            "status": "constructed",
        })
        rows.append(row)
        exponent += 1
    return {
        "method": "explicit live-carry/KMP graph construction",
        "q": q,
        "word": word,
        "transition_candidate_budget": FRONTIER_CANDIDATE_BUDGET,
        "budget_rule": "construct a layer iff carry_kmp_states*10*10 <= transition_candidate_budget",
        "timing_claim": "none; this is a deterministic operation-count frontier",
        "rows": rows,
    }


def generate_tau_probes():
    """Small exact probes plus a reproducible explicit-state frontier."""
    probes = []
    # Broad shallow sample: every one-digit forbidden word, all q, ell <= 2.
    for word in map(str, DIGITS):
        for q in MULTIPLIERS:
            for ell in (1, 2):
                tau, frontier, uncovered = exact_tau(word, q, ell, max_m=3)
                probes.append({"word": word, "q": q, "ell": ell, "tau": tau,
                               "max_m": 3, "frontier": frontier,
                               "uncovered_if_incomplete": uncovered})
    # A few overlap-sensitive length-two/three words at depth one.
    for word in ("00", "01", "11", "09", "000", "010", "999"):
        for q in MULTIPLIERS:
            tau, frontier, uncovered = exact_tau(word, q, 1, max_m=2)
            probes.append({"word": word, "q": q, "ell": 1, "tau": tau,
                           "max_m": 2, "frontier": frontier,
                           "uncovered_if_incomplete": uncovered})
    return {
        "format_version": FORMAT_VERSION,
        "definition": "least M>=0 such that union_{0<=m<=M} prefix_language_ell(T_{q^m}(K_w)) is all decimal words of length ell",
        "convention": "one-sided symbolic infinite decimal strings; carry paths must have an infinite continuation; no circle-endpoint claim",
        "probes": probes,
        "feasibility_frontier": generate_feasibility_frontier(),
        "extrapolation": "No growth classification is claimed. Any continuation of the shallow data is heuristic.",
    }


def generate(directory: Path):
    directory.mkdir(parents=True, exist_ok=True)
    statement = directory / "pi-positive-decimal-factor-entropy.txt"
    if sha256(statement) != STATEMENT_SHA256:
        raise SystemExit("canonical statement hash mismatch")
    self_checks = transducer_self_checks()
    cases = []
    for word in words():
        for q in MULTIPLIERS:
            cases.append(certify_case(word, q))
    payload = {
        "format_version": FORMAT_VERSION,
        "convention": "one-sided symbolic decimal strings with unrestricted infinite carry paths",
        "carry_equation": "q*a_j+c_(j+1)=b_j+10*c_j",
        "entropy_unit": "natural logarithm; ranking uses exact Perron-root ratios before logarithms",
        "self_checks": self_checks,
        "cases": cases,
    }
    write_gzip_json(directory / "entropy_certificates.json.gz", payload)

    rows = []
    for case in cases:
        lower = parse_fraction(case["ratio_lower"])
        upper = parse_fraction(case["ratio_upper"]) if case["ratio_upper"] else None
        rows.append({
            "word": case["word"], "length": len(case["word"]), "q": case["q"],
            "rho_ratio_lower": f"{lower.numerator}/{lower.denominator}",
            "rho_ratio_upper": f"{upper.numerator}/{upper.denominator}" if upper else "infinity",
            "delta_lower_nats": decimal_log_bound(lower, True),
            "delta_upper_nats": decimal_log_bound(upper, False) if upper else "infinity",
            "states": case["state_count"], "reachable": case["reachable_count"],
        })
    with (directory / "delta_table.csv").open("w", newline="", encoding="ascii") as f:
        writer = csv.DictWriter(f, fieldnames=list(rows[0]))
        writer.writeheader()
        writer.writerows(rows)

    gamma = []
    for length in (1, 2, 3):
        for q in MULTIPLIERS:
            selected = [case for case in cases if len(case["word"]) == length and case["q"] == q]
            lower = min(parse_fraction(case["ratio_lower"]) for case in selected)
            finite_uppers = [(parse_fraction(case["ratio_upper"]), case["word"])
                             for case in selected if case["ratio_upper"]]
            upper, witness = min(finite_uppers)
            gamma.append({"length": length, "q": q, "ratio_lower": fraction_pair(lower),
                          "ratio_upper": fraction_pair(upper), "upper_witness": witness,
                          "gamma_lower_nats": decimal_log_bound(lower, True),
                          "gamma_upper_nats": decimal_log_bound(upper, False)})
    ranking = []
    for q in MULTIPLIERS:
        selected = [g for g in gamma if g["q"] == q]
        lower = min(parse_fraction(g["ratio_lower"]) for g in selected)
        upper_entry = min((parse_fraction(g["ratio_upper"]), g["length"]) for g in selected)
        ranking.append({"q": q, "ratio_lower": fraction_pair(lower),
                        "ratio_upper": fraction_pair(upper_entry[0]),
                        "witness_length": upper_entry[1],
                        "gap_lower_nats": decimal_log_bound(lower, True),
                        "gap_upper_nats": decimal_log_bound(upper_entry[0], False)})
    ranking.sort(key=lambda item: parse_fraction(item["ratio_lower"]), reverse=True)
    for rank, item in enumerate(ranking, 1):
        item["rank"] = rank
    summary = {
        "format_version": FORMAT_VERSION,
        "case_count": len(cases),
        "word_count": sum(10**k for k in (1, 2, 3)),
        "gamma": gamma,
        "worst_case_ranking": ranking,
        "ranking_rule": "descending certified worst-case entropy gap; verification requires pairwise-disjoint exact ratio intervals",
        "scope": "finite symbolic experiment only; no statement about pi",
    }
    (directory / "summary.json").write_text(
        json.dumps(summary, indent=2, sort_keys=True) + "\n", encoding="ascii")
    tau = generate_tau_probes()
    (directory / "tau_probes.json").write_text(
        json.dumps(tau, indent=2, sort_keys=True) + "\n", encoding="ascii")


def verify_case(case):
    word, q = case["word"], case["q"]
    base_edges, base_starts = baseline_graph(word)
    states, product_edges, product_starts = product_graph(word, q)
    assert case["state_count"] == len(states)
    assert case["reachable_count"] == len(reachable(product_edges, product_starts))
    for stored, edges, starts in ((case["base"], base_edges, base_starts),
                                  (case["product"], product_edges, product_starts)):
        allowed = reachable(edges, starts)
        actual_components = []
        for component in tarjan_scc(edges, allowed):
            rows = component_matrix(edges, component)
            if is_cyclic(rows):
                actual_components.append(component)
        assert [entry["nodes"] for entry in stored["components"]] == actual_components
        bounds = []
        for entry in stored["components"]:
            rows = component_matrix(edges, entry["nodes"])
            vector = [int(x) for x in entry["vector"]]
            lower, upper = collatz_bounds(rows, vector)
            assert fraction_pair(lower) == entry["lower"]
            assert fraction_pair(upper) == entry["upper"]
            bounds.append((lower, upper))
        expected_lower = max((x[0] for x in bounds), default=Fraction(0))
        expected_upper = max((x[1] for x in bounds), default=Fraction(0))
        assert parse_fraction(stored["lower"]) == expected_lower
        assert parse_fraction(stored["upper"]) == expected_upper
    base_l = parse_fraction(case["base"]["lower"])
    base_u = parse_fraction(case["base"]["upper"])
    prod_l = parse_fraction(case["product"]["lower"])
    prod_u = parse_fraction(case["product"]["upper"])
    assert parse_fraction(case["ratio_lower"]) == base_l / prod_u
    assert case["ratio_upper"] is not None and parse_fraction(case["ratio_upper"]) == base_u / prod_l


def verify(directory: Path):
    assert sha256(directory / "pi-positive-decimal-factor-entropy.txt") == STATEMENT_SHA256
    payload = read_gzip_json(directory / "entropy_certificates.json.gz")
    assert payload["format_version"] == FORMAT_VERSION
    assert payload["self_checks"] == transducer_self_checks()
    assert len(payload["cases"]) == 3330
    expected_keys = [(word, q) for word in words() for q in MULTIPLIERS]
    assert [(case["word"], case["q"]) for case in payload["cases"]] == expected_keys
    for number, case in enumerate(payload["cases"], 1):
        verify_case(case)
        assert parse_fraction(case["ratio_lower"]) > 1
        if number % 250 == 0:
            print(f"verified Perron certificates: {number}/3330", flush=True)

    with (directory / "delta_table.csv").open(newline="", encoding="ascii") as f:
        delta_rows = list(csv.DictReader(f))
    assert len(delta_rows) == 3330
    by_key = {(case["word"], case["q"]): case for case in payload["cases"]}
    for row in delta_rows:
        case = by_key[(row["word"], int(row["q"]))]
        assert row["rho_ratio_lower"] == "/".join(case["ratio_lower"])
        assert row["rho_ratio_upper"] == "/".join(case["ratio_upper"])
        assert row["delta_lower_nats"] == decimal_log_bound(
            parse_fraction(case["ratio_lower"]), True)
        assert row["delta_upper_nats"] == decimal_log_bound(
            parse_fraction(case["ratio_upper"]), False)

    summary = json.loads((directory / "summary.json").read_text(encoding="ascii"))
    assert summary["case_count"] == 3330 and summary["word_count"] == 1110
    for gamma in summary["gamma"]:
        selected = [case for case in payload["cases"]
                    if len(case["word"]) == gamma["length"] and case["q"] == gamma["q"]]
        assert parse_fraction(gamma["ratio_lower"]) == min(parse_fraction(c["ratio_lower"]) for c in selected)
        witness_upper = parse_fraction(by_key[(gamma["upper_witness"], gamma["q"])]["ratio_upper"])
        assert parse_fraction(gamma["ratio_upper"]) == witness_upper
        assert witness_upper == min(parse_fraction(c["ratio_upper"]) for c in selected)
        assert gamma["gamma_lower_nats"] == decimal_log_bound(
            parse_fraction(gamma["ratio_lower"]), True)
        assert gamma["gamma_upper_nats"] == decimal_log_bound(
            parse_fraction(gamma["ratio_upper"]), False)
    ranking = summary["worst_case_ranking"]
    assert [entry["rank"] for entry in ranking] == list(range(1, len(ranking) + 1))
    # Exact interval separation certifies the displayed order, strongest first.
    for stronger, weaker in zip(ranking, ranking[1:]):
        assert parse_fraction(stronger["ratio_lower"]) > parse_fraction(weaker["ratio_upper"])
    for entry in ranking:
        assert entry["gap_lower_nats"] == decimal_log_bound(
            parse_fraction(entry["ratio_lower"]), True)
        assert entry["gap_upper_nats"] == decimal_log_bound(
            parse_fraction(entry["ratio_upper"]), False)

    tau = json.loads((directory / "tau_probes.json").read_text(encoding="ascii"))
    expected_tau = generate_tau_probes()
    assert tau == expected_tau
    for probe in tau["probes"]:
        if probe["tau"] is not None:
            assert probe["frontier"][-1]["exponent"] == probe["tau"]
            assert probe["frontier"][-1]["uncovered_after"] == 0
            assert all(row["uncovered_after"] > 0 for row in probe["frontier"][:-1])
    frontier = tau["feasibility_frontier"]
    assert frontier["transition_candidate_budget"] == FRONTIER_CANDIDATE_BUDGET
    assert frontier["timing_claim"] == "none; this is a deterministic operation-count frontier"
    rows = frontier["rows"]
    assert rows and rows[-1]["status"] == "deterministic-budget-stop"
    assert all(row["status"] == "constructed" for row in rows[:-1])
    for row in rows:
        multiplier = frontier["q"] ** row["exponent"]
        state_count = multiplier * len(frontier["word"])
        candidate_count = state_count * len(DIGITS) * len(DIGITS)
        assert row["multiplier"] == multiplier
        assert row["carry_kmp_states"] == state_count
        assert row["transition_candidates"] == candidate_count
        if row["status"] == "constructed":
            assert candidate_count <= FRONTIER_CANDIDATE_BUDGET
            edges = live_input_graph(frontier["word"], multiplier)
            assert len(edges) == row["carry_kmp_states"]
            assert sum(len(outgoing) for outgoing in edges) == row["directed_edges"]
            assert len(live_vertices(edges)) == row["live_states"]
        else:
            assert candidate_count > FRONTIER_CANDIDATE_BUDGET
            assert row["directed_edges"] is None and row["live_states"] is None
    print("verified tau probes and feasibility frontier", flush=True)
    print("ALL T38 CHECKS PASSED", flush=True)


def replay(directory: Path):
    with tempfile.TemporaryDirectory(prefix="t38-replay-") as temp:
        target = Path(temp)
        for name in ("t38_experiment.py", "pi-positive-decimal-factor-entropy.txt"):
            shutil.copy2(directory / name, target / name)
        generate(target)
        for name in ("entropy_certificates.json.gz", "delta_table.csv", "summary.json", "tau_probes.json"):
            if (target / name).read_bytes() != (directory / name).read_bytes():
                raise AssertionError(f"regenerated artifact differs: {name}")
        verify(target)
    print("artifact-only regeneration matched byte-for-byte", flush=True)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("mode", choices=("generate", "verify", "replay"))
    parser.add_argument("--directory", type=Path, default=Path(__file__).resolve().parent)
    args = parser.parse_args()
    if args.mode == "generate":
        generate(args.directory)
    elif args.mode == "verify":
        verify(args.directory)
    else:
        replay(args.directory)


if __name__ == "__main__":
    main()
