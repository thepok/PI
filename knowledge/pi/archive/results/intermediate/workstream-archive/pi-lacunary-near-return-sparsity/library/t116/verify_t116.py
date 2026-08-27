#!/usr/bin/env python3
"""Self-contained integrity and finite transcription checks for T116.

All finite computations are experiments. They do not prove the universal
proof-sketch deductions in REPORT.md or any statement about pi, C1, or C2.
"""

from __future__ import annotations

import hashlib
from fractions import Fraction
from pathlib import Path


ROOT = Path(__file__).resolve().parent
CANONICAL_SHA = "cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8"
PDF_HASHES = {
    "rosenfeld-shen-2503.20529v1.pdf":
        "35e39cbf5006aa1dd459a51df5225f3fdbde214ddd4fb03d9bb4f81660e43f1c",
    "fishman-merrill-simmons-2018.pdf":
        "a1aa39f1783491077c55513c737895253bb7a7323fa7eb823afac672e48924d4",
    "moshchevitin-0709.3419v2.pdf":
        "d6b435d06149f5b5030be9a0e31175a8b8676d64e612acee282be74fd9f874a5",
    "broderick-fishman-kleinbock-1001.0318v3.pdf":
        "af22faa5bd33c9bf719c0c6fbfdf3c173d35ea7bee71368cffd0da0c0f0c9b36",
}
TEXT_HASHES = {
    "rosenfeld-shen-2503.20529v1.txt":
        "f9ad4a894679bbd3a7db5787a5bdef87fcab74265a3bb251438f111086b076a3",
    "fishman-merrill-simmons-2018.txt":
        "34621967d63c119b5b1f0d25fda15804cdfbb2dafaae17e0008ec9b9eaa9eff8",
    "moshchevitin-0709.3419v2.txt":
        "117fc4dee8a4d5bbeef0d1d36af90599146d228f0af6529068bdd437b2ae5278",
    "broderick-fishman-kleinbock-1001.0318v3.txt":
        "c7fffee401ed7249ca6d9641b30b88738bd861a7b57c597ad7a3f4f97724e259",
}


def sha256(name: str) -> str:
    return hashlib.sha256((ROOT / name).read_bytes()).hexdigest()


def assert_contains(name: str, markers: list[str]) -> None:
    text = (ROOT / name).read_text(encoding="utf-8")
    for marker in markers:
        assert marker in text, f"missing marker in {name}: {marker!r}"


def assert_line_contains(name: str, start: int, end: int, marker: str) -> None:
    lines = (ROOT / name).read_text(encoding="utf-8").splitlines()
    excerpt = "\n".join(lines[start - 1:end])
    assert marker in excerpt, f"missing {marker!r} in {name}:{start}-{end}"


def ceil_fraction(value: Fraction) -> int:
    return -(-value.numerator // value.denominator)


def shell_index(value: int) -> int:
    """Return j with 2^j < value <= 2^(j+1)."""
    j = value.bit_length() - 1
    if value == 1 << j:
        j -= 1
    return j


def decimal_shells(max_j: int) -> dict[int, set[int]]:
    shells = {j: set() for j in range(3, max_j + 1)}
    i = 1
    while 9 * 10 ** (i - 1) <= 2 ** (max_j + 1):
        for h in range(i):
            value = 10**i - 10**h
            j = shell_index(value)
            if 3 <= j <= max_j:
                shells[j].add(value)
        i += 1
    return shells


def r_for_shell(j: int) -> int:
    r = 3
    while 3 ** (r - 2) < 9 * (j + 1) * 2 ** (r - 2):
        r += 1
    return r


def check_rs_constants(max_j: int = 500) -> list[str]:
    shells = decimal_shells(max_j)
    nonempty = 0
    largest = 0
    for j, values in shells.items():
        if values:
            nonempty += 1
        largest = max(largest, len(values))
        assert len(values) <= j + 1
        r = r_for_shell(j)
        assert Fraction(3 * len(values) * 2 ** (r - 2), 3 ** (r - 2)) <= Fraction(1, 3)
        assert Fraction(1, 2**r) > Fraction(1, 648 * (j + 1) ** 2)
    return [
        f"rs_shells_checked=3..{max_j}",
        f"rs_nonempty_shells={nonempty}",
        f"rs_largest_observed_shell={largest}",
        "rs_weight_and_delta_bounds=ok",
    ]


def shell_forbidden_vertices(
    j: int, values: set[int], current_depth: int, current_index: int
) -> tuple[int, set[tuple[int, int]]]:
    r = r_for_shell(j)
    target_depth = j + r
    assert current_depth == j + 2
    epsilon = Fraction(1, 2**r)
    current_left = Fraction(current_index, 2**current_depth)
    current_right = Fraction(current_index + 1, 2**current_depth)
    first_descendant = current_index * 2 ** (target_depth - current_depth)
    last_descendant = (current_index + 1) * 2 ** (target_depth - current_depth) - 1
    result: set[tuple[int, int]] = set()
    for t in values:
        first_a = max(0, ceil_fraction(t * current_left - epsilon))
        last_a = min(t, (t * current_right + epsilon).numerator // (t * current_right + epsilon).denominator)
        for a in range(first_a, last_a + 1):
            lower = Fraction(a, t) - Fraction(epsilon, t)
            upper = Fraction(a, t) + Fraction(epsilon, t)
            scaled_lower = lower * 2**target_depth
            scaled_upper = upper * 2**target_depth
            first_q = max(first_descendant, ceil_fraction(scaled_lower - 1))
            last_q = min(last_descendant, scaled_upper.numerator // scaled_upper.denominator)
            for q in range(first_q, last_q + 1):
                result.add((target_depth, q))
    assert len(result) <= 3 * len(values)
    return target_depth, result


def interval_meets_bad(depth: int, index: int, t: int, epsilon: Fraction) -> bool:
    left = Fraction(index, 2**depth)
    right = Fraction(index + 1, 2**depth)
    first_a = max(0, ceil_fraction(t * left - epsilon))
    last_a = min(t, (t * right + epsilon).numerator // (t * right + epsilon).denominator)
    return first_a <= last_a


def check_rs_interval_experiment(max_j: int = 20) -> list[str]:
    target_depths = {j: j + r_for_shell(j) for j in range(3, max_j + 1)}
    final_depth = max(target_depths.values())
    schedule_max_j = final_depth - 3
    shells = decimal_shells(schedule_max_j)
    announced: set[tuple[int, int]] = set()
    by_shell: dict[int, set[tuple[int, int]]] = {}
    path_indices = [0]

    for m in range(final_depth):
        current = path_indices[m]
        j = m - 2
        if 3 <= j <= schedule_max_j:
            depth, new_vertices = shell_forbidden_vertices(j, shells[j], m, current)
            if j <= max_j:
                assert depth == target_depths[j]
            by_shell[j] = new_vertices
            announced.update(new_vertices)

        weights = []
        for bit in (0, 1):
            child = 2 * current + bit
            weight = Fraction(0)
            for depth, index in announced:
                if depth >= m + 1 and index // 2 ** (depth - (m + 1)) == child:
                    weight += Fraction(2 ** (depth - (m + 1)), 3 ** (depth - (m + 1)))
            weights.append(weight)
        bit = 0 if weights[0] < 1 else 1
        assert weights[bit] < 1
        assert 1 - weights[bit] > 0
        path_indices.append(2 * current + bit)

    for j in range(3, max_j + 1):
        depth = target_depths[j]
        index = path_indices[depth]
        assert (depth, index) not in by_shell[j]
        for earlier in range(3, j + 1):
            epsilon = Fraction(1, 2 ** r_for_shell(earlier))
            for t in shells[earlier]:
                assert not interval_meets_bad(depth, index, t, epsilon)
    return [f"rs_macro_stages={max_j - 2}", "rs_extendible_and_safe_intervals=ok"]


def blocks(word: list[int], length: int, starts: int) -> list[tuple[int, ...]]:
    return [tuple(word[i:i + length]) for i in range(starts)]


def fms_extension(old: list[int], order: int, alphabet_size: int) -> list[int]:
    """One deterministic corrected-Corollary-4.3 extension for experiments."""
    assert len(old) == alphabet_size**order + order - 1
    fixed = old + [old[order - 1]]
    used_edges = {
        tuple(fixed[i:i + order + 1])
        for i in range(alphabet_size**order)
    }
    vertices = blocks(old, order, alphabet_size**order)
    outgoing: dict[tuple[int, ...], list[int]] = {}
    for vertex in vertices:
        allowed = []
        for digit in range(alphabet_size):
            edge = vertex + (digit,)
            if edge not in used_edges:
                allowed.append(digit)
        outgoing[vertex] = list(reversed(allowed))

    labels_reversed: list[int] = []

    def visit(vertex: tuple[int, ...]) -> None:
        while outgoing[vertex]:
            digit = outgoing[vertex].pop()
            nxt = vertex[1:] + (digit,) if order > 1 else (digit,)
            visit(nxt)
            labels_reversed.append(digit)

    visit(tuple(fixed[:order]))
    result = fixed + list(reversed(labels_reversed))
    assert len(result) == alphabet_size ** (order + 1) + order
    return result


def decimal_code(block: tuple[int, ...]) -> int:
    value = 0
    for digit in block:
        value = 10 * value + digit
    return value


def check_fms_experiment() -> list[str]:
    alphabet_size = 4
    odd_digits = [1, 3, 5, 7]
    word = list(range(alphabet_size))
    lines = []
    for order in range(1, 5):
        starts = alphabet_size**order
        factors = blocks(word, order, starts)
        assert len(set(factors)) == starts
        codes = [decimal_code(tuple(odd_digits[d] for d in factor)) for factor in factors]
        modulus = 10**order
        for i, left in enumerate(codes):
            for j, right in enumerate(codes):
                cyclic = min((left - right) % modulus, (right - left) % modulus)
                if cyclic <= 1:
                    assert i == j
        lines.append(f"fms_order={order} starts={starts} diagonal_only=ok")
        if order < 4:
            word = fms_extension(word, order, alphabet_size)
    return lines


def check_threshold_experiment() -> list[str]:
    checked = 0
    for a in range(1, 101):
        for n in range(16 * a, 16 * a + 8):
            assert 10368 * a * a * n * n < 10**n
            checked += 1
    return [f"rs_threshold_instances={checked}", "rs_threshold_instances=ok"]


def check_report_contract() -> None:
    report = (ROOT / "REPORT.md").read_text(encoding="utf-8")
    pins = (ROOT / "SOURCE_PINS.md").read_text(encoding="utf-8")
    required = [
        "PRIMARY_SOURCE_COUNT: 4",
        "PRIMARY_SOURCE_CAP: 12",
        "SEARCHED_LANE_COUNT: 4",
        "RETAINED_CANDIDATE_COUNT: 4",
        "RETAINED_CANDIDATE_CAP: 4",
        "TERMINAL_VERDICT_COUNT: 1",
        "SUCCESSOR_COUNT: 1",
        "Q_(x_RS)(n,A*n)=A*n",
        "Q_(x_FMS)(n,A*n)=A*n",
        "PI-RS:",
        "active T114",
        "active T115",
        "semantic memory",
        "TERMINAL_VERDICT: hold as model",
    ]
    for marker in required:
        assert marker in report, f"missing report marker: {marker!r}"
    assert report.count("TERMINAL_VERDICT:") == 1
    assert report.count("TERMINAL_VERDICT_COUNT:") == 1
    assert report.count("SUCCESSOR_COUNT:") == 1
    assert report.count("The sole bounded successor") == 1
    assert report.count("## S1:") == 0
    assert pins.count("## S1:") == 1
    assert pins.count("## S2:") == 1
    assert pins.count("## S3:") == 1
    assert pins.count("## S4:") == 1
    for expected in [*PDF_HASHES.values(), *TEXT_HASHES.values()]:
        assert expected in pins
    for prior in ["T90", "T104", "T105", "T111", "T112", "T113", "T109"]:
        assert prior in report
    for candidate in ["C-RS", "C-FMS", "C-MOS", "C-BFK"]:
        assert candidate in report
    candidate_headings = [
        "## 3. C-RS:", "## 4. C-FMS:", "## 5. C-MOS:", "## 6. C-BFK:",
    ]
    assert sum(report.count(heading) for heading in candidate_headings) == 4
    comparison = report.split("## 8. Comparison with every mandatory prior and active fingerprint", 1)[1]
    comparison = comparison.split("## 9. Explicit additional pi-specific certificate", 1)[0]
    rows = [line for line in comparison.splitlines() if line.startswith("| C-")]
    assert len(rows) == 4
    assert all(len(row.split("|")) == 13 for row in rows), "comparison table must have 11 columns"
    assert "content unavailable" not in comparison
    assert "db21ac7d0a7845264c727132293db149a06a832d6f67700fd9ceb0f69a142cca" in comparison
    assert "29cd0707df354aef8f50e4dfa4b9a780b863d93aef26cebdc4cbb8488ee27a36" in comparison
    for row in rows:
        cells = [cell.strip() for cell in row.split("|")[1:-1]]
        assert "T114" in cells[8], f"missing candidate-specific T114 comparison: {cells[0]}"
        assert "T115" in cells[9], f"missing candidate-specific T115 comparison: {cells[0]}"
    files = [path for path in ROOT.rglob("*") if path.is_file()]
    assert len(files) <= 16
    assert len([path for path in files if path.suffix == ".pdf"]) == 4
    assert not any("__pycache__" in path.parts for path in files)
    prohibited = [
        "PI-RS holds",
        "canonical C1 is proved",
        "progress on pi",
        "progress on C1",
        "progress on C2",
    ]
    for phrase in prohibited:
        assert phrase not in report, f"prohibited assertion: {phrase!r}"


def main() -> None:
    assert sha256("canonical_statement.txt") == CANONICAL_SHA
    for name, expected in PDF_HASHES.items():
        assert sha256(name) == expected, f"hash mismatch: {name}"
    for name, expected in TEXT_HASHES.items():
        assert sha256(name) == expected, f"hash mismatch: {name}"

    assert_contains("rosenfeld-shen-2503.20529v1.txt", [
        "Theorem 1.", "Theorem 2.", "Theorem 8.", "Lemma 1.",
    ])
    assert_contains("fishman-merrill-simmons-2018.txt", [
        "Corollary 4.3.", "Proposition 4.2.", "Remark 3.3.",
    ])
    assert_contains("moshchevitin-0709.3419v2.txt", [
        "Theorem 1.", "Theorem 2.", "H(n,",
    ])
    assert_contains("broderick-fishman-kleinbock-1001.0318v3.txt", [
        "Theorem 1.3.", "Lemma 3.2.", "Theorem 4.1.",
    ])
    assert_line_contains("rosenfeld-shen-2503.20529v1.txt", 87, 149, "Theorem 2.")
    assert_line_contains("rosenfeld-shen-2503.20529v1.txt", 430, 524, "Lemma 1.")
    assert_line_contains("fishman-merrill-simmons-2018.txt", 137, 155, "de Bruijn")
    assert_line_contains("fishman-merrill-simmons-2018.txt", 503, 617, "Corollary 4.3.")
    assert_line_contains("moshchevitin-0709.3419v2.txt", 66, 129, "Theorem 2.")
    assert_line_contains("broderick-fishman-kleinbock-1001.0318v3.txt", 390, 480, "Theorem 4.1.")
    check_report_contract()
    artifact_count = len([path for path in ROOT.rglob("*") if path.is_file()])
    output = [
        "canonical_sha256=ok",
        "primary_pdf_hashes=4/4",
        "source_pdf_and_text_hashes=8/8",
        "source_anchor_sets=4/4",
        "report_contract=ok",
        f"artifact_files={artifact_count}/16",
        "comparison_cells=40/40",
        "t114_t115_comparisons=8/8",
        *check_rs_constants(),
        *check_rs_interval_experiment(),
        *check_threshold_experiment(),
        *check_fms_experiment(),
        "finite_checks_label=experiment",
    ]
    expected = (ROOT / "raw_output.txt").read_text(encoding="utf-8").splitlines()
    assert output == expected, "replay output differs from raw_output.txt"
    print("\n".join(output))


if __name__ == "__main__":
    main()
