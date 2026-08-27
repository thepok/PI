#!/usr/bin/env python3
"""Finite validation for T165. This script is an experiment, not a proof."""

from __future__ import annotations

from collections import Counter, defaultdict
from hashlib import sha256
from pathlib import Path


CANONICAL_SHA256 = "cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8"


def length_formula(k: int) -> int:
    return (1 + (9 * k - 1) * 10**k) // 9


def carry_length(n: int) -> int:
    count = 0
    while n % 10 == 9:
        count += 1
        n //= 10
    return count


def build_prefix(k: int):
    chars = []
    anchors = []
    for n in range(1, 10**k):
        digits = str(n)
        d = len(digits)
        for a, digit in enumerate(digits):
            chars.append(digit)
            anchors.append((n, d, a))
    return "".join(chars), anchors


def start_class(anchors, i: int, m: int):
    n, d, a = anchors[i]
    endpoint = i + m - 1
    crossed = []
    previous = n
    for position in range(i + 1, endpoint + 1):
        current = anchors[position][0]
        if current != previous:
            assert current == previous + 1
            old_d = len(str(previous))
            if previous == 10**old_d - 1:
                crossed.append((old_d, "rollover"))
            else:
                inspected_suffix = old_d - a if previous == n else old_d
                crossed.append(
                    (old_d, "ordinary", min(carry_length(previous), inspected_suffix))
                )
            previous = current
    if d < m:
        return ("low", d, a, tuple(crossed))
    b = d - a
    if b >= m:
        assert not crossed
        return ("high", d, a, "internal")
    assert len(crossed) == 1
    return ("high", d, a, "crossing", crossed[0])


def exact_bound(k: int, m: int) -> int:
    low = length_formula(m - 1) if m > 1 else 0
    return low + sum(d * (10 ** (d - m) + 1) for d in range(m, k + 1))


def check_prefix(k: int, m: int, word: str, anchors) -> tuple[int, int, int, int]:
    length = len(word)
    assert length == length_formula(k) == len(anchors)
    starts = length - m + 1
    blocks = [word[i : i + m] for i in range(starts)]
    counts = Counter(blocks)
    energy = sum(value * value for value in counts.values())
    positions = defaultdict(list)
    for i, block in enumerate(blocks):
        positions[block].append(i)
    assert energy == sum(len(group) ** 2 for group in positions.values())
    if starts <= 600:
        literal_pairs = sum(1 for left in blocks for right in blocks if left == right)
        assert energy == literal_pairs
    assert energy >= starts

    class_counts = defaultdict(Counter)
    low_count = 0
    for i, block in enumerate(blocks):
        assert i + m - 1 < length
        key = start_class(anchors, i, m)
        class_counts[key][block] += 1
        if key[0] == "low":
            low_count += 1
    assert sum(sum(counter.values()) for counter in class_counts.values()) == starts

    classified_energy = 0
    counters = list(class_counts.values())
    for left in counters:
        for right in counters:
            classified_energy += sum(value * right.get(block, 0) for block, value in left.items())
    assert classified_energy == energy

    assert low_count <= (length_formula(m - 1) if m > 1 else 0)
    high_by_alignment = defaultdict(Counter)
    for key, counter in class_counts.items():
        if key[0] == "high":
            _, d, a, *_rest = key
            high_by_alignment[(d, a)].update(counter)
    for (d, a), counter in high_by_alignment.items():
        b = d - a
        cap = 10 ** (d - m) + (1 if b < m else 0)
        assert max(counter.values(), default=0) <= cap
        assert max(counter.values(), default=0) <= 10 ** (d - m) + 1

    bound = exact_bound(k, m) if m <= k else starts
    if m <= k:
        assert max(counts.values()) <= bound
        assert energy <= starts * max(counts.values()) <= starts * bound
    return starts, len(counts), max(counts.values()), energy


def check_constants() -> int:
    cases = 0
    for k in range(4, 129):
        for m in range(1, k // 4 + 1):
            bound = exact_bound(k, m)
            assert bound <= 3 * k * 10 ** (k - m)
            starts = length_formula(k) - m + 1
            assert starts >= 8 * k * 10 ** (k - 1)
            assert 4 * 10**m * bound <= 15 * starts
            if 15 * m <= 4 * 10**m:
                assert m * bound <= starts
            cases += 1
    for a in range(1, 33):
        for k in range(8 * a, 8 * a + 17):
            for m in range(2 * a, k // 4 + 1):
                assert 15 * a * m <= 4 * 10**m
                cases += 1
    return cases


def check_report_and_canonical() -> None:
    root = Path(__file__).resolve().parent
    canonical = root / "canonical_statement.txt"
    report = root / "REPORT.md"
    assert sha256(canonical.read_bytes()).hexdigest() == CANONICAL_SHA256
    text = report.read_text(encoding="ascii")
    required = [
        "T160_USED_AS_PREMISE: no",
        "E_(K,m)=sum_w c_(K,m)(w)^2",
        "15*A*m <= 4*10^m",
        "2A<=m<=floor(K/4)",
        "active T163",
        "active T164",
        "PI-ARITHMETIC-FIBER-T165",
        "SCOPED VERDICT (1/1): HOLD AS MODEL.",
        "AUTOMATIC_SUCCESSOR_COUNT: 0",
    ]
    for marker in required:
        assert marker in text, marker
    assert text.count("SCOPED VERDICT (1/1)") == 1


def main() -> None:
    check_report_and_canonical()
    rows = []
    prefix_cases = 0
    for k in range(1, 5):
        word, anchors = build_prefix(k)
        for m in range(1, min(6, len(word)) + 1):
            starts, distinct, maximum, energy = check_prefix(k, m, word, anchors)
            prefix_cases += 1
            if (k, m) in {(2, 1), (2, 2), (3, 3), (4, 1), (4, 4), (4, 6)}:
                rows.append((k, m, starts, distinct, maximum, energy))
    constant_cases = check_constants()
    print("T165 finite validation (experiment; not proof)")
    print(f"canonical_sha256={CANONICAL_SHA256}")
    print(f"prefix_cases={prefix_cases}")
    print("literal_pair_enumeration_cases=12")
    print(f"constant_grid_cases={constant_cases}")
    print("selected_rows: K m M distinct cmax E")
    for row in rows:
        print(" ".join(str(value) for value in row))
    print("class_partition=PASS")
    print("ordered_diagonal_energy=PASS")
    print("stratum_alignment_boundary_carry=PASS")
    print("explicit_constants=PASS")
    print("status=PASS")


if __name__ == "__main__":
    main()
