#!/usr/bin/env python3
"""Finite falsification checks for T169; this script is not a proof."""

from __future__ import annotations

from collections import Counter, defaultdict
from hashlib import sha256
from pathlib import Path


CANONICAL_SHA256 = "cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8"
T160_SHA256 = "94858ae03b2bad5ef66a0d46fa869c3f0dd3cd62d1cf076e7ae2c7104ca30b76"
T165_SHA256 = "a151ea4c939c65c48d3b728664ccc26b7eb0d7c7b2826b4babf1286c060384fc"


def length_formula(k: int) -> int:
    if k == 0:
        return 0
    return (1 + (9 * k - 1) * 10**k) // 9


def carry_length(n: int) -> int:
    result = 0
    while n % 10 == 9:
        result += 1
        n //= 10
    return result


def build_prefix(k: int):
    digits = []
    anchors = []
    for n in range(1, 10**k):
        text = str(n)
        for a, digit in enumerate(text):
            digits.append(digit)
            anchors.append((n, len(text), a))
    return "".join(digits), anchors


def start_record(anchors, i: int, m: int):
    n, d, a = anchors[i]
    endpoint = i + m - 1
    signature = []
    previous = n
    for position in range(i + 1, endpoint + 1):
        current = anchors[position][0]
        if current != previous:
            assert current == previous + 1
            q = len(str(previous))
            if previous == 10**q - 1:
                signature.append(("rollover", q))
            else:
                signature.append(("ordinary", q, carry_length(previous)))
            previous = current
    return d, a, tuple(signature)


def A(k: int, m: int) -> int:
    return sum(10 ** (d - m) for d in range(m, k + 1))


def B(k: int, m: int) -> int:
    return sum(9 * (d - m) * 10 ** (d - m - 1) for d in range(m + 1, k + 1))


def rho(k: int, m: int, a: int) -> str:
    b = k - a
    r = m - b
    assert 1 <= b < m and r >= 1
    return "9" * b + "1" + "0" * (r - 1)


def check_case(k: int, m: int, word: str, anchors):
    M = len(word) - m + 1
    blocks = [word[i : i + m] for i in range(M)]
    counts = Counter(blocks)
    energy = sum(c * c for c in counts.values())

    classes = defaultdict(Counter)
    low = Counter()
    high_alignment = defaultdict(Counter)
    for i, block in enumerate(blocks):
        record = start_record(anchors, i, m)
        classes[record][block] += 1
        d, a, _ = record
        if d < m:
            low[block] += 1
        else:
            high_alignment[(d, a)][block] += 1

    classified = 0
    for left in classes.values():
        for right in classes.values():
            classified += sum(c * right.get(block, 0) for block, c in left.items())
    assert classified == energy

    all_words = [f"{value:0{m}d}" for value in range(10**m)]
    for d in range(m, k + 1):
        for a in range(d):
            actual = high_alignment[(d, a)]
            crossing = a + m > d
            terminal = rho(k, m, a) if d == k and crossing else None
            for block in all_words:
                if a == 0:
                    expected = (1 if block[0] != "0" else 0) * 10 ** (d - m)
                elif not crossing:
                    expected = 9 * 10 ** (d - m - 1)
                else:
                    expected = (1 if block[d - a] != "0" else 0) * 10 ** (d - m)
                if terminal == block:
                    expected -= 1
                assert actual.get(block, 0) == expected, (k, m, d, a, block)

    low_total = length_formula(m - 1)
    assert sum(low.values()) == low_total
    terminal_words = {rho(k, m, a) for a in range(k - m + 1, k)}
    assert len(terminal_words) == m - 1
    for block in all_words:
        z = sum(digit != "0" for digit in block)
        exact = A(k, m) * z + B(k, m) + low.get(block, 0) - (block in terminal_words)
        assert counts.get(block, 0) == exact

    assert sum(counts.values()) == M == length_formula(k) - m + 1
    centered_numerator = sum((10**m * counts.get(block, 0) - M) ** 2 for block in all_words)
    assert 10**m * energy - M * M == centered_numerator // 10**m
    assert centered_numerator % 10**m == 0

    x2_scaled = sum((10 * sum(digit != "0" for digit in block) - 9 * m) ** 2 for block in all_words)
    assert x2_scaled == 9 * m * 10**m

    S = low_total + m - 1
    left = 10**m * energy - M * M
    right = (3 * A(k, m) * m**0.5 / 10 + S) ** 2 * 10 ** (2 * m)
    assert left <= right + 1e-7 * max(1, right)
    return M, len(counts), max(counts.values()), energy


def check_report() -> None:
    root = Path(__file__).resolve().parent
    assert sha256((root / "canonical_statement.txt").read_bytes()).hexdigest() == CANONICAL_SHA256
    t160 = root / "prior-T160-REPORT.md"
    t165 = root / "prior-T165-REPORT.md"
    assert sha256(t160.read_bytes()).hexdigest() == T160_SHA256
    assert sha256(t165.read_bytes()).hexdigest() == T165_SHA256
    t160_text = t160.read_text(encoding="ascii")
    t165_text = t165.read_text(encoding="ascii")
    for marker in ["`literature-checked`", "`proof sketch`", "`experiment`", "Candidate C-CHAMP"]:
        assert marker in t160_text, marker
    for marker in ["universal argument in Sections 2--7 is a `proof sketch`", "finite\n`experiment`", "15/(4*10^m)", "E<=M*cmax"]:
        assert marker in t165_text, marker
    text = (root / "REPORT.md").read_text(encoding="ascii")
    required = [
        "E_(K,m)=sum_(w in {0,...,9}^m) c_(K,m)(w)^2",
        "sum_(ordered alpha,beta) sum_w c_alpha(w)c_beta(w)",
        "c_(K,m)(w)=A_(K,m)Z(w)+B_(K,m)+D_(K,m)(w)-R_(K,m)(w)",
        "<= 1/(16K)",
        "T160_USED_AS_PREMISE: no",
        "T165_USED_AS_PREMISE: no",
        "PI-PAIR-CLASS-CANCELLATION-T169",
        "FINITE_CHECKS_ARE_PROOF: no",
    ]
    for marker in required:
        assert marker in text, marker


def main() -> None:
    check_report()
    rows = []
    cases = 0
    for k in range(1, 5):
        word, anchors = build_prefix(k)
        for m in range(1, min(k, 4) + 1):
            row = check_case(k, m, word, anchors)
            cases += 1
            if (k, m) in {(2, 1), (2, 2), (3, 2), (3, 3), (4, 1), (4, 4)}:
                rows.append((k, m, *row))
    print("T169 finite falsification replay (experiment; not proof)")
    print(f"canonical_sha256={CANONICAL_SHA256}")
    print(f"enumerated_cases={cases}")
    print("selected_rows: K m M distinct cmax E")
    for row in rows:
        print(" ".join(str(value) for value in row))
    print("complete_start_records=PASS")
    print("ordered_pair_class_reconstruction=PASS")
    print("exact_high_stratum_formula=PASS")
    print("exact_centered_energy_identity=PASS")
    print("finite_checks_are_proof=no")
    print("status=PASS")


if __name__ == "__main__":
    main()
