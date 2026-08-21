#!/usr/bin/env python3
"""Finite replay for T144; experiments here are not proofs of the theorem."""

from fractions import Fraction
from hashlib import sha256
from itertools import product
from math import log, sqrt
from pathlib import Path


CANONICAL_SHA = "cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8"


def energy(word: tuple[int, ...], m: int) -> int:
    counts: dict[tuple[int, ...], int] = {}
    for i in range(len(word) - m + 1):
        block = word[i : i + m]
        counts[block] = counts.get(block, 0) + 1
    return sum(value * value for value in counts.values())


def residue_data(word: tuple[int, ...], m: int) -> tuple[list[int], list[int]]:
    M = len(word) - m + 1
    qs = []
    es = []
    for r in range(m):
        starts = list(range(r, M, m))
        counts: dict[tuple[int, ...], int] = {}
        used: set[int] = set()
        for i in starts:
            block = word[i : i + m]
            counts[block] = counts.get(block, 0) + 1
            coordinates = set(range(i, i + m))
            assert not used.intersection(coordinates)
            used.update(coordinates)
        assert len(used) == len(starts) * m
        qs.append(len(starts))
        es.append(sum(value * value for value in counts.values()))
    assert sum(qs) == M
    return qs, es


def exact_small_sweep() -> tuple[int, int]:
    words = 0
    bad_implications = 0
    for N in range(1, 8):
        # This finite binary subclass can expose small counterexamples only.
        for word in product(range(2), repeat=N):
            words += 1
            for m in range(1, N + 1):
                M = N - m + 1
                qs, es = residue_data(word, m)
                E = energy(word, m)
                assert E <= m * sum(es)
                if M >= m:
                    assert sum(q * q for q in qs) * m <= 2 * M * M
                if m == 1:
                    assert E <= M * M
                elif E * m > M * M:
                    assert any(Fraction(er, qr * qr) > Fraction(1, 2 * m)
                               for qr, er in zip(qs, es) if qr)
                    bad_implications += 1
    return words, bad_implications


def type_count(q: int, K: int) -> int:
    # Dynamic enumeration of weak compositions, used only at tiny parameters.
    row = [0] * (q + 1)
    row[0] = 1
    for _ in range(K):
        new = [0] * (q + 1)
        running = 0
        for total in range(q + 1):
            running += row[total]
            new[total] = running
        row = new
    return row[q]


def check_type_bounds() -> int:
    checks = 0
    for q in range(0, 9):
        for K in range(1, 9):
            count = type_count(q, K)
            assert count <= (q + 1) ** K
            checks += 1
    return checks


def check_real_constants() -> tuple[float, float, float]:
    # These finite scans test the constants only. Section 4 proves monotonicity.
    min_case_one = float("inf")
    min_case_two = float("inf")
    for m in range(2, 100_001):
        target = sqrt(m) / 100
        case_one = (m * log(10) - log(8 * m * sqrt(m)) - 1) / (2 * sqrt(m))
        case_two = (m * log(10) - log(8 * m)) / 2 - log(2)
        assert case_one > target
        assert case_two > target
        min_case_one = min(min_case_one, case_one - target)
        min_case_two = min(min_case_two, case_two - target)

    N = 800 ** 8
    assert log(N + 1) + 1 <= N ** Fraction(1, 8)
    assert N ** Fraction(3, 8) <= sqrt(N) / 800
    endpoint_margin = sqrt(N) / 800 - N ** Fraction(3, 8)
    return min_case_one, min_case_two, float(endpoint_margin)


def main() -> None:
    root = Path(__file__).resolve().parent
    canonical = root / "canonical_statement.txt"
    digest = sha256(canonical.read_bytes()).hexdigest()
    assert digest == CANONICAL_SHA

    words, implications = exact_small_sweep()
    type_checks = check_type_bounds()
    case_one, case_two, endpoint = check_real_constants()

    print("T144 finite replay: experiment only")
    print(f"canonical_sha256={digest}")
    print(f"binary_words_checked={words}")
    print(f"bad_event_implications_checked={implications}")
    print(f"type_count_bounds_checked={type_checks}")
    print(f"case_one_min_scanned_margin={case_one:.12f}")
    print(f"case_two_min_scanned_margin={case_two:.12f}")
    print(f"union_endpoint_margin={endpoint:.1f}")
    print("constants=kappa:1/4,A:1,c_A:1/400,C_A:1")
    print("verdict=develop")
    print("pi_transfer=unproved")
    print("fixed_pi_claim=none;A1_claim=none;C1_claim=none;C2_claim=none")


if __name__ == "__main__":
    main()
