#!/usr/bin/env python3
"""Self-contained finite and source-pin replay for the T140 literature audit."""

from __future__ import annotations

import hashlib
import itertools
import math
import pathlib
import subprocess
import tarfile


ROOT = pathlib.Path(__file__).resolve().parent
CANONICAL_SHA = "cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8"
PDF_PINS = {
    "saxton-thomason-1204.6595v3.pdf":
        "23dd1542e20d1513b7021828cb4e4153a5091774117616727791272357622437",
    "balogh-morris-samotij-1204.6530v2.pdf":
        "2e2a7973b172bdb6e539d1cd541c0d8640fcb72f07f58b7816e94854dceb47fe",
}


def sha256(name: str) -> str:
    return hashlib.sha256((ROOT / name).read_bytes()).hexdigest()


def page_text(name: str, first: int, last: int) -> str:
    return subprocess.check_output(
        ["pdftotext", "-f", str(first), "-l", str(last), "-layout",
         str(ROOT / name), "-"], text=True
    )


def blocks(word: tuple[int, ...], n: int, m: int) -> list[tuple[int, ...]]:
    return [word[i:i + m] for i in range(n)]


def collision_energy(word: tuple[int, ...], n: int, m: int) -> int:
    ws = blocks(word, n, m)
    return sum(a == b for a in ws for b in ws)


def label_edges(word: tuple[int, ...], n: int, m: int) -> int:
    ws = blocks(word, n, m)
    return sum(ws[i] == ws[j] for i in range(n) for j in range(i + 1, n))


def far_edges(word: tuple[int, ...], n: int, m: int) -> int:
    ws = blocks(word, n, m)
    return sum(ws[i] == ws[j]
               for i in range(n) for j in range(i + m, n))


def digit_edges(n: int, m: int, alphabet: int = 10) -> set[frozenset[tuple[int, int]]]:
    edges: set[frozenset[tuple[int, int]]] = set()
    for i in range(n):
        for j in range(i + m, n):
            for u in itertools.product(range(alphabet), repeat=m):
                edge = {(i + t, u[t]) for t in range(m)}
                edge |= {(j + t, u[t]) for t in range(m)}
                edges.add(frozenset(edge))
    return edges


def max_codegree(edges: set[frozenset[tuple[int, int]]], size: int) -> int:
    counts: dict[frozenset[tuple[int, int]], int] = {}
    for edge in edges:
        for subset in itertools.combinations(edge, size):
            key = frozenset(subset)
            counts[key] = counts.get(key, 0) + 1
    return max(counts.values())


def main() -> None:
    assert sha256("canonical_statement.txt") == CANONICAL_SHA
    for name, expected in PDF_PINS.items():
        assert sha256(name) == expected

    st = page_text("saxton-thomason-1204.6595v3.pdf", 11, 14)
    for anchor in ["Definition 3.1", "Definition 3.2", "Definition 3.3",
                   "Theorem 3.4", "independent set", "degenerate"]:
        assert anchor in st
    bms = page_text("balogh-morris-samotij-1204.6530v2.pdf", 11, 12)
    for anchor in ["Deﬁnition 2.1", "Theorem 2.2", "dense",
                   "∆ℓ (H)", "I(H)"]:
        assert anchor in bms

    report = (ROOT / "REPORT.md").read_text()
    required = [
        "PRIMARY_SOURCE_COUNT: 2", "PRIMARY_SOURCE_CAP: 6",
        "RETAINED_THEOREM_COUNT: 2", "RETAINED_THEOREM_CAP: 2",
        "N>=10^8", "kappa = 1/4", "rho = 1/4",
        "SCOPED_VERDICT (1/1): **close**",
        "T139 | absent", "PI-CONTAINER-EXCLUSION-T140",
        "FIXED_PI_CLAIM: none", "C1_CLAIM: none", "C2_CLAIM: none",
        "inapplicability, not falsification", "SUCCESSOR_COUNT: 0",
        "e(H^dig[X_z])/e(H^dig) <= 10^(-m)",
        "d_avg=r*e/v=2m*P_(N,m)*10^(m-1)/L",
    ]
    for marker in required:
        assert marker in report, marker
    for item in range(89, 140):
        assert f"| T{item} |" in report, f"missing novelty row T{item}"

    # Exact ordered, diagonal-inclusive identity and Encoding A identity.
    word = tuple(int(c) for c in "001001001001")
    n, m = 9, 3
    energy = collision_energy(word, n, m)
    pairs = label_edges(word, n, m)
    assert energy == n + 2 * pairs

    # Encoding B edge count and 2m-uniformity at a finite decimal instance.
    n2, m2 = 7, 2
    edges = digit_edges(n2, m2)
    p = (n2 - m2) * (n2 - m2 + 1) // 2
    assert len(edges) == p * 10**m2
    assert {len(edge) for edge in edges} == {2 * m2}
    vertices = 10 * (n2 + m2 - 1)
    average_degree = sum(len(edge) for edge in edges) / vertices
    expected_degree = (2 * m2) * p * 10**m2 / vertices
    assert average_degree == expected_degree

    # Direct finite equality between induced digit edges and far collisions.
    word2 = tuple(int(c) for c in "0120120120")
    chosen = {(q, digit) for q, digit in enumerate(word2)}
    induced = sum(edge <= chosen for edge in edges)
    assert induced == far_edges(word2, n2, m2)
    assert induced / len(edges) <= 10**(-m2)

    # Finite exact second-codegree and the formula behind the BMS ratio (5.11).
    delta2_exact = max_codegree(edges, 2)
    e_over_v = len(edges) / vertices
    assert delta2_exact / e_over_v >= (
        (m2 - 1) * (n2 / 2 - m2) * (n2 + m2 - 1) / (10 * p)
    )

    # Directly check the adjacent-coordinate construction (5.7) at larger
    # parameters without enumerating the full hypergraph.
    for m6 in range(2, 12):
        n6 = 16 * m6
        l6 = n6 + m6 - 1
        p6 = (n6 - m6) * (n6 - m6 + 1) // 2
        adjacent_lower = (m6 - 1) * (n6 / 2 - m6) * 10**(m6 - 2)
        assert adjacent_lower > 0
        bms_ratio_lower = adjacent_lower / (p6 * 10**m6 / (10 * l6))
        stated_ratio = (m6 - 1) * (n6 / 2 - m6) * l6 / (10 * p6)
        assert math.isclose(bms_ratio_lower, stated_ratio)
        # The S1 delta_2 bound (5.8), using the report's conservative summed
        # lower bound and exact v*d=2m*e.
        summed = 10 * (n6 / 2 - m6) * adjacent_lower
        vd = 2 * m6 * p6 * 10**m6
        tau6 = 0.5
        delta2_lower = summed / (tau6 * vd)
        assert delta2_lower >= 9 / (1280 * tau6)

    # Exact label-graph codegree formula delta=1/(tau*(N-1)).
    tau = 0.1
    n3 = 101
    delta2 = 1.0 / (tau * (n3 - 1))
    assert math.isclose(delta2, 0.1)

    # Exhaustively verify the short-lag subtraction behind (5.5) on all
    # binary words of a small size. Decimal is no harder for this identity.
    n4, m4 = 6, 2
    for bits in itertools.product(range(2), repeat=n4 + m4 - 1):
        e = collision_energy(bits, n4, m4)
        far = far_edges(bits, n4, m4)
        assert far >= (e - n4) / 2 - n4 * (m4 - 1)

    # Arithmetic implication used in (5.6).
    for m5 in range(1, 20):
        n5 = 16 * m5 * m5
        lower = n5 * n5 / (8 * m5) - n5 * m5 + n5 / 2
        assert lower >= n5 * n5 / (16 * m5)

    # Any useful S1 measure saving forces tau<1; it is not an unstated theorem
    # hypothesis in the report's codegree obstruction.
    for r in range(4, 14, 2):
        zeta = 1 / (12 * math.factorial(r))
        tau_ceiling = zeta / (2 * r * math.factorial(r))
        assert tau_ceiling < 1

    with tarfile.open(ROOT / "prior_evidence.tar.gz", "r:gz") as tf:
        members = {member.name for member in tf.getmembers() if member.isfile()}
    for needed in ["t89/REPORT.md", "t121/REPORT.md", "t128/REPORT.md",
                   "t135/REPORT.md", "notes/t137/REPORT.md",
                   "t106/FiniteBranchingResonanceTree.lean",
                   "t92/T92ConstantRunDiscriminator.lean",
                   "t100/T100UniversalCharging.lean",
                   "t107/T107AveragedTriangularFejer.lean",
                   "t108/T108LiteralTransport.lean",
                   "t117/prior-t109-REPORT.md",
                   "t130/prior-t119-REPORT.md",
                   "t125/prior-t122-REJECTED-REPORT.md",
                   "t125/prior-t123-R0-REPORT.md"]:
        assert needed in members, needed

    print(f"canonical_sha256={CANONICAL_SHA}")
    print(f"source_count={len(PDF_PINS)} retained_theorem_count=2")
    print(f"ordered_energy_sample={energy} label_edges={pairs}")
    print(f"digit_hypergraph_N={n2} m={m2} vertices={10*(n2+m2-1)} "
          f"edges={len(edges)} uniformity={2*m2}")
    print("finite_supersaturation_checks=passed")
    print("novelty_ledger=T89-T139; T129_T139_unavailable_no_novelty_claim")
    print("verdict=close; classification=inapplicability_not_falsification")


if __name__ == "__main__":
    main()
