#!/usr/bin/env python3
"""Deterministic finite replay for T121.

Finite checks validate transcription and algebra only. They do not prove the
asymptotic source claims or any property of the prescribed decimal orbit.
"""

from __future__ import annotations

import hashlib
import itertools
import math
import re
from pathlib import Path


ROOT = Path(__file__).resolve().parent

EXPECTED = {
    "canonical_statement.txt": "cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8",
    "mauduit-sarkozy-1997.pdf": "d95bbd2b7cbecfb0cee08f82a41f7879579277f865b8f0d0dc53c5e79e2a39fa",
    "weil-1948-pnas.pdf": "c19b498bacb4878f2067e679f92306f3f2a3fa54f53937f12c5d6650a5f5abef",
    "hofer-larcher-2211.04212v1.pdf": "cc8fd0a4373161ed1e4c6b15599e1a65cf648d5bd8856f3108fe0912e8b7ed0b",
    "larcher-stockinger-1803.05236v2.pdf": "a9ea7099fb191b68cd7a322bf6b50a1d009820c69c5fa16fc3d2746a1c4baeae",
    "konieczny-1611.09985v2.pdf": "92cc1e1f37a924d89bb2788d883670eba2604c2d56a029d94c750803e78c2360",
    "fan-konieczny-1806.04267v2.pdf": "e5fdb01f5f1c717cd5733158edcb97cf70d2f4a18f423c9ab6fd8476fb67f114",
    "becher-carton-1805.03713v1.pdf": "3197ae6ff0aecb4cfc80bb89688bdc3250d09f9c11b168c9f401fdb835602448",
}


def sha256(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def legendre(x: int, p: int) -> int:
    x %= p
    if x == 0:
        return 0
    value = pow(x, (p - 1) // 2, p)
    return -1 if value == p - 1 else value


def legendre_sign(x: int, p: int) -> int:
    return 1 if legendre(x, p) == 1 else -1


def cyclic_word(signs: list[int], start: int, m: int) -> tuple[int, ...]:
    p = len(signs)
    return tuple(signs[(start + offset) % p] for offset in range(m))


def collision_from_counts(counts: dict[tuple[int, ...], int]) -> int:
    return sum(value * value for value in counts.values())


def check_hashes() -> None:
    for name, expected in EXPECTED.items():
        actual = sha256(ROOT / name)
        assert actual == expected, (name, actual, expected)
    print(f"hashes: {len(EXPECTED)} passed")


def check_report_contract() -> None:
    report = (ROOT / "REPORT.md").read_text(encoding="utf-8")
    pins = (ROOT / "SOURCE_PINS.md").read_text(encoding="utf-8")
    log = (ROOT / "SEARCH_LOG.md").read_text(encoding="utf-8")

    required = [
        "PRIMARY_SOURCE_COUNT: 7",
        "PRIMARY_SOURCE_CAP: 12",
        "SEARCHED_DOMAIN_COUNT: 4",
        "RETAINED_CANDIDATE_COUNT: 4",
        "CANDIDATE_CAP: 4",
        "TERMINAL_VERDICT_COUNT: 1",
        "SUCCESSOR_COUNT: 1",
        "F-LEG: aggregate Walsh--Legendre orthogonality",
        "F-NECK: nested-perfect necklace block energy",
        "F-ST: Stoneham close-pair energy",
        "F-AUT: fixed-order automatic Gowers bounds",
        "`PI-AGG` (`conjectural transfer`)",
        "active T119",
        "active T120",
    ]
    for marker in required:
        assert marker in report, marker

    comparators = [
        "T6/T7", "T72", "T91", "T104", "T105", "T110", "T112",
        "T115", "T117", "T118", "active T119", "active T120",
    ]
    for comparator in comparators:
        assert comparator in report, comparator

    actual_pdfs = {path.name for path in ROOT.glob("*.pdf")}
    expected_pdfs = {name for name in EXPECTED if name.endswith(".pdf")}
    assert actual_pdfs == expected_pdfs, (actual_pdfs, expected_pdfs)

    source_sections = re.findall(r"^## S[1-9][0-9]*\.", pins, flags=re.MULTILINE)
    candidate_sections = re.findall(
        r"^## [5-8]\. F-(?:LEG|NECK|ST|AUT):", report, flags=re.MULTILINE
    )
    assert len(source_sections) == 7, source_sections
    assert len(candidate_sections) == 4, candidate_sections

    endpoint_markers = [
        "starts are all `x in F_p`",
        "1-based positions `1,...,R`",
        "starts are all orbit indices `J={0,...,N-1}`",
        "linear starts `J={0,...,M-1}`",
    ]
    for marker in endpoint_markers:
        assert marker in report, marker

    assert report.count("SCOPED VERDICT (1/1):") == 1
    assert report.count("BOUNDED SUCCESSOR (1/1):") == 1
    assert report.count("Card result:") == 4
    assert pins.count("## S") == 7
    assert "No retrieval failed." in log
    print("report contract: passed")


def check_legendre() -> None:
    primes = [3, 5, 7, 11, 13, 17, 19]
    cases = 0
    for p in primes:
        signs = [legendre_sign(x, p) for x in range(p)]
        for m in range(1, p):
            counts: dict[tuple[int, ...], int] = {}
            for x in range(p):
                word = cyclic_word(signs, x, m)
                counts[word] = counts.get(word, 0) + 1
            collision = collision_from_counts(counts)

            walsh_numerator = 0
            for mask in range(1 << m):
                correlation = 0
                for x in range(p):
                    product = 1
                    for t in range(m):
                        if mask & (1 << t):
                            product *= signs[(x + t) % p]
                    correlation += product
                walsh_numerator += correlation * correlation
            assert walsh_numerator == (1 << m) * collision

            variance_numerator = (1 << m) * collision - p * p
            assert variance_numerator >= 0
            bound = m * (m + 1) * (math.sqrt(p) + 1) ** 2 / 4
            assert variance_numerator / (1 << m) <= bound + 1e-9
            cases += 1
    print(f"Legendre Walsh/bound cases: {cases} passed")


def check_necklace_endpoint_algebra() -> None:
    cases = 0
    for b, t, level in [(2, 3, 4), (2, 5, 8), (3, 2, 5), (3, 4, 9)]:
        words = list(itertools.product(range(b), repeat=t))
        removed = [words[(7 * index + t) % len(words)] for index in range(t - 1)]
        r = {word: 0 for word in words}
        for word in removed:
            r[word] += 1
        counts = {word: level - r[word] for word in words}
        period = level * (b**t)
        mass = period - t + 1
        assert sum(counts.values()) == mass

        variance = sum((count - mass / (b**t)) ** 2 for count in counts.values())
        rhs = sum(value * value for value in r.values()) - (t - 1) ** 2 / (b**t)
        assert abs(variance - rhs) < 1e-9
        assert variance <= (t - 1) ** 2 + 1e-9
        collision = collision_from_counts(counts)
        assert abs(collision - (mass * mass / (b**t) + variance)) < 1e-9
        cases += 1
    print(f"necklace endpoint cases: {cases} passed")


def check_coarsening() -> None:
    cases = 0
    for w in range(2, 9):
        fine = {word: 1 + (sum(word) * 5 + int("".join(map(str, word)), 2)) % 7
                for word in itertools.product((0, 1), repeat=w)}
        fine_energy = collision_from_counts(fine)
        for m in range(1, w + 1):
            coarse: dict[tuple[int, ...], int] = {}
            for word, value in fine.items():
                prefix = word[:m]
                coarse[prefix] = coarse.get(prefix, 0) + value
            coarse_energy = collision_from_counts(coarse)
            assert coarse_energy <= (1 << (w - m)) * fine_energy
            cases += 1
    print(f"coarsening cases: {cases} passed")


def check_binomial_mass() -> None:
    for m in range(1, 30):
        second = sum(math.comb(m, s) * s * s for s in range(1, m + 1))
        assert second == m * (m + 1) * (1 << (m - 2)) if m >= 2 else second == 1

    s0 = 3
    values = []
    for m in [8, 16, 32, 64]:
        unresolved = sum(math.comb(m, d) for d in range(s0 + 1, m + 1)) / (1 << m)
        values.append(unresolved)
    assert values == sorted(values)
    assert values[-1] > 0.999999
    print("binomial moments/unresolved mass: passed")


def exponent_snapshot() -> None:
    kappa = 0.6
    rows = []
    for exponent in [10, 14, 18, 22]:
        p_proxy = 2**exponent
        m = math.floor(kappa * math.log2(p_proxy))
        legendre_proxy = m * (2 * p_proxy ** (-kappa) + (m * (m + 1) / 4) / p_proxy)
        fixed_order_mass = 1 - sum(math.comb(m, d) for d in range(4)) / (1 << m)
        rows.append((exponent, m, legendre_proxy, fixed_order_mass))
    assert rows[-1][2] < rows[0][2]
    print("exponent snapshot (experiment):")
    for exponent, m, legendre_proxy, fixed_order_mass in rows:
        print(
            f"  log2N={exponent:2d} m={m:2d} "
            f"aggregate_proxy={legendre_proxy:.8f} "
            f"unresolved_fixed_order={fixed_order_mass:.8f}"
        )


def main() -> None:
    check_hashes()
    check_report_contract()
    check_legendre()
    check_necklace_endpoint_algebra()
    check_coarsening()
    check_binomial_mass()
    exponent_snapshot()
    print("T121 finite replay: PASS")


if __name__ == "__main__":
    main()
