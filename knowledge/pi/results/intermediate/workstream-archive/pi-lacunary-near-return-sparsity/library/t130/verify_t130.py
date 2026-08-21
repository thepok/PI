#!/usr/bin/env python3
"""Self-contained transcription and finite-identity checks for T130.

These checks are experiments. They do not prove an asymptotic statement or a
property of pi.
"""

from __future__ import annotations

import hashlib
import itertools
import math
from fractions import Fraction
from pathlib import Path
import re
import subprocess
import tempfile
import unicodedata


ROOT = Path(__file__).resolve().parent

EXPECTED = {
    "canonical_statement.txt": "cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8",
    "T7FiniteCylinderEnergy.lean": "cac7b8da11c9369510e2e6e76b8bc74820b50ffe0285310475c7cf8ee1cfe91c",
    "beukers-schlickewei-1996.pdf": "f1b115cd8c5f190a0bce8628e229e019191c83b6562a891d8d84f2ed82832a0e",
    "amoroso-viada-2009.pdf": "eca4350c7787b8caa26fba8d8c950214fc048a11c3259903f83fd4590a740a67",
    "evertse-schlickewei-schmidt-math0409604.pdf": "3c809fcadaddbc08f57045e4f55562c8a379b5fa33d7e83046b63a9c14766e8f",
    "bugeaud-evertse-0709.1560.pdf": "81d7e7d57867dbfcd08e6c17e8d48a3ecc23f562701be1e68c5acf3bb0ef35db",
    "fischler-rivoal-1512.06534.pdf": "2cc01bb677d29ac3b2aa79b54eff131928d747489335ff90e4bf4a48778736b8",
    "prior-t81-REPORT.md": "73b4198003d637e5b7277dbdfe05e4f2606613f8e906860243331a293dd3b77f",
    "prior-t87-REPORT.md": "a1232df07fa5c1ce31ba605217038c948bacd8f07f89b569b04da67cf1159078",
    "prior-t114-REPORT.md": "db21ac7d0a7845264c727132293db149a06a832d6f67700fd9ceb0f69a142cca",
    "prior-t119-REPORT.md": "72b10e921761874158893bb9cbb7454094bcbc59bbdfc787f33bbf355b63f23a",
    "prior-t125-REPORT.md": "1ce372d3a99323eae9460a4dbc25b329b93b66e0a356aa3284f1fc9c543f461a",
}


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def normalized(text: str) -> str:
    text = unicodedata.normalize("NFKD", text)
    return " ".join(text.replace("−", "-").split()).lower()


def extract_pdf(name: str, first_page: int, last_page: int | None = None) -> str:
    if last_page is None:
        last_page = first_page
    with tempfile.TemporaryDirectory(prefix="t130-") as tmp:
        out = Path(tmp) / "source.txt"
        subprocess.run(
            [
                "pdftotext",
                "-layout",
                "-f",
                str(first_page),
                "-l",
                str(last_page),
                str(ROOT / name),
                str(out),
            ],
            check=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        )
        return normalized(out.read_text(errors="replace"))


def check_hashes() -> None:
    for name, expected in EXPECTED.items():
        actual = digest(ROOT / name)
        assert actual == expected, (name, actual, expected)


def check_source_anchors() -> None:
    anchors = [
        ("beukers-schlickewei-1996.pdf", 1, 1, [
            "theorem 1.1",
            "q-closure",
            "x + y = 1",
            "8r+8",
        ]),
        ("amoroso-viada-2009.pdf", 27, 27, [
            "theorem 6.2",
            "algebraically closed field of characteristic 0",
            "(6.24)",
            "non-degenerate solutions",
        ]),
        ("amoroso-viada-2009.pdf", 6, 6, [
            "a solution is called non-degenerate",
            "no subsum",
        ]),
        ("evertse-schlickewei-schmidt-math0409604.pdf", 1, 2, [
            "theorem 1.1",
            "called nondegenerate",
            "finite rank r",
            "(6n)3n (r + 1)",
        ]),
        ("bugeaud-evertse-0709.1560.pdf", 1, 1, [
            "block complexity",
            "card {ak+1 ak+2",
        ]),
        ("bugeaud-evertse-0709.1560.pdf", 3, 3, [
            "theorem 2.1",
            "algebraic irrational",
            "1/11",
            "lim sup",
        ]),
        ("fischler-rivoal-1512.06534.pdf", 5, 5, [
            "theorem 3",
            "g-function with rational taylor coefficients",
            "dilogarithm",
            "provided s",
        ]),
        ("fischler-rivoal-1512.06534.pdf", 15, 15, [
            "qn = bn-1 (bt - 1)",
            "proof of theorem 3",
        ]),
    ]
    for name, first_page, last_page, required in anchors:
        text = extract_pdf(name, first_page, last_page)
        for anchor in required:
            assert normalized(anchor) in text, (name, first_page, last_page, anchor)


def floor_fraction(x: Fraction) -> int:
    return x.numerator // x.denominator


def has_zero_proper_subsum(terms: tuple[int, ...]) -> bool:
    for size in range(1, len(terms)):
        for subset in itertools.combinations(terms, size):
            if sum(subset) == 0:
                return True
    return False


def check_collision_identities() -> None:
    digits = "1200" * 40
    scale = 10 ** len(digits)
    x = Fraction(3 * scale + int(digits), scale)

    for n_starts, m in [(20, 2), (20, 6), (31, 9)]:
        q = 10**m
        p = [floor_fraction((10**t) * x) for t in range(n_starts + m)]
        assert all(p[t] < p[t + 1] for t in range(len(p) - 1))
        blocks = [p[t + m] - q * p[t] for t in range(n_starts)]
        assert all(0 <= block < q for block in blocks)

        energy_by_fibers = sum(blocks.count(block) ** 2 for block in set(blocks))
        collision_pairs = [
            (i, j)
            for i in range(n_starts)
            for j in range(n_starts)
            if blocks[i] == blocks[j]
        ]
        assert energy_by_fibers == len(collision_pairs)
        assert len(collision_pairs) >= n_starts

        overlap_pairs = 0
        for i, j in collision_pairs:
            block = blocks[i]
            u, v = p[i + m], p[j + m]
            s, t = q * p[i], q * p[j]
            assert u - v - s + t == 0
            assert (u - s) == block and (-v + t) == -block
            predicted_degenerate = i == j or block == 0
            assert has_zero_proper_subsum((u, -v, -s, t)) == predicted_degenerate

            if i < j and j - i < m:
                overlap_pairs += 2
                d = j - i
                a = p[i + d] - (10**d) * p[i]
                a_prime = p[i + m + d] - (10**d) * p[i + m]
                assert q * a - (10**d - 1) * block - a_prime == 0
                copies, r = divmod(m, d)
                if r:
                    c = a // (10 ** (d - r))
                    d0 = a % (10 ** (d - r))
                    assert a_prime == (10**r) * d0 + c
                else:
                    c = 0
                    assert a_prime == a
                repeated = a * sum(10 ** (r + h * d) for h in range(copies)) + c
                assert block == repeated

        dmax = min(m - 1, n_starts - 1)
        overlap_cap = 2 * dmax * n_starts - dmax * (dmax + 1)
        assert overlap_pairs <= overlap_cap


def check_parameter_substitutions() -> None:
    for kappa in (0.2, 0.5, 1.0, 1.75):
        for n_starts in (10**3, 10**5, 10**8):
            m = math.floor(kappa * math.log10(n_starts))
            if m < 1:
                continue
            q = 10**m
            assert n_starts**kappa / 10 < q <= n_starts**kappa
            endpoint_count = n_starts + min(m, n_starts)
            assert m < n_starts and endpoint_count == n_starts + m
            r_bound = n_starts + m + 1
            bs_log2 = 16 * r_bound + 24
            explicit_bs_log2 = (
                16 * n_starts
                + 40
                + 16 * kappa * math.log10(n_starts)
            )
            assert bs_log2 <= explicit_bs_log2 + 1e-9
            av_exponent = 324 * (3 * r_bound + 4)
            explicit_av_exponent = (
                972 * n_starts
                + 2268
                + 972 * kappa * math.log10(n_starts)
            )
            assert av_exponent <= explicit_av_exponent + 1e-9
            dmax = min(m - 1, n_starts - 1)
            overlap = 2 * dmax * n_starts - dmax * (dmax + 1)
            assert 0 <= overlap < n_starts * n_starts

    assert abs(16 * math.log10(2) - 4.8164799306) < 1e-9
    assert abs(972 * math.log10(24) - 1341.5653269) < 1e-7
    assert abs(1 / (8 * math.log10(2)) - 0.4152410119) < 1e-9
    assert abs(2 / (324 * math.log10(24)) - 0.0044723875) < 1e-9


def check_support_counterexample() -> None:
    for n_starts in (20, 100, 1000):
        for support in (1, 2, max(2, n_starts // 10)):
            occupancies = [n_starts - support + 1] + [1] * (support - 1)
            assert sum(occupancies) == n_starts
            energy = sum(value * value for value in occupancies)
            assert energy == (n_starts - support + 1) ** 2 + support - 1
            assert energy >= n_starts * n_starts / support


def check_report_contract() -> None:
    report = (ROOT / "REPORT.md").read_text()
    pins = (ROOT / "SOURCE_PINS.md").read_text()
    assert "PRIMARY_SOURCE_COUNT: 5" in report
    assert "PRIMARY_SOURCE_CAP: 8" in report
    assert "RETAINED_CANDIDATE_COUNT: 3" in report
    assert "RETAINED_CANDIDATE_CAP: 3" in report
    assert report.count("SCOPED_VERDICT (1/1):") == 1
    assert "SUCCESSOR_COUNT: 0" in report
    assert "FIXED_PI_CLAIM: none" in report
    assert "C1_CLAIM: none" in report
    assert "C2_CLAIM: none" in report
    assert "PI-SUNIT-RANK (conjectural transfer; not asserted)" in report
    assert "a sequence of integers" in report
    assert "epsilon_m>=0" in report
    assert "epsilon_m->0" in report
    assert "depend only on `(m,B,l)`" in report
    assert "m=floor(kappa*log_10 N)" in report
    for card in ("C1", "C2", "C3"):
        assert f"CHEAP_REJECTION_{card}:" in report
    for item in ("T81", "T87", "T114", "T119", "T125", "active T127"):
        assert f"| {item} |" in report
    for marker in (
        "H_coeff=q<=N^kappa",
        "R_(N,m)<=N+kappa*log_10 N+1",
        "C_overlap=2N(m-1)-m(m-1)",
        "M_BS(N,m)",
        "M_AV(N,m)",
        "E_concentrated(N,p)",
        "rho*kappa<1/(8*log_10 2)=0.415241",
        "rho*kappa<2/(324*log_10 24)=0.004472",
        "s>=10^7/epsilon",
    ):
        assert marker in report
    assert len(re.findall(r"^## S[1-5]:", pins, flags=re.MULTILINE)) == 5


def check_t7_anchors() -> None:
    text = (ROOT / "T7FiniteCylinderEnergy.lean").read_text()
    for theorem in (
        "piCylinderCollisionEnergy_eq_equalPairs_card",
        "normalizedPiCylinderCollisionEnergy_eq_equalPairs_card_div",
        "diagonal_le_piCylinderCollisionEnergy",
        "piCylinderCollisionEnergy_le_Q_pi_le_three_mul",
        "canonical_C1_iff_piFiniteCylinderEnergyFrontier",
    ):
        assert theorem in text


def main() -> None:
    check_hashes()
    check_source_anchors()
    check_t7_anchors()
    check_collision_identities()
    check_parameter_substitutions()
    check_support_counterexample()
    check_report_contract()
    print("T130 verification passed")
    print("5 primary sources <= 8; 3 retained candidates <= 3")
    print("finite checks are experiments, not evidence for pi, C1, or C2")


if __name__ == "__main__":
    main()
