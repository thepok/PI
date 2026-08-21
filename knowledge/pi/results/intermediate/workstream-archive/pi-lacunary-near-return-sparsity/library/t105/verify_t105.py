#!/usr/bin/env python3
"""Self-contained replay for the finite and transcription checks in T105.

All D_N enumerations are experiments. They select or reject mechanisms at the
displayed finite parameters; they are not evidence for a universal or pi claim.
"""

from collections import Counter
from fractions import Fraction
from hashlib import sha256
from itertools import combinations
from pathlib import Path


ROOT = Path(__file__).resolve().parent

EXPECTED_HASHES = {
    "canonical_statement.txt": "cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8",
    "rss-energy-1607.05053v5.pdf": "007586b8b40da3ac99f22035968e6bb2b6546fed99af686ddf64e2293a6bec03",
    "rss-energy-1607.05053v5.txt": "3df6d0a7e337a29ffb49b6dbdd966d046f48d4bb0a637e5090c4ce45c1c63590",
    "bloom-control-2501.09470v1.pdf": "c7aec98a1dc993a5a52048bf2b5939f3ce474b7019adb9c00d77768db45eaafe",
    "bloom-control-2501.09470v1.txt": "412abbdf098d6ed4c8a3818bdc309724f36297345afd669e22dd31bef840c3fb",
    "tan-zhou-2504.21555v1.pdf": "f9544bf4a8fa1f40240231fcaedfb0b04df70b965fa70fd033194b55bf319b19",
    "tan-zhou-2504.21555v1.txt": "2cb7ebbfb88ca915ea423acc884193ccb9e4c8b064bb76145a950b72eaf1fce2",
    "kerr-1302.4170v1.pdf": "9136dc3965da376942f653b2b06de8d92d7e5e997ee536e1257979698b73e4bd",
    "kerr-1302.4170v1.txt": "2a13bcbb1416ceaf783095661282cf08f9834a71b7a71a97f750d7c314d6ea6b",
    "dibenedetto-et-al-2003.06165v1.pdf": "4434b3992292e881139055eb0390ed7a7ff9ce9b243c156ac631c1442c2930d1",
    "dibenedetto-et-al-2003.06165v1.txt": "3529db3774a5b33b0489844e91b507246037aee700ca0e8f7474407e6af75845",
}

ANCHORS = {
    "rss-energy-1607.05053v5.txt": [
        "To avoid trivialities we further assume the 0 6∈ A and |A| > 1",
        "Theorem 5. Let A",
        "min[E+ (A′ ), E× (A′ )]",
        "constraint |A| ≤ p5/8",
    ],
    "bloom-control-2501.09470v1.txt": [
        "Theorem 8. Let",
        "K −100/81",
        "K 100/27",
    ],
    "tan-zhou-2504.21555v1.txt": [
        "Theorem 1.7. Let",
        "minimal singular values",
        "uniformly bounded below by K > 1",
        "Since α > 0, the series",
        "3. Proof of Theorem 1.8",
    ],
    "kerr-1302.4170v1.txt": [
        "Theorem 2. For g",
        "N ≤ t1/2",
        "71/96+o(1)",
    ],
    "dibenedetto-et-al-2003.06165v1.txt": [
        "Theorem 3.1. Let H",
        "p1/2 > H > p1/4",
        "H 2689/2880 p1/72",
    ],
}


def file_hash(name: str) -> str:
    return sha256((ROOT / name).read_bytes()).hexdigest()


def difference_set(n: int) -> set[int]:
    return {10**i - 10**j for i in range(n) for j in range(n)}


def energy(values: set[int]) -> int:
    counts = Counter(a + b for a in values for b in values)
    return sum(count * count for count in counts.values())


def choose4(n: int) -> int:
    return n * (n - 1) * (n - 2) * (n - 3) // 24


def interval_sum(a: int, b: int, c: int, d: int) -> int:
    return (10**b - 10**a) + (10**d - 10**c)


def main() -> None:
    for name, expected in EXPECTED_HASHES.items():
        actual = file_hash(name)
        assert actual == expected, (name, actual, expected)

    for name, anchors in ANCHORS.items():
        text = (ROOT / name).read_text(encoding="utf-8")
        for anchor in anchors:
            assert anchor in text, (name, anchor)

    canonical = (ROOT / "canonical_statement.txt").read_text(encoding="utf-8")
    assert "pairs are ordered and the diagonal is included" in canonical
    assert "for every integer A >= 1" in canonical

    report = (ROOT / "REPORT.md").read_text(encoding="utf-8")
    source_pins = (ROOT / "SOURCE_PINS.md").read_text(encoding="utf-8")
    assert "`PRIMARY_SOURCE_COUNT: 5` (cap: 8)" in report
    assert "`CANDIDATE_COUNT: 3` (cap: 3)" in report
    assert "`TERMINAL_DECISION_COUNT: 1`" in report
    assert report.count("## 4. Candidate 1:") == 1
    assert report.count("## 5. Candidate 2:") == 1
    assert report.count("## 6. Candidate 3:") == 1
    assert report.count("TERMINAL VERDICT (1/1):") == 1
    for item in ["T10", "T45", "T73", "T81", "T87"] + [
        f"T{number}" for number in range(90, 105)
    ]:
        assert f"| {item} |" in report, item
    for token in [
        "J/(131072*A^2*n^2)",
        "9J/[524288*pi*A^2*n^2*h(10^r-1)(10^J-1)]",
        "J/(262144*A^2*n^2)",
        "lambda_source = lambda_target*10^(-1) mod p",
        "m^8 <= p^5",
        "0 notin B,  |B|>1",
        "for some alpha>0",
        "J <= ord_p(10)^(1/2)",
        "J<=N=O(log p)",
        "T104-F4",
        "Candidates 1 and 3 still justify the terminal negative map",
        "delta_R>3/4",
        "no fixed-pi, C1, or C2 claim",
    ]:
        assert token in report, token
    for token in [
        "ed690a31fbc19d08c817bcb2558ec259788e37d4f8243261ece1b9eafbbb5df0",
        "2dee0c91ce8480785a851df4aad06e0ab65f92e647fa7f67605b868129fc16d5",
        "f07b9e579360cff6843fccb526086d27ea454925d6ed46d297fff274ca5689e6",
        "Theorem 1.2, Proposition 2.5, and",
        "Theorem 2.7",
        "complete primary-source search corpus is exactly S1-S5",
        "No other\nprimary paper was screened",
        "every `alpha>0`",
        "additionally requires `N<=t^(1/2)`",
    ]:
        assert token in source_pins, token
    assert "Screened but not retained" not in source_pins
    assert "absent from supplied library and workspace" not in report
    assert "No `t103` or `t104` directory" not in source_pins

    print("CLAIM_LABEL=experiment")
    print("PRIMARY_SOURCE_COUNT=5")
    print("CANDIDATE_COUNT=3")
    print("TERMINAL_DECISION_COUNT=1")
    print("CANONICAL_SHA256=" + EXPECTED_HASHES["canonical_statement.txt"])
    print("SOURCE_HASH_AND_ANCHOR_CHECKS=passed")
    print("REPORT_STRUCTURE_CHECKS=passed")
    print("T103_T104_COMPARISON_CHECKS=passed")
    print("D_N_TABLE columns=N,|D|,E_plus(D),E_plus(D\\{0}),|D+D|,|A*A|,K_A")

    for n in range(1, 13):
        dset = difference_set(n)
        aset = dset - {0}
        assert len(dset) == n * (n - 1) + 1

        nonzero_pairs = [(i, j) for i in range(n) for j in range(n) if i != j]
        represented = [10**i - 10**j for i, j in nonzero_pairs]
        assert len(represented) == len(set(represented))

        sums = {a + b for a in dset for b in dset}
        products = {a * b for a in aset for b in aset}
        e_d = energy(dset)
        e_a = energy(aset) if aset else 0
        k_a = Fraction(len(aset) ** 3, e_a) if e_a else Fraction(0)

        disjoint = {
            interval_sum(a, b, c, d)
            for a, b, c, d in combinations(range(n), 4)
        }
        assert len(disjoint) == choose4(n)
        assert disjoint <= sums

        # These polynomial matches are bounded observations, not universal proofs.
        assert e_d == 9 * n**4 - 34 * n**3 + 48 * n**2 - 23 * n + 1
        assert e_a == 9 * n**4 - 42 * n**3 + 66 * n**2 - 33 * n
        assert len(products) == n * (n - 1) ** 2

        print(
            f"{n},{len(dset)},{e_d},{e_a},{len(sums)},{len(products)},"
            f"{k_a.numerator}/{k_a.denominator}"
        )

    # Exact arithmetic form of the two modular scale discriminators.
    # Kerr's first-range main power is nontrivial only past N > p^(12/25).
    # Di Benedetto et al. need a complete subgroup H=N with H > p^(1/4).
    print("MODULAR_SCALE_TABLE columns=p,N,N^25<p^12,N^4<p")
    for p, n in [(10007, 9), (100003, 11), (1000003, 13), (10000019, 16)]:
        assert n < p
        kerr_too_short = n**25 < p**12
        subgroup_too_short = n**4 < p
        assert kerr_too_short and subgroup_too_short
        print(f"{p},{n},{kerr_too_short},{subgroup_too_short}")

    print("FINITE_COMPUTATION_SCOPE=N<=12 plus four displayed modular pairs")
    print("FINITE_COMPUTATION_INTERPRETATION=selection_or_rejection_only")
    print("TERMINAL_VERDICT=close with a source-pinned negative map")
    print("NO_FIXED_PI_C1_C2_CLAIM=true")


if __name__ == "__main__":
    main()
