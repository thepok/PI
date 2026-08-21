#!/usr/bin/env python3
"""Self-contained bounded replay for the T89 literature note.

Finite checks below are transcription tests, not proofs of universal claims and
not evidence about pi.
"""

from __future__ import annotations

import hashlib
import math
import re
import subprocess
from fractions import Fraction
from pathlib import Path


ROOT = Path(__file__).resolve().parent

PINS = {
    "canonical_statement.txt":
        "cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8",
    "kempner-1916.pdf":
        "99c4bf8d04d2dbdc63e8d274266f212072d4c248fcbc659e60ca7fa9350eb014",
    "badziahin-zorin-1707.06677v1.pdf":
        "f8de296ba104cca97f4f6c3d45647e21c3db3d2207274facaf2c16b445483d15",
    "hwang-janson-tsai-2017.pdf":
        "d47477fa8b92a4f213b6bfe4febd1075bacb77ec706f2823efaedfeda48c9481",
    "T7FiniteCylinderEnergy.lean":
        "cac7b8da11c9369510e2e6e76b8bc74820b50ffe0285310475c7cf8ee1cfe91c",
    "T10LongLagResonance.lean":
        "63ccfd2417aca055ef9071e03b70092acb1fee26a279db6c5c35c9295aa91947",
    "T61DirectLabelAdjacentPhaseVariance.lean":
        "2eaecb2df11027d6ed5911a16fe571b042afbe42e18daf57eaaffc668f74dbdb",
    "prior-t63-REPORT.md":
        "28e7bdc28628404532afcecda50ed954836df3eb7d6578315604907a7f10ad59",
    "SEMANTIC_OBSTRUCTION_MEMORY.md":
        "aa8b0f84010f2850807e383e21f45dcb9c0dc548b5e22e0c3c4cd2779528f76f",
    "prior-t86-REPORT.md":
        "16cff30f045a0b5bf56aa80c98c63add19d55c6a5a5b126602d8c785e48e11fa",
    "prior-t87-REPORT.md":
        "a1232df07fa5c1ce31ba605217038c948bacd8f07f89b569b04da67cf1159078",
}


def digest(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def pdf_text(name: str) -> str:
    proc = subprocess.run(
        ["pdftotext", "-layout", str(ROOT / name), "-"],
        check=True,
        capture_output=True,
        text=True,
    )
    return " ".join(proc.stdout.lower().split())


def thue_prefix(length: int) -> list[int]:
    return [n.bit_count() & 1 for n in range(length)]


def terminal_zeroes(word: list[int]) -> int:
    count = 0
    for bit in reversed(word):
        if bit:
            break
        count += 1
    return count


def nearest_power_distance(r: int) -> int:
    lower = 1 << (r.bit_length() - 1)
    upper = lower << 1
    return min(r - lower, upper - r)


def thue_complexity_formula(n: int) -> int:
    if n == 1:
        return 2
    if n == 2:
        return 4
    r = n - 1
    return 3 * r + nearest_power_distance(r)


def distinct_factors(word: list[int], n: int) -> int:
    return len({tuple(word[j:j + n]) for j in range(len(word) - n + 1)})


def main() -> None:
    for name, expected in PINS.items():
        actual = digest(ROOT / name)
        assert actual == expected, (name, actual, expected)
    print(f"hash pins: {len(PINS)} passed")

    statement = (ROOT / "canonical_statement.txt").read_text()
    assert "pairs are ordered and the diagonal is included" in statement
    assert "for every integer A >= 1" in statement
    assert "for every integer n >= n_0" in statement
    assert "there exists an integer N >= 1" in statement
    print("canonical quantifiers and normalization: passed")

    report = (ROOT / "REPORT.md").read_text()
    source_pins = (ROOT / "SOURCE_PINS.md").read_text()
    assert report.count("`PRIMARY_SOURCE_COUNT: 3`") == 1
    assert report.count("`RETAINED_CANDIDATE_COUNT: 2`") == 1
    assert report.count("`FINAL_VERDICT_COUNT: 2`") == 1
    assert source_pins.count("`PRIMARY_SOURCE_COUNT: 3`") == 1
    assert source_pins.count("`RETAINED_CANDIDATE_COUNT: 2`") == 1
    assert len(list(ROOT.glob("*.pdf"))) == 3 <= 8
    assert len(re.findall(r"^## [45]\. Candidate", report, re.MULTILINE)) == 2 <= 4
    verdicts = re.findall(
        r"^FINAL VERDICT C[12]: (develop|hold as model|close)$",
        report,
        re.MULTILINE,
    )
    assert verdicts == ["hold as model", "hold as model"]
    for marker in (
        "Stoneham constants", "Champernowne", "T63", "T68", "T78",
        "T79/T85", "T80", "T81", "T82", "T86", "T87 survey note",
        "K1", "K1a", "K1b", "K1c", "K2",
        "TM0", "TM1", "TM2", "TM3", "Smallest kill test",
    ):
        assert marker in report, marker
    assert "Q_x(n,N)" in report
    assert "for `m>=2`" in report
    assert "u_t\\equiv u2^{t-a}5^{t-b}" in report
    assert "one actual label" in report
    assert "This report proves no estimate" in report
    assert "No formula here identifies either model with pi" in report
    print("caps, non-duplication, transfer tests, verdicts: passed")

    kempner = pdf_text("kempner-1916.pdf")
    assert "the object of the present paper is to prove" in kempner
    assert "fredholm" in kempner
    bz = pdf_text("badziahin-zorin-1707.06677v1.pdf")
    assert "t2n = tn" in bz
    assert "t2n+1 = 1" in bz
    assert "theorem 2. let d" in bz
    hjt = pdf_text("hwang-janson-tsai-2017.pdf")
    assert "a005942" in hjt
    assert "complexity of thue-morse seq." in hjt
    print("primary-source PDF anchors: 3 passed")

    # Kempner/Fredholm exact truncations and tail inequalities.
    for m in range(8):
        transient = 1 << m
        q = 10 ** transient
        numerator = sum(10 ** (transient - (1 << k)) for k in range(m + 1))
        assert numerator % 10 == 1
        assert math.gcd(numerator, q) == 1
        value = Fraction(numerator, q)
        assert value.denominator == q
        for j in range(transient):
            assert (value * (10 ** j)).denominator == 10 ** (transient - j)
        assert (value * (10 ** transient)).denominator == 1

        lower = Fraction(1, q * q)
        upper = Fraction(1, q * q - 1)
        sampled_tail = sum(
            (Fraction(1, 10 ** (1 << k)) for k in range(m + 1, m + 7)),
            Fraction(0),
        )
        assert lower < sampled_tail < upper
    print("Kempner denominators, transients, and tail bounds: passed M=0..7")

    # Exact near-zero bound after t=16. The omitted terms after the first are
    # dominated by ratio 10^(-2t).
    t = 16
    for n in range(1, 10):
        for s in range(t - n):
            first = Fraction(1, 10 ** (t - s))
            upper = first / (1 - Fraction(1, 10 ** (2 * t)))
            assert upper < Fraction(1, 10 ** n)
    for n in range(2, 1000):
        assert Fraction(3 * n, 2 * n + 1) > 1
    for j in (2, 3, 10):
        # M=0: transient contribution 1 plus a post-transient sum of j-1 ones.
        k2_left = 1 + abs(j - 1)
        assert k2_left == j
        assert Fraction(k2_left, 1) > Fraction(j, 262144)
    print("Kempner cluster, collision ratio, and K2 kill: passed")

    # Thue--Morse recurrence, pure-decimal truncations, and tail bounds.
    word = thue_prefix(1 << 16)
    assert word[:16] == [0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0]
    for n in range(1 << 15):
        assert word[2 * n] == word[n]
        assert word[2 * n + 1] == 1 - word[n]
    assert "000" not in "".join(map(str, word))

    for k in range(2, 513):
        prefix = word[:k]
        z = terminal_zeroes(prefix)
        assert z <= 2
        numerator = sum(bit * 10 ** (k - 1 - j) for j, bit in enumerate(prefix))
        value = Fraction(numerator, 10 ** k)
        assert value.denominator == 10 ** (k - z)
        assert (value * (10 ** (k - z))).denominator == 1
        omitted = word[k:k + 3]
        assert 1 in omitted
        sampled_tail = sum(
            (Fraction(word[j], 10 ** (j + 1)) for j in range(k, k + 100)),
            Fraction(0),
        )
        assert sampled_tail >= Fraction(1, 10 ** (k + 3))
        assert sampled_tail <= Fraction(1, 9 * 10 ** k)
    print("Thue-Morse recurrence, denominators, and tail bounds: passed K=2..512")

    # The large prefix is a bounded check of the source formula, not a proof
    # that the prefix has captured every factor for arbitrary n.
    for n in range(1, 129):
        observed = distinct_factors(word, n)
        expected = thue_complexity_formula(n)
        assert observed == expected, (n, observed, expected)
        if n >= 3:
            assert 3 * (n - 1) <= expected
            assert 3 * expected <= 10 * (n - 1)
            assert Fraction(4 * n, expected) > 1
    for m in range(2, 1000):
        assert thue_complexity_formula(2 * m) == (
            thue_complexity_formula(m) + thue_complexity_formula(m + 1)
        )
        assert thue_complexity_formula(2 * m + 1) == (
            2 * thue_complexity_formula(m + 1)
        )

    signs = [1 if bit == 0 else -1 for bit in word[:4]]
    variance = sum((signs[j + 1] - signs[j]) ** 2 for j in range(3))
    assert signs == [1, -1, -1, 1]
    assert variance == 8 > 2 * 3
    print("Thue-Morse complexity through n=128 and literal sign test V=8>6: passed")

    print("ALL T89 CHECKS PASSED")


if __name__ == "__main__":
    main()
