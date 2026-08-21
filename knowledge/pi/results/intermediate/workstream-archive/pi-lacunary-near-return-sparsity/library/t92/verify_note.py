#!/usr/bin/env python3
from __future__ import annotations

from fractions import Fraction
import hashlib
import itertools
import pathlib
import re


ROOT = pathlib.Path(__file__).resolve().parent
CANONICAL_SHA256 = (
    "cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8"
)


def sha256(name: str) -> str:
    return hashlib.sha256((ROOT / name).read_bytes()).hexdigest()


def counts(n: int) -> tuple[int, int, int]:
    length = 2 ** (n // 2)
    last_short_lag = min(n - 1, length - 1)
    short = 2 * last_short_lag * length - last_short_lag * (last_short_lag + 1)
    long = length * (length - 1) - short
    assert short + long == length * (length - 1)
    return length, short, long


def binary_discriminator(n: int) -> tuple[int, int, int, bool]:
    length = 2 ** (n // 2)
    word_length = length + n - 1
    best = -10**9
    best_short = 0
    best_long = 0
    constant_is_maximizer = False
    for word in itertools.product(range(2), repeat=word_length):
        blocks = [word[i : i + n] for i in range(length)]
        short = 0
        long = 0
        for i in range(length):
            for j in range(length):
                if i == j or blocks[i] != blocks[j]:
                    continue
                if abs(i - j) < n:
                    short += 1
                else:
                    long += 1
        numerator = 2 * short - 3 * long
        if numerator > best:
            best = numerator
            best_short = short
            best_long = long
            constant_is_maximizer = all(symbol == 0 for symbol in word)
        elif numerator == best and all(symbol == 0 for symbol in word):
            constant_is_maximizer = True
    return best, best_short, best_long, constant_is_maximizer


def main() -> None:
    manifest: dict[str, str] = {}
    for line in (ROOT / "SHA256SUMS").read_text().splitlines():
        digest, name = line.split("  ", 1)
        manifest[name] = digest
    expected_files = {
        "T92ConstantRunDiscriminator.lean",
        "REPORT.md",
        "canonical_statement.txt",
        "verify_note.py",
    }
    assert set(manifest) == expected_files
    for name, expected_digest in manifest.items():
        assert sha256(name) == expected_digest, name

    actual = sha256("canonical_statement.txt")
    assert actual == CANONICAL_SHA256, (actual, CANONICAL_SHA256)

    lean = (ROOT / "T92ConstantRunDiscriminator.lean").read_text()
    report = (ROOT / "REPORT.md").read_text()

    required_lean = [
        "namespace DecimalFactorComplexity.T92ConstantRunDiscriminator",
        "def constantBinaryStream : Stream (Fin 2)",
        "theorem binaryExactShortPairCount_constantBinaryStream",
        "theorem binaryExactLongPairCount_constantBinaryStream",
        "theorem constantRun_short_add_long",
        "theorem twenty_mul_add_ten_le_three_mul_two_pow_sub_one",
        "theorem late_constantShortCount_charged_by_long",
        "theorem legal_constantBinaryStream_uniform_reviewB_bound",
        "theorem constant_family_equality_at_seven",
    ]
    for needle in required_lean:
        assert needle in lean, f"missing Lean declaration: {needle}"

    forbidden = re.compile(
        r"\b(sorry|admit|native_decide|unsafe\s+(?:def|theorem)|axiom)\b"
    )
    assert not forbidden.search(lean), "forbidden Lean construct found"

    required_report = [
        "Pairs are ordered, all `N` diagonal pairs are included",
        "The frequency range is strict, signed, and includes `h=0`.",
        "long cutoff includes lag `n`",
        "Candidate disposition: uniformly bounded.",
        "No fixed-pi, C1, or C2 claim is made.",
    ]
    for needle in required_report:
        assert needle in report, f"missing report marker: {needle}"

    expected = {
        1: (1, 0, 0, Fraction(0)),
        2: (2, 2, 0, Fraction(1)),
        3: (2, 2, 0, Fraction(1)),
        4: (4, 12, 0, Fraction(3)),
        5: (4, 12, 0, Fraction(3)),
        6: (8, 50, 6, Fraction(41, 8)),
        7: (8, 54, 2, Fraction(51, 8)),
        8: (16, 168, 72, Fraction(15, 4)),
        9: (16, 184, 56, Fraction(25, 4)),
        10: (32, 486, 506, Fraction(-273, 32)),
        11: (32, 530, 462, Fraction(-163, 32)),
    }
    for n, row in expected.items():
        length, short, long = counts(n)
        assert short == 2 * sum(
            length - r for r in range(1, min(n, length))
        )
        assert long == 2 * sum(length - r for r in range(n, length))
        discriminator = Fraction(2 * short - 3 * long, 2 * length)
        assert (length, short, long, discriminator) == row

    expected_maxima = [0, 4, 4, 24, 24, 82]
    for n, expected_numerator in enumerate(expected_maxima, start=1):
        numerator, short, long, constant_is_maximizer = binary_discriminator(n)
        assert numerator == expected_numerator, (n, numerator, short, long)
        assert constant_is_maximizer, n

    # Replay checks are finite sanity checks; the Lean induction is the proof.
    for n in range(1, 257):
        length, short, long = counts(n)
        assert 8 * short <= 51 * length + 12 * long
        if n >= 12:
            assert 2 * short <= 3 * long

    for k in range(6, 257):
        assert 20 * k + 10 <= 3 * (2**k - 1)
        assert 3 * (2 ** (k + 1) - 1) - 3 * (2**k - 1) == 3 * 2**k

    assert counts(7) == (8, 54, 2)
    print("T92 replay passed")
    print(f"canonical SHA-256: {actual}")
    print("constant binary family: uniform discriminator <= 51/8")
    print("sharp family equality: n=7, L=8, S=54, R=2")
    print("T87 binary maxima replayed exhaustively for 1 <= n <= 6")


if __name__ == "__main__":
    main()
