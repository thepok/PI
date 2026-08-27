#!/usr/bin/env python3
"""Artifact-only falsification and integrity replay for T173.

This program checks hashes, source anchors, finite indexing identities, the
residue extraction implication, bounded prime-concatenation classifications,
and displayed numerical inequalities. It is an experiment, not a proof of the
universal statements in REPORT.md.
"""

from collections import Counter
from fractions import Fraction
from hashlib import sha256
from itertools import product
from math import exp, log
from pathlib import Path
import tarfile

ROOT = Path(__file__).resolve().parent

EXPECTED = {
    "canonical_statement.txt": "cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8",
    "dusart-1002.0442v1.pdf": "3f11eca84613ad00e6a447f99b318d5c3d76e360283efcc6d3eebdda25ff3923",
    "dusart-1002.0442v1.txt": "f12bc7db244353d9e69ba54d5d9d292b752eeaa11f66a9fcf576078001466f90",
    "prior-comparators.tar": "45cfe9215e9d38557847cbea8055e454f16c866ebc62408ef5f4026c46851a0e",
}

COMPARATOR_MEMBERS = {
    "prior-T2-NormalOrbitNearReturns.lean": "1f0a50bc5286e997b897d03d49cc2613370c4cea0a20e41340f099b6278ff174",
    "prior-T89-REPORT.md": "ad90a5a5084f7ef19f4fce052ae99330f0cab9103f2942ee164d713de2a8b5b9",
    "prior-T111-REPORT.md": "89eae292ac15699fd7175b879189d6eb5560fd692029f8a9dbdc1093583156d8",
    "prior-T144-REPORT.md": "96c685692710b05035208ca459e4536f992bef2a69c030cc318625c5de00da7a",
    "prior-T160-REPORT.md": "94858ae03b2bad5ef66a0d46fa869c3f0dd3cd62d1cf076e7ae2c7104ca30b76",
    "prior-T165-REPORT.md": "a151ea4c939c65c48d3b728664ccc26b7eb0d7c7b2826b4babf1286c060384fc",
    "prior-T167-REPORT.md": "c918090e1a3c90b7b9ea1c819e19ead8813ac8ddb830e6712a5b663d29f808ae",
    "prior-T169-REPORT.md": "c714d671805944520bce7579499c9fc6cb0201a5d6a5b3866b56c45244c44467",
    "prior-T171-REPORT.md": "74f2a8789ad54796f7c08ed52c5bc0b450e00a14bcc6867dc9db11fc52d634cf",
    "prior-T172-REPORT.md": "f7ecacfa0bd8c1e0566bd19737fb157defb8eb6fff23984718e4efe5a73e5b3f",
}


def digest(name):
    return sha256((ROOT / name).read_bytes()).hexdigest()


def blocks(word, m):
    return [word[i : i + m] for i in range(len(word) - m + 1)]


def energy(words):
    c = Counter(words)
    return sum(v * v for v in c.values())


def row_energy(word, m, r):
    b = blocks(word, m)[r::m]
    return len(b), energy(b)


def primes_below(n):
    sieve = bytearray(b"\x01") * n
    if n:
        sieve[0] = 0
    if n > 1:
        sieve[1] = 0
    for p in range(2, int(n**0.5) + 1):
        if sieve[p]:
            sieve[p * p : n : p] = b"\x00" * (((n - 1 - p * p) // p) + 1)
    return [i for i, flag in enumerate(sieve) if flag]


def check_hashes_and_anchors():
    for name, wanted in EXPECTED.items():
        got = digest(name)
        assert got == wanted, (name, got, wanted)
    with tarfile.open(ROOT / "prior-comparators.tar", "r") as archive:
        members = {member.name: member for member in archive.getmembers()}
        assert set(members) == set(COMPARATOR_MEMBERS), set(members)
        for name, wanted in COMPARATOR_MEMBERS.items():
            stream = archive.extractfile(members[name])
            assert stream is not None, name
            got = sha256(stream.read()).hexdigest()
            assert got == wanted, (name, got, wanted)
    source = (ROOT / "dusart-1002.0442v1.txt").read_text(errors="replace")
    for anchor in ["Theorem 6.9.", "x⩾599", "1.2762", "x>1"]:
        assert anchor in source, anchor
    report = (ROOT / "REPORT.md").read_text()
    for marker in [
        "BAD-WORD CENSUS T173",
        "GOOD-PRIME INTERIORS",
        "EXCEPTIONAL-PRIME INTERIORS",
        "PRIME BOUNDARIES",
        "EARLIER DIGIT-LENGTH SHELLS",
        "TERMINAL ENDPOINT",
        "UNPROVED TRANSFER TOWARD T7/T107",
        "| T171 | source statements are `literature-checked`",
        "| T172 | unverified `proof sketch`",
        "SCOPED_VERDICT (1/1): HOLD AS MODEL",
    ]:
        assert marker in report, marker
    assert report.count("SCOPED_VERDICT (1/1):") == 1


def check_residue_extraction():
    # Exhaustive decimal instances small enough for a quick replay. The report's
    # theorem starts at m=3; these tests target the indexing implication itself.
    checked = 0
    for n, m in [(4, 2), (5, 2)]:
        q = n - m + 1
        for digits in product("0123456789", repeat=n):
            word = "".join(digits)
            e = energy(blocks(word, m))
            if Fraction(e, 1) > Fraction(q * q, m * m):
                heavy = False
                for r in range(m):
                    qr, er = row_energy(word, m, r)
                    if Fraction(er, 1) > Fraction(qr * qr, 2 * m * m):
                        heavy = True
                assert heavy, (word, n, m, e)
            checked += 1
    return checked


def check_prime_prefixes():
    checked = 0
    for d in range(2, 5):
        ps = primes_below(10**d)
        word = "".join(map(str, ps))
        for m in range(1, min(4, len(word)) + 1):
            literal = blocks(word, m)
            M = len(word) - m + 1
            assert len(literal) == M
            assert energy(literal) == sum(v * v for v in Counter(literal).values())

            # Classify each legal start by whether its endpoint remains in the
            # same prime. The classes are disjoint and exhaustive.
            spans = []
            pos = 0
            for p in ps:
                nxt = pos + len(str(p))
                spans.append((pos, nxt))
                pos = nxt
            interiors = boundaries = 0
            for i in range(M):
                owner = next((ab for ab in spans if ab[0] <= i < ab[1]), None)
                assert owner is not None
                if i + m <= owner[1]:
                    interiors += 1
                else:
                    boundaries += 1
            assert interiors + boundaries == M
            assert boundaries <= (m - 1) * max(0, len(ps) - 1)
            assert len(word) - M == m - 1
            checked += 1
    return checked


def check_displayed_arithmetic():
    # Dusart subtraction used in Section 6 and the elementary entropy constant.
    ln10 = log(10)
    for s in range(4, 1000):
        # This is the subtraction divided by 10^s/(2s log 10), exactly
        # equation (4.3) of the report, so no enormous power is evaluated.
        normalized = 2 * (1 + 1 / (s * ln10)) - s / (5 * (s - 1)) * (
            1 + 1.2762 / ((s - 1) * ln10)
        )
        assert normalized >= 1
    for m in range(3, 1000):
        deficit = (m * ln10 - log(8 * m**3) - 1) / (2 * m)
        assert deficit > 0.01
        assert log(8 * m * ln10) <= 6 * m
        assert 8 * m * ln10 + log(8 * m * ln10) <= 25 * m
        assert log(16 * m * ln10) <= 6 * m
        assert 8 * m * ln10 + log(16 * m * ln10) <= 25 * m
        assert log(25 * m / ln10) <= 8 * m * ln10

    # Floating-point checks only, at log scale, for the census absorption and
    # final error terms at the smallest theorem endpoint.
    for m in range(3, 21):
        log_h = 8 * m * ln10
        # Check the complete displayed sum in (3.12), scaled by its right side
        # so only one representable exponential is needed.
        scaled_left = 400 * m * (
            exp(m * ln10 - log_h) * (log_h + 1)
            + exp(log(m) - log_h)
        )
        assert scaled_left <= 1
        h = 10.0 ** (8 * m)
        log_eta = log(2 * ln10) + log_h - h / (400 * m)
        boundary = 4 * m / h
        log_delta = log(4 * ln10) + log_h - h * ln10
        eta = exp(log_eta) if log_eta > -745 else 0.0
        delta = exp(log_delta) if log_delta > -745 else 0.0
        assert eta + boundary + delta < 1 / m


def main():
    check_hashes_and_anchors()
    residue_words = check_residue_extraction()
    prefix_cases = check_prime_prefixes()
    check_displayed_arithmetic()
    print("T173 artifact-only replay")
    print("LABEL: experiment; finite checks are not proof")
    print(f"HASHED_INPUTS: {len(EXPECTED)}")
    print(f"COMPARATOR_ARCHIVE_MEMBERS: {len(COMPARATOR_MEMBERS)}")
    print("PRIMARY_SOURCE_COUNT: 1")
    print(f"RESIDUE_EXTRACTION_WORDS: {residue_words}")
    print(f"PRIME_PREFIX_CASES: {prefix_cases}")
    print("DUSART_SUBTRACTION_GRID: s=4..999")
    print("ENTROPY_DEFICIT_GRID: m=3..999")
    print("GROWING_RANGE_LOG_CHECK: m=3..20")
    print("SCOPED_VERDICT_COUNT: 1")
    print("STATUS: all checks passed")


if __name__ == "__main__":
    main()
