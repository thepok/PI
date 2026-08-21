#!/usr/bin/env python3
"""Self-contained transcription checks for the T103 proof-sketch note."""

from collections import Counter
from fractions import Fraction
from hashlib import sha256
from pathlib import Path


ROOT = Path(__file__).resolve().parent

EXPECTED = {
    "canonical_statement.txt":
        "cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8",
    "akl-1304.3587v2.pdf":
        "6d65ce118a10b38450fd0d38716a3624ec3a2dea56bb08c32771a88165b88ce3",
    "akl-1304.3587v2.txt":
        "cba463bd9a3522b3ece79f760aa8d08f65e058c0088a36b07fb5f7b6037ab97a",
    "downarowicz-kasjan-1502.02307.pdf":
        "11f3315b34ec2d84a59c849860c2a2a90903348160e7a4316788840f2713e540",
    "downarowicz-kasjan-1502.02307.txt":
        "a8f7432f3e2a85641b39020a98b129816f3d9fd9187747e6fa2dd2e78fb7003d",
}


def digest(name):
    return sha256((ROOT / name).read_bytes()).hexdigest()


def mobius(n):
    if n == 0:
        return 0
    result = 1
    p = 2
    while p * p <= n:
        exponent = 0
        while n % p == 0:
            n //= p
            exponent += 1
        if exponent >= 2:
            return 0
        if exponent == 1:
            result = -result
        p += 1
    if n > 1:
        result = -result
    return result


def initials_through(limit):
    initials = []
    for n in range(limit + 1):
        owner = next(
            (u for u in initials if n >= u and (n - u) % (5 ** (u + 1)) == 0),
            None,
        )
        if owner is None:
            initials.append(n)
    return initials


def initial_of(n, known_initials):
    for u in known_initials:
        if u > n:
            break
        if (n - u) % (5 ** (u + 1)) == 0:
            return u
    return n


def z_value(n, known_initials):
    return mobius(initial_of(n, known_initials))


def block(start, length, known_initials):
    return tuple(z_value(start + t, known_initials) for t in range(length))


def energy(length, cutoff, known_initials):
    counts = Counter(block(i, length, known_initials) for i in range(cutoff))
    by_squares = sum(c * c for c in counts.values())
    by_pairs = sum(
        block(i, length, known_initials) == block(j, length, known_initials)
        for i in range(cutoff)
        for j in range(cutoff)
    )
    assert by_squares == by_pairs
    return by_squares


def successor_drop(length, cutoff, known_initials):
    parents = Counter(block(i, length, known_initials) for i in range(cutoff))
    children = Counter(block(i, length + 1, known_initials) for i in range(cutoff))
    grouped = {}
    for child, count in children.items():
        grouped.setdefault(child[:-1], []).append(count)
    rhs = 0
    for parent in parents:
        values = grouped.get(parent, [])
        rhs += 2 * sum(
            values[i] * values[j]
            for i in range(len(values))
            for j in range(i + 1, len(values))
        )
    assert energy(length, cutoff, known_initials) - energy(
        length + 1, cutoff, known_initials
    ) == rhs


def main():
    for name, expected in EXPECTED.items():
        assert digest(name) == expected, name

    report = (ROOT / "REPORT.md").read_text(encoding="utf-8")
    assert report.count("RETAINED_CANDIDATE_COUNT: 1") == 1
    assert report.count("RETAINED_PRIMARY_SOURCE_COUNT: 2") == 1
    assert report.count("TERMINAL_VERDICT: close") == 1
    assert "TERMINAL_VERDICT: " + "develop" not in report
    assert "TERMINAL_VERDICT: " + "hold as " + "model" not in report
    assert "mobius(0)=0" in report
    assert "(1-mu*eta)" in report
    assert "rho_*" in report

    akl = (ROOT / "akl-1304.3587v2.txt").read_text(encoding="utf-8")
    dk = (ROOT / "downarowicz-kasjan-1502.02307.txt").read_text(
        encoding="utf-8"
    )
    for marker in ["(For instance, an = 5n .)", "Proposition 5.",
                   "Thanks to the property 3, z is a Toeplitz sequence"]:
        assert marker in akl, marker
    for marker in ["Example 6.3.", "Lemma 7.1.",
                   "8. Entropy of the Example 6.3",
                   "positive topological entropy"]:
        assert marker in dk, marker

    initials = initials_through(40)
    for r in range(21):
        height = 5 ** (r + 1)
        stage_initials = [u for u in initials if u <= r]
        expected_resolved = sum(height // (5 ** (u + 1)) for u in stage_initials)
        for index, u in enumerate(stage_initials):
            for v in stage_initials[index + 1:]:
                assert (v - u) % (5 ** (u + 1)) != 0
        holes = height - expected_resolved
        assert 4 * holes > 3 * height

    for r in range(6):
        height = 5 ** (r + 1)
        stage_initials = [u for u in initials if u <= r]
        resolved = {
            residue
            for residue in range(height)
            if any((residue - u) % (5 ** (u + 1)) == 0 for u in stage_initials)
        }
        expected_resolved = sum(height // (5 ** (u + 1)) for u in stage_initials)
        assert len(resolved) == expected_resolved

    enough_initials = initials_through(300)
    for start in range(20):
        for length in range(1, 7):
            owners = [initial_of(start + t, enough_initials) for t in range(length)]
            return_height = 5 ** (max(owners) + 1)
            shifted = tuple(
                z_value(start + return_height + t, enough_initials)
                for t in range(length)
            )
            assert shifted == block(start, length, enough_initials)

    finite_initials = initials_through(500)
    for cutoff in range(1, 31):
        for length in range(1, 7):
            value = energy(length, cutoff, finite_initials)
            assert cutoff <= value <= cutoff * cutoff
            successor_drop(length, cutoff, finite_initials)

    for eta in [Fraction(1, 10), Fraction(1, 5), Fraction(1, 3)]:
        for x in range(10):
            for y in range(10):
                for z in range(10):
                    counts = [x, y, z]
                    total = sum(counts)
                    if total == 0:
                        continue
                    large = [count for count in counts if count >= eta * total]
                    if len(large) >= 2:
                        assert sum(count * count for count in counts) <= (
                            1 - eta
                        ) * total * total

    for start, length, q in [(0, 1, 4), (1, 1, 3), (1, 2, 2)]:
        owners = [initial_of(start + t, finite_initials) for t in range(length)]
        height = 5 ** (max(owners) + 1)
        assert start < height
        assert energy(length, q * height, finite_initials) >= q * q

    print("T103 replay: PASS")
    print("checked 1 retained candidate and 2 retained primary sources")
    print("checked source hashes and authenticated text markers")
    print("checked stage-hole formulas through R=20 and enumerated through R=5")
    print("checked pointwise periods, collisions, and exact T14-sibling decrement")
    print("finite checks are experiments; universal claims remain a proof sketch")


if __name__ == "__main__":
    main()
