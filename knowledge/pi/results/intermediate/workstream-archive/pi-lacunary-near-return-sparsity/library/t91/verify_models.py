#!/usr/bin/env python3
"""Self-contained exact replay for the bounded T91 model checks."""

from collections import Counter
from hashlib import sha256
from pathlib import Path


ROOT = Path(__file__).resolve().parent
CANONICAL_SHA256 = "cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8"


def morph(word: str, rule: dict[str, str]) -> str:
    return "".join(rule[c] for c in word)


def iterate(seed: str, rule: dict[str, str], exponent: int) -> str:
    word = seed
    for _ in range(exponent):
        word = morph(word, rule)
    return word


def aligned_counts(word: str, block_length: int) -> Counter[str]:
    assert len(word) % block_length == 0
    return Counter(
        word[start : start + block_length]
        for start in range(0, len(word), block_length)
    )


def collision_energy(counts: Counter[str]) -> int:
    # Ordered and diagonal-inclusive, matching the normalization used in T7/T14.
    return sum(count * count for count in counts.values())


def thue_morse_checks() -> None:
    rule = {"0": "01", "1": "10"}
    checked = 0
    for K in range(1, 11):
        word = iterate("0", rule, K)
        for r in range(K):
            counts = aligned_counts(word, 2**r)
            q = 2 ** (K - r - 1)
            assert counts == Counter({iterate("0", rule, r): q,
                                      iterate("1", rule, r): q})
            Q = 2 ** (K - r)
            assert sum(counts.values()) == Q
            assert collision_energy(counts) == 2 * q * q == Q * Q // 2
            checked += 1

    example = aligned_counts(iterate("0", rule, 4), 2**2)
    assert example == Counter({"0110": 2, "1001": 2})
    assert collision_energy(example) == 8
    print(f"THUE_MORSE formula_checks={checked} K=4 r=2 counts={dict(sorted(example.items()))} E=8 Q=4")


def period_doubling_checks() -> None:
    rule = {"0": "01", "1": "00"}
    checked = 0
    for K in range(1, 11):
        word = iterate("0", rule, K)
        for r in range(K):
            s = K - r
            counts = aligned_counts(word, 2**r)
            sign = -1 if s % 2 else 1
            zeros = (2 ** (s + 1) + sign) // 3
            ones = (2**s - sign) // 3
            assert counts == Counter({iterate("0", rule, r): zeros,
                                      iterate("1", rule, r): ones})
            Q = 2**s
            expected = (5 * 4**s + 2 * 2**s * sign + 2) // 9
            assert sum(counts.values()) == Q
            assert collision_energy(counts) == zeros * zeros + ones * ones == expected
            checked += 1

    example = aligned_counts(iterate("0", rule, 5), 2**2)
    assert example == Counter({"0100": 5, "0101": 3})
    assert collision_energy(example) == 34
    print(f"PERIOD_DOUBLING formula_checks={checked} K=5 r=2 counts={dict(sorted(example.items()))} E=34 Q=8")


def paperfolding_digit(n: int) -> int:
    """One-based regular paperfolding convention n=2^a(2j+1), digit=j mod 2."""
    assert n >= 1
    while n % 2 == 0:
        n //= 2
    j = (n - 1) // 2
    return j % 2


def paperfolding_block(start: int, length: int) -> str:
    return "".join(str(paperfolding_digit(n)) for n in range(start, start + length))


def canonical_positions(k: int) -> set[int]:
    assert k >= 1
    if k == 1:
        return {1, 2, 3, 6}
    if k % 2 == 0:
        half = canonical_positions(k // 2)
        return {2 * p - 1 for p in half} | {2 * p for p in half}
    lower = canonical_positions(k // 2)
    upper = canonical_positions(k // 2 + 1)
    return {2 * p - 1 for p in lower} | {2 * p for p in upper}


def paperfolding_checks() -> None:
    # Cardinality is an exact consequence of the displayed recursion; this loop
    # is only a bounded replay, not a proof of the source theorem.
    for k in range(1, 65):
        assert len(canonical_positions(k)) == 4 * k

    expected_p7 = {
        *range(1, 13), 14, 15, 16, 18, 19, 20, 21, 22, 23, 24,
        42, 43, 44, 46, 47, 48,
    }
    p7 = canonical_positions(7)
    assert p7 == expected_p7
    blocks = {p: paperfolding_block(p, 7) for p in sorted(p7)}
    assert len(set(blocks.values())) == 28

    collisions = [(13, 5), (17, 1), (45, 21)]
    values = []
    for noncanonical, canonical in collisions:
        left = paperfolding_block(noncanonical, 7)
        right = paperfolding_block(canonical, 7)
        assert left == right
        assert noncanonical not in p7 and canonical in p7
        values.append(f"{noncanonical}->{canonical}:{left}")

    first_48 = Counter(paperfolding_block(start, 7) for start in range(1, 49))
    assert len(first_48) == 28
    assert collision_energy(first_48) == 98
    print("PAPERFOLDING k=7 |P7|=28 distinct=28 first48_types=28 first48_E=98 collisions="
          + ",".join(values))


def main() -> None:
    canonical = (ROOT / "canonical_statement.txt").read_bytes()
    actual = sha256(canonical).hexdigest()
    assert actual == CANONICAL_SHA256
    print(f"CANONICAL sha256={actual}")
    thue_morse_checks()
    period_doubling_checks()
    paperfolding_checks()
    print("ALL_CHECKS_PASSED")


if __name__ == "__main__":
    main()
