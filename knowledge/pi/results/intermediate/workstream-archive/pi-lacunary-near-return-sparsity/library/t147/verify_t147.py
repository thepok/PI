#!/usr/bin/env python3
"""Self-contained finite replay for T147; experiments are not universal proof."""

from __future__ import annotations

from fractions import Fraction
from hashlib import sha256
from itertools import product
from math import ceil, log, sqrt
from pathlib import Path


ROOT = Path(__file__).resolve().parent
CANONICAL_SHA = "cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8"
T140_SHA = "ff05177ccaaebfd56d41467f2f74dce085aae3b855be95f6d1c458526541f35c"
T144_SHA = "96c685692710b05035208ca459e4536f992bef2a69c030cc318625c5de00da7a"


def digest(name: str) -> str:
    return sha256((ROOT / name).read_bytes()).hexdigest()


def block_counts(word: tuple[int, ...], n: int, m: int) -> dict[tuple[int, ...], int]:
    counts: dict[tuple[int, ...], int] = {}
    for i in range(n):
        block = word[i : i + m]
        assert len(block) == m
        counts[block] = counts.get(block, 0) + 1
    return counts


def energy(word: tuple[int, ...], n: int, m: int) -> int:
    return sum(value * value for value in block_counts(word, n, m).values())


def direct_energy(word: tuple[int, ...], n: int, m: int) -> int:
    blocks = [word[i : i + m] for i in range(n)]
    return sum(u == v for u in blocks for v in blocks)


def check_marginals(word: tuple[int, ...], n: int, m: int) -> None:
    short = block_counts(word, n, m - 1)
    long = block_counts(word, n, m)
    for prefix in product(range(10), repeat=m - 1):
        assert short.get(prefix, 0) == sum(
            long.get(prefix + (digit,), 0) for digit in range(10)
        )
    c_short = Fraction(sum(v * v for v in short.values()), n * n)
    c_long = Fraction(sum(v * v for v in long.values()), n * n)
    assert c_long <= c_short <= 10 * c_long


def exact_small_sweep() -> tuple[int, int]:
    words = 0
    depth_checks = 0
    # Binary words are embedded in the decimal alphabet and suffice to check
    # the exact identities at every endpoint in this finite range.
    for n in range(1, 7):
        k = 3
        length = n + k - 1
        for word in product(range(2), repeat=length):
            words += 1
            for m in range(1, k + 1):
                assert energy(word, n, m) == direct_energy(word, n, m)
                assert energy(word, n, m) >= n
                if m >= 2:
                    check_marginals(word, n, m)
                depth_checks += 1
    return words, depth_checks


def check_counterfamilies() -> tuple[int, int]:
    families = 0
    words = 0
    # Small bases are used only to exhaust the construction. The proof is
    # alphabet-independent and the report specializes it to base 10.
    for n, k in [(16, 4), (25, 5), (36, 6)]:
        a = ceil(k / 2)
        r = ceil(n / sqrt(a))
        length = n + k - 1
        fixed = r + k - 1
        assert length - fixed == n - r
        # Enumerate a binary subfamily with the same forced zero prefix.
        free = n - r
        assert free <= 32
        for suffix in product(range(2), repeat=free):
            word = (0,) * fixed + suffix
            assert len(word) == length
            for m in range(a, k + 1):
                e = energy(word, n, m)
                assert e * m >= n * n
                assert block_counts(word, n, m).get((0,) * m, 0) >= r
            words += 1
        assert 2**free == sum(1 for _ in product(range(2), repeat=free))
        families += 1
    return families, words


def check_additive_constants(k: int) -> tuple[float, float, float]:
    # Floating point is only a falsification check of the report's elementary
    # real inequalities; the monotone symbolic estimates are in Section 5.
    n = 10 ** (4 * k)
    a = ceil(k / 2)
    reciprocal_sum = sum(1 / sqrt(m) for m in range(a, k + 1))
    assert reciprocal_sum >= sqrt(k) / 2
    # log(N+1) < 10k is proved symbolically in the report.  Its normalized
    # contribution is bounded here without converting the enormous N to float.
    assert 4 * k * log(10) + log(2) < 10 * k
    cost_over_n_upper = log(10) / sqrt(a) + 3 * float(Fraction(1, n))
    assert cost_over_n_upper < 5 / sqrt(k) + 3 * float(Fraction(1, n))

    # This is the explicit lower bound (5.4), divided by N. Fractions preserve
    # the enormous powers exactly before the negligible terms become floats.
    type_ratio_upper = Fraction(10 * k * k * 10**k, n)
    linear_ratio_upper = Fraction(k * k, n)
    phi_over_n = (
        sqrt(k) / 800 - float(type_ratio_upper) - float(linear_ratio_upper)
    )
    assert phi_over_n > cost_over_n_upper

    coarse_margin = (
        sqrt(k) / 800
        - 10 * k * k * 10**k / n
        - k * k / n
        - 5 / sqrt(k)
        - 3 / n
    )
    assert coarse_margin > 0
    return reciprocal_sum, phi_over_n, cost_over_n_upper


def check_report_markers() -> None:
    report = (ROOT / "REPORT.md").read_text()
    required = [
        "KAPPA: 1/4",
        "RHO: 1/2",
        "FIRST_K: 8000",
        "SCOPED_VERDICT_COUNT: 1",
        "SCOPED_VERDICT (1/1): **close**",
        "PI-MULTISCALE-MEMBERSHIP-EXCLUSION-T147",
        "UNPROVED PI-SPECIFIC PREMISE; NOT",
        "FIXED_PI_CLAIM: none",
        "A1_CLAIM: none",
        "C1_CLAIM: none",
        "C2_CLAIM: none",
        "CONJECTURE_CLAIM: none",
        "F_k subset B_k for every integer k>=8000",
        "h_2(m|m-1)=H_2(m)-H_2(m-1)",
        "prior-T140-REPORT.md",
        "prior-T144-REPORT.md",
    ]
    for marker in required:
        assert marker in report, marker
    assert report.count("SCOPED_VERDICT (1/1)") == 1


def main() -> None:
    assert digest("canonical_statement.txt") == CANONICAL_SHA
    assert digest("prior-T140-REPORT.md") == T140_SHA
    assert digest("prior-T144-REPORT.md") == T144_SHA
    check_report_markers()

    words, depth_checks = exact_small_sweep()
    families, family_words = check_counterfamilies()
    constant_rows = []
    for k in [8000, 8001, 10000, 16000]:
        reciprocal_sum, phi_over_n, cost_over_n = check_additive_constants(k)
        constant_rows.append((k, reciprocal_sum, phi_over_n, cost_over_n))

    print("T147 finite replay: experiment only")
    print(f"canonical_sha256={CANONICAL_SHA}")
    print(f"t140_report_sha256={T140_SHA}")
    print(f"t144_report_sha256={T144_SHA}")
    print(f"small_words_checked={words}")
    print(f"ordered_diagonal_depth_checks={depth_checks}")
    print(f"counterfamilies_checked={families}")
    print(f"counterfamily_words_checked={family_words}")
    for k, reciprocal_sum, phi_over_n, cost_over_n in constant_rows:
        print(
            f"k={k};sum_inv_sqrt={reciprocal_sum:.12f};"
            f"phi_over_N={phi_over_n:.12f};cost_over_N={cost_over_n:.12f}"
        )
    print("terminal=exact_infinite_counterfamily")
    print("verdict=close")
    print("pi_transfer=unproved_not_asserted")
    print("fixed_pi_claim=none;A1_claim=none;C1_claim=none;C2_claim=none")


if __name__ == "__main__":
    main()
