#!/usr/bin/env python3
"""Dependency-free exact replay for the T87 start-truncation audit."""

from fractions import Fraction
import hashlib
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parent

EXPECTED_HASHES = {
    "pi-positive-decimal-factor-entropy.txt":
        "a70dd741b27595aeb3dfc902b5e201579fed6bae24e2191f58c5ac64a22939e6",
    "zeilberger-zudilin-2020.pdf":
        "3b11c4bf3e25927227ac8f7f4e49d7f1d3efeb42beecd7f3b8c64efb162d20b5",
    "zeilberger-zudilin-2020.txt":
        "49ca4907538e4ccea23cee27f051f5b33832ed2cf3e3093b4aab58a13c814a68",
}


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def check(condition, message):
    if not condition:
        raise RuntimeError(message)


def cutoff_data(n):
    a = 125 * n // 763
    beta = 125 * n - 763 * a
    return a, beta


def q_value(j, r):
    return 10**j * (10**r - 1)


def q_below_onset(j, r, q0):
    # If j has at least as many decimal places as q0, then q>=9*10^j>q0.
    if j >= len(str(q0)):
        return False
    return q_value(j, r) < q0


def direct_power_eligible(n, j, r):
    return q_value(j, r) ** 763 <= 10 ** (125 * n)


def classified_power_eligible(n, j, r):
    a, beta = cutoff_data(n)
    s = j + r
    if s <= a:
        return True
    if s >= a + 2:
        return False
    if r == 1:
        return beta >= 729
    if r == 2:
        return a >= 1 and beta >= 760
    return False


def early_residual_direct(n, q0):
    a, _ = cutoff_data(n)
    count = 0
    for j in range(a):
        for r in range(1, n):
            if q_below_onset(j, r, q0) or not direct_power_eligible(n, j, r):
                count += 1
    return count


def early_residual_formula(n, q0):
    a, beta = cutoff_data(n)
    p = 0
    for j in range(a):
        for r in range(1, n):
            if q_below_onset(j, r, q0) and direct_power_eligible(n, j, r):
                p += 1
    return (
        a * (n - 1)
        - a * (a + 1) // 2
        - int(a >= 1 and beta >= 760)
        + p
    )


def late_residual_formula(n, q0):
    a, beta = cutoff_data(n)
    length = 10 ** (n // 2)
    unmasked = (n - 1) * (length - a) - n * (n - 1) // 2
    removed = int(beta >= 729 and q0 <= 9 * 10**a)
    return unmasked - removed


def late_residual_direct_small(n, q0):
    a, _ = cutoff_data(n)
    length = 10 ** (n // 2)
    count = 0
    for r in range(1, n):
        for j in range(a, length - r):
            if q_below_onset(j, r, q0) or not classified_power_eligible(n, j, r):
                count += 1
    return count


def envelope_tail(n):
    return -Fraction(120 * n * n + 60 * n + 45, 4 * 5**n)


def main():
    hashes = {name: sha256(ROOT / name) for name in EXPECTED_HASHES}
    check(hashes == EXPECTED_HASHES, "pinned input hash mismatch")

    statement = (ROOT / "pi-positive-decimal-factor-entropy.txt").read_text()
    source = (ROOT / "zeilberger-zudilin-2020.txt").read_text()
    check("CANONICAL QUESTION" in statement, "canonical statement anchor missing")
    check("one fixed eta > 0" in statement, "canonical quantifier anchor missing")
    check("The irrationality measure of" in source, "source title anchor missing")
    check(
        "7.10320533413700172750577342281" in source,
        "source exponent anchor missing",
    )
    check("Proposition 7." in source, "source Proposition 7 anchor missing")
    check("Proposition 8." in source, "source Proposition 8 anchor missing")

    threshold_checks = {
        "nine": 10**728 < 9**763 < 10**729,
        "ninety_nine": 10 ** (763 + 759) < 99**763 < 10 ** (763 + 760),
        "nine_ninety_nine": 999**763 > 10 ** (2 * 763 + 762),
    }
    check(all(threshold_checks.values()), "boundary power threshold failed")

    classification_cases = 0
    for n in range(2, 101):
        a, beta = cutoff_data(n)
        check(a == 125 * n // 763, "cutoff floor identity failed")
        check(0 <= beta <= 762, "cutoff remainder range failed")
        # Direct checks only need the main wedge and the sole boundary line.
        for s in range(max(1, a - 1), a + 3):
            for r in range(1, min(n, s + 1)):
                j = s - r
                check(
                    direct_power_eligible(n, j, r)
                    == classified_power_eligible(n, j, r),
                    "power-eligibility classification failed",
                )
                classification_cases += 1

    count_cases = 0
    for n in range(2, 10):
        length = 10 ** (n // 2)
        a, _ = cutoff_data(n)
        check(length >= 2 * n, "sample length comparison failed")
        check(a < n, "cutoff below scale failed")
        for q0 in (2, 10, 100, 1000):
            check(
                early_residual_direct(n, q0) == early_residual_formula(n, q0),
                "early residual count formula failed",
            )
            check(
                late_residual_direct_small(n, q0) == late_residual_formula(n, q0),
                "late residual count formula failed",
            )
            count_cases += 1

    for n in range(2, 1001):
        check(10 ** (n // 2) >= 2 * n, "sample length finite check failed")

    telescope_cases = 0
    for n in range(0, 101):
        term = Fraction(24 * n * n, 5**n)
        check(
            term == envelope_tail(n + 1) - envelope_tail(n),
            "envelope telescope step failed",
        )
        telescope_cases += 1
    envelope_sum = -envelope_tail(2)
    check(envelope_sum == Fraction(129, 20), "envelope sum constant failed")
    envelope_square = envelope_sum * envelope_sum
    check(
        envelope_square == Fraction(16641, 400),
        "envelope square constant failed",
    )
    check(envelope_square < 42, "grouped square integer envelope failed")

    asymptotic_coefficient = Fraction(125, 763) - Fraction(1, 2) * Fraction(
        125, 763
    ) ** 2
    check(
        asymptotic_coefficient == Fraction(175125, 1164338),
        "early asymptotic coefficient failed",
    )

    output = {
        "status": "experiment",
        "hashes": hashes,
        "cutoff": "J_n=floor(125*n/763)",
        "lambda": "763/125",
        "boundary_thresholds": threshold_checks,
        "classification_cases": classification_cases,
        "count_cases": count_cases,
        "early_asymptotic_coefficient": str(asymptotic_coefficient),
        "envelope_sum": str(envelope_sum),
        "envelope_square": str(envelope_square),
        "grouped_square_strict_upper_integer": 42,
    }
    print(json.dumps(output, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
