#!/usr/bin/env python3
"""Exact replay checks for the T67 moving-seed counterfamily."""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
import math
from fractions import Fraction
from pathlib import Path


CANONICAL_SHA256 = "a70dd741b27595aeb3dfc902b5e201579fed6bae24e2191f58c5ac64a22939e6"


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def digit(n: int, i: int) -> int:
    require(n >= 1 and i >= 0, "digit indices must be nonnegative and n positive")
    if i < n:
        return 2
    if i < 2 * n:
        return 3
    if i < 3 * n:
        return 4
    if i < 4 * n:
        return 6
    t = (i - 4 * n) % (5 * n)
    return 0 if t < 4 * n else 5


def block(n: int, start: int, length: int) -> tuple[int, ...]:
    return tuple(digit(n, start + i) for i in range(length))


def pow10neg(k: int) -> Fraction:
    return Fraction(1, 10**k)


def seed(n: int) -> Fraction:
    return (
        Fraction(2, 9) * (1 - pow10neg(n))
        + Fraction(3, 9) * (pow10neg(n) - pow10neg(2 * n))
        + Fraction(4, 9) * (pow10neg(2 * n) - pow10neg(3 * n))
        + Fraction(6, 9) * (pow10neg(3 * n) - pow10neg(4 * n))
        + Fraction(5, 9)
        * (pow10neg(8 * n) - pow10neg(9 * n))
        / (1 - pow10neg(5 * n))
    )


def floor_fraction(x: Fraction) -> int:
    return x.numerator // x.denominator


def decimal_digits(x: Fraction, count: int) -> tuple[int, ...]:
    out: list[int] = []
    y = x
    for _ in range(count):
        y *= 10
        a = floor_fraction(y)
        out.append(a)
        y -= a
    return tuple(out)


def circle_distance(x: Fraction) -> Fraction:
    f = x - floor_fraction(x)
    return min(f, 1 - f)


def sample_length(n: int) -> int:
    return 10 ** (n // 2)


def component_start(n: int, k: int) -> int:
    return 4 * n + 5 * n * k


def component_count(n: int) -> int:
    return (sample_length(n) - 4 * n) // (5 * n)


def selected_events(n: int, k: int) -> list[tuple[int, int]]:
    a0 = component_start(n, k)
    return [
        (j, r)
        for r in range(1, n)
        for j in range(a0, a0 + 3 * n - r + 1)
    ]


def interval(event: tuple[int, int], n: int) -> tuple[int, int]:
    j, r = event
    return j, j + n + r


def overlaps(x: tuple[int, int], y: tuple[int, int]) -> bool:
    return max(x[0], y[0]) < min(x[1], y[1])


def connected_components(events: list[tuple[int, int]], n: int) -> list[list[int]]:
    intervals = [interval(v, n) for v in events]
    unseen = set(range(len(events)))
    components: list[list[int]] = []
    while unseen:
        root = unseen.pop()
        stack = [root]
        comp = [root]
        while stack:
            i = stack.pop()
            adjacent = [j for j in unseen if overlaps(intervals[i], intervals[j])]
            for j in adjacent:
                unseen.remove(j)
                stack.append(j)
                comp.append(j)
        components.append(comp)
    return components


def has_period(word: tuple[int, ...], p: int) -> bool:
    return p > 0 and all(word[i] == word[i - p] for i in range(p, len(word)))


def check_fine_wilf_small() -> int:
    checks = 0
    for p in range(1, 6):
        for q in range(1, 6):
            g = math.gcd(p, q)
            m = p + q - g
            for word in itertools.product(range(2), repeat=m):
                if has_period(word, p) and has_period(word, q):
                    require(has_period(word, g), "finite Fine-Wilf check failed")
                checks += 1
    return checks


def check_merge_propagation_small() -> int:
    checks = 0
    for p in range(1, 5):
        for q in range(1, 5):
            g = math.gcd(p, q)
            overlap = p + q - g
            for left_length in range(overlap, overlap + 3):
                for right_length in range(overlap, overlap + 3):
                    right_start = left_length - overlap
                    union_length = max(left_length, right_start + right_length)
                    for word in itertools.product(range(2), repeat=union_length):
                        left_periodic = has_period(word[:left_length], p)
                        right_periodic = has_period(
                            word[right_start : right_start + right_length], q
                        )
                        if left_periodic and right_periodic:
                            require(has_period(word, g), "Fine-Wilf merge check failed")
                        checks += 1
    return checks


def verify_scale(n: int, exact_metric: bool) -> dict[str, int]:
    require(n >= 6, "counterfamily audit starts at n=6")
    length = sample_length(n)
    count = component_count(n)
    require(2 * 4 * n <= length, "4n must be at most L_n/2")
    require(20 * n * count >= length, "K_n lower bound failed")

    per_component = (n - 1) * (5 * n + 2) // 2
    ordered = count * (n - 1) * (5 * n + 2)
    require(8 * ordered >= n * length, "ordered incidence lower bound failed")

    first_events = selected_events(n, 0)
    require(len(first_events) == per_component, "per-component count failed")
    for j, r in first_events:
        left, right = interval((j, r), n)
        a0 = component_start(n, 0)
        require(1 <= r < n and r < length, "short-lag range failed")
        require(0 <= j < length - r, "triangular start range failed")
        require(a0 <= left < right <= a0 + 4 * n, "component endpoint failed")
        require(block(n, j, n) == block(n, j + r, n), "block equality failed")
        require(has_period(block(n, j, n + r), r), "induced period failed")
        require(n + r <= j + 2 * r + 1, "individual T36 inequality failed")
        q = 10**j * (10**r - 1)
        require(q > 10**n, "residual-mask denominator inequality failed")

    components = connected_components(first_events, n)
    require(len(components) == 1, "first selected component is disconnected")
    support_left = min(interval(first_events[i], n)[0] for i in components[0])
    support_right = max(interval(first_events[i], n)[1] for i in components[0])
    require(
        (support_left, support_right)
        == (component_start(n, 0), component_start(n, 0) + 4 * n),
        "first component support is not the full zero run",
    )
    require(4 * n <= support_left + 2 + 1, "maximal T36 inequality failed")

    # The last full component audits the opposite endpoint. All intervening
    # components are translates by 5n and obey the same affine inequalities.
    last_k = count - 1
    require(last_k >= 0, "there must be at least one full component")
    last_start = component_start(n, last_k)
    require(last_start + 4 * n <= length, "last component exceeds L_n")
    for r in range(1, n):
        last_j = last_start + 3 * n - r
        require(last_j < length - r, "last selected T56 start is out of range")
        require(last_j + n + r == last_start + 4 * n, "last endpoint formula failed")

    if exact_metric:
        x = seed(n)
        require(
            decimal_digits(x, 14 * n) == tuple(digit(n, i) for i in range(14 * n)),
            "rational seed digit formula failed",
        )
        radius = pow10neg(n)
        for j, r in first_events:
            q = 10**j * (10**r - 1)
            require(circle_distance(q * x) < radius, "strict near return failed")
            # For mu=2 and c=1, ArithmeticExcluded's second conjunct is false.
            require(Fraction(1, q) < radius, "residual-mask strict inequality failed")

    return {
        "n": n,
        "L_n": length,
        "K_n": count,
        "upper_events_per_component": per_component,
        "selected_ordered_incidence_count": ordered,
        "eight_I_minus_nL": 8 * ordered - n * length,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--write", type=Path)
    args = parser.parse_args()

    canonical = Path(__file__).with_name("pi-positive-decimal-factor-entropy.txt")
    canonical_hash = hashlib.sha256(canonical.read_bytes()).hexdigest()
    require(canonical_hash == CANONICAL_SHA256, "canonical statement hash mismatch")

    exact_scales = [verify_scale(n, exact_metric=True) for n in range(6, 11)]
    symbolic_scales = [verify_scale(n, exact_metric=False) for n in range(11, 41)]

    constant_witnesses = []
    for c in range(1, 21):
        n = max(6, 8 * c + 1)
        length = sample_length(n)
        ordered = component_count(n) * (n - 1) * (5 * n + 2)
        require(ordered > c * length, "constant witness failed")
        constant_witnesses.append(
            {"constant": c, "n": n, "I_minus_C_L": ordered - c * length}
        )

    output = {
        "label": "experiment",
        "canonical_sha256": canonical_hash,
        "construction": "2^n 3^n 4^n 6^n (0^(4n) 5^n)^infinity",
        "mu": 2,
        "c": 1,
        "fine_wilf_binary_checks": check_fine_wilf_small(),
        "fine_wilf_merge_binary_checks": check_merge_propagation_small(),
        "exact_fraction_scales": exact_scales,
        "symbolic_formula_scales": symbolic_scales,
        "constant_witnesses": constant_witnesses,
        "nonclaim": "Moving rational seeds do not satisfy effective irrationality and say nothing unconditional about pi, C7, C2, or C1.",
    }
    text = json.dumps(output, indent=2, sort_keys=True) + "\n"
    if args.write:
        args.write.write_text(text, encoding="ascii")
    else:
        print(text, end="")


if __name__ == "__main__":
    main()
