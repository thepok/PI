#!/usr/bin/env python3
"""Exact finite checks for the fixed Salikhov binary exception sieve.

The unbounded shell and counting statements are proved in the companion
note. This audit checks their arithmetic inputs using integer operations;
it does not import an unmerged multiplier evaluator or infer an infinite
statement from sampled values.
"""

from __future__ import annotations

import argparse
from fractions import Fraction
import json
from math import comb
from pathlib import Path


def v2(n: int) -> int:
    assert n != 0
    n = abs(n)
    return (n & -n).bit_length() - 1


def factorial_v2(n: int) -> int:
    """Legendre's formula, evaluated by successive divisions."""
    assert n >= 0
    out = 0
    while n:
        n //= 2
        out += n
    return out


def binomial_v2(n: int, k: int) -> int:
    assert 0 <= k <= n
    return factorial_v2(n) - factorial_v2(k) - factorial_v2(n - k)


def rational_v2(value: Fraction) -> int:
    assert value != 0
    return v2(value.numerator) - v2(value.denominator)


def power_of_two(exponent: int) -> Fraction:
    return Fraction(1 << exponent) if exponent >= 0 else Fraction(1, 1 << -exponent)


def truncated_power(base: list[int], exponent: int, degree: int) -> list[int]:
    """Direct polynomial multiplication, truncated only past the wanted degree."""
    out = [1]
    for _ in range(exponent):
        following = [0] * min(len(out) + len(base) - 1, degree + 1)
        for i, a in enumerate(out):
            for j, b in enumerate(base[:len(following) - i]):
                following[i + j] += a * b
        out = following
    return out


def source_multiplier(n: int) -> Fraction:
    """Original partial-fraction coefficient at x=5, before root coordinates."""
    degree = 3 * n
    # (w-1) * (32-112w+156w^2-100w^3+25w^4).
    numerator = truncated_power([-32, 144, -268, 256, -125, 25], 2 * n, degree)
    coefficient = sum((
        Fraction(a * comb(6 * n - r, 3 * n - r), 1 << (6 * n + 1 - r))
        for r, a in enumerate(numerator)
    ), Fraction(0))
    return (-1)**n * power_of_two(1 - 5 * n // 2) * coefficient


def root_coordinate_multiplier(n: int) -> Fraction:
    """Literal coefficient in (4a), using rational binomial-series arithmetic."""
    degree = 3 * n
    polynomial = truncated_power([32, 56, 25], 2 * n, degree)
    binomial = Fraction(1)
    coefficient = Fraction(0)
    for h in range(degree + 1):
        if degree - h < len(polynomial):
            coefficient += polynomial[degree - h] * binomial
        binomial *= Fraction(2 * n - 1 - 2 * h, 2 * (h + 1))
    return power_of_two(-(5 * n // 2)) * coefficient


def inner(r: int, k: int, t: int) -> Fraction:
    """Literal T_{R,k}(t), valid also at t=0 and n=-R."""
    n, s, maximum_h = 2 * t - r, t + k, 2 * k + r
    assert s >= 0 and maximum_h >= 0
    units = [Fraction(1)]
    for h in range(1, maximum_h + 1):
        units.append(units[-1] * Fraction(2 * n + 1 - 2 * h, h >> v2(h)))
        assert rational_v2(units[-1]) == 0
    return sum((
        Fraction(comb(s, b) * 7**b * (1 << (k + (r + 1) // 2 + (maximum_h - b).bit_count())))
        * units[maximum_h - b]
        for b in range(min(s, maximum_h) + 1)
    ), Fraction(0))


def short_shell_checks() -> dict[str, object]:
    """Exact inner coefficients, substitution margins, and consecutive low shells."""
    expected = {(1, 0): -12, (2, 0): 140, (3, 0): -3696,
                (3, 1): 48048, (3, 2): -247104}
    identities = []
    for (r, k), value in expected.items():
        actual = inner(r, k, 0)
        assert actual == value
        margin = 5 - ((2 * k + r).bit_length() - 1) + k + (r + 1) // 2
        assert margin > rational_v2(actual)
        identities.append({"R": r, "k": k, "inner_at_zero": value,
                           "valuation": rational_v2(actual), "substitution_margin": margin})

    representatives = [31, 95, (1 << 40) - 33, (1 << 80) - 33,
                       (1 << 160) - 33, (1 << 1049) - 33]
    substitution_checks = short_outer_checks = short_shell_comparisons = 0
    for m in representatives:
        t, w = 32 * m, (3 * m).bit_count()
        assert m > 0 and m % 64 == 31
        for (r, k), value in expected.items():
            difference = inner(r, k, t) - value
            margin = 5 - ((2 * k + r).bit_length() - 1) + k + (r + 1) // 2
            assert difference == 0 or rational_v2(difference) >= margin
            substitution_checks += 1
        for r in (1, 2, 3):
            leader = w + (2 if r == 3 else 0)
            for k in range(-(r // 2), 5):
                outer = binomial_v2(4 * t - 2 * r, t + k)
                if k >= 0:
                    assert outer - w == -2 + binomial_v2(2 * r + k - 1, k)
                    short_outer_checks += 1
                else:
                    assert outer == w + 3
                actual_inner = inner(r, k, t)
                if k == 0:
                    assert actual_inner != 0 and outer + rational_v2(actual_inner) == leader
                else:
                    assert actual_inner == 0 or outer + rational_v2(actual_inner) > leader
                short_shell_comparisons += 1
            n = 2 * t - r
            h = n.bit_length() - 1
            assert w <= h - 3 and leader <= h

    small_multipliers = []
    for n in range(13):
        original = source_multiplier(n)
        transformed = root_coordinate_multiplier(n)
        assert original == transformed and original.denominator == 1
        small_multipliers.append({"n": n, "q_n": original.numerator})
    assert small_multipliers[0]["q_n"] == 1
    assert small_multipliers[1]["q_n"] == 1196
    return {"five_exact_inner_identities": identities,
            "substitution_comparisons": substitution_checks,
            "short_outer_binomial_equalities": short_outer_checks,
            "short_shell_comparisons": short_shell_comparisons,
            "largest_short_shell_m_bit_length": max(m.bit_length() for m in representatives),
            "independent_coordinate_multiplier_comparisons": small_multipliers}


def interval_max_v2(t: int, k: int) -> int:
    """Maximum v2 on the nonempty interval (t,t+k], by binary search."""
    assert t >= 0 and k > 0
    low, high = 0, (t + k).bit_length()
    while low + 1 < high:
        middle = (low + high) // 2
        if (t >> middle) < ((t + k) >> middle):
            low = middle
        else:
            high = middle
    return low


def possible_a(y: int) -> range:
    """All classes that can meet [1,y], using the proved 2y bound."""
    assert y >= 1
    cap = ((2 * y).bit_length() - 1 + 7) // 32
    return range(33, cap + 1, 64)


def exceptional_a(m: int) -> list[int]:
    assert m > 0
    return [a for a in possible_a(m) if (m + a) % (1 << (32 * a - 7)) == 0]


def progression_class_count(residue: int, modulus: int, length: int) -> int:
    """Count u in [0,length) with u == residue modulo modulus."""
    assert 0 <= residue < modulus and length >= 0
    if residue >= length:
        return 0
    return 1 + (length - 1 - residue) // modulus


def run() -> dict[str, object]:
    short_shells = short_shell_checks()
    counts = {
        "interval_max_direct_comparisons": 0,
        "anchor_binomial_equalities": 0,
        "outer_interval_valuation_bounds": 0,
        "tail_inequality_checks": 0,
        "failing_tail_to_exception_checks": 0,
        "explicit_exception_witnesses": 0,
        "local_congruence_comparisons": 0,
        "local_class_count_comparisons": 0,
        "local_union_bound_checks": 0,
    }

    for t in range(1, 81):
        for k in range(1, 81):
            assert interval_max_v2(t, k) == max(v2(t + i) for i in range(1, k + 1))
            counts["interval_max_direct_comparisons"] += 1

    ordinary_m = [31 + 64 * h for h in range(24)]
    large_good_m = [
        (1 << e) - 33 + 64 * u
        for e in (160, 1049, 3097)
        for u in (1, 2, 7)
    ]
    large_exception_m = [
        (1 << (32 * a - 7)) * multiple - a
        for a in (33, 97, 161)
        for multiple in (1, 2, 3)
    ]
    all_m = ordinary_m + large_good_m + large_exception_m

    outer_k = sorted(set(range(5, 105)) | {127, 128, 129, 255, 511, 1055, 1056, 1057, 3104, 5152})
    for m in all_m:
        assert m > 0 and m % 64 == 31
        t = 32 * m
        w = (3 * m).bit_count()
        assert binomial_v2(4 * t, t) == w
        counts["anchor_binomial_equalities"] += 1
        for r in (1, 2, 3):
            assert binomial_v2(4 * t - 2 * r, t) == w - 2
            counts["anchor_binomial_equalities"] += 1
            for k in outer_k:
                if k > 3 * t - 2 * r:
                    continue
                observed = binomial_v2(4 * t - 2 * r, t + k)
                assert observed >= w - 2 - interval_max_v2(t, k)
                counts["outer_interval_valuation_bounds"] += 1

        for k in range(98, min(3 * t - 6, 5400) + 1):
            maximum = interval_max_v2(t, k)
            counts["tail_inequality_checks"] += 1
            if maximum <= k - 3:
                continue
            i = (((t >> maximum) + 1) << maximum) - t
            assert 1 <= i <= k and i % 32 == 0
            a = i // 32
            assert a >= 33 and a % 64 == 33
            assert v2(m + a) >= 32 * a - 7
            assert a in exceptional_a(m)
            counts["failing_tail_to_exception_checks"] += 1

    for m in ordinary_m + large_good_m:
        assert not exceptional_a(m)
    for a in (33, 97, 161):
        exponent = 32 * a - 7
        assert exponent >= 1049 and (exponent - 1049) % 2048 == 0
        for multiple in (1, 2, 3):
            m = multiple * (1 << exponent) - a
            assert a in exceptional_a(m)
            assert interval_max_v2(32 * m, 32 * a) >= 32 * a - 2
            counts["explicit_exception_witnesses"] += 1

    delta = Fraction(1, 1 << 1043) / (1 - Fraction(1, 1 << 2048))
    assert delta < Fraction(1, 1 << 1042)
    raw_delta = Fraction(1, 1 << 1049) / (1 - Fraction(1, 1 << 2048))
    assert delta == 64 * raw_delta
    partial = sum((Fraction(1, 1 << (32 * a - 13)) for a in (33, 97, 161)), Fraction(0))
    assert partial < delta

    local_lengths = (1, 17, 80, 257)
    for chosen_a in (33, 97, 161):
        for position in (0, 11, 35):
            witness = (1 << (32 * chosen_a - 7)) - chosen_a
            m0 = witness - 8000 * position
            assert m0 > 0 and m0 % 64 == 31
            for length in local_lengths:
                y = m0 + 8000 * (length - 1)
                direct_union = set()
                sum_class_counts = 0
                for a in possible_a(y):
                    exponent = 32 * a - 7
                    modulus = 1 << (exponent - 6)
                    residue = (-(m0 + a) // 64 * pow(125, -1, modulus)) % modulus
                    direct = []
                    for u in range(length):
                        original = (m0 + 8000 * u + a) % (1 << exponent) == 0
                        reduced = u % modulus == residue
                        assert original == reduced
                        counts["local_congruence_comparisons"] += 1
                        if original:
                            direct.append(u)
                            direct_union.add(u)
                    class_count = progression_class_count(residue, modulus, length)
                    assert class_count == len(direct)
                    assert Fraction(class_count) <= Fraction(length, modulus) + 1
                    sum_class_counts += class_count
                    counts["local_class_count_comparisons"] += 1
                j_y = 1 + (2 * y).bit_length() - 1
                assert len(direct_union) <= sum_class_counts
                assert Fraction(len(direct_union)) <= delta * length + j_y
                counts["local_union_bound_checks"] += 1

    assert counts["failing_tail_to_exception_checks"] > 0
    return {
        "status": "passed",
        "scope": "finite exact arithmetic checks; unbounded proof is in the companion note",
        "fixed_j": 5,
        "binary_base_modulus": 4096,
        "binary_base_residue": 1981,
        "low_progression_m_step": 8000,
        "first_exception_modulus_exponent": 1049,
        "conditional_first_modulus_exponent": 1043,
        "successive_exponent_gap": 2048,
        "conditional_density_upper_bound": "2^(-1042)",
        "largest_sample_m_bit_length": max(m.bit_length() for m in all_m),
        "short_shells": short_shells,
        "counts": counts,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json", type=Path, help="write a deterministic JSON certificate")
    args = parser.parse_args()
    result = run()
    payload = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.json is not None:
        args.json.parent.mkdir(parents=True, exist_ok=True)
        args.json.write_text(payload, encoding="utf-8")
    print(payload, end="")


if __name__ == "__main__":
    main()
