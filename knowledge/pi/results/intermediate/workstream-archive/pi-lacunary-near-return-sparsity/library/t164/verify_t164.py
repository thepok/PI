#!/usr/bin/env python3
"""Exact finite validation for T164; not a proof of any universal statement."""

from fractions import Fraction
import hashlib
import json
from pathlib import Path


EXPECTED_CANONICAL_SHA256 = (
    "cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8"
)


def image(word, substitution):
    return "".join(substitution[a] for a in word)


def iterate(word, substitution, count):
    for _ in range(count):
        word = image(word, substitution)
    return word


def prefix(substitution, seed, length):
    word = seed
    while len(word) < length:
        word = image(word, substitution)
    return word[:length]


def primitive_exponent(substitution):
    alphabet = set(substitution)
    words = dict(substitution)
    exponent = 1
    while not all(set(words[a]) == alphabet for a in alphabet):
        words = {a: image(words[a], substitution) for a in alphabet}
        exponent += 1
    return exponent


def exact_pair_language(substitution):
    pairs = {
        word[i : i + 2]
        for word in substitution.values()
        for i in range(len(word) - 1)
    }
    while True:
        enlarged = set(pairs)
        for pair in pairs:
            word = image(pair, substitution)
            enlarged.update(word[i : i + 2] for i in range(len(word) - 1))
        if enlarged == pairs:
            return sorted(pairs)
        pairs = enlarged


def all_pairs_level(substitution, pairs):
    words = {a: a for a in substitution}
    level = 0
    while not all(all(pair in words[a] for pair in pairs) for a in words):
        words = {a: image(words[a], substitution) for a in words}
        level += 1
    return level


def constants(substitution):
    e = primitive_exponent(substitution)
    lengths = {
        n: [len(iterate(a, substitution, n)) for a in substitution]
        for n in range(e + 1)
    }
    q_candidates = [max(lengths[e])]
    for n in range(e):
        maximum, minimum = max(lengths[n]), min(lengths[n])
        q_candidates.append((maximum + minimum - 1) // minimum)
    q = max(q_candidates)
    pairs = exact_pair_language(substitution)
    t = all_pairs_level(substitution, pairs)
    s_t = max(len(iterate(a, substitution, t)) for a in substitution)
    r = 2 * s_t
    s = max(len(word) for word in substitution.values())
    power_bound = 4 * r * s * q
    return {
        "primitive_exponent_e": e,
        "Q": q,
        "length_two_language": pairs,
        "all_pairs_level_t": t,
        "S_t": s_t,
        "r": r,
        "S": s,
        "N": power_bound,
        "c": f"1/{power_bound - 1}",
    }


def finite_statistics(substitution, seed, starts, max_m, check_m, power_bound):
    word = prefix(substitution, seed, starts + max(max_m, check_m) - 1)
    best = None
    best_witness = None
    for m in range(1, max_m + 1):
        previous = {}
        gap = None
        witness = None
        for i in range(starts):
            block = word[i : i + m]
            if block in previous:
                distance = i - previous[block]
                if gap is None or distance < gap:
                    gap = distance
                    witness = (previous[block], i, block)
            previous[block] = i
        if gap is not None:
            ratio = Fraction(gap, m)
            if best is None or ratio < best:
                best = ratio
                best_witness = (m, gap, *witness)

    counts = {}
    for i in range(starts):
        block = word[i : i + check_m]
        counts[block] = counts.get(block, 0) + 1
    maximum_occupancy = max(counts.values())
    energy = sum(count * count for count in counts.values())
    integer_gap = check_m // (power_bound - 1) + 1
    occupancy_bound = (starts - 1) // integer_gap + 1
    return {
        "starts_M": starts,
        "tested_m_range": [1, max_m],
        "minimum_observed_gap_ratio": f"{best.numerator}/{best.denominator}",
        "minimum_ratio_witness": {
            "m": best_witness[0],
            "distance": best_witness[1],
            "starts": [best_witness[2], best_witness[3]],
            "factor": best_witness[4],
        },
        "declared_collision_check": {
            "m": check_m,
            "distinct_factors": len(counts),
            "maximum_occupancy": maximum_occupancy,
            "ordered_diagonal_inclusive_energy": energy,
            "certified_integer_gap": integer_gap,
            "certified_maximum_occupancy_bound": occupancy_bound,
            "certified_energy_bound": starts * occupancy_bound,
        },
    }


def periodic_control(substitution, seed):
    proposed_c = Fraction(1, 10)
    m = 21
    starts = (0, 2)
    word = prefix(substitution, seed, starts[1] + m)
    left = word[starts[0] : starts[0] + m]
    right = word[starts[1] : starts[1] + m]
    assert left == right
    assert starts[1] - starts[0] < proposed_c * m
    return {
        "substitution": substitution,
        "named_fixed_point": "(01)^omega",
        "proposed_c": "1/10",
        "counterexample": {
            "m": m,
            "starts": list(starts),
            "distance": starts[1] - starts[0],
            "factor": left,
            "exact_inequality": "2 < (1/10)*21 = 21/10",
        },
    }


def main():
    canonical = Path("canonical_statement.txt")
    digest = hashlib.sha256(canonical.read_bytes()).hexdigest()
    assert digest == EXPECTED_CANONICAL_SHA256

    examples = {
        "Fibonacci": ({"0": "01", "1": "0"}, "0", 768),
        "Thue-Morse": ({"0": "01", "1": "10"}, "0", 512),
    }
    output = {
        "label": "experiment: exact finite validation only",
        "canonical_sha256": digest,
        "aperiodic_examples": {},
    }
    for name, (substitution, seed, check_m) in examples.items():
        data = constants(substitution)
        data["substitution"] = substitution
        data["named_fixed_point"] = f"sigma^omega({seed})"
        data["finite_validation"] = finite_statistics(
            substitution,
            seed,
            starts=4096,
            max_m=64,
            check_m=check_m,
            power_bound=data["N"],
        )
        output["aperiodic_examples"][name] = data

    output["periodic_control"] = periodic_control(
        {"0": "01", "1": "01"}, "0"
    )
    print(json.dumps(output, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
