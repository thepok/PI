#!/usr/bin/env python3
"""Independent small-prefix oracle using explicit ordered-pair counts."""

from __future__ import annotations

import argparse
import hashlib
import json
from collections import Counter
from fractions import Fraction
from pathlib import Path


def iid(length: int, seed: bytes) -> str:
    result = ""
    counter = 0
    while len(result) < length:
        digest = hashlib.sha256(seed + counter.to_bytes(8, "big")).digest()
        counter += 1
        result += "".join(str(byte % 10) for byte in digest if byte < 250)
    return result[:length]


def champernowne(length: int) -> str:
    result = ""
    integer = 1
    while len(result) < length:
        result += str(integer)
        integer += 1
    return result[:length]


def rational(pair) -> Fraction:
    return Fraction(pair[0], pair[1])


def ordered_pair_energy(digits: str, cutoff: int, width: int) -> int:
    total = 0
    for left in range(cutoff):
        left_factor = digits[left : left + width]
        for right in range(cutoff):
            if left_factor == digits[right : right + width]:
                total += 1
    return total


def independently_group(digits: str, cutoff: int, level: int):
    groups = {}
    for start in range(cutoff):
        word = "".join(digits[start + offset] for offset in range(level))
        digit = int(digits[start + level])
        key = tuple(ord(char) - 48 for char in word)
        groups.setdefault(key, Counter())[digit] += 1
    parents = []
    for counts in groups.values():
        vector = tuple(counts.get(digit, 0) for digit in range(10))
        parents.append((sum(vector), vector))
    return parents


def expected_cells(parents):
    boundaries = {Fraction(1, 10)}
    for total, counts in parents:
        second = sorted(counts, reverse=True)[1]
        threshold = Fraction(second, total)
        if 0 < threshold < Fraction(1, 10):
            boundaries.add(threshold)
    energy = sum(total * total for total, _ in parents)
    result = []
    lower = Fraction(0)
    for upper in sorted(boundaries):
        split_energy = 0
        dominant_energy = 0
        for total, counts in parents:
            second = sorted(counts, reverse=True)[1]
            maximum = max(counts)
            if second * upper.denominator >= upper.numerator * total:
                split_energy += total * total
            if maximum * upper.denominator >= (upper.denominator - 9 * upper.numerator) * total:
                dominant_energy += total * total
        result.append((lower, upper, split_energy, dominant_energy, Fraction(split_energy, energy)))
        lower = upper
    return result


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--config", type=Path, required=True)
    parser.add_argument("--pi-digits", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    config = json.loads(args.config.read_text(encoding="utf-8"))
    output = json.loads(args.output.read_text(encoding="utf-8"))
    raw_pi = args.pi_digits.read_bytes()
    assert hashlib.sha256(raw_pi).hexdigest() == config["pi_digits_sha256"]
    pi = raw_pi[:-1].decode("ascii")
    needed = max(config["naive_prefixes"]) + max(config["naive_depths"]) + 1
    controls = {
        "pi": pi,
        "seeded_iid": iid(needed, config["iid_seed_ascii"].encode("ascii")),
        "champernowne": champernowne(needed),
    }
    cases = 0
    for dataset in output["datasets"]:
        name = dataset["name"]
        digits = controls[name]
        row_map = {(row["cutoff"], row["level"]): row for row in dataset["rows"]}
        for cutoff in config["naive_prefixes"]:
            for level in config["naive_depths"]:
                row = row_map[(cutoff, level)]
                energy = ordered_pair_energy(digits, cutoff, level)
                child_energy = ordered_pair_energy(digits, cutoff, level + 1)
                parents = independently_group(digits, cutoff, level)
                successor_energy = sum(count * count for _, vector in parents for count in vector)
                assert row["energy"] == energy
                assert row["child_energy"] == child_energy == successor_energy
                expected = expected_cells(parents)
                assert len(row["pareto_cells"]) == len(expected)
                for stored, values in zip(row["pareto_cells"], expected):
                    lower, upper, split_energy, dominant_energy, cap = values
                    assert rational(stored["eta_lower_exclusive"]) == lower
                    assert rational(stored["eta_upper_inclusive"]) == upper
                    assert stored["split_energy"] == split_energy
                    assert stored["dominant_energy"] == dominant_energy
                    assert rational(stored["mu_cap"]) == cap
                cases += 1
    print(f"T20 independent naive check passed: {cases} dataset/prefix/level cases.")


if __name__ == "__main__":
    main()
