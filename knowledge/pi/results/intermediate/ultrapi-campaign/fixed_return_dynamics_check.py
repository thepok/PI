#!/usr/bin/env python3
"""Finite replay for fixed_return_dynamics_attack.md.

This script checks source pins, exact finite orbit/coset algebra, the elementary
Euler-lattice identities, and one bounded cylinder-overlap experiment.  Its
output is an `experiment`; it does not prove a statement about pi or an
infinite-dimensional measure.
"""

from __future__ import annotations

from collections import Counter
from fractions import Fraction
from hashlib import sha256
from itertools import product
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
REPORT = ROOT / "work/ultrapi-resume/fixed_return_dynamics_attack.md"

PINS = {
    "problems/local/pi-digits.txt":
        "2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825",
    "work/theory/pi-digits/library/t44/furstenberg-1967-disjointness.pdf":
        "cd07faa4521080272cf2c303ee4e3a41ee6a3ba9e6aea114604becaca0ba9358",
    "work/theory/pi-digits/library/t44/hochman-2022-host-equidistribution-v2.pdf":
        "2fa94bec2580725a6b2d3e83761af1510f86061a6090528350c44ea785087d0b",
    "work/theory/pi-digits/library/t44/rudolph-1990-times2-times3.pdf":
        "9016e14ea8a3125dbea8532c6f8b2230fb24a33fe5e8818db8bcf0f7a7b57c85",
    "work/theory/pi-lacunary-near-return-sparsity/library/t103/"
    "akl-1304.3587v2.pdf":
        "6d65ce118a10b38450fd0d38716a3624ec3a2dea56bb08c32771a88165b88ce3",
    "work/theory/pi-lacunary-near-return-sparsity/library/t103/"
    "downarowicz-kasjan-1502.02307.pdf":
        "11f3315b34ec2d84a59c849860c2a2a90903348160e7a4316788840f2713e540",
}


def file_sha(path: Path) -> str:
    return sha256(path.read_bytes()).hexdigest()


def document_integrity() -> dict[str, object]:
    raw = REPORT.read_bytes()
    forbidden_controls = tuple(
        byte for byte in raw
        if byte < 32 and byte not in (9, 10, 13)
    )
    assert forbidden_controls == ()

    report = raw.decode("utf-8")
    assert report.count("\\[") == report.count("\\]")
    assert report.count("```") % 2 == 0
    assert report.count("$") % 2 == 0
    for corrupted_fragment in (
        "=left(",
        "times-(a\\)",
        "times-(b\\)",
        "(x\\)",
        "(M\\)",
        "(mu\\)",
    ):
        assert corrupted_fragment not in report
    return {
        "utf8": True,
        "forbidden_control_count": len(forbidden_controls),
        "display_math_open": report.count("\\["),
        "display_math_close": report.count("\\]"),
        "fence_count": report.count("```"),
        "dollar_delimiter_count": report.count("$"),
    }


def orbit(generator: int, modulus: int) -> tuple[int, ...]:
    seen: list[int] = []
    x = 1
    while x not in seen:
        seen.append(x)
        x = generator * x % modulus
    assert x == 1
    return tuple(seen)


def finite_coset_model() -> dict[str, object]:
    """The exact mod-11 analogue of disjoint fixed slices with dense union."""
    modulus = 11
    base_orbit = set(orbit(10, modulus))
    assert base_orbit == {1, 10}

    cosets: list[tuple[int, ...]] = []
    for t in range(5):
        coset = tuple(sorted((pow(16, t, modulus) * h) % modulus
                             for h in base_orbit))
        cosets.append(coset)

    assert len(set(cosets)) == 5
    assert all(set(cosets[i]).isdisjoint(cosets[j])
               for i in range(5) for j in range(i + 1, 5))
    assert set().union(*(set(c) for c in cosets)) == set(range(1, modulus))
    assert tuple(sorted((pow(16, 5, modulus) * h) % modulus
                        for h in base_orbit)) == cosets[0]
    return {
        "modulus": modulus,
        "times_ten_minimal_cycle": sorted(base_orbit),
        "times_sixteen_cosets": cosets,
        "coset_count": len(cosets),
        "union": list(range(1, modulus)),
        "repeat_depth": 5,
    }


def euler_lattice_checks() -> dict[str, object]:
    checked = []
    for n in range(1, 81):
        q = 10**n - 16
        assert q % 2 == 0
        assert q // 2 == 5 * 10 ** (n - 1) - 8
        checked.append(n)

    # dim(C_{0,...,8}) = log(9)/log(10) > 19/20, checked without floats.
    assert 9**20 > 10**19
    # The Rudolph exponent determinant for (10,16^r) is -4r.
    assert all(1 * 0 - 1 * (4 * r) == -4 * r != 0 for r in range(1, 81))
    # The equality-of-pushforwards step uses composition, never inversion.
    assert all(16 ** (t - s) * 16**s == 16**t
               for s in range(10) for t in range(s + 1, 11))
    return {
        "fixed_return_exponents_checked": [checked[0], checked[-1]],
        "identity": "(10^n-16)/2 = 5*10^(n-1)-8",
        "cantor_dimension_exact_test": "9^20 > 10^19",
        "cantor_dimension_lower_bound": "log(9)/log(10) > 19/20",
        "rudolph_determinants_checked": [1, 80],
        "pushforward_composition_checked": "0 <= s < t <= 10",
    }


def truncated_cylinder_experiment(length: int = 6, depth: int = 4) -> dict[str, object]:
    """Exact finite truncations of the 0..8 Bernoulli measure and its dilates."""
    modulus = 10**length
    divisor = 10 ** (length - depth)
    values: list[int] = []
    for digits in product(range(9), repeat=length):
        value = 0
        for digit in digits:
            value = 10 * value + digit
        values.append(value)

    distributions: list[Counter[int]] = []
    for t in range(4):
        multiplier = 16**t
        distributions.append(Counter(
            ((multiplier * value) % modulus) // divisor for value in values
        ))

    overlaps: dict[str, dict[str, object]] = {}
    denominator = len(values)
    for s in range(3):
        for t in range(s + 1, 4):
            keys = distributions[s].keys() | distributions[t].keys()
            numerator = sum(min(distributions[s].get(k, 0),
                                distributions[t].get(k, 0)) for k in keys)
            overlap = Fraction(numerator, denominator)
            overlaps[f"{s},{t}"] = {
                "numerator": overlap.numerator,
                "denominator": overlap.denominator,
                "decimal": float(overlap),
            }

    assert overlaps["0,1"]["numerator"] == 12881
    assert overlaps["0,1"]["denominator"] == 19683
    return {
        "claim_label": "experiment",
        "digit_alphabet": list(range(9)),
        "truncation_length": length,
        "cylinder_depth": depth,
        "sample_count": denominator,
        "common_mass": overlaps,
        "warning": "finite truncation overlap is not infinite-measure affinity",
    }


def main() -> None:
    pins = {}
    for relative, expected in PINS.items():
        actual = file_sha(ROOT / relative)
        assert actual == expected, (relative, expected, actual)
        pins[relative] = actual

    result = {
        "status": "PASS",
        "claim_label": "experiment",
        "document_integrity": document_integrity(),
        "source_pins": pins,
        "finite_coset_model": finite_coset_model(),
        "exact_algebra": euler_lattice_checks(),
        "truncated_cylinder_experiment": truncated_cylinder_experiment(),
        "asserts_v1": False,
        "asserts_fixed_return": False,
    }
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
