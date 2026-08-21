#!/usr/bin/env python3
"""Independent finite replay for the fixed-return dynamics audit.

Every output has claim status ``experiment``.  The script pins the frozen
report, its replay, and all primary PDFs; extracts a few theorem markers without
importing the branch checker; and checks exact finite shadows of the coding,
determinant, pushforward, dimension inequality, and mod-11 separator.  It does
not prove any infinite dynamics theorem or any statement about pi.
"""

from __future__ import annotations

from fractions import Fraction
from hashlib import sha256
from itertools import product
import json
from pathlib import Path
import subprocess
import tempfile


ROOT = Path(__file__).resolve().parents[2]

PINS = {
    "problems/local/pi-digits.txt":
        "2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825",
    "work/ultrapi-resume/fixed_return_dynamics_attack.md":
        "147969553dbb57d9678b9351953d2142f3d4984af4ff5ffa752362a6dd7839e7",
    "work/ultrapi-resume/fixed_return_dynamics_check.py":
        "3111a947706ef7a8ba280b8d27d98ef5c6f9ef34bd6e6dd6bc55c54c32b30d52",
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


def digest(path: Path) -> str:
    return sha256(path.read_bytes()).hexdigest()


def pdf_text(relative: str) -> str:
    with tempfile.TemporaryDirectory(prefix="fixed-return-audit-") as tmp:
        target = Path(tmp) / "source.txt"
        subprocess.run(
            ["pdftotext", "-layout", str(ROOT / relative), str(target)],
            check=True,
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
        )
        return " ".join(target.read_text(errors="replace").split())


def source_markers() -> dict[str, bool]:
    furstenberg = pdf_text(
        "work/theory/pi-digits/library/t44/furstenberg-1967-disjointness.pdf"
    )
    hochman = pdf_text(
        "work/theory/pi-digits/library/t44/"
        "hochman-2022-host-equidistribution-v2.pdf"
    )
    rudolph = pdf_text(
        "work/theory/pi-digits/library/t44/rudolph-1990-times2-times3.pdf"
    )
    akl = pdf_text(
        "work/theory/pi-lacunary-near-return-sparsity/library/t103/"
        "akl-1304.3587v2.pdf"
    )
    downarowicz = pdf_text(
        "work/theory/pi-lacunary-near-return-sparsity/library/t103/"
        "downarowicz-kasjan-1502.02307.pdf"
    )

    checks = {
        "furstenberg_definition_iv1": "Definition IV.1" in furstenberg,
        "furstenberg_theorem_iv1": "T H E O R E M IV. 1" in furstenberg,
        "hochman_theorem_1_1": "Theorem 1.1" in hochman
            and "multiplicatively independent" in hochman,
        "rudolph_corollary_4_11": "COROLLARY 4.11" in rudolph
            and "cofinite subgroup" in rudolph,
        "akl_toeplitz_conclusion": "z is a Toeplitz sequence" in akl,
        "downarowicz_entropy_section":
            "Entropy of the Example 6.3" in downarowicz
            and "positive topological entropy" in downarowicz,
    }
    assert all(checks.values()), checks
    return checks


def exact_algebra() -> dict[str, object]:
    assert 9**20 > 10**19

    determinants = []
    for r in range(1, 257):
        determinant = 1 * 0 - 1 * (4 * r)
        assert determinant == -4 * r != 0
        determinants.append(determinant)

    composition_checks = 0
    for s in range(17):
        for t in range(s + 1, 18):
            assert 16 ** (t - s) * 16**s == 16**t
            composition_checks += 1

    # Exact first-difference lower bounds used by the two decimal codings.
    finite_tail = sum(Fraction(1, 10**offset) for offset in range(1, 40))
    assert 1 - 2 * finite_tail > Fraction(7, 9)
    assert 1 - 8 * finite_tail > Fraction(1, 9)

    # Finite injectivity shadows, using integer numerators at a common depth.
    for alphabet_size, depth in ((3, 8), (9, 5)):
        values = set()
        for digits in product(range(alphabet_size), repeat=depth):
            numerator = 0
            for digit in digits:
                numerator = 10 * numerator + digit
            assert numerator not in values
            values.add(numerator)
        assert len(values) == alphabet_size**depth

    return {
        "claim_label": "experiment",
        "dimension_inequality": "9^20 > 10^19",
        "rudolph_r_range": [1, 256],
        "rudolph_first_last_determinants": [determinants[0], determinants[-1]],
        "pushforward_composition_checks": composition_checks,
        "finite_coding_depths": {"digits_0_2": 8, "digits_0_8": 5},
    }


def finite_cosets() -> dict[str, object]:
    base = {1, 10}
    cosets = [
        tuple(sorted(pow(16, t, 11) * value % 11 for value in base))
        for t in range(5)
    ]
    expected = [(1, 10), (5, 6), (3, 8), (4, 7), (2, 9)]
    assert cosets == expected
    assert all(
        set(cosets[i]).isdisjoint(cosets[j])
        for i in range(5)
        for j in range(i + 1, 5)
    )
    assert set().union(*(set(coset) for coset in cosets)) == set(range(1, 11))
    return {"claim_label": "experiment", "modulus": 11, "cosets": cosets}


def main() -> None:
    actual_pins = {}
    for relative, expected in PINS.items():
        actual = digest(ROOT / relative)
        assert actual == expected, (relative, expected, actual)
        actual_pins[relative] = actual

    report = (ROOT / "work/ultrapi-resume/fixed_return_dynamics_attack.md").read_text()
    assert "Canonical V1 remains a `conjecture`." in report
    assert "No proof of the fixed return" in report
    assert "machine-checked` claims: none" in report

    result = {
        "status": "PASS",
        "claim_label": "experiment",
        "source_pins": actual_pins,
        "source_markers": source_markers(),
        "exact_algebra": exact_algebra(),
        "finite_coset_model": finite_cosets(),
        "asserts_v1": False,
        "asserts_fixed_return": False,
    }
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
