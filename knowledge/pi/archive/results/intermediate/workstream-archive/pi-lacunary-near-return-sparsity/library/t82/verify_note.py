#!/usr/bin/env python3
"""Self-contained exact-arithmetic replay for the T82 proof-sketch note."""

from __future__ import annotations

import hashlib
import json
import math
import subprocess
import sys
import tempfile
from fractions import Fraction
from pathlib import Path


if hasattr(sys, "set_int_max_str_digits"):
    sys.set_int_max_str_digits(0)

ROOT = Path(__file__).resolve().parent

EXPECTED = {
    "canonical_statement.txt": "cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8",
    "milla-1809.00533v6.pdf": "69e9513d3c03c7c5c5dce12b24187b2522e0f1b08d54266a15eef93a3421cd20",
    "milla-1809.00533v6.txt": "edf60a42b2e1c7dc56f3f5fd5175f381860d944d38a5ee131d0815e838ce5a83",
    "t17_certify_pi.py": "5ef0ca84488829bcdcc89c2f49dc283bba4867bce38f813af09de80dd18c5f2a",
    "t17_interval_endpoints.hex": "30e7186d43de56ceba645ef7170fed40ddc22bd50f6eb2bf6a39b1fcb170a0f9",
    "T64AggregateFejerCriterion.lean": "ce4dac5fbb5ab1e7dd539e8dcc81a2c58351d4078e8e30ca774e30fea612ab16",
    "T14CoherentSuccessorSplitting.lean": "bbc5c0323aaa0213e1d86dd4ec711e5f1a9d5421c7d946c88c56ee0f017bf833",
    "chudnovsky-crossref.json": "67f5af4ad7c4c5377c72762947d3e13a276605715b18c34a9ee3493a9ab089c2",
    "chudnovsky-primary-formula.json": "65b756cdb5019e09a6b2ade96668a03c9655553e52c123995e95e9e0ceac937b",
    "chudnovsky-primary-derivation.json": "11c5349c04a1dd142d81505631a334eec90b6dbf3dbe5d831228c2bed5a84729",
}

A = 13_591_409
B = 545_140_134
C = 640_320
C3_OVER_24 = C**3 // 24


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def leaf(k: int) -> tuple[int, int, int]:
    if k == 0:
        return 1, 1, A
    p = (6 * k - 5) * (2 * k - 1) * (6 * k - 1)
    q = k**3 * C3_OVER_24
    t = p * (A + B * k)
    if k % 2:
        t = -t
    return p, q, t


def split(a: int, b: int) -> tuple[int, int, int]:
    if b - a == 1:
        return leaf(a)
    m = (a + b) // 2
    p1, q1, t1 = split(a, m)
    p2, q2, t2 = split(m, b)
    return p1 * p2, q1 * q2, t1 * q2 + p1 * t2


def global_term(k: int) -> Fraction:
    return Fraction(
        (-1) ** k * math.factorial(6 * k) * (A + B * k),
        math.factorial(3 * k) * math.factorial(k) ** 3 * C ** (3 * k),
    )


def parse_endpoints() -> dict[str, int | str]:
    values: dict[str, int | str] = {}
    for line in (ROOT / "t17_interval_endpoints.hex").read_text().splitlines():
        key, value = line.split("=", 1)
        if key in {"format"}:
            values[key] = value
        elif key == "scale_power":
            values[key] = int(value)
        else:
            values[key] = int(value, 16)
    return values


def floor_fraction(num: int, den: int) -> int:
    assert num >= 0 and den > 0
    return num // den


def main() -> None:
    for name, expected in EXPECTED.items():
        actual = digest(ROOT / name)
        assert actual == expected, (name, expected, actual)

    source_text = (ROOT / "milla-1809.00533v6.txt").read_text(errors="strict")
    assert "Theorem 10.12" in source_text
    assert "13591409" in source_text
    assert "545140134" in source_text
    assert "640320" in source_text

    t64 = (ROOT / "T64AggregateFejerCriterion.lean").read_text()
    for anchor in (
        "def rowFourierRemainder",
        "40 * (10 ^ ell) ^ 3",
        "8000 * (10 ^ ell) ^ 3",
        "boundary_and_fourier_imply_literal_t14_row",
        "3281 / 7281",
        "1 / 100",
    ):
        assert anchor in t64

    t14 = (ROOT / "T14CoherentSuccessorSplitting.lean").read_text()
    for anchor in (
        "def PiCoherentPositiveDensitySplittingAt",
        "StrictMono N",
        "piSplittingLevelCount m (N k) mu eta",
        "piCoherentPositiveDensitySplittingAt_iff_quantifiers",
    ):
        assert anchor in t14

    # The root binary split equals the literal Chudnovsky partial sum. These
    # bounded checks are sanity checks; REPORT.md gives the all-N algebra.
    for n in range(1, 13):
        _, q, t = split(0, n)
        direct = sum((global_term(k) for k in range(n)), Fraction(0))
        assert Fraction(t, q) == direct

    # Re-run the full retained T17 computation and byte-compare the actual
    # million-digit endpoint output. This connects the pinned endpoints to the
    # stated 74,919-term recurrence rather than merely checking their shape.
    with tempfile.TemporaryDirectory(prefix="t82-t17-") as temp_dir:
        subprocess.run(
            [sys.executable, str(ROOT / "t17_certify_pi.py"), temp_dir],
            check=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
        )
        regenerated = Path(temp_dir)
        assert (regenerated / "interval_endpoints.hex").read_bytes() == (
            ROOT / "t17_interval_endpoints.hex"
        ).read_bytes()
        assert digest(regenerated / "pi_digits.txt") == (
            "77eeccb0067283e14c460b33dc230de54ef15c2e825fc2a35c984fb6984bf684"
        )
        certificate = json.loads((regenerated / "certificate.json").read_text())
        assert certificate["series_terms"] == 74_919
        assert certificate["series_terms_adjacent"] == 74_920

    values = parse_endpoints()
    assert values["format"] == "t17-rational-interval-v1"
    d = int(values["scale_power"])
    ln = int(values["lower_numerator"])
    ld = int(values["lower_denominator"])
    un = int(values["upper_numerator"])
    ud = int(values["upper_denominator"])

    # These are endpoints for pi*10^D. They are strictly ordered and both lie
    # in the same open unit interval (K,K+1), a stronger check than merely
    # forcing the integer between them.
    k = floor_fraction(ln, ld)
    assert ln * ud < un * ld
    assert k * ld < ln < (k + 1) * ld
    assert k * ud < un < (k + 1) * ud
    assert k == (un - 1) // ud
    width_num = un * ld - ln * ud
    width_den = ld * ud
    assert 0 < width_num < width_den

    # At orbit index j=D-r, the exact endpoint separation is
    # width/10^r. Check the factor-ten denominator update and half-circle
    # safety by cross products. The proof in REPORT.md derives the actual
    # carry representatives for every 0 <= j <= D-2 from (K,K+1).
    for r in range(2, 34):
        ten_r = 10**r
        current_den = width_den * ten_r
        next_den = width_den * (ten_r // 10)
        assert current_den == 10 * next_den
        assert 2 * width_num < next_den

    result = {
        "label": "exact replay and finite sanity checks; not proof of T64, T14, C1, or C2",
        "source_hashes": "PASS",
        "full_t17_regeneration": {
            "series_terms": 74_919,
            "endpoint_byte_comparison": "PASS",
            "digit_file_sha256": "PASS",
        },
        "binary_split_root_checks": {"N_min": 1, "N_max": 12, "result": "PASS"},
        "scaled_endpoint_checks": {
            "D": d,
            "positive_width": True,
            "both_strictly_between_K_and_K_plus_1": True,
            "shared_certified_prefix": True,
        },
        "carry_checks": {
            "terminal_r_min": 2,
            "terminal_r_max": 33,
            "exact_circle_expansion_factor": 10,
            "result": "PASS",
        },
        "t14_t64_source_anchors": "PASS",
    }
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
