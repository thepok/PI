#!/usr/bin/env python3
"""Independent source hygiene and finite arithmetic replay for T73.

The arithmetic replay is an ``experiment``.  Lean kernel compilation, not
this script, is the proof check.
"""

from __future__ import annotations

import hashlib
import json
import re
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
T73 = ROOT / "TheoryLib/PiQuantitativeBlockHitting/T73T73ThreePrimaryOrbit.lean"
AXIOM_AUDIT = ROOT / "audit/AxiomAudit.lean"
INDEPENDENT_LEAN = (
    ROOT / "work/ultrapi-resume/t73_three_primary_orbit_independent_checks.lean"
)
FROZEN_HASHES = {
    ROOT / "problems/local/pi-digits.txt":
        "2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825",
    T73:
        "1499b29893a05fe91d64ee468ff320f0f59c23eb07f13220dab64b9fbfe23009",
    AXIOM_AUDIT:
        "26b5c4bdb4d13e2caeca2885fff6b7e4284c366f511a40033202d943328af6fa",
    ROOT / "work/ultrapi-resume/bbp_three_primary_epoch_20260813.md":
        "5b34ceb3aa2857b9227cce5ac7ae84cafbbac47d2c12adf889c37f11280d6fd7",
    ROOT / "scripts/check.ps1":
        "953387f14651d68915361ca5baf1514ed1d22a434e1d2b1d4d417df62d3271b3",
    INDEPENDENT_LEAN:
        "da35143093d1f77fd7b63592b1a66aab40223e12cf43fa29b1c471aba95d2cb7",
}

NAMESPACE = "Theory.PiDigits.T73ThreePrimaryOrbit"
THEOREMS = (
    "tenUnit_coe",
    "orderOf_tenUnit",
    "tenUnit_pow_eq_iff",
    "tenUnit_pow_injective_on_period",
    "three_mul_residualTen",
    "residualTen_mod_three",
    "residualClass_injective_on_period",
    "residualClass_range_ncard",
    "residualClass_cast_three",
)
DEFINITIONS = ("tenUnit", "residualTen", "residualClass")


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def strip_lean_comments_and_strings(source: str) -> str:
    """Remove nested Lean comments, line comments, and string contents."""

    out: list[str] = []
    i = 0
    block_depth = 0
    in_string = False
    while i < len(source):
        pair = source[i:i + 2]
        char = source[i]
        if block_depth:
            if pair == "/-":
                block_depth += 1
                out.extend("  ")
                i += 2
            elif pair == "-/":
                block_depth -= 1
                out.extend("  ")
                i += 2
            else:
                out.append("\n" if char == "\n" else " ")
                i += 1
            continue
        if in_string:
            if char == "\\" and i + 1 < len(source):
                out.extend("  ")
                i += 2
            elif char == '"':
                in_string = False
                out.append(" ")
                i += 1
            else:
                out.append("\n" if char == "\n" else " ")
                i += 1
            continue
        if pair == "/-":
            block_depth = 1
            out.extend("  ")
            i += 2
        elif pair == "--":
            while i < len(source) and source[i] != "\n":
                out.append(" ")
                i += 1
        elif char == '"':
            in_string = True
            out.append(" ")
            i += 1
        else:
            out.append(char)
            i += 1
    assert block_depth == 0 and not in_string
    return "".join(out)


def residual_mod(e: int, n: int) -> int:
    """Compute ((10^n - 16) / 3) modulo 3^(e+1), without huge powers."""

    low_modulus = 3 ** (e + 1)
    representative = pow(10, n, 3 * low_modulus)
    assert (representative - 16) % 3 == 0
    return ((representative - 16) // 3) % low_modulus


def run() -> dict[str, object]:
    for path, expected in FROZEN_HASHES.items():
        assert sha256(path) == expected, path

    source = T73.read_text(encoding="utf-8")
    audit = AXIOM_AUDIT.read_text(encoding="utf-8")
    independent = INDEPENDENT_LEAN.read_text(encoding="utf-8")
    clean_source = strip_lean_comments_and_strings(source)
    clean_independent = strip_lean_comments_and_strings(independent)

    assert "Source: `problems/local/pi-digits.txt`" in source
    assert FROZEN_HASHES[ROOT / "problems/local/pi-digits.txt"] in source

    theorem_names = tuple(re.findall(
        r"(?m)^\s*(?:@\[[^\n]*\]\s*)?theorem\s+([A-Za-z0-9_']+)",
        clean_source,
    ))
    definition_names = tuple(re.findall(
        r"(?m)^\s*def\s+([A-Za-z0-9_']+)", clean_source
    ))
    assert set(theorem_names) == set(THEOREMS), theorem_names
    assert len(theorem_names) == len(THEOREMS)
    assert set(definition_names) == set(DEFINITIONS), definition_names
    assert len(definition_names) == len(DEFINITIONS)

    forbidden_patterns = (
        r"\b(?:sorry|admit|native_decide|sorryAx)\b",
        r"\b(?:Lean\.ofReduceBool|Lean\.trustCompiler)\b",
        r"(?m)^\s*(?:axiom|opaque|constant|unsafe|extern)\b",
        r"\bimplemented_by\b",
        r"\brun_tac\b",
    )
    forbidden_hits: list[str] = []
    for label, clean in (("T73", clean_source), ("independent", clean_independent)):
        for pattern in forbidden_patterns:
            if re.search(pattern, clean):
                forbidden_hits.append(f"{label}:{pattern}")
    assert not forbidden_hits, forbidden_hits

    import_line = (
        "import TheoryLib.PiQuantitativeBlockHitting.T73T73ThreePrimaryOrbit"
    )
    assert audit.count(import_line) == 1
    audit_names = re.findall(
        rf"#print\s+axioms\s+{re.escape(NAMESPACE)}\.([A-Za-z0-9_']+)",
        audit,
    )
    assert set(audit_names) == set(THEOREMS), audit_names
    assert len(audit_names) == len(THEOREMS)
    for name in THEOREMS:
        assert audit_names.count(name) == 1
        assert source.count(f"#print axioms {NAMESPACE}.{name}") == 1

    order_checks = 0
    residual_checks = 0
    period_shift_checks = 0
    coset_equality_checks = 0
    for e in range(9):
        period = 3**e
        high_modulus = 3 ** (e + 2)
        low_modulus = 3 ** (e + 1)
        assert pow(10, period, high_modulus) == 1
        if e:
            assert pow(10, period // 3, high_modulus) != 1
        order_checks += 1

        orbit = [residual_mod(e, n) for n in range(period)]
        expected_coset = list(range(1, low_modulus, 3))
        assert len(set(orbit)) == period
        assert set(orbit) == set(expected_coset)
        assert all(value % 3 == 1 for value in orbit)
        residual_checks += period
        coset_equality_checks += 1

        for n in range(2 * period):
            assert residual_mod(e, n + period) == residual_mod(e, n)
            period_shift_checks += 1

    assert residual_mod(0, 0) == 1
    assert [residual_mod(1, n) for n in range(3)] == [4, 7, 1]

    return {
        "status": "PASS",
        "claim_status": "experiment",
        "t73_theorem_declarations": len(theorem_names),
        "t73_definitions": len(definition_names),
        "axiom_audit_registrations": len(audit_names),
        "forbidden_construct_hits": len(forbidden_hits),
        "order_checks": order_checks,
        "residual_orbit_points_checked": residual_checks,
        "period_shift_checks": period_shift_checks,
        "complete_coset_checks": coset_equality_checks,
        "asserts_bbp_epoch_formula": False,
        "asserts_joint_crt_control": False,
        "asserts_v1": False,
        "asserts_pi_normal": False,
    }


if __name__ == "__main__":
    print(json.dumps(run(), indent=2, sort_keys=True))
