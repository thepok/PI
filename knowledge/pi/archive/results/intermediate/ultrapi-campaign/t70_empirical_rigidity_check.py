#!/usr/bin/env python3
"""Focused deterministic checker for T70's conditional Lean bridge."""

from __future__ import annotations

from hashlib import sha256
import json
from pathlib import Path
import re
import subprocess


ROOT = Path(__file__).resolve().parents[2]
MODULE = "TheoryLib/PiQuantitativeBlockHitting/T70T70EmpiricalRigidityBridge.lean"

PINS = {
    "problems/local/pi-digits.txt":
        "2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825",
    "TheoryLib/PiPositiveDecimalFactorEntropy/T39T39ErgodicAffinityRigidity.lean":
        "f4982dacc90a436ca14e52d0529acbbfa8067d47e80679fb0173dff559d2ba09",
    "TheoryLib/PiQuantitativeBlockHitting/T69T69FixedSixteenReturn.lean":
        "fb7eb54d99bb904c28da0f49d33f8a40979ffcbf22a4024fcae73de7149886f9",
    "TheoryLib/PiPositiveDecimalFactorEntropy/T77T77FixedWordCoreStabilization.lean":
        "efa2fe46b508539891e00097a52fb9df6cd4c6bb958aa7e49a300c9450a4550c",
    MODULE:
        "f3798779a55a280d43e98ea5324c7cc0bdf18f7b8648a6b4e3a1352e7ccf9a3e",
}

THEOREMS = [
    "support_mapsTo_of_continuous_map_eq_self",
    "support_mapsTo_of_continuous_map_absolutelyContinuous",
    "support_timesTen_mapsTo",
    "support_timesSixteen_mapsTo",
    "support_timesSixteen_mapsTo_of_absolutelyContinuous",
    "notMutuallySingular_implies_timesSixteen_invariant",
    "tenSixteenOrbit_subset_of_mapsTo",
    "dense_support_orbit_implies_support_eq_univ",
    "infinite_compact_common_invariant_eq_univ",
    "infinite_support_common_invariant_implies_support_eq_univ",
    "support_subset_piOrbitClosure_of_measure_eq_one",
    "pi_empirical_rigidity_bridge",
    "pi_empirical_rigidity_bridge_of_measure_eq_one",
    "pi_ergodic_infinite_support_bridge",
    "pi_absolutelyContinuous_infinite_support_bridge",
]


def digest(relative: str) -> str:
    return sha256((ROOT / relative).read_bytes()).hexdigest()


def main() -> None:
    pins = {}
    for relative, expected in PINS.items():
        actual = digest(relative)
        assert actual == expected, (relative, expected, actual)
        pins[relative] = actual

    module_text = (ROOT / MODULE).read_text()
    audit_text = (ROOT / "audit/AxiomAudit.lean").read_text()

    forbidden = re.compile(
        r"\b(sorry|admit|native_decide|sorryAx|Lean\.ofReduceBool|"
        r"Lean\.trustCompiler)\b|^\s*(axiom|opaque|constant|unsafe)\b",
        re.MULTILINE,
    )
    assert forbidden.search(module_text) is None
    assert "does not construct an empirical limit" in module_text
    assert "consume `FurstenbergSourcePremise` explicitly" in module_text
    assert "constructs no" in module_text and "inhabitant" in module_text

    declaration_checks = {}
    audit_checks = {}
    for theorem in THEOREMS:
        declaration_checks[theorem] = bool(
            re.search(rf"\btheorem\s+{re.escape(theorem)}\b", module_text)
        )
        audit_checks[theorem] = (
            f"Theory.PiDigits.T70EmpiricalRigidityBridge.{theorem}" in audit_text
        )
    assert all(declaration_checks.values()), declaration_checks
    assert all(audit_checks.values()), audit_checks
    assert "import TheoryLib.PiQuantitativeBlockHitting.T70T70EmpiricalRigidityBridge" \
        in audit_text

    lean = subprocess.run(
        ["lake", "env", "lean", MODULE],
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        check=False,
    )
    assert lean.returncode == 0, lean.stdout
    assert "sorryAx" not in lean.stdout
    for theorem in THEOREMS:
        assert theorem in lean.stdout, theorem

    result = {
        "status": "PASS",
        "claim_label": "machine-checked",
        "pins": pins,
        "declarations": declaration_checks,
        "axiom_audit_registrations": audit_checks,
        "lean_exit_code": lean.returncode,
        "allowed_axioms_observed": ["propext", "Classical.choice", "Quot.sound"],
        "asserts_unconditional_v1": False,
        "remaining_explicit_premises": [
            "FurstenbergSourcePremise",
            "an infinite-support pi empirical limit with the stated invariance or nonsingularity hypotheses",
        ],
    }
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
