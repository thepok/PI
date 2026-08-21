#!/usr/bin/env python3
"""Independent deterministic audit for T70's infinite-support extension."""

from __future__ import annotations

from hashlib import sha256
from pathlib import Path
import json
import re
import subprocess


ROOT = Path(__file__).resolve().parents[2]
MODULE = Path(
    "TheoryLib/PiQuantitativeBlockHitting/T70T70EmpiricalRigidityBridge.lean"
)
SOURCE_PREMISE_MODULE = Path(
    "TheoryLib/PiPositiveDecimalFactorEntropy/"
    "T77T77FixedWordCoreStabilization.lean"
)
TYPE_CHECKS = Path(
    "work/ultrapi-resume/t70_infinite_support_independent_checks.lean"
)
AUDIT = Path("audit/AxiomAudit.lean")

PINS = {
    Path("problems/local/pi-digits.txt"):
        "2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825",
    SOURCE_PREMISE_MODULE:
        "efa2fe46b508539891e00097a52fb9df6cd4c6bb958aa7e49a300c9450a4550c",
    MODULE:
        "f3798779a55a280d43e98ea5324c7cc0bdf18f7b8648a6b4e3a1352e7ccf9a3e",
    TYPE_CHECKS:
        "23cc27b8a679405190f0f467958897f64228cde921d08ff4f433c92201f2301f",
}

NAMESPACE = "Theory.PiDigits.T70EmpiricalRigidityBridge."
EXTENSION_THEOREMS = [
    "support_mapsTo_of_continuous_map_absolutelyContinuous",
    "support_timesSixteen_mapsTo_of_absolutelyContinuous",
    "infinite_compact_common_invariant_eq_univ",
    "infinite_support_common_invariant_implies_support_eq_univ",
    "pi_ergodic_infinite_support_bridge",
    "pi_absolutelyContinuous_infinite_support_bridge",
]
PRINTED_THEOREMS = [
    "support_mapsTo_of_continuous_map_absolutelyContinuous",
    "infinite_compact_common_invariant_eq_univ",
    "infinite_support_common_invariant_implies_support_eq_univ",
    "pi_ergodic_infinite_support_bridge",
    "pi_absolutelyContinuous_infinite_support_bridge",
]
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def digest(path: Path) -> str:
    return sha256((ROOT / path).read_bytes()).hexdigest()


def run_lean(path: Path) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        ["lake", "env", "lean", str(path)],
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        check=False,
    )


def main() -> None:
    observed_pins = {}
    for path, expected in PINS.items():
        actual = digest(path)
        assert actual == expected, (str(path), expected, actual)
        observed_pins[str(path)] = actual

    module_text = (ROOT / MODULE).read_text()
    audit_text = (ROOT / AUDIT).read_text()

    forbidden = re.compile(
        r"\b(sorry|admit|native_decide|sorryAx|Lean\.ofReduceBool|"
        r"Lean\.trustCompiler)\b|^\s*(axiom|opaque|constant|unsafe)\b",
        re.MULTILINE,
    )
    assert forbidden.search(module_text) is None

    registrations = {}
    declarations = {}
    for theorem in EXTENSION_THEOREMS:
        declarations[theorem] = len(re.findall(
            rf"\btheorem\s+{re.escape(theorem)}\b", module_text
        ))
        registrations[theorem] = len(re.findall(
            rf"#print\s+axioms\s+{re.escape(NAMESPACE + theorem)}\b",
            audit_text,
        ))
    assert set(declarations.values()) == {1}, declarations
    assert set(registrations.values()) == {1}, registrations

    # The source premise is a Prop-valued structure and remains an explicit
    # argument.  A repository-wide declaration scan guards against silently
    # manufacturing an inhabitant elsewhere.
    lean_files = list((ROOT / "TheoryLib").rglob("*.lean"))
    corpus = "\n".join(path.read_text() for path in lean_files)
    assert len(re.findall(
        r"\bstructure\s+FurstenbergSourcePremise\s*:\s*Prop\s+where",
        corpus,
    )) == 1
    hidden_inhabitant = re.compile(
        r"^\s*(?:def|theorem|lemma|instance|axiom|opaque|constant)\b[^\n:]*:"
        r"\s*FurstenbergSourcePremise\b",
        re.MULTILINE,
    )
    assert hidden_inhabitant.search(corpus) is None

    focused = run_lean(MODULE)
    assert focused.returncode == 0, focused.stdout
    independent = run_lean(TYPE_CHECKS)
    assert independent.returncode == 0, independent.stdout

    axiom_blocks = {
        name: {token.strip() for token in body.split(",") if token.strip()}
        for name, body in re.findall(
            r"'([^']+)' depends on axioms: \[([^\]]*)\]",
            independent.stdout,
        )
    }
    expected_full_names = {NAMESPACE + theorem for theorem in PRINTED_THEOREMS}
    assert expected_full_names <= set(axiom_blocks), axiom_blocks
    for name in expected_full_names:
        assert axiom_blocks[name] <= ALLOWED_AXIOMS, (name, axiom_blocks[name])

    audit = run_lean(AUDIT)
    assert audit.returncode == 0, audit.stdout
    for theorem in EXTENSION_THEOREMS:
        assert NAMESPACE + theorem in audit.stdout, theorem

    print(json.dumps({
        "status": "PASS",
        "claim_label": "machine-checked conditional bridge",
        "pins": observed_pins,
        "declaration_counts": declarations,
        "axiom_audit_registration_counts": registrations,
        "allowed_axioms_observed": sorted(ALLOWED_AXIOMS),
        "focused_module_exit_code": focused.returncode,
        "independent_type_checks_exit_code": independent.returncode,
        "full_axiom_audit_exit_code": audit.returncode,
        "source_premise_inhabitant_found": False,
        "unconditional_v1_proved": False,
        "limitations": [
            "FurstenbergSourcePremise remains an explicit unconstructed input",
            "no infinite-support or pushforward absolute-continuity fact is proved for pi",
        ],
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
