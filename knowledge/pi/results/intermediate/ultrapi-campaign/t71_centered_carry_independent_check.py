#!/usr/bin/env python3
"""Independent deterministic audit of T71 centered-carry algebra.

This checker pins the audited source surface, recompiles the module and an
independent Lean restatement, verifies AxiomAudit registration, replays the
primary exact-integer checker, and exhaustively checks small integer models of
the half-open convention.  It asserts neither carry density nor V1.
"""

from __future__ import annotations

from hashlib import sha256
import json
from pathlib import Path
import re
import subprocess


ROOT = Path(__file__).resolve().parents[2]
MODULE = Path(
    "TheoryLib/PiQuantitativeBlockHitting/"
    "T71T71CenteredCarryRecurrence.lean"
)
TYPE_CHECKS = Path(
    "work/ultrapi-resume/t71_centered_carry_independent_checks.lean"
)
AXIOM_AUDIT = Path("audit/AxiomAudit.lean")
PRIMARY_REPORT = Path(
    "work/ultrapi-resume/bbp_centered_carry_recurrence_20260813.md"
)
PRIMARY_CHECKER = Path(
    "work/ultrapi-resume/bbp_centered_carry_recurrence_20260813_check.py"
)

PINS = {
    Path("problems/local/pi-digits.txt"):
        "2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825",
    MODULE:
        "566ba24822d98366faaa7208b3b655cea5b6157522ee54ed02cea9073b2443e7",
    TYPE_CHECKS:
        "6ca67044ab3ae702e9fd3c7fe829246dcb33d837c1d97fe9d6a7186e8017a130",
    AXIOM_AUDIT:
        "0bb45a8f484d7ef47e40e3fce362df15fae7532395a06bec4af09daf47cbf77b",
    PRIMARY_REPORT:
        "3a357c5b1932b76357259613c338dc6ca49f4bf68baef96730ad31b2a13e69e6",
    PRIMARY_CHECKER:
        "b83276cc2aceb61e903e8764424e2a3b9dddec8a5ac16ffff4b8370200316fff",
}

NAMESPACE = "Theory.PiDigits.T71CenteredCarryRecurrence."
THEOREMS = [
    "centeredRepresentation_unique",
    "centeredNumerator_step",
    "advancedQuotient_representation",
    "carry_eq_zero_iff_uncorrected_centered",
]
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def digest(relative: Path) -> str:
    return sha256((ROOT / relative).read_bytes()).hexdigest()


def run(command: list[str]) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        command,
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        check=False,
    )


def nearest(numerator: int, denominator: int) -> int:
    assert denominator > 0
    return (2 * numerator + denominator) // (2 * denominator)


def centered(D: int, U: int, z: int, S: int) -> bool:
    return 0 < D and U == D * z + S and -D <= 2 * S < D


def exhaustive_integer_replay() -> dict[str, int | bool]:
    representation_rows = 0
    recurrence_rows = 0

    for D in range(1, 13):
        for U in range(-50, 51):
            z = nearest(U, D)
            S = U - D * z
            assert centered(D, U, z, S)
            candidates = [
                zp
                for zp in range(z - 3, z + 4)
                if centered(D, U, zp, U - D * zp)
            ]
            assert candidates == [z]
            representation_rows += 1

    # Pin ties separately: lower is included, upper is excluded and advances.
    assert centered(10, -5, 0, -5)
    assert not centered(10, 5, 0, 5)
    assert centered(10, 5, 1, -5)

    for base in (-3, 0, 2, 10):
        for scale in (1, 2, 3):
            for D in range(1, 8):
                D_next = scale * D
                for U in range(-12, 13):
                    z = nearest(U, D)
                    S = U - D * z
                    for forcing in range(-8, 9):
                        U_next = base * scale * U + forcing
                        z_next = nearest(U_next, D_next)
                        S_next = U_next - D_next * z_next
                        carry = z_next - base * z
                        uncorrected = base * scale * S + forcing
                        assert S_next == uncorrected - carry * D_next
                        assert (carry == 0) == (
                            -D_next <= 2 * uncorrected < D_next
                        )
                        recurrence_rows += 1

    return {
        "representation_rows": representation_rows,
        "recurrence_rows": recurrence_rows,
        "lower_tie_included": True,
        "upper_tie_excluded": True,
    }


def main() -> None:
    observed_pins: dict[str, str] = {}
    for relative, expected in PINS.items():
        actual = digest(relative)
        assert actual == expected, (str(relative), expected, actual)
        observed_pins[str(relative)] = actual

    module_text = (ROOT / MODULE).read_text(encoding="utf-8")
    audit_text = (ROOT / AXIOM_AUDIT).read_text(encoding="utf-8")

    assert "Source: `problems/local/pi-digits.txt`" in module_text
    assert PINS[Path("problems/local/pi-digits.txt")] in module_text

    forbidden = re.compile(
        r"\b(sorry|admit|native_decide|sorryAx|Lean\.ofReduceBool|"
        r"Lean\.trustCompiler)\b|^\s*(axiom|opaque|constant|unsafe)\b",
        re.MULTILINE,
    )
    assert forbidden.search(module_text) is None

    declared = re.findall(r"^theorem\s+([A-Za-z0-9_']+)\b", module_text, re.MULTILINE)
    assert declared == THEOREMS, declared

    registrations = {
        theorem: len(re.findall(
            rf"#print\s+axioms\s+{re.escape(NAMESPACE + theorem)}\b",
            audit_text,
        ))
        for theorem in THEOREMS
    }
    assert set(registrations.values()) == {1}, registrations

    module_build = run(["lake", "env", "lean", str(MODULE)])
    assert module_build.returncode == 0, module_build.stdout

    type_build = run(["lake", "env", "lean", str(TYPE_CHECKS)])
    assert type_build.returncode == 0, type_build.stdout
    axiom_blocks = {
        name: {token.strip() for token in body.split(",") if token.strip()}
        for name, body in re.findall(
            r"'([^']+)' depends on axioms: \[([^\]]*)\]",
            type_build.stdout,
        )
    }
    expected_names = {NAMESPACE + theorem for theorem in THEOREMS}
    assert expected_names <= set(axiom_blocks), axiom_blocks
    for name in expected_names:
        assert axiom_blocks[name] <= ALLOWED_AXIOMS, (name, axiom_blocks[name])

    audit_build = run(["lake", "env", "lean", str(AXIOM_AUDIT)])
    assert audit_build.returncode == 0, audit_build.stdout
    for theorem in THEOREMS:
        assert NAMESPACE + theorem in audit_build.stdout, theorem

    primary = run([".venv/bin/python", str(PRIMARY_CHECKER)])
    assert primary.returncode == 0, primary.stdout
    primary_result = json.loads(primary.stdout)
    assert primary_result["status"] == "PASS"
    assert primary_result["one_step_recurrence_checks"] == 3000
    assert primary_result["asserts_positive_carry_density"] is False
    assert primary_result["asserts_sublinear_zero_run_bound"] is False
    assert primary_result["asserts_v1"] is False

    integer_replay = exhaustive_integer_replay()

    print(json.dumps({
        "status": "PASS",
        "claim_label": "machine-checked generic algebra",
        "pins": observed_pins,
        "theorem_declarations": declared,
        "axiom_audit_registration_counts": registrations,
        "allowed_axioms_observed": sorted(
            set().union(*(axiom_blocks[name] for name in expected_names))
        ),
        "focused_module_exit_code": module_build.returncode,
        "independent_type_checks_exit_code": type_build.returncode,
        "full_axiom_audit_exit_code": audit_build.returncode,
        "primary_integer_checker_status": primary_result["status"],
        "independent_integer_replay": integer_replay,
        "asserts_positive_carry_density": False,
        "asserts_sublinear_zero_run_bound": False,
        "asserts_v1": False,
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
