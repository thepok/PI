from __future__ import annotations

import hashlib
import json
import subprocess
import tempfile
import unittest
from pathlib import Path
from unittest import mock

from workflows.verification.lean_candidate_gate import gate_candidate


ROOT = Path(__file__).resolve().parents[2]


class LeanCandidateGateTest(unittest.TestCase):
    def _template(self, directory: Path, statement: str = "True") -> tuple[Path, str]:
        path = directory / "PinnedTemplate.lean"
        path.write_text(
            "import Mathlib\n\n"
            "namespace AllMathGateTest\n\n"
            f"theorem target : {statement} := by\n"
            "  -- ALLMATH_PROOF_HOLE\n\n"
            "end AllMathGateTest\n",
            encoding="utf-8",
        )
        digest = hashlib.sha256(path.read_bytes()).hexdigest()
        return path, digest

    def _gate(
        self,
        directory: Path,
        template: Path,
        digest: str,
        proof: str,
        *,
        allowed_axioms: set[str] | None = None,
    ):
        kwargs = {}
        if allowed_axioms is not None:
            kwargs["allowed_axioms"] = allowed_axioms
        return gate_candidate(
            project_root=ROOT,
            template_path=template,
            expected_template_sha256=digest,
            proof=proof,
            theorem_name="AllMathGateTest.target",
            candidate_path=directory / "Candidate.lean",
            timeout_seconds=120,
            **kwargs,
        )

    def test_accepts_kernel_checked_proof(self) -> None:
        with tempfile.TemporaryDirectory(dir=ROOT / "workflows" / "state") as raw:
            directory = Path(raw)
            template, digest = self._template(directory)
            report = self._gate(directory, template, digest, "exact True.intro")
            self.assertTrue(report.accepted, report)
            self.assertEqual(report.axioms, [])

    def test_accepts_multiline_tactic_layout(self) -> None:
        with tempfile.TemporaryDirectory(dir=ROOT / "workflows" / "state") as raw:
            directory = Path(raw)
            template, digest = self._template(directory)
            report = self._gate(
                directory,
                template,
                digest,
                "refine ?_\nexact True.intro",
            )
            self.assertTrue(report.accepted, report)

    def test_rejects_forbidden_construct_before_lean(self) -> None:
        with tempfile.TemporaryDirectory(dir=ROOT / "workflows" / "state") as raw:
            directory = Path(raw)
            template, digest = self._template(directory)
            for proof in ("sorry", "native_decide", "axiom bad : False"):
                with self.subTest(proof=proof):
                    report = self._gate(directory, template, digest, proof)
                    self.assertFalse(report.accepted)
                    self.assertEqual(report.reason, "forbidden_construct")
                    self.assertEqual(report.command, [])

    def test_rejects_template_mutation(self) -> None:
        with tempfile.TemporaryDirectory(dir=ROOT / "workflows" / "state") as raw:
            directory = Path(raw)
            template, digest = self._template(directory)
            template.write_text(
                template.read_text(encoding="utf-8").replace("True", "False"),
                encoding="utf-8",
            )
            report = self._gate(directory, template, digest, "exact True.intro")
            self.assertFalse(report.accepted)
            self.assertEqual(report.reason, "template_hash_mismatch")
            self.assertEqual(report.command, [])

    def test_rejects_invalid_proof(self) -> None:
        with tempfile.TemporaryDirectory(dir=ROOT / "workflows" / "state") as raw:
            directory = Path(raw)
            template, digest = self._template(directory)
            report = self._gate(directory, template, digest, "exact False.elim")
            self.assertFalse(report.accepted)
            self.assertEqual(report.reason, "lean_compile_failed")

    def test_enforces_exact_axiom_allowlist(self) -> None:
        with tempfile.TemporaryDirectory(dir=ROOT / "workflows" / "state") as raw:
            directory = Path(raw)
            template, digest = self._template(directory, "True = True")
            report = self._gate(
                directory,
                template,
                digest,
                "exact propext Iff.rfl",
                allowed_axioms=set(),
            )
            self.assertFalse(report.accepted)
            self.assertEqual(report.reason, "disallowed_axiom")
            self.assertEqual(report.disallowed_axioms, ["propext"])

    def test_timeout_byte_output_is_json_serializable(self) -> None:
        with tempfile.TemporaryDirectory(dir=ROOT / "workflows" / "state") as raw:
            directory = Path(raw)
            template, digest = self._template(directory)
            with mock.patch(
                "workflows.verification.lean_candidate_gate.subprocess.run",
                side_effect=subprocess.TimeoutExpired(
                    ["lean-gate"],
                    1,
                    output=b"partial \xff stdout",
                    stderr=b"timeout stderr",
                ),
            ):
                report = gate_candidate(
                    project_root=ROOT,
                    template_path=template,
                    expected_template_sha256=digest,
                    proof="exact True.intro",
                    theorem_name="AllMathGateTest.target",
                    candidate_path=directory / "Candidate.lean",
                    timeout_seconds=1,
                    command_builder=lambda _command: ["lean-gate"],
                )
            self.assertEqual(report.reason, "lean_timeout")
            self.assertIsInstance(report.stdout, str)
            self.assertIsInstance(report.stderr, str)
            json.dumps(report.__dict__)

if __name__ == "__main__":
    unittest.main()
