#!/usr/bin/env python3
"""Deterministic consistency checks for the inactive T120 stage specs."""

import hashlib
import json
from pathlib import Path

STAGES = Path(__file__).resolve().parents[1]
ROOT = STAGES.parent
REPO = ROOT.parents[5]
EXPERIMENT = "pi-q10-j10-lag-determinant-20260822-v1"
BUNDLE = "fe180d8a5db818d3b4a9b3931779b3cc3d313a2437e9f4db808f3afecba51f98"
DIRS = ("s1-combined-term-generator", "s2-literal-four-pole-verifier",
        "a1-source-separation-audit", "a2-index-arithmetic-audit",
        "a3-byte-cas-receipt-audit", "a4-decision-claim-audit", "t120-prew13")


def load_unique(path):
    def pairs(items):
        out = {}
        for key, value in items:
            assert key not in out, f"duplicate key {key!r} in {path}"
            out[key] = value
        return out
    return json.loads(path.read_text(encoding="utf-8"), object_pairs_hook=pairs)


def binding(contract):
    parent = contract.get("parent_binding", {})
    return (contract.get("experiment_id", parent.get("experiment_id")),
            contract.get("parent_spec_bundle_sha256", parent.get("spec_bundle_sha256")))


def test_planned_contracts():
    contracts = {name: load_unique(STAGES / name / "TASK_CONTRACT.json") for name in DIRS}
    for name, contract in contracts.items():
        assert contract["active"] is False and contract["launch_authorized"] is False, name
        assert contract["claim_label"] == "experiment", name
        assert binding(contract) == (EXPERIMENT, BUNDLE), name

    hashes = {"CONTRACT.json": "5e6ac96f7c3c8a003ffbfbf1b65e582b5583700a68c597968d903e70075ce327",
              "INTERFACE.md": "cd1eb2d91c02e866c9f0bf27e2aadeaa4f9c8e1774ccc4d6dfd1a4114f7d8fde",
              "TEST_PLAN.md": "ab7f0e1261d472a82789731b9db34ced32afea74f36d188e5b06308357f344ea"}
    for name, expected in hashes.items():
        assert hashlib.sha256((ROOT / name).read_bytes()).hexdigest() == expected, name
    rows = [{"name": name, "sha256": digest} for name, digest in hashes.items()]
    payload = json.dumps(rows, sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode("ascii")
    digest = hashlib.sha256(payload).hexdigest()
    assert digest == BUNDLE

    s1, s2 = contracts[DIRS[0]], contracts[DIRS[1]]
    assert s1["exact_deliverables"] == ["t120_s1_generator.py", "REPORT.md"]
    assert s2["exact_deliverables"] == ["literal_four_pole_verifier.py", "REPORT.md"]
    assert s1["tiny_tests"]["shards"] == [{"index": 0, "range": [0, 2]},
                                          {"index": 1, "range": [2, 7]},
                                          {"index": 2, "range": [7, 11]}]
    assert s1["tiny_tests"]["execution_order"] == [2, 0, 1]
    assert s2["tiny_tests"]["shards"] == [[0, 2], [2, 7], [7, 11]]
    assert s2["tiny_tests"]["execution_order"] == [[7, 11], [0, 2], [2, 7]]
    assert "no endpoint state" in s1["job_contract"]
    assert set(s1["modes"]) == {"tiny_point", "future_window_256"}
    assert "entire parent/S0 canonical artifact" in " ".join(s2["verification_contract"])
    canonical = [
        {"name": "T74", "path": "TheoryLib/PiQuantitativeBlockHitting/T74T74ThreePrimaryDecimation.lean", "sha256": "eb103c72fd7cf7b0f91c85a102d8d7ed5165028b1d64ae23dac714f6093f2727"},
        {"name": "T77", "path": "TheoryLib/PiQuantitativeBlockHitting/T77T77SelectedPadicDefectShell.lean", "sha256": "7185e8ca571cebc326f717d18dc660d2e31e4cbbaee1a3910498ac7f441de3e0"},
        {"name": "T98", "path": "TheoryLib/PiQuantitativeBlockHitting/T98T98BBPArchimedeanTerm.lean", "sha256": "879fb2d44de3b737324ad8a58a04d7bbb8775cd76f9611823964576961ddf304"},
        {"name": "T106", "path": "TheoryLib/PiQuantitativeBlockHitting/T106T106BBPForcedOrbit.lean", "sha256": "f757ea2d54c2563fe0d21e1ebbe4447a22efdba98349c3ecec26a839eed68fe2"},
        {"name": "T113", "path": "TheoryLib/PiQuantitativeBlockHitting/T113T113SampledBBPReducedCellRecurrence.lean", "sha256": "1ae6b4f775380d3cd4e087ea87655d5b3609333797021eee3c763caffc7ac76b"},
        {"name": "T118", "path": "TheoryLib/PiQuantitativeBlockHitting/T118T118SampledBBPNormalizedExcessCell.lean", "sha256": "9189eec2abf3c1f5cd56bd4199af1e411792cadc11ef4ccae2a59666e25f9e04"},
        {"name": "T119", "path": "TheoryLib/PiQuantitativeBlockHitting/T119T119SampledBBPSameCellCrossDeterminant.lean", "sha256": "a356d728b7a9ba99347d8c411b937366f4a7b35de7c260dbe25e48b028f7fd88"},
    ]
    assert s1["parent_binding"]["repository_commit"] == s2["parent_binding"]["repository_commit"] == "0b03dadf8c542d4e5bc19567625162e73a9a7959"
    assert s1["parent_binding"]["canonical_sources"] == canonical
    assert s2["parent_binding"]["canonical_sources"] == canonical
    for row in canonical:
        assert hashlib.sha256((REPO / row["path"]).read_bytes()).hexdigest() == row["sha256"], row["name"]
    assert s1["combined_formula_contract"] == {
        "b_k": "(120*k^2 + 151*k + 47) / ((2*k+1)*(4*k+3)*(8*k+1)*(8*k+5)*16^k)",
        "P_N": "sum k=0..7*N inclusive of b_k",
        "Q_N": "10^N * P_N",
        "F_N": "10^(N+1) * sum j=1..7 inclusive of b_(7*N+j)",
        "forbidden": "literal pole summation or any p1/p2/p3/p4 implementation",
    }
    assert s2["literal_formula_contract"] == {
        "p1_k": "4 / ((8*k+1)*16^k)",
        "p2_k": "-1 / (2*(2*k+1)*16^k)",
        "p3_k": "-1 / ((8*k+5)*16^k)",
        "p4_k": "-1 / (2*(4*k+3)*16^k)",
        "P_N": "sum k=0..7*N inclusive of (p1_k+p2_k+p3_k+p4_k)",
        "Q_N": "10^N * P_N",
        "F_N": "10^(N+1) * (P_(N+1)-P_N) = 10^(N+1) * sum j=1..7 inclusive of (p1+p2+p3+p4) at 7*N+j",
    }
    independence = json.dumps(s2["arithmetic_independence"], sort_keys=True)
    assert "fractions.Fraction" in independence and "combined numerator identity" in independence
    assert "unscaled F" in " ".join(s2["tiny_tests"]["mutations"])
    assert "endpoint state" not in " ".join(s1["tiny_tests"]["requirements"])
    for route in (s1, s2):
        hook = route["controller_test_hook"]
        assert "controller-only isolated" in hook and "unreachable from production jobs" in hook
        mode = route["modes"]["future_window_256"] if route is s1 else " ".join(route["verification_contract"])
        assert "extra identity fields" in mode and ("do not emit" in mode or "may be emitted" in mode)
        assert "operational only" in mode and "13" in mode
        assert "C0=256" in mode and "never emitted" in mode

    audits = [contracts[name] for name in DIRS[2:6]]
    assert len({audit["role"] for audit in audits}) == 4
    assert all(audit["exact_deliverables"] == ["AUDIT.json", "REPORT.md"] for audit in audits)
    assert all(audit["read_only_inputs"] and audit["noncircularity"] for audit in audits)

    pre = contracts["t120-prew13"]
    assert pre["readiness_schema"]["window13_authorized"] is False
    assert "window13_action" in pre["decision"] and "operational only" in pre["decision"] and "exactly 13" in pre["decision"]
    assert len(pre["required_predecessors"]) == 5
    required_tests = " ".join(pre["third_route_oracle"]["required_tests"])
    assert "hidden synthetic 256-point" in required_tests
    assert "unscaled-F" in required_tests and "C0 is never emitted" in required_tests
    forbidden = " ".join(pre["forbidden"])
    assert "[3840,4096)" in forbidden and "[512,4096)" in forbidden
    print("T120 planned stage contracts: OK")


if __name__ == "__main__":
    test_planned_contracts()
