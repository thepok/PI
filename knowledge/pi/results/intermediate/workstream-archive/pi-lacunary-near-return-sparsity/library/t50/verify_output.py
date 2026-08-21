#!/usr/bin/env python3
"""Structural verifier for T50's deterministic output tables."""

from __future__ import annotations

import argparse
import json
from fractions import Fraction
from pathlib import Path


def as_fraction(pair: list[int]) -> Fraction:
    return Fraction(pair[0], pair[1])


def density(D: int, k: int) -> int:
    value = D
    for _ in range(k):
        value = 8 * value * value
    return value


def verify(config_path: Path, output_path: Path, report_path: Path) -> None:
    config = json.loads(config_path.read_text(encoding="ascii"))
    output = json.loads(output_path.read_text(encoding="ascii"))
    report = report_path.read_text(encoding="ascii")
    assert output["format"] == "t50-certified-bounded-experiment-output-v1"
    assert output["canonical_statement_sha256"] == config["canonical_sha256"]
    assert output["parameters"] == config
    assert output["claims"] == {
        "evidence_label": "experiment",
        "finite_heuristic_only": True,
        "proves_C1": False,
        "proves_FSFS": False,
        "proves_canonical_A1": False,
        "proves_compatibility": False,
    }
    assert [dataset["name"] for dataset in output["datasets"]] == [
        "pi",
        "rational_cycle",
        "seeded_random",
    ]
    expected_candidates = (
        len(config["search"]["M_values"])
        * len(config["search"]["D_values"])
        * len(config["search"]["r_values"])
        * len(config["search"]["h_values"])
        * len(config["search"]["shift_lists"])
    )
    checked_strata = 0
    checked_primitive_classes = 0
    checked_joint_pairs = 0
    for dataset in output["datasets"]:
        candidates = dataset["candidates"]
        assert len(candidates) == expected_candidates
        assert dataset["summary"]["candidate_count"] == expected_candidates
        by_id = {candidate["id"]: candidate for candidate in candidates}
        assert len(by_id) == len(candidates)
        for candidate in candidates:
            M = candidate["M"]
            D = candidate["D"]
            r = candidate["r"]
            h = candidate["h"]
            shifts = candidate["shifts"]
            predicates = candidate["discrete_predicates"]
            assert predicates == {
                "length_eq_depth": len(shifts) == config["search"]["depth"],
                "nodup": len(set(shifts)) == len(shifts),
                "shift_lower": all(config["search"]["B"] <= s for s in shifts),
                "shift_avoids_singleton_r": all(s != r for s in shifts),
                "final_residual": config["search"]["K"] <= M - sum(shifts),
            }
            assert candidate["N_equals_M_plus_r"] == M + r
            assert len(candidate["nodes"]) == config["search"]["depth"] + 1
            for node in candidate["nodes"]:
                k = node["k"]
                assert node["residual"] == M - sum(shifts[:k])
                assert node["density_denominator"] == density(D, k)
                multiplier = h * (10**r - 1)
                for shift in shifts[:k]:
                    multiplier *= 10**shift - 1
                assert node["coefficient_multiplier_of_alpha"] == multiplier
                expected_threshold = Fraction(node["residual"] ** 2, density(D, k) ** 2)
                assert as_fraction(node["threshold_squared"]) == expected_threshold
                assert node["strict_resonance"] in {"true", "false", "unresolved"}
            expected_witness = all(predicates.values()) and all(
                node["strict_resonance"] == "true" for node in candidate["nodes"]
            )
            assert candidate["is_witness"] == expected_witness
        witnesses = dataset["witnesses"]
        assert len(witnesses) == sum(candidate["is_witness"] for candidate in candidates)
        assert dataset["summary"]["witness_count"] == len(witnesses)
        for witness in witnesses:
            candidate = by_id[witness["candidate_id"]]
            assert candidate["is_witness"]
            M = candidate["M"]
            shift = candidate["shifts"][0]
            common_depth = min(M, M - shift)
            assert witness["adjacent_node"] == 0
            assert witness["U"] == 10**shift - 1
            assert witness["common_depth"] == common_depth
            assert [stratum["ell"] for stratum in witness["strata"]] == list(
                range(1, common_depth)
            )
            for stratum in witness["strata"]:
                checked_strata += 1
                ell = stratum["ell"]
                U = witness["U"]
                assert all(stratum["legal_predicates"].values())
                assert stratum["denominators"] == [10**ell - 10**j for j in range(ell)]
                assert stratum["delta_selected_entry"] == "mixed_budget"
                assert stratum["R"] == 2 * U * 10**ell
                R = stratum["R"]
                primitive = stratum["primitive_classes"]
                expected_m = [m for m in range(1, R) if m % 10 != 0]
                assert [record["m"] for record in primitive] == expected_m
                checked_primitive_classes += len(primitive)
                represented = []
                for record in primitive:
                    m = record["m"]
                    exponents = record["valuation_exponents"]
                    assert exponents == list(range(len(exponents)))
                    represented.extend(10**a * m for a in exponents)
                    expected_weight = sum(
                        (Fraction(R - 10**a * m, R) for a in exponents), Fraction(0)
                    )
                    assert as_fraction(record["weight"]) == expected_weight
                    assert record["quarter_correlation_status"] in {
                        "true",
                        "false",
                        "unresolved",
                    }
                assert sorted(represented) == list(range(1, R))
                assert as_fraction(stratum["primitive_weight_sum"]) == Fraction(R - 1, 2)
                assert stratum["t43_regrouping_interval_contains_zero"]
                assert stratum["fsfs_status"] in {"true", "false", "unresolved"}
                assert stratum["apc_status"] in {"true", "false", "unresolved"}
                boundary = stratum["boundary_loss"]
                assert boundary["cutoffs"] == [R - 1, R - 1]
                expected_pairs = common_depth * (common_depth - 1) // 2
                assert len(boundary["joint_pairs"]) == expected_pairs
                checked_joint_pairs += expected_pairs
                for pair in boundary["joint_pairs"]:
                    assert all(pair["domain_predicates"].values())
                    assert pair["s"] >= 1
                    assert pair["j"] + pair["s"] == pair["ell"]
                    assert pair["denominator"] == 10 ** pair["ell"] - 10 ** pair["j"]
                    assert pair["joint_good"]["status"] in {"true", "false", "unresolved"}
        all_strata = [s for witness in witnesses for s in witness["strata"]]
        assert dataset["summary"]["stratum_count"] == len(all_strata)
        assert dataset["summary"]["fsfs_true"] == sum(s["fsfs_status"] == "true" for s in all_strata)
        assert dataset["summary"]["apc_true"] == sum(s["apc_status"] == "true" for s in all_strata)
    for marker in (
        "finite heuristic evidence only",
        "FSFS nor its negation",
        "neither adjacent compatibility nor",
        "neither C1 nor canonical A1",
        "`GeometricResonanceChain` domain",
        "Run `bash reproduce.sh`",
    ):
        assert marker in report
    print(
        "T50 structural verification passed: "
        f"{checked_strata} strata, {checked_primitive_classes} primitive classes, "
        f"and {checked_joint_pairs} joint pairs."
    )


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--config", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--report", type=Path, required=True)
    args = parser.parse_args()
    verify(args.config, args.output, args.report)


if __name__ == "__main__":
    main()
