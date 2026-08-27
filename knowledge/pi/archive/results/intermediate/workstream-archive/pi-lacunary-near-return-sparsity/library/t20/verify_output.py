#!/usr/bin/env python3
"""Deterministic exact verifier for T20 raw_output.json."""

from __future__ import annotations

import argparse
import itertools
import json
import math
from fractions import Fraction
from pathlib import Path


def fraction(value) -> Fraction:
    if not isinstance(value, list) or len(value) != 2:
        raise AssertionError(f"not a rational pair: {value!r}")
    numerator, denominator = value
    if not isinstance(numerator, int) or not isinstance(denominator, int) or denominator <= 0:
        raise AssertionError(f"invalid rational pair: {value!r}")
    if math.gcd(numerator, denominator) != 1:
        raise AssertionError(f"rational is not reduced: {value!r}")
    return Fraction(numerator, denominator)


def row_cell(row: dict, eta: Fraction) -> dict:
    for cell in row["pareto_cells"]:
        if fraction(cell["eta_lower_exclusive"]) < eta <= fraction(cell["eta_upper_inclusive"]):
            return cell
    raise AssertionError("eta not covered by row cells")


def verify_row(row: dict, eta_upper: Fraction) -> int:
    assert row["t9_refinement_equal"] is True
    assert row["successor_energy"] == row["child_energy"]
    assert row["energy"] >= row["child_energy"] >= row["cutoff"]
    cells = row["pareto_cells"]
    assert cells
    lower = Fraction(0)
    previous_split = row["energy"] + 1
    for cell in cells:
        assert fraction(cell["eta_lower_exclusive"]) == lower
        upper = fraction(cell["eta_upper_inclusive"])
        assert lower < upper <= eta_upper
        split_energy = cell["split_energy"]
        dominant_energy = cell["dominant_energy"]
        assert 0 <= split_energy <= row["energy"]
        assert 0 <= dominant_energy <= row["energy"]
        assert split_energy <= previous_split
        cap = fraction(cell["mu_cap"])
        assert cap == Fraction(split_energy, row["energy"])
        # Every retained T14 boundary inequality is checked as integers.
        assert cell["t14_boundary_lhs"] == cap.numerator * row["energy"]
        assert cell["t14_boundary_rhs"] == cap.denominator * split_energy
        assert cell["t14_boundary_lhs"] <= cell["t14_boundary_rhs"]
        assert cell["mu_cap_attained_in_T14_domain"] == (0 < cap < 1)
        previous_split = split_energy
        lower = upper
    assert lower == eta_upper
    return len(cells)


def checkpoint_score(row_map, cutoff, eta, mu, B, m0, max_depth):
    level_split = []
    for level in range(max_depth):
        cap = fraction(row_cell(row_map[(cutoff, level)], eta)["mu_cap"])
        level_split.append(mu <= cap)
    counts = [sum(level_split[:m]) for m in range(max_depth + 1)]
    score = min((Fraction(counts[m]) + B) / m for m in range(m0, max_depth + 1))
    return score, counts


def verify_point(point, row_map, config) -> int:
    eta_lower = fraction(point["eta_lower_exclusive"])
    eta = fraction(point["eta_upper_inclusive"])
    mu_lower = fraction(point["mu_lower_exclusive"])
    mu_upper = fraction(point["mu_upper"])
    mu = fraction(point["mu_witness"])
    d = fraction(point["d"])
    B = fraction(point["B"])
    assert Fraction(0) <= eta_lower < eta <= Fraction(1, 10)
    assert Fraction(0) <= mu_lower < mu_upper <= 1
    if point["mu_upper_inclusive"]:
        assert mu == mu_upper < 1
    else:
        assert mu_lower < mu < mu_upper == 1
    assert 0 < mu < 1 and d > 0
    assert B == fraction(config["affine_B"])
    checkpoints = config["optimization_checkpoints"]
    selected = point["subsequence"]
    assert len(selected) == config["sequence_length"]
    assert selected == sorted(selected)
    assert all(cutoff in checkpoints for cutoff in selected)
    scores = []
    counts_by_cutoff = {}
    for cutoff in checkpoints:
        score, counts = checkpoint_score(
            row_map,
            cutoff,
            eta,
            mu,
            B,
            config["affine_m0"],
            config["max_depth"],
        )
        scores.append(score)
        counts_by_cutoff[cutoff] = counts
    choices = []
    for indices in itertools.combinations(range(len(checkpoints)), config["sequence_length"]):
        choices.append((min(scores[index] for index in indices), indices))
    optimum = max(value for value, _ in choices)
    expected_indices = min(indices for value, indices in choices if value == optimum)
    expected_selected = [checkpoints[index] for index in expected_indices]
    assert d == optimum
    assert selected == expected_selected
    expected_margins = []
    for cutoff in selected:
        counts = counts_by_cutoff[cutoff]
        for depth in range(config["affine_m0"], config["max_depth"] + 1):
            expected_margins.append((cutoff, depth, counts[depth], Fraction(counts[depth]) + B - d * depth))
    assert len(point["affine_margins"]) == len(expected_margins)
    for stored, expected in zip(point["affine_margins"], expected_margins):
        cutoff, depth, count, margin = expected
        assert stored["cutoff"] == cutoff
        assert stored["depth"] == depth
        assert stored["splitting_count"] == count
        assert fraction(stored["margin"]) == margin >= 0
    expected_obstructions = []
    for cutoff in selected:
        for level in range(config["max_depth"]):
            row = row_map[(cutoff, level)]
            cell = row_cell(row, eta)
            energy = row["energy"]
            split_energy = cell["split_energy"]
            if mu.numerator * energy > mu.denominator * split_energy:
                dominant_energy = cell["dominant_energy"]
                expected_obstructions.append((cutoff, level, energy, split_energy, dominant_energy))
    assert len(point["dominant_obstructions"]) == len(expected_obstructions)
    for stored, expected in zip(point["dominant_obstructions"], expected_obstructions):
        cutoff, level, energy, split_energy, dominant_energy = expected
        assert (stored["cutoff"], stored["level"]) == (cutoff, level)
        assert stored["energy"] == energy
        assert stored["split_energy"] == split_energy
        assert stored["dominant_energy"] == dominant_energy
        assert stored["splitting_failure_lhs"] == mu.numerator * energy
        assert stored["splitting_failure_rhs"] == mu.denominator * split_energy
        assert stored["splitting_failure_lhs"] > stored["splitting_failure_rhs"]
        assert stored["dominance_lhs"] == (mu.denominator - mu.numerator) * energy
        assert stored["dominance_rhs"] == mu.denominator * dominant_energy
        assert stored["dominance_lhs"] < stored["dominance_rhs"]
        assert stored["strict_dominance_verified"] is True
    return len(expected_obstructions)


def verify_frontier(points: list[dict]) -> None:
    coordinates = [
        (
            fraction(point["eta_upper_inclusive"]),
            fraction(point["mu_upper"]),
            fraction(point["d"]),
        )
        for point in points
    ]
    assert len(coordinates) == len(set(coordinates))
    for index, point in enumerate(coordinates):
        for other_index, other in enumerate(coordinates):
            if index == other_index:
                continue
            assert not (
                other[0] >= point[0]
                and other[1] >= point[1]
                and other[2] >= point[2]
            ), f"retained point {index} is dominated by {other_index}"


def verify_complete_frontier(dataset: dict, row_map: dict, config: dict) -> None:
    """Independently enumerate all finite cells and compare the exact frontier."""
    checkpoints = config["optimization_checkpoints"]
    max_depth = config["max_depth"]
    m0 = config["affine_m0"]
    B = fraction(config["affine_B"])
    sequence_length = config["sequence_length"]
    eta_boundaries = sorted(
        {
            fraction(cell["eta_upper_inclusive"])
            for cutoff in checkpoints
            for level in range(max_depth)
            for cell in row_map[(cutoff, level)]["pareto_cells"]
        }
    )
    candidates = []
    eta_lower = Fraction(0)
    for eta in eta_boundaries:
        caps = {
            fraction(row_cell(row_map[(cutoff, level)], eta)["mu_cap"])
            for cutoff in checkpoints
            for level in range(max_depth)
        }
        upper_bounds = sorted(cap for cap in caps if 0 < cap < 1)
        previous = Fraction(0)
        mu_cells = []
        for upper in upper_bounds:
            mu_cells.append((previous, upper, True, upper))
            previous = upper
        if Fraction(1) in caps:
            mu_cells.append((previous, Fraction(1), False, (previous + 1) / 2))
        for mu_lower, mu_upper, inclusive, mu in mu_cells:
            scores = []
            for cutoff in checkpoints:
                score, _counts = checkpoint_score(
                    row_map, cutoff, eta, mu, B, m0, max_depth
                )
                scores.append(score)
            choices = []
            for indices in itertools.combinations(range(len(checkpoints)), sequence_length):
                choices.append((min(scores[index] for index in indices), indices))
            d = max(value for value, _indices in choices)
            indices = min(indices for value, indices in choices if value == d)
            candidates.append(
                {
                    "coordinate": (eta, mu_upper, d),
                    "eta_lower": eta_lower,
                    "mu_lower": mu_lower,
                    "inclusive": inclusive,
                    "mu_witness": mu,
                    "subsequence": tuple(checkpoints[index] for index in indices),
                }
            )
        eta_lower = eta
    expected = []
    for index, candidate in enumerate(candidates):
        eta, mu, d = candidate["coordinate"]
        dominated = False
        for other_index, other in enumerate(candidates):
            if index == other_index:
                continue
            other_eta, other_mu, other_d = other["coordinate"]
            if other_eta >= eta and other_mu >= mu and other_d >= d:
                dominated = True
                break
        if not dominated:
            expected.append(candidate)
    stored = dataset["global_affine_pareto"]
    stored_by_coordinate = {
        (
            fraction(point["eta_upper_inclusive"]),
            fraction(point["mu_upper"]),
            fraction(point["d"]),
        ): point
        for point in stored
    }
    expected_by_coordinate = {candidate["coordinate"]: candidate for candidate in expected}
    assert stored_by_coordinate.keys() == expected_by_coordinate.keys()
    for coordinate, candidate in expected_by_coordinate.items():
        point = stored_by_coordinate[coordinate]
        assert fraction(point["eta_lower_exclusive"]) == candidate["eta_lower"]
        assert fraction(point["mu_lower_exclusive"]) == candidate["mu_lower"]
        assert point["mu_upper_inclusive"] == candidate["inclusive"]
        assert fraction(point["mu_witness"]) == candidate["mu_witness"]
        assert tuple(point["subsequence"]) == candidate["subsequence"]
    stats = dataset["frontier_stats"]
    assert stats["eta_cells"] == len(eta_boundaries)
    assert stats["parameter_cells_evaluated"] == len(candidates)
    assert stats["pareto_points_retained"] == len(expected)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--config", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    config = json.loads(args.config.read_text(encoding="utf-8"))
    output = json.loads(args.output.read_text(encoding="utf-8"))
    assert output["format"] == "t20-exact-pareto-output-v1"
    assert output["parameters"] == config
    assert output["canonical_statement_sha256"] == config["canonical_sha256"]
    assert output["claims"] == {
        "evidence_label": "experiment",
        "finite_heuristic_only": True,
        "proves_or_refutes_C2": False,
        "proves_or_refutes_canonical_A1": False,
    }
    expected_names = ["pi", "seeded_iid", "champernowne"]
    assert [dataset["name"] for dataset in output["datasets"]] == expected_names
    row_total = 0
    cell_total = 0
    point_total = 0
    obstruction_total = 0
    for dataset in output["datasets"]:
        rows = dataset["rows"]
        assert len(rows) == len(config["checkpoints"]) * config["max_depth"]
        row_map = {(row["cutoff"], row["level"]): row for row in rows}
        assert len(row_map) == len(rows)
        for row in rows:
            assert row["dataset"] == dataset["name"]
            cell_total += verify_row(row, fraction(config["t14_eta_upper"]))
        points = dataset["global_affine_pareto"]
        assert dataset["frontier_stats"]["pareto_points_retained"] == len(points)
        verify_frontier(points)
        verify_complete_frontier(dataset, row_map, config)
        for point in points:
            obstruction_total += verify_point(point, row_map, config)
        row_total += len(rows)
        point_total += len(points)
    print(
        f"T20 exact verification passed: {row_total} rows, {cell_total} row-envelope cells, "
        f"{point_total} global Pareto points, {obstruction_total} dominant obstructions."
    )


if __name__ == "__main__":
    main()
