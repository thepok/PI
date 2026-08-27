#!/usr/bin/env python3
"""Independent floating-point oracle for T50's declared M=3 cases."""

from __future__ import annotations

import argparse
import cmath
import hashlib
import json
import math
from pathlib import Path


def close_to_interval(value: float, interval: dict[str, str], tolerance: float) -> bool:
    return float(interval["lo"]) - tolerance <= value <= float(interval["hi"]) + tolerance


def fejer(x: float, R: int) -> float:
    total = sum((cmath.exp(2j * math.pi * v * x) for v in range(R)), 0j)
    return abs(total) ** 2 / R


def norm_squared(beta: float, residual: int) -> float:
    total = sum((cmath.exp(2j * math.pi * beta * 10**j) for j in range(residual)), 0j)
    return abs(total) ** 2


def alpha_for(name: str, config: dict) -> float:
    if name == "pi":
        return math.pi
    if name == "rational_cycle":
        numerator, denominator = config["controls"]["rational_cycle"]
        return numerator / denominator
    seed = config["controls"]["seeded_random_seed_ascii"].encode("ascii")
    numerator = int.from_bytes(hashlib.sha256(seed).digest(), "big")
    denominator = 2 ** config["controls"]["seeded_random_denominator_power"]
    return numerator / denominator


def joint_good(beta0: float, beta1: float, D: int, U: int, q: int) -> bool:
    D1 = 8 * D * D
    emax0 = math.acos(1 / (8 * D * D)) / (2 * math.pi)
    emax1 = math.acos(1 / (8 * D1 * D1)) / (2 * math.pi)
    x0 = q * beta0
    x1 = q * beta1
    a0s = range(math.floor(x0 - emax0) - 1, math.ceil(x0 + emax0) + 2)
    a1s = range(math.floor(x1 - emax1) - 1, math.ceil(x1 + emax1) + 2)
    for a0 in a0s:
        e0 = abs(x0 - a0)
        for a1 in a1s:
            e1 = abs(x1 - a1)
            if e0 < emax0 and e1 < emax1 and q * e1 + U * q * e0 < 1:
                return True
    return False


def check(config_path: Path, output_path: Path) -> None:
    config = json.loads(config_path.read_text(encoding="ascii"))
    output = json.loads(output_path.read_text(encoding="ascii"))
    tolerance = float(config["naive_cases"]["absolute_tolerance"])
    checked_candidates = 0
    checked_strata = 0
    checked_classes = 0
    for dataset in output["datasets"]:
        alpha = alpha_for(dataset["name"], config)
        candidate_by_id = {candidate["id"]: candidate for candidate in dataset["candidates"]}
        for candidate in dataset["candidates"]:
            if candidate["M"] not in config["naive_cases"]["M_values"]:
                continue
            checked_candidates += 1
            M = candidate["M"]
            D = candidate["D"]
            r = candidate["r"]
            h = candidate["h"]
            shift = candidate["shifts"][0]
            multipliers = [h * (10**r - 1), h * (10**r - 1) * (10**shift - 1)]
            residuals = [M, M - shift]
            densities = [D, 8 * D * D]
            statuses = []
            for node, multiplier, residual, density in zip(
                candidate["nodes"], multipliers, residuals, densities
            ):
                value = norm_squared(multiplier * alpha, residual)
                assert close_to_interval(value, node["norm_squared"], tolerance)
                status = value > (residual / density) ** 2
                assert node["strict_resonance"] != "unresolved"
                assert status == (node["strict_resonance"] == "true")
                statuses.append(status)
            assert candidate["is_witness"] == all(statuses) and all(
                candidate["discrete_predicates"].values()
            )
        for witness in dataset["witnesses"]:
            candidate = candidate_by_id[witness["candidate_id"]]
            if candidate["M"] not in config["naive_cases"]["M_values"]:
                continue
            beta0 = candidate["h"] * (10 ** candidate["r"] - 1) * alpha
            U = witness["U"]
            beta1 = U * beta0
            D = candidate["D"]
            for stratum in witness["strata"]:
                checked_strata += 1
                ell = stratum["ell"]
                R = stratum["R"]
                delta = 1 / (2 * U * 10**ell)
                denominators = [10**ell - 10**j for j in range(ell)]
                fejer_sum = sum(fejer(beta0 * q, R) for q in denominators)
                fsfs_threshold = ell / (4 * R * delta * delta)
                fsfs_margin = fejer_sum - fsfs_threshold
                assert close_to_interval(fejer_sum, stratum["fejer_sum"], tolerance)
                assert close_to_interval(fsfs_margin, stratum["fsfs_margin"], tolerance)
                assert (fsfs_margin > 0) == (stratum["fsfs_status"] == "true")
                primitive_total = 0.0
                by_m = {record["m"]: record for record in stratum["primitive_classes"]}
                for m, record in by_m.items():
                    contribution = 0.0
                    u = m
                    while u < R:
                        weight = 1 - u / R
                        contribution += weight * sum(
                            math.cos(2 * math.pi * beta0 * u * q) for q in denominators
                        )
                        u *= 10
                    assert close_to_interval(contribution, record["contribution"], tolerance)
                    primitive_total += contribution
                    checked_classes += 1
                apc_threshold = ell / (8 * R * delta * delta) - ell / 2
                apc_margin = primitive_total - apc_threshold
                assert close_to_interval(primitive_total, stratum["primitive_total"], tolerance)
                assert close_to_interval(apc_margin, stratum["apc_margin"], tolerance)
                assert (apc_margin > 0) == (stratum["apc_status"] == "true")
                boundary = 0.0
                common_depth = witness["common_depth"]
                for pair_ell in range(1, common_depth):
                    for j in range(pair_ell):
                        q = 10**pair_ell - 10**j
                        if not joint_good(beta0, beta1, D, U, q):
                            boundary += fejer(beta0 * q, R) * fejer(beta1 * q, R)
                assert close_to_interval(boundary, stratum["boundary_loss"]["enclosure"], tolerance)
    print(
        "T50 independent naive agreement passed: "
        f"{checked_candidates} candidates, {checked_strata} strata, "
        f"and {checked_classes} primitive classes."
    )


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--config", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    check(args.config, args.output)


if __name__ == "__main__":
    main()
