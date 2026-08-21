#!/usr/bin/env python3
"""Exact finite T14 successor-splitting experiment for T20."""

from __future__ import annotations

import argparse
import bisect
import hashlib
import json
import shutil
from collections import Counter, defaultdict
from fractions import Fraction
from pathlib import Path


def frac_json(x: Fraction) -> list[int]:
    return [x.numerator, x.denominator]


def as_frac(value: list[int]) -> Fraction:
    return Fraction(value[0], value[1])


def sha256(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1 << 20), b""):
            h.update(block)
    return h.hexdigest()


def iid_digits(length: int, seed: bytes) -> str:
    out: list[str] = []
    counter = 0
    while len(out) < length:
        block = hashlib.sha256(seed + counter.to_bytes(8, "big")).digest()
        counter += 1
        for byte in block:
            if byte < 250:
                out.append(chr(48 + byte % 10))
                if len(out) == length:
                    break
    return "".join(out)


def champernowne_digits(length: int) -> str:
    parts: list[str] = []
    size = 0
    value = 1
    while size < length:
        text = str(value)
        parts.append(text)
        size += len(text)
        value += 1
    return "".join(parts)[:length]


def load_datasets(config: dict, pi_path: Path) -> tuple[dict[str, str], dict]:
    if sha256(pi_path) != config["pi_digits_sha256"]:
        raise ValueError("pi_digits.txt does not have the T17-certified hash")
    raw = pi_path.read_bytes()
    if len(raw) != config["pi_digits_bytes"] or not raw.endswith(b"\n"):
        raise ValueError("unexpected T17 digit-file framing")
    pi_digits = raw[:-1].decode("ascii")
    if len(pi_digits) != config["pi_digits_fraction_count"] or not pi_digits.isdigit():
        raise ValueError("unexpected T17 digit payload")
    needed = max(config["checkpoints"]) + config["max_depth"]
    datasets = {
        "pi": pi_digits,
        "seeded_iid": iid_digits(needed, config["iid_seed_ascii"].encode("ascii")),
        "champernowne": champernowne_digits(needed),
    }
    pins = {}
    for name, digits in datasets.items():
        used = digits[:needed].encode("ascii")
        pins[name] = {
            "used_digits": needed,
            "used_prefix_sha256": hashlib.sha256(used).hexdigest(),
        }
    pins["pi"]["complete_file_sha256"] = config["pi_digits_sha256"]
    return datasets, pins


def parent_statistics(digits: str, level: int, cutoff: int) -> list[tuple[int, tuple[int, ...]]]:
    counts: dict[str, list[int]] = {}
    for start in range(cutoff):
        parent = digits[start : start + level]
        successor = ord(digits[start + level]) - 48
        if parent not in counts:
            counts[parent] = [0] * 10
        counts[parent][successor] += 1
    result = []
    for successor_counts in counts.values():
        total = sum(successor_counts)
        result.append((total, tuple(successor_counts)))
    return result


def split(parent: tuple[int, tuple[int, ...]], eta: Fraction) -> bool:
    total, successors = parent
    second = sorted(successors, reverse=True)[1]
    return second * eta.denominator >= eta.numerator * total


def dominant(parent: tuple[int, tuple[int, ...]], eta: Fraction) -> bool:
    total, successors = parent
    maximum = max(successors)
    # max/total >= 1-9*eta, checked without division.
    return maximum * eta.denominator >= (eta.denominator - 9 * eta.numerator) * total


def row_record(digits: str, dataset: str, cutoff: int, level: int) -> tuple[dict, dict]:
    parents = parent_statistics(digits, level, cutoff)
    energy = sum(total * total for total, _ in parents)
    successor_energy = sum(count * count for _, counts in parents for count in counts)
    child_counts = Counter(digits[start : start + level + 1] for start in range(cutoff))
    child_energy = sum(count * count for count in child_counts.values())
    boundaries = {
        Fraction(sorted(counts, reverse=True)[1], total)
        for total, counts in parents
        if sorted(counts, reverse=True)[1] > 0
        and Fraction(sorted(counts, reverse=True)[1], total) < Fraction(1, 10)
    }
    boundaries.add(Fraction(1, 10))
    cells = []
    lower = Fraction(0)
    for upper in sorted(boundaries):
        split_energy = sum(total * total for total, counts in parents if split((total, counts), upper))
        dominant_energy = sum(
            total * total for total, counts in parents if dominant((total, counts), upper)
        )
        cap = Fraction(split_energy, energy)
        cells.append(
            {
                "eta_lower_exclusive": frac_json(lower),
                "eta_upper_inclusive": frac_json(upper),
                "split_energy": split_energy,
                "dominant_energy": dominant_energy,
                "mu_cap": frac_json(cap),
                "mu_cap_attained_in_T14_domain": 0 < cap < 1,
                "t14_boundary_lhs": cap.numerator * energy,
                "t14_boundary_rhs": cap.denominator * split_energy,
            }
        )
        lower = upper
    public = {
        "dataset": dataset,
        "cutoff": cutoff,
        "level": level,
        "parent_fibers": len(parents),
        "energy": energy,
        "successor_energy": successor_energy,
        "child_energy": child_energy,
        "t9_refinement_equal": successor_energy == child_energy,
        "pareto_cells": cells,
    }
    internal = {
        "boundaries": [as_frac(cell["eta_upper_inclusive"]) for cell in cells],
        "cells": cells,
    }
    return public, internal


def cell_at(row: dict, eta: Fraction) -> dict:
    index = bisect.bisect_left(row["boundaries"], eta)
    if index == len(row["boundaries"]):
        raise ValueError("eta outside row envelope")
    return row["cells"][index]


def better_state(left, right):
    if left is None:
        return right
    if right is None:
        return left
    if left[0] != right[0]:
        return left if left[0] > right[0] else right
    return left if left[1] < right[1] else right


def optimal_subsequence(scores: list[Fraction], length: int) -> tuple[Fraction, tuple[int, ...]]:
    # DP state is (largest achievable bottleneck, lexicographically first indices).
    dp: list[tuple[Fraction, tuple[int, ...]] | None] = [None] * (length + 1)
    dp[0] = (Fraction(10**9), ())
    for index, score in enumerate(scores):
        new = list(dp)
        for used in range(length):
            if dp[used] is None:
                continue
            candidate = (min(dp[used][0], score), dp[used][1] + (index,))
            new[used + 1] = better_state(new[used + 1], candidate)
        dp = new
    if dp[length] is None:
        raise ValueError("subsequence length exceeds checkpoint count")
    return dp[length]


def local_frontier(points: list[dict]) -> list[dict]:
    # eta is fixed. Maximize mu boundary and d; equal boundaries retain the
    # lexicographically first deterministic witness.
    ordered = sorted(
        points,
        key=lambda point: (
            -as_frac(point["mu_upper"]),
            -as_frac(point["d"]),
            tuple(point["subsequence"]),
        ),
    )
    result = []
    best_d: Fraction | None = None
    for point in ordered:
        d = as_frac(point["d"])
        if best_d is not None and best_d >= d:
            continue
        result.append(point)
        best_d = d
    return result


def skyline_dominates(skyline: list[tuple[Fraction, Fraction]], mu: Fraction, d: Fraction) -> bool:
    return any(old_mu >= mu and old_d >= d for old_mu, old_d in skyline)


def add_skyline(skyline: list[tuple[Fraction, Fraction]], mu: Fraction, d: Fraction) -> None:
    if skyline_dominates(skyline, mu, d):
        return
    skyline[:] = [
        (old_mu, old_d)
        for old_mu, old_d in skyline
        if not (mu >= old_mu and d >= old_d)
    ]
    skyline.append((mu, d))


def global_affine_frontier(
    dataset: str,
    config: dict,
    rows: dict[tuple[int, int], dict],
) -> tuple[list[dict], dict]:
    checkpoints = config["optimization_checkpoints"]
    max_depth = config["max_depth"]
    m0 = config["affine_m0"]
    B = as_frac(config["affine_B"])
    sequence_length = config["sequence_length"]
    eta_boundaries = sorted(
        {
            boundary
            for cutoff in checkpoints
            for level in range(max_depth)
            for boundary in rows[(cutoff, level)]["boundaries"]
        }
    )
    eta_groups: list[tuple[Fraction, Fraction, list[dict]]] = []
    eta_lower = Fraction(0)
    candidate_count = 0
    for eta in eta_boundaries:
        caps = {
            as_frac(cell_at(rows[(cutoff, level)], eta)["mu_cap"])
            for cutoff in checkpoints
            for level in range(max_depth)
        }
        positive_caps = sorted(cap for cap in caps if 0 < cap < 1)
        candidates: list[tuple[Fraction, Fraction, bool]] = []
        previous = Fraction(0)
        for cap in positive_caps:
            candidates.append((previous, cap, True))
            previous = cap
        if Fraction(1) in caps:
            candidates.append((previous, Fraction(1), False))
        points = []
        for mu_lower, mu_upper, inclusive in candidates:
            mu = mu_upper if inclusive else (mu_lower + mu_upper) / 2
            checkpoint_counts: dict[int, list[int]] = {}
            scores = []
            for cutoff in checkpoints:
                level_splits = [
                    as_frac(cell_at(rows[(cutoff, level)], eta)["mu_cap"]) >= mu
                    for level in range(max_depth)
                ]
                counts = [sum(level_splits[:m]) for m in range(max_depth + 1)]
                checkpoint_counts[cutoff] = counts
                scores.append(min((Fraction(counts[m]) + B) / m for m in range(m0, max_depth + 1)))
            d, selected_indices = optimal_subsequence(scores, sequence_length)
            selected = [checkpoints[index] for index in selected_indices]
            margins = []
            obstructions = []
            for cutoff in selected:
                for m in range(m0, max_depth + 1):
                    margin = Fraction(checkpoint_counts[cutoff][m]) + B - d * m
                    margins.append(
                        {
                            "cutoff": cutoff,
                            "depth": m,
                            "splitting_count": checkpoint_counts[cutoff][m],
                            "margin": frac_json(margin),
                        }
                    )
                for level in range(max_depth):
                    cell = cell_at(rows[(cutoff, level)], eta)
                    energy = cell["_energy"]
                    split_energy = cell["split_energy"]
                    if mu.numerator * energy > mu.denominator * split_energy:
                        dominant_energy = cell["dominant_energy"]
                        lhs = (mu.denominator - mu.numerator) * energy
                        rhs = mu.denominator * dominant_energy
                        obstructions.append(
                            {
                                "cutoff": cutoff,
                                "level": level,
                                "energy": energy,
                                "split_energy": split_energy,
                                "dominant_energy": dominant_energy,
                                "splitting_failure_lhs": mu.numerator * energy,
                                "splitting_failure_rhs": mu.denominator * split_energy,
                                "dominance_lhs": lhs,
                                "dominance_rhs": rhs,
                                "strict_dominance_verified": lhs < rhs,
                            }
                        )
            point = {
                "eta_lower_exclusive": frac_json(eta_lower),
                "eta_upper_inclusive": frac_json(eta),
                "mu_lower_exclusive": frac_json(mu_lower),
                "mu_upper": frac_json(mu_upper),
                "mu_upper_inclusive": inclusive,
                "mu_witness": frac_json(mu),
                "d": frac_json(d),
                "B": frac_json(B),
                "subsequence": selected,
                "affine_margins": margins,
                "dominant_obstructions": obstructions,
            }
            points.append(point)
            candidate_count += 1
        eta_groups.append((eta_lower, eta, local_frontier(points)))
        eta_lower = eta
    skyline: list[tuple[Fraction, Fraction]] = []
    retained: list[dict] = []
    for _lower, _upper, points in reversed(eta_groups):
        survivors = []
        for point in points:
            mu = as_frac(point["mu_upper"])
            d = as_frac(point["d"])
            if not skyline_dominates(skyline, mu, d):
                survivors.append(point)
        retained.extend(survivors)
        for point in points:
            add_skyline(skyline, as_frac(point["mu_upper"]), as_frac(point["d"]))
    retained.sort(
        key=lambda point: (
            as_frac(point["eta_upper_inclusive"]),
            as_frac(point["mu_upper"]),
            as_frac(point["d"]),
        )
    )
    stats = {
        "dataset": dataset,
        "eta_cells": len(eta_boundaries),
        "parameter_cells_evaluated": candidate_count,
        "pareto_points_retained": len(retained),
    }
    return retained, stats


def clean_internal_cells(rows: list[dict]) -> None:
    for row in rows:
        for cell in row["pareto_cells"]:
            cell.pop("_energy", None)


def build_report(result: dict) -> str:
    config = result["parameters"]
    lines = [
        "# T20 exact successor-splitting Pareto experiment",
        "",
        "Status: `experiment` (finite heuristic evidence only).",
        "",
        "## Scope and normalization",
        "",
        "The immutable canonical statement is retained byte-for-byte with SHA-256",
        f"`{result['canonical_statement_sha256']}`. Canonical A1 keeps its literal",
        "quantifiers: every A, every sufficiently large n, and an N depending on A,n.",
        "This experiment instead measures the bounded A14 sibling on declared decimal",
        "prefixes. The seeded-iid and Champernowne rows are controls, not claims about pi.",
        "`STATEMENT_ALIGNMENT.md` maps every acceptance clause to the experiment files.",
        "The accepted T9/T14 Lean sources are hash-pinned semantic dependencies, are not",
        "enclosed as T20 theorem artifacts, and no Lean theorem is claimed by T20.",
        "",
        "For a level, parent occupancy c and its ten successor occupancies c_e are",
        "computed as integers. A parent is eta-split exactly when its second-largest",
        "c_e satisfies eta*c <= c_e. The row split mass S is the sum of c^2 over",
        "split parents and E=sum c^2. Thus T14's finite weighted condition is exactly",
        "mu*E <= S. Every stored boundary is reduced rational data and the verifier",
        "checks numerator(mu)*E <= denominator(mu)*S by integer cross-multiplication.",
        "Open mu=1 boundaries are stored as open and have a strict rational witness.",
        "",
        "## Declared finite ranges",
        "",
        f"- Checkpoints: `{config['checkpoints']}`.",
        f"- Levels: `0 <= l < {config['max_depth']}`; affine depths: `{config['affine_m0']} <= m <= {config['max_depth']}`.",
        f"- Optimized increasing subsequences have length `{config['sequence_length']}` from `{config['optimization_checkpoints']}`.",
        f"- Affine intercept: `B={config['affine_B'][0]}/{config['affine_B'][1]}`.",
        "- Eta domain: `0 < eta <= 1/10`; mu domain: `0 < mu < 1`.",
        "",
        "## Completeness of the finite envelope",
        "",
        "For each measured row, split membership changes only when eta crosses the",
        "exact ratio (second-largest successor count)/c. The output lists every such",
        "cell below 1/10 plus the terminal 1/10 cell. Within a cell, S/E is the exact",
        "mu cap. The global calculation takes the union of all row eta breakpoints and",
        "all resulting mu caps, so splitting counts are constant inside every enumerated",
        "parameter cell. It evaluates every cell and removes only coordinatewise dominated",
        "(eta,mu,d) cells. This is a complete finite rational Pareto envelope, not T16's grid.",
        "",
        "For each parameter cell, exact dynamic programming selects the increasing",
        "checkpoint subsequence maximizing the common d in d*m-B <= splitting_count(m).",
        "All retained margins and every T9 weighted dominant-successor obstruction are",
        "stored in `raw_output.json` as integers or reduced numerator-denominator pairs.",
        "",
        "## Results",
        "",
    ]
    for dataset in result["datasets"]:
        stats = dataset["frontier_stats"]
        rows = dataset["rows"]
        refinement_ok = sum(row["t9_refinement_equal"] for row in rows)
        lines.extend(
            [
                f"### {dataset['name']}",
                "",
                f"Measured `{len(rows)}` rows; exact T9 refinement held on `{refinement_ok}`/`{len(rows)}` rows.",
                f"Evaluated `{stats['parameter_cells_evaluated']}` global parameter cells over `{stats['eta_cells']}` eta cells; retained `{stats['pareto_points_retained']}` Pareto points.",
            ]
        )
        if dataset["global_affine_pareto"]:
            point = max(
                dataset["global_affine_pareto"],
                key=lambda p: (as_frac(p["d"]), as_frac(p["eta_upper_inclusive"]), as_frac(p["mu_upper"])),
            )
            lines.extend(
                [
                    "One maximum-d retained point (not privileged as a theorem target):",
                    f"`eta={point['eta_upper_inclusive'][0]}/{point['eta_upper_inclusive'][1]}`, "
                    f"`mu-boundary={point['mu_upper'][0]}/{point['mu_upper'][1]}` "
                    f"(`inclusive={str(point['mu_upper_inclusive']).lower()}`), "
                    f"`d={point['d'][0]}/{point['d'][1]}`, checkpoints `{point['subsequence']}`.",
                    "",
                ]
            )
    total_rows = sum(len(dataset["rows"]) for dataset in result["datasets"])
    total_cells = sum(
        len(row["pareto_cells"])
        for dataset in result["datasets"]
        for row in dataset["rows"]
    )
    total_points = sum(len(dataset["global_affine_pareto"]) for dataset in result["datasets"])
    total_obstructions = sum(
        len(point["dominant_obstructions"])
        for dataset in result["datasets"]
        for point in dataset["global_affine_pareto"]
    )
    lines.extend(
        [
            "## Replay and independent check",
            "",
            "Run `bash run_experiment.sh` in this directory. It verifies pinned hashes,",
            "regenerates and byte-compares the JSON and report, checks all exact inequalities,",
            "independently re-enumerates the complete global nondominated frontier,",
            "and runs a separately implemented naive pair-counting oracle on the declared",
            "small prefixes. Requirements are Python 3.11+ and standard Unix `bash`,",
            "`sha256sum`, `cmp`, and `mktemp`; there are no third-party packages or network calls.",
            "Declared budget: 300 seconds and 4 GiB RAM.",
            "",
            f"The retained output contains `{total_rows}` measured rows, `{total_cells}` row-envelope cells, `{total_points}` global Pareto points, and `{total_obstructions}` explicit dominant-obstruction rows.",
            "",
            "## Limitation",
            "",
            "Every conclusion here is finite heuristic evidence. The calculation neither",
            "proves nor refutes C2, and it neither proves nor refutes canonical A1. It does",
            "not establish normality, an asymptotic positive density, a coherent weak limit,",
            "or any statement beyond the declared finite prefixes and controls.",
            "",
        ]
    )
    return "\n".join(lines)


def run(config_path: Path, pi_path: Path, output_path: Path, report_path: Path) -> None:
    config = json.loads(config_path.read_text(encoding="utf-8"))
    datasets, input_pins = load_datasets(config, pi_path)
    result = {
        "format": "t20-exact-pareto-output-v1",
        "canonical_statement_sha256": config["canonical_sha256"],
        "parameters": config,
        "input_pins": input_pins,
        "datasets": [],
        "claims": {
            "evidence_label": "experiment",
            "finite_heuristic_only": True,
            "proves_or_refutes_C2": False,
            "proves_or_refutes_canonical_A1": False,
        },
    }
    for dataset_name in ("pi", "seeded_iid", "champernowne"):
        digits = datasets[dataset_name]
        public_rows = []
        internal_rows = {}
        for cutoff in config["checkpoints"]:
            for level in range(config["max_depth"]):
                public, internal = row_record(digits, dataset_name, cutoff, level)
                for cell in internal["cells"]:
                    cell["_energy"] = public["energy"]
                public_rows.append(public)
                internal_rows[(cutoff, level)] = internal
        frontier, stats = global_affine_frontier(dataset_name, config, internal_rows)
        clean_internal_cells(public_rows)
        result["datasets"].append(
            {
                "name": dataset_name,
                "rows": public_rows,
                "frontier_stats": stats,
                "global_affine_pareto": frontier,
            }
        )
    output_path.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    report_path.write_text(build_report(result), encoding="utf-8")


def snapshot(source: Path, destination: Path, expected_hash: str) -> None:
    if sha256(source) != expected_hash:
        raise ValueError(f"snapshot source hash mismatch: {source}")
    shutil.copyfile(source, destination)
    if sha256(destination) != expected_hash:
        raise ValueError(f"snapshot destination hash mismatch: {destination}")


def main() -> None:
    parser = argparse.ArgumentParser()
    subparsers = parser.add_subparsers(dest="command", required=True)
    run_parser = subparsers.add_parser("run")
    run_parser.add_argument("--config", type=Path, required=True)
    run_parser.add_argument("--pi-digits", type=Path, required=True)
    run_parser.add_argument("--output", type=Path, required=True)
    run_parser.add_argument("--report", type=Path, required=True)
    snapshot_parser = subparsers.add_parser("snapshot")
    snapshot_parser.add_argument("--source", type=Path, required=True)
    snapshot_parser.add_argument("--destination", type=Path, required=True)
    snapshot_parser.add_argument("--sha256", required=True)
    args = parser.parse_args()
    if args.command == "run":
        run(args.config, args.pi_digits, args.output, args.report)
    else:
        snapshot(args.source, args.destination, args.sha256)


if __name__ == "__main__":
    main()
