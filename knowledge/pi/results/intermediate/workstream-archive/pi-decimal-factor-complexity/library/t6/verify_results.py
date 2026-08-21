#!/usr/bin/env python3
"""Independently verify every exact T6 row with direct byte-slice counting."""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
from collections import Counter
from decimal import Decimal, localcontext
from fractions import Fraction
from pathlib import Path


PI_COUNT = 1_000_011
PI_SHA256 = "3d11a0e07b0fe7fbc6cb78dbc99afbeec8cfb277c64a559463822da236aff779"
STATEMENT_SHA256 = "e2b6c9375936a97fe6cdd10c3f014613267f3c491935b536c6ec016c5f501e43"
PRIMARY_URL = "https://files.pilookup.com/pi/2000000.txt"
PRIMARY_SHA256 = "f533022c5d2a21db137b158345c6276355e89b301d76d1531c1ca26f9a026612"
CROSSCHECK_URL = "https://www.angio.net/pi/digits/pi1000000.txt"
CROSSCHECK_SHA256 = "b50ea720602439dcb8a56265b75fadfa4d0a0fbd46d9705693dde14b8a053fb0"
N_VALUES = (1_000, 10_000, 100_000, 1_000_000)
N_LENGTHS = tuple(range(1, 13))
SEEDS = {
    "control_1": 2_026_072_201,
    "control_2": 2_026_072_202,
    "control_3": 2_026_072_203,
}
OUTPUT_NAMES = ("results.json", "results.csv", "comparison.csv", "REPORT.md")
MASK64 = (1 << 64) - 1
LIMIT = (1 << 64) - ((1 << 64) % 10)


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def control_digits(seed: int) -> bytes:
    state = seed & MASK64
    digits = bytearray()
    while len(digits) < PI_COUNT:
        state = (state + 0x9E3779B97F4A7C15) & MASK64
        word = state
        word = ((word ^ (word >> 30)) * 0xBF58476D1CE4E5B9) & MASK64
        word = ((word ^ (word >> 27)) * 0x94D049BB133111EB) & MASK64
        word ^= word >> 31
        if word < LIMIT:
            digits.append(word % 10)
    return bytes(digits)


def display(value: Fraction) -> str:
    with localcontext() as context:
        context.prec = 12
        return format(Decimal(value.numerator) / Decimal(value.denominator), ".11g")


def exact_energy(digits: bytes, n: int, sample_size: int) -> int:
    multiplicities = Counter(digits[start : start + n] for start in range(sample_size))
    return sum(multiplicity * multiplicity for multiplicity in multiplicities.values())


def as_fraction(value: dict[str, int]) -> Fraction:
    return Fraction(value["numerator"], value["denominator"])


def ratio_text(value: Fraction) -> str:
    return f"{value.numerator}/{value.denominator}"


def verify_json(artifact_dir: Path, digit_path: Path) -> tuple[dict, dict[tuple[str, int, int], dict]]:
    document = json.loads((artifact_dir / "results.json").read_text(encoding="ascii"))
    expected_metadata = {
        "schema_version": 1,
        "canonical_statement_sha256": STATEMENT_SHA256,
        "classification": "experiment",
        "grid": {"N": list(N_VALUES), "n": list(N_LENGTHS)},
    }
    for field, expected in expected_metadata.items():
        if document.get(field) != expected:
            raise AssertionError(f"unexpected results.json metadata field {field}")
    if document["classification"] != "experiment" or "cannot prove or refute C1 or A1" not in document["finite_evidence_warning"]:
        raise AssertionError("finite-evidence classification is missing")
    expected_pi_metadata = {
        "count": PI_COUNT,
        "sha256": PI_SHA256,
        "hash_encoding": "ASCII fractional digits without a trailing newline",
        "primary_source": {
            "url": PRIMARY_URL,
            "download_sha256": PRIMARY_SHA256,
            "fractional_digits": 2_000_000,
        },
        "crosscheck_source": {
            "url": CROSSCHECK_URL,
            "download_sha256": CROSSCHECK_SHA256,
            "fractional_digits": 1_000_000,
            "matched_primary_fractional_digits": 1_000_000,
        },
    }
    if document.get("pi_digits") != expected_pi_metadata:
        raise AssertionError("unexpected pi source metadata")
    expected_controls_metadata = {
        "generator": "SplitMix64 with rejection above 2^64-(2^64 mod 10), then word mod 10",
        "hash_encoding": "ASCII digits without a trailing newline",
        "seed_origin": "decimal run date 20260722 followed by fixed control indices 01, 02, 03",
        "seeds": {name: f"0x{seed:016x}" for name, seed in SEEDS.items()},
    }
    if document.get("controls") != expected_controls_metadata:
        raise AssertionError("unexpected control metadata")

    pi_ascii = digit_path.read_bytes()
    if len(pi_ascii) != PI_COUNT or sha256(pi_ascii) != PI_SHA256:
        raise AssertionError("pi digit file length or hash mismatch")
    if not all(48 <= value <= 57 for value in pi_ascii):
        raise AssertionError("pi digit file contains a non-digit")
    datasets = {"pi": bytes(value - 48 for value in pi_ascii)}
    datasets.update({name: control_digits(seed) for name, seed in SEEDS.items()})

    rows = document["rows"]
    if len(rows) != 4 * len(N_LENGTHS) * len(N_VALUES):
        raise AssertionError(f"expected 192 JSON rows, got {len(rows)}")
    indexed = {(row["dataset"], row["n"], row["N"]): row for row in rows}
    if len(indexed) != len(rows):
        raise AssertionError("duplicate JSON row key")

    for dataset_name, digits in datasets.items():
        ascii_hash = sha256(bytes(value + 48 for value in digits))
        for n in N_LENGTHS:
            for sample_size in N_VALUES:
                key = (dataset_name, n, sample_size)
                row = indexed[key]
                energy = exact_energy(digits, n, sample_size)
                ratio = Fraction(sample_size**2, n * energy)
                model = Fraction(
                    sample_size * 10**n + sample_size * (sample_size - 1), 10**n
                )
                energy_over_model = Fraction(energy, 1) / model
                model_ratio = Fraction(sample_size**2, n) / model
                expected = {
                    "seed_hex": None if dataset_name == "pi" else f"0x{SEEDS[dataset_name]:016x}",
                    "digits_sha256": ascii_hash,
                    "energy": energy,
                    "R": ratio,
                    "R_decimal": display(ratio),
                    "iid_model_energy": model,
                    "energy_over_iid_model": energy_over_model,
                    "energy_over_iid_model_decimal": display(energy_over_model),
                    "iid_model_R": model_ratio,
                    "iid_model_R_decimal": display(model_ratio),
                }
                for field, value in expected.items():
                    actual = as_fraction(row[field]) if isinstance(value, Fraction) else row[field]
                    if actual != value:
                        raise AssertionError(f"JSON mismatch at {key} field {field}: {actual} != {value}")
    return document, indexed


def verify_results_csv(artifact_dir: Path, indexed: dict[tuple[str, int, int], dict]) -> None:
    with (artifact_dir / "results.csv").open(newline="", encoding="ascii") as handle:
        rows = list(csv.DictReader(handle))
    if len(rows) != 192:
        raise AssertionError(f"expected 192 results.csv rows, got {len(rows)}")
    expected_keys = set(indexed)
    actual_keys = {(row["dataset"], int(row["n"]), int(row["N"])) for row in rows}
    if actual_keys != expected_keys or len(actual_keys) != len(rows):
        raise AssertionError("results.csv does not contain each expected grid key exactly once")
    for csv_row in rows:
        key = (csv_row["dataset"], int(csv_row["n"]), int(csv_row["N"]))
        row = indexed[key]
        expected = {
            "seed_hex": row["seed_hex"] or "",
            "digits_sha256": row["digits_sha256"],
            "energy": str(row["energy"]),
            "R_numerator": str(row["R"]["numerator"]),
            "R_denominator": str(row["R"]["denominator"]),
            "R_decimal": row["R_decimal"],
            "iid_model_energy_numerator": str(row["iid_model_energy"]["numerator"]),
            "iid_model_energy_denominator": str(row["iid_model_energy"]["denominator"]),
            "energy_over_iid_model_numerator": str(row["energy_over_iid_model"]["numerator"]),
            "energy_over_iid_model_denominator": str(row["energy_over_iid_model"]["denominator"]),
            "energy_over_iid_model_decimal": row["energy_over_iid_model_decimal"],
            "iid_model_R_numerator": str(row["iid_model_R"]["numerator"]),
            "iid_model_R_denominator": str(row["iid_model_R"]["denominator"]),
            "iid_model_R_decimal": row["iid_model_R_decimal"],
        }
        for field, value in expected.items():
            if csv_row[field] != value:
                raise AssertionError(f"results.csv mismatch at {key} field {field}")


def parse_ratio(text: str) -> Fraction:
    numerator, denominator = text.split("/")
    return Fraction(int(numerator), int(denominator))


def verify_comparison_csv(artifact_dir: Path, indexed: dict[tuple[str, int, int], dict]) -> None:
    with (artifact_dir / "comparison.csv").open(newline="", encoding="ascii") as handle:
        rows = list(csv.DictReader(handle))
    if len(rows) != 48:
        raise AssertionError(f"expected 48 comparison.csv rows, got {len(rows)}")
    expected_keys = {(n, sample_size) for n in N_LENGTHS for sample_size in N_VALUES}
    actual_keys = {(int(row["n"]), int(row["N"])) for row in rows}
    if actual_keys != expected_keys or len(actual_keys) != len(rows):
        raise AssertionError("comparison.csv does not contain each expected grid key exactly once")
    for row in rows:
        n, sample_size = int(row["n"]), int(row["N"])
        pi_energy = int(indexed[("pi", n, sample_size)]["energy"])
        controls = [int(indexed[(name, n, sample_size)]["energy"]) for name in SEEDS]
        mean = Fraction(sum(controls), 3)
        model = Fraction(sample_size * 10**n + sample_size * (sample_size - 1), 10**n)
        expected = {
            "iid_model_energy": model,
            "pi_energy": pi_energy,
            "control_1_energy": controls[0],
            "control_2_energy": controls[1],
            "control_3_energy": controls[2],
            "control_mean_energy": mean,
            "pi_over_iid_model": Fraction(pi_energy, 1) / model,
            "control_mean_over_iid_model": mean / model,
            "pi_over_control_mean": Fraction(pi_energy, 1) / mean,
            "pi_R": Fraction(sample_size**2, n * pi_energy),
        }
        for field, value in expected.items():
            actual = int(row[field]) if isinstance(value, int) else parse_ratio(row[field])
            if actual != value:
                raise AssertionError(f"comparison.csv mismatch at n={n}, N={sample_size}, field {field}")


def verify_report_table(artifact_dir: Path, indexed: dict[tuple[str, int, int], dict]) -> None:
    lines = (artifact_dir / "REPORT.md").read_text(encoding="ascii").splitlines()
    table_rows = [line for line in lines if line.startswith("| ") and line[2:3].isdigit()]
    if len(table_rows) != 12:
        raise AssertionError(f"expected 12 report data rows, got {len(table_rows)}")
    report_ns = [int(line.split("|", 2)[1].strip()) for line in table_rows]
    if set(report_ns) != set(N_LENGTHS) or len(set(report_ns)) != len(report_ns):
        raise AssertionError("REPORT.md does not contain each n exactly once")
    for line in table_rows:
        cells = [cell.strip() for cell in line.strip("|").split("|")]
        n = int(cells[0])
        pi_row = indexed[("pi", n, 1_000_000)]
        pi_energy = int(pi_row["energy"])
        controls = [int(indexed[(name, n, 1_000_000)]["energy"]) for name in SEEDS]
        model = Fraction(1_000_000 * 10**n + 1_000_000 * 999_999, 10**n)
        expected = [
            str(n),
            str(pi_energy),
            ", ".join(str(value) for value in controls),
            ratio_text(Fraction(pi_energy, 1) / model),
            ratio_text(Fraction(sum(controls), 3) / model),
            ratio_text(Fraction(1_000_000**2, n * pi_energy)),
        ]
        if cells != expected:
            raise AssertionError(f"REPORT.md table mismatch at n={n}: {cells} != {expected}")


def verify_report_boundaries(artifact_dir: Path) -> None:
    report = (artifact_dir / "REPORT.md").read_text(encoding="ascii")
    required = (
        "EXPERIMENT ONLY",
        "cannot prove or refute sibling conjecture C1 or",
        "canonical statement A1",
        "No universal claim about pi follows",
        "same grid",
        "0.9 <= E/E_iid <= 1.1",
        "for every real `C>0`",
    )
    for phrase in required:
        if phrase not in report:
            raise AssertionError(f"REPORT.md is missing required boundary text: {phrase}")


def verify_checksums(artifact_dir: Path, checksum_path: Path) -> None:
    expected_by_name = {}
    for line in checksum_path.read_text(encoding="ascii").splitlines():
        expected, relative = line.split("  ", 1)
        expected_by_name[relative] = expected
    for relative in OUTPUT_NAMES:
        if relative not in expected_by_name:
            raise AssertionError(f"checksum manifest has no entry for {relative}")
        expected = expected_by_name[relative]
        actual = sha256((artifact_dir / relative).read_bytes())
        if actual != expected:
            raise AssertionError(f"checksum mismatch for {relative}")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--artifact-dir", type=Path, default=Path("."))
    parser.add_argument("--digits", type=Path, required=True)
    parser.add_argument("--checksums", type=Path, required=True)
    args = parser.parse_args()
    _document, indexed = verify_json(args.artifact_dir, args.digits)
    verify_results_csv(args.artifact_dir, indexed)
    verify_comparison_csv(args.artifact_dir, indexed)
    verify_report_table(args.artifact_dir, indexed)
    verify_report_boundaries(args.artifact_dir)
    verify_checksums(args.artifact_dir, args.checksums)
    print("verified: complete exact grids (192 JSON/CSV, 48 comparison, 12 report) and output checksums")


if __name__ == "__main__":
    main()
