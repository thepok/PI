#!/usr/bin/env python3
"""Reproduce the T6 finite collision-energy experiment using only the stdlib."""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
import tempfile
import urllib.request
from collections import Counter
from decimal import Decimal, localcontext
from fractions import Fraction
from pathlib import Path


STATEMENT_SHA256 = "e2b6c9375936a97fe6cdd10c3f014613267f3c491935b536c6ec016c5f501e43"
PRIMARY_URL = "https://files.pilookup.com/pi/2000000.txt"
PRIMARY_SHA256 = "f533022c5d2a21db137b158345c6276355e89b301d76d1531c1ca26f9a026612"
CROSSCHECK_URL = "https://www.angio.net/pi/digits/pi1000000.txt"
CROSSCHECK_SHA256 = "b50ea720602439dcb8a56265b75fadfa4d0a0fbd46d9705693dde14b8a053fb0"
PI_DIGIT_COUNT = 1_000_011
PI_DIGITS_SHA256 = "3d11a0e07b0fe7fbc6cb78dbc99afbeec8cfb277c64a559463822da236aff779"
N_VALUES = (1_000, 10_000, 100_000, 1_000_000)
N_LENGTHS = tuple(range(1, 13))
CONTROL_SEEDS = (
    ("control_1", 2_026_072_201),
    ("control_2", 2_026_072_202),
    ("control_3", 2_026_072_203),
)
MASK64 = (1 << 64) - 1
UNIFORM_LIMIT_10 = (1 << 64) - ((1 << 64) % 10)


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def ascii_digit_sha256(digits: bytes) -> str:
    return sha256_bytes(bytes(value + 48 for value in digits))


def read_verified(path: Path, expected_sha256: str) -> bytes:
    data = path.read_bytes()
    actual = sha256_bytes(data)
    if actual != expected_sha256:
        raise ValueError(f"SHA-256 mismatch for {path}: expected {expected_sha256}, got {actual}")
    return data


def download(url: str, destination: Path) -> None:
    request = urllib.request.Request(url, headers={"User-Agent": "AllMath-T6-reproducer/1"})
    with urllib.request.urlopen(request, timeout=60) as response:
        destination.write_bytes(response.read())


def normalized_pi_source(data: bytes, fractional_count: int, label: str) -> bytes:
    normalized = data.rstrip(b"\r\n")
    if not normalized.startswith(b"3."):
        raise ValueError(f"{label} does not start with '3.'")
    fractional = normalized[2:]
    if len(fractional) != fractional_count:
        raise ValueError(
            f"{label} has {len(fractional)} fractional digits, expected {fractional_count}"
        )
    if not all(48 <= value <= 57 for value in fractional):
        raise ValueError(f"{label} contains non-decimal bytes")
    return normalized


def prepare_digits(output: Path, primary_path: Path | None, crosscheck_path: Path | None) -> None:
    with tempfile.TemporaryDirectory(prefix="allmath-t6-sources-") as temporary:
        temp_dir = Path(temporary)
        if primary_path is None:
            primary_path = temp_dir / "pilookup-2000000.txt"
            download(PRIMARY_URL, primary_path)
        if crosscheck_path is None:
            crosscheck_path = temp_dir / "angio-1000000.txt"
            download(CROSSCHECK_URL, crosscheck_path)

        primary_raw = read_verified(primary_path, PRIMARY_SHA256)
        crosscheck_raw = read_verified(crosscheck_path, CROSSCHECK_SHA256)
        primary = normalized_pi_source(primary_raw, 2_000_000, "PILookup primary")
        crosscheck = normalized_pi_source(crosscheck_raw, 1_000_000, "Angio cross-check")
        if primary[: len(crosscheck)] != crosscheck:
            raise ValueError("the primary and second-host sources disagree in their overlap")

        fractional = primary[2 : 2 + PI_DIGIT_COUNT]
        actual = sha256_bytes(fractional)
        if actual != PI_DIGITS_SHA256:
            raise ValueError(
                f"derived fractional-digit SHA-256 mismatch: expected {PI_DIGITS_SHA256}, got {actual}"
            )
        output.parent.mkdir(parents=True, exist_ok=True)
        output.write_bytes(fractional)
        print(f"wrote {len(fractional)} fractional digits to {output}")
        print(f"sha256 {actual}")
        print("cross-check matched for the first 1000000 fractional digits")


def splitmix64_digits(seed: int, count: int) -> bytes:
    """Return deterministic uniform decimal digits using rejection over SplitMix64 words."""
    state = seed & MASK64
    result = bytearray()
    while len(result) < count:
        state = (state + 0x9E3779B97F4A7C15) & MASK64
        value = state
        value = ((value ^ (value >> 30)) * 0xBF58476D1CE4E5B9) & MASK64
        value = ((value ^ (value >> 27)) * 0x94D049BB133111EB) & MASK64
        value ^= value >> 31
        if value < UNIFORM_LIMIT_10:
            result.append(value % 10)
    return bytes(result)


def load_pi_digits(path: Path) -> bytes:
    raw = read_verified(path, PI_DIGITS_SHA256)
    if len(raw) != PI_DIGIT_COUNT or not all(48 <= value <= 57 for value in raw):
        raise ValueError(f"{path} must contain exactly {PI_DIGIT_COUNT} ASCII decimal digits")
    return bytes(value - 48 for value in raw)


def collision_energies(digits: bytes, n: int) -> dict[int, int]:
    max_n = max(N_VALUES)
    if len(digits) < max_n + n - 1:
        raise ValueError(f"need at least {max_n + n - 1} digits for n={n}")
    code = 0
    for digit in digits[:n]:
        code = code * 10 + digit
    suffix_modulus = 10 ** (n - 1)
    multiplicities: Counter[int] = Counter()
    energy = 0
    answers: dict[int, int] = {}
    checkpoints = set(N_VALUES)
    for start in range(max_n):
        old_multiplicity = multiplicities[code]
        energy += 2 * old_multiplicity + 1
        multiplicities[code] = old_multiplicity + 1
        starts_seen = start + 1
        if starts_seen in checkpoints:
            answers[starts_seen] = energy
        if starts_seen < max_n:
            code = (code % suffix_modulus) * 10 + digits[start + n]
    return answers


def fraction_fields(value: Fraction) -> dict[str, int]:
    return {"numerator": value.numerator, "denominator": value.denominator}


def decimal_string(value: Fraction, significant_digits: int = 12) -> str:
    with localcontext() as context:
        context.prec = significant_digits
        return format(Decimal(value.numerator) / Decimal(value.denominator), ".11g")


def make_rows(datasets: list[tuple[str, int | None, bytes, str]]) -> list[dict[str, object]]:
    rows: list[dict[str, object]] = []
    for dataset_name, seed, digits, digits_hash in datasets:
        for n in N_LENGTHS:
            energies = collision_energies(digits, n)
            alphabet_size = 10**n
            for sample_size in N_VALUES:
                energy = energies[sample_size]
                ratio = Fraction(sample_size**2, n * energy)
                model_energy = Fraction(
                    sample_size * alphabet_size + sample_size * (sample_size - 1),
                    alphabet_size,
                )
                energy_over_model = Fraction(energy, 1) / model_energy
                model_ratio = Fraction(sample_size**2, n) / model_energy
                rows.append(
                    {
                        "dataset": dataset_name,
                        "seed_hex": None if seed is None else f"0x{seed:016x}",
                        "digits_sha256": digits_hash,
                        "n": n,
                        "N": sample_size,
                        "energy": energy,
                        "R": fraction_fields(ratio),
                        "R_decimal": decimal_string(ratio),
                        "iid_model_energy": fraction_fields(model_energy),
                        "energy_over_iid_model": fraction_fields(energy_over_model),
                        "energy_over_iid_model_decimal": decimal_string(energy_over_model),
                        "iid_model_R": fraction_fields(model_ratio),
                        "iid_model_R_decimal": decimal_string(model_ratio),
                    }
                )
    return rows


def write_results_csv(rows: list[dict[str, object]], output: Path) -> None:
    fields = (
        "dataset",
        "seed_hex",
        "digits_sha256",
        "n",
        "N",
        "energy",
        "R_numerator",
        "R_denominator",
        "R_decimal",
        "iid_model_energy_numerator",
        "iid_model_energy_denominator",
        "energy_over_iid_model_numerator",
        "energy_over_iid_model_denominator",
        "energy_over_iid_model_decimal",
        "iid_model_R_numerator",
        "iid_model_R_denominator",
        "iid_model_R_decimal",
    )
    with output.open("w", newline="", encoding="ascii") as handle:
        writer = csv.DictWriter(handle, fieldnames=fields, lineterminator="\n")
        writer.writeheader()
        for row in rows:
            writer.writerow(
                {
                    "dataset": row["dataset"],
                    "seed_hex": row["seed_hex"] or "",
                    "digits_sha256": row["digits_sha256"],
                    "n": row["n"],
                    "N": row["N"],
                    "energy": row["energy"],
                    "R_numerator": row["R"]["numerator"],
                    "R_denominator": row["R"]["denominator"],
                    "R_decimal": row["R_decimal"],
                    "iid_model_energy_numerator": row["iid_model_energy"]["numerator"],
                    "iid_model_energy_denominator": row["iid_model_energy"]["denominator"],
                    "energy_over_iid_model_numerator": row["energy_over_iid_model"]["numerator"],
                    "energy_over_iid_model_denominator": row["energy_over_iid_model"]["denominator"],
                    "energy_over_iid_model_decimal": row["energy_over_iid_model_decimal"],
                    "iid_model_R_numerator": row["iid_model_R"]["numerator"],
                    "iid_model_R_denominator": row["iid_model_R"]["denominator"],
                    "iid_model_R_decimal": row["iid_model_R_decimal"],
                }
            )


def row_index(rows: list[dict[str, object]]) -> dict[tuple[str, int, int], dict[str, object]]:
    return {(str(row["dataset"]), int(row["n"]), int(row["N"])): row for row in rows}


def make_comparisons(rows: list[dict[str, object]]) -> list[dict[str, object]]:
    indexed = row_index(rows)
    comparisons: list[dict[str, object]] = []
    control_names = tuple(name for name, _seed in CONTROL_SEEDS)
    for n in N_LENGTHS:
        for sample_size in N_VALUES:
            pi_row = indexed[("pi", n, sample_size)]
            control_rows = [indexed[(name, n, sample_size)] for name in control_names]
            control_energies = [int(row["energy"]) for row in control_rows]
            control_mean = Fraction(sum(control_energies), len(control_energies))
            model_energy_data = pi_row["iid_model_energy"]
            model_energy = Fraction(
                model_energy_data["numerator"], model_energy_data["denominator"]
            )
            pi_energy = int(pi_row["energy"])
            comparisons.append(
                {
                    "n": n,
                    "N": sample_size,
                    "iid_model_energy": model_energy,
                    "pi_energy": pi_energy,
                    "control_energies": control_energies,
                    "control_mean_energy": control_mean,
                    "pi_over_model": Fraction(pi_energy, 1) / model_energy,
                    "control_mean_over_model": control_mean / model_energy,
                    "pi_over_control_mean": Fraction(pi_energy, 1) / control_mean,
                    "pi_R": Fraction(
                        pi_row["R"]["numerator"], pi_row["R"]["denominator"]
                    ),
                }
            )
    return comparisons


def ratio_text(value: Fraction) -> str:
    return f"{value.numerator}/{value.denominator}"


def write_comparison_csv(comparisons: list[dict[str, object]], output: Path) -> None:
    fields = (
        "n",
        "N",
        "iid_model_energy",
        "pi_energy",
        "control_1_energy",
        "control_2_energy",
        "control_3_energy",
        "control_mean_energy",
        "pi_over_iid_model",
        "control_mean_over_iid_model",
        "pi_over_control_mean",
        "pi_R",
    )
    with output.open("w", newline="", encoding="ascii") as handle:
        writer = csv.DictWriter(handle, fieldnames=fields, lineterminator="\n")
        writer.writeheader()
        for item in comparisons:
            control_energies = item["control_energies"]
            writer.writerow(
                {
                    "n": item["n"],
                    "N": item["N"],
                    "iid_model_energy": ratio_text(item["iid_model_energy"]),
                    "pi_energy": item["pi_energy"],
                    "control_1_energy": control_energies[0],
                    "control_2_energy": control_energies[1],
                    "control_3_energy": control_energies[2],
                    "control_mean_energy": ratio_text(item["control_mean_energy"]),
                    "pi_over_iid_model": ratio_text(item["pi_over_model"]),
                    "control_mean_over_iid_model": ratio_text(item["control_mean_over_model"]),
                    "pi_over_control_mean": ratio_text(item["pi_over_control_mean"]),
                    "pi_R": ratio_text(item["pi_R"]),
                }
            )


def write_report(comparisons: list[dict[str, object]], output: Path) -> None:
    indexed = {(int(item["n"]), int(item["N"])): item for item in comparisons}
    pi_model_ratios = [item["pi_over_model"] for item in comparisons]
    control_model_ratios = []
    for item in comparisons:
        model = item["iid_model_energy"]
        control_model_ratios.extend(
            Fraction(energy, 1) / model for energy in item["control_energies"]
        )
    lines = [
        "# T6 finite collision-energy experiment",
        "",
        "> **EXPERIMENT ONLY. Every result here concerns a finite digit prefix. It is",
        "> heuristic evidence only and cannot prove or refute sibling conjecture C1 or",
        "> canonical statement A1. No universal claim about pi follows.**",
        "",
        "## Scope and definitions",
        "",
        "For each `n` and `N`, the sample consists of the length-`n` contiguous blocks",
        "starting at fractional-digit positions `d_1, ..., d_N`. If `m_w` is the",
        "multiplicity of block `w`, the exact integer energy is `E(n,N) = sum_w m_w^2`;",
        "diagonal ordered collisions are included. The reported exact reduced ratio is",
        "`R(n,N) = N^2/(n E(n,N))`. This tests the stronger sibling statistic C1, not A1",
        "itself. The grid is `1 <= n <= 12` and `N in {1000,10000,100000,1000000}`.",
        "Here C1 is the unproved sibling statement: for every real `C>0`, eventually for",
        "every `n` there exists `N>=1` such that `N^2 > C n E_pi(n,N)`. The experiment",
        "checks only the displayed finite grid and does not establish any C1 quantifier.",
        "",
        "The ideal iid-uniform comparison has exact expected energy",
        "`N + N(N-1)/10^n`: the `N` diagonal ordered pairs always match, and each of",
        "the `N(N-1)` off-diagonal pairs matches with probability `10^-n`. This remains",
        "true for overlapping starts because equality reduces the free digit count by `n`.",
        "Three deterministic controls use the same grid and exactly",
        "`1000011` digits. Their SplitMix64 seeds are listed in `results.json`; rejection",
        "of words at or above `2^64-(2^64 mod 10)` makes each accepted residue uniform",
        "under an ideal uniform 64-bit generator. The seeds are the decimal run date",
        "`20260722` followed by control indices `01`, `02`, and `03`; they were fixed before",
        "inspecting these control outputs. Since the generator is deterministic, the controls",
        "are reproducible pseudorandom comparators, not independent empirical samples.",
        "",
        "## Reproduction",
        "",
        "From this artifact directory, with Python 3.11 or later and network access:",
        "",
        "```sh",
        "python3 run_experiment.py prepare --output pi_fractional_1000011.txt",
        "python3 run_experiment.py compute --digits pi_fractional_1000011.txt --output-dir rerun",
        "python3 verify_results.py --artifact-dir rerun --digits pi_fractional_1000011.txt --checksums CHECKSUMS.sha256",
        "sha256sum rerun/results.json rerun/results.csv rerun/comparison.csv rerun/REPORT.md",
        "```",
        "",
        "`prepare` verifies both complete downloaded-file hashes, checks all one million",
        "shared fractional digits, then verifies the extracted digit-file hash. Computation",
        "uses only Python's standard library. `results.csv` has all 192 exact rows;",
        "`comparison.csv` aligns pi and all controls on all 48 grid points; `results.json`",
        "records definitions, hashes, seeds, and the same exact values structurally.",
        "",
        "## Finite comparison",
        "",
        "Across the tested grid, pi's `E/E_iid` ranges from",
        f"`{ratio_text(min(pi_model_ratios))}` ({decimal_string(min(pi_model_ratios))}) to",
        f"`{ratio_text(max(pi_model_ratios))}` ({decimal_string(max(pi_model_ratios))}).",
        "Across all individual control rows, `E/E_iid` ranges from",
        f"`{ratio_text(min(control_model_ratios))}` ({decimal_string(min(control_model_ratios))}) to",
        f"`{ratio_text(max(control_model_ratios))}` ({decimal_string(max(control_model_ratios))}).",
        "For the limited descriptive phrase `same tested scale`, this report uses the declared",
        "criterion `0.9 <= E/E_iid <= 1.1` at every grid point. Pi and every individual",
        "control satisfy that finite criterion. It is only a coarse numerical comparison; it",
        "is not an uncertainty interval or evidence of convergence, normality, C1, or A1.",
        "",
        "At `N=1000000` the exact comparison is:",
        "",
        "| n | pi E | control energies | pi E/E_iid | control mean E/E_iid | pi R |",
        "|---:|---:|---:|---:|---:|---:|",
    ]
    for n in N_LENGTHS:
        item = indexed[(n, 1_000_000)]
        controls = ", ".join(str(value) for value in item["control_energies"])
        lines.append(
            f"| {n} | {item['pi_energy']} | {controls} | "
            f"{ratio_text(item['pi_over_model'])} | "
            f"{ratio_text(item['control_mean_over_model'])} | "
            f"{ratio_text(item['pi_R'])} |"
        )
    lines.extend(
        [
            "",
            "The complete exact tables, including every smaller `N`, are the generated CSV",
            "and JSON files. Decimal columns are displays only; integer and reduced-fraction",
            "columns are authoritative.",
            "",
            "## Interpretation boundary",
            "",
            "This finite computation neither supplies the eventual quantifiers in C1 nor",
            "controls the full arbitrary-position factor language in A1. It therefore cannot",
            "prove or refute either statement. Its only role is to measure tested finite",
            "behavior and expose departures from the naive iid comparison for later analysis.",
            "",
        ]
    )
    output.write_text("\n".join(lines), encoding="ascii")


def compute(digit_path: Path, output_dir: Path) -> None:
    pi_digits = load_pi_digits(digit_path)
    datasets: list[tuple[str, int | None, bytes, str]] = [
        ("pi", None, pi_digits, PI_DIGITS_SHA256)
    ]
    for name, seed in CONTROL_SEEDS:
        control_digits = splitmix64_digits(seed, PI_DIGIT_COUNT)
        datasets.append((name, seed, control_digits, ascii_digit_sha256(control_digits)))

    rows = make_rows(datasets)
    comparisons = make_comparisons(rows)
    output_dir.mkdir(parents=True, exist_ok=True)
    results = {
        "schema_version": 1,
        "classification": "experiment",
        "finite_evidence_warning": (
            "Finite heuristic evidence only; these results cannot prove or refute C1 or A1."
        ),
        "canonical_statement_sha256": STATEMENT_SHA256,
        "definitions": {
            "starts": "first N fractional-digit starts d_1 through d_N",
            "energy": "sum of squared length-n block multiplicities; diagonal collisions included",
            "R": "N^2/(n*energy)",
            "iid_model_expected_energy": "N + N(N-1)/10^n",
        },
        "grid": {"n": list(N_LENGTHS), "N": list(N_VALUES)},
        "pi_digits": {
            "count": PI_DIGIT_COUNT,
            "sha256": PI_DIGITS_SHA256,
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
        },
        "controls": {
            "generator": "SplitMix64 with rejection above 2^64-(2^64 mod 10), then word mod 10",
            "hash_encoding": "ASCII digits without a trailing newline",
            "seed_origin": "decimal run date 20260722 followed by fixed control indices 01, 02, 03",
            "seeds": {name: f"0x{seed:016x}" for name, seed in CONTROL_SEEDS},
        },
        "rows": rows,
    }
    (output_dir / "results.json").write_text(
        json.dumps(results, indent=2, sort_keys=True) + "\n", encoding="ascii"
    )
    write_results_csv(rows, output_dir / "results.csv")
    write_comparison_csv(comparisons, output_dir / "comparison.csv")
    write_report(comparisons, output_dir / "REPORT.md")
    for name in ("results.json", "results.csv", "comparison.csv", "REPORT.md"):
        path = output_dir / name
        print(f"{sha256_bytes(path.read_bytes())}  {path}")


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)

    prepare_parser = subparsers.add_parser("prepare", help="download, cross-check, and extract digits")
    prepare_parser.add_argument("--output", type=Path, required=True)
    prepare_parser.add_argument("--primary", type=Path)
    prepare_parser.add_argument("--crosscheck", type=Path)

    compute_parser = subparsers.add_parser("compute", help="compute exact experiment tables")
    compute_parser.add_argument("--digits", type=Path, required=True)
    compute_parser.add_argument("--output-dir", type=Path, required=True)
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    if args.command == "prepare":
        prepare_digits(args.output, args.primary, args.crosscheck)
    elif args.command == "compute":
        compute(args.digits, args.output_dir)
    else:
        raise AssertionError(args.command)


if __name__ == "__main__":
    main()
