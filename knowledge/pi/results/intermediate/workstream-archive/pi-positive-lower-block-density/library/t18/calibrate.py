#!/usr/bin/env python3
"""Reproducible finite T18 calibration using only the Python standard library."""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
import sys
import tempfile
from collections import Counter
from decimal import Decimal, localcontext
from itertools import product
from pathlib import Path


CANONICAL_STATEMENT_SHA256 = (
    "11ec455612e8ab182b7f6c71ba1a64c3b5b30beb5f3ded632cb2ecdc50129cc8"
)
PREFIX_LENGTHS = (1000, 3000, 10000)
WORD_LENGTHS = (1, 2, 3, 4)
BLOCK_SCALES = (1, 2, 4, 8, 16, 32)
FORBIDDEN_WORDS = (
    "0", "1", "00", "01", "11", "000", "001", "012", "123", "0000", "0123"
)
MATRIX_POWERS = (0, 1, 2, 4, 8, 16, 32)
IID_SEED = "T18-iid-sha256-rejection-v1"
KNOWN_PI_PREFIX = "14159265358979323846264338327950288419716939937510"
GENERATED_FILES = (
    "ranges.json",
    "digit_hashes.json",
    "word_counts.csv",
    "block_entropies.csv",
    "forbidden_calibration.csv",
    "automaton_certificates.json",
    "certificate_checks.json",
)

if hasattr(sys, "set_int_max_str_digits"):
    sys.set_int_max_str_digits(100_000)


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sha256_file(path: Path) -> str:
    return sha256_bytes(path.read_bytes())


def write_json(path: Path, value: object) -> None:
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="ascii")


def pi_digits_machin(count: int, guard: int = 30) -> str:
    """Decimal digits after the point from an integer fixed-point Machin series."""
    places = count + guard
    scale = 10**places

    def arctan_inverse(q: int) -> int:
        q2 = q * q
        qpow = q
        total = 0
        n = 0
        sign = 1
        while True:
            term = scale // (qpow * (2 * n + 1))
            if term == 0:
                break
            total += sign * term
            qpow *= q2
            n += 1
            sign = -sign
        return total

    scaled_pi = 16 * arctan_inverse(5) - 4 * arctan_inverse(239)
    text = str(scaled_pi).zfill(places + 1)
    if text[0] != "3":
        raise AssertionError("Machin computation did not produce integer part 3")
    return text[1 : count + 1]


def pi_digits_chudnovsky(count: int, guard: int = 30) -> str:
    """Independent Decimal/Chudnovsky computation of digits after the point."""
    precision = count + guard + 10
    with localcontext() as ctx:
        ctx.prec = precision
        m = 1
        ell = 13591409
        x = 1
        k = 6
        series = Decimal(ell)
        for i in range(1, count // 14 + 4):
            m = (m * (k**3 - 16 * k)) // (i**3)
            ell += 545140134
            x *= -262537412640768000
            series += Decimal(m * ell) / Decimal(x)
            k += 12
        pi = (Decimal(426880) * Decimal(10005).sqrt()) / series
        text = format(pi, "f")
    integer, fractional = text.split(".")
    if integer != "3" or len(fractional) < count:
        raise AssertionError("Chudnovsky computation did not produce enough pi digits")
    return fractional[:count]


def champernowne_digits(count: int) -> str:
    chunks: list[str] = []
    size = 0
    n = 1
    while size < count:
        chunk = str(n)
        chunks.append(chunk)
        size += len(chunk)
        n += 1
    return "".join(chunks)[:count]


def balanced_digits(count: int, champernowne: str) -> str:
    """Exact T4 stream: C_m = Champernowne[0:3^m] followed by 3^m zeros."""
    chunks: list[str] = []
    size = 0
    m = 0
    while size < count:
        stage_size = 3**m
        chunk = champernowne[:stage_size] + "0" * stage_size
        chunks.append(chunk)
        size += len(chunk)
        m += 1
    return "".join(chunks)[:count]


def sparse_island_digits(count: int) -> str:
    """Exact T2 stream: B_k = 0^((k+1)^4) followed by decimal(k+1)."""
    chunks: list[str] = []
    size = 0
    k = 0
    while size < count:
        chunk = "0" * ((k + 1) ** 4) + str(k + 1)
        chunks.append(chunk)
        size += len(chunk)
        k += 1
    return "".join(chunks)[:count]


def iid_sha256_digits(count: int) -> str:
    """A fixed pseudorandom iid-control realization with unbiased byte rejection."""
    seed = IID_SEED.encode("ascii")
    digits: list[str] = []
    counter = 0
    while len(digits) < count:
        block = hashlib.sha256(seed + counter.to_bytes(8, "big")).digest()
        counter += 1
        for value in block:
            if value < 250:
                digits.append(str(value % 10))
                if len(digits) == count:
                    break
    return "".join(digits)


def count_starts(stream: str, word: str, starts: int) -> int:
    width = len(word)
    return sum(stream[i : i + width] == word for i in range(starts))


def contained_word_counter(stream: str, prefix_length: int, width: int) -> Counter[str]:
    return Counter(stream[i : i + width] for i in range(prefix_length + 1 - width))


def decimal_entropy_from_spectrum(
    total: int, width: int, spectrum: Counter[int]
) -> tuple[str, str, str, str]:
    """Return an exact expression and 30-place entropy normalizations."""
    terms = [f"{multiplicity * count}*ln({count})" for count, multiplicity in sorted(spectrum.items())]
    expression = f"ln({total})-({'+'.join(terms)})/{total}"
    with localcontext() as ctx:
        ctx.prec = 50
        t = Decimal(total)
        weighted = sum(
            Decimal(multiplicity * count) * Decimal(count).ln()
            for count, multiplicity in spectrum.items()
        )
        entropy = t.ln() - weighted / t
        per_digit = entropy / Decimal(width)
        normalized = per_digit / Decimal(10).ln()
    return (
        expression,
        format(entropy, ".30f"),
        format(per_digit, ".30f"),
        format(normalized, ".30f"),
    )


def matrix_identity(size: int) -> list[list[int]]:
    return [[int(i == j) for j in range(size)] for i in range(size)]


def matrix_multiply(a: list[list[int]], b: list[list[int]]) -> list[list[int]]:
    size = len(a)
    result = [[0] * size for _ in range(size)]
    for i in range(size):
        for k in range(size):
            if a[i][k]:
                for j in range(size):
                    result[i][j] += a[i][k] * b[k][j]
    return result


def matrix_power(matrix: list[list[int]], exponent: int) -> list[list[int]]:
    result = matrix_identity(len(matrix))
    base = matrix
    while exponent:
        if exponent & 1:
            result = matrix_multiply(result, base)
        base = matrix_multiply(base, base)
        exponent //= 2
    return result


def prefix_subset_automaton(word: str) -> tuple[list[int], list[list[int]]]:
    """T14's full proper-prefix subset automaton, including unreachable states."""
    ell = len(word)
    if ell == 0:
        raise ValueError("T14 requires a nonempty forbidden word")
    states = [mask for mask in range(1 << ell) if mask & 1]
    index = {mask: i for i, mask in enumerate(states)}
    matrix = [[0] * len(states) for _ in states]
    for source in states:
        for digit in "0123456789":
            if source & (1 << (ell - 1)) and digit == word[-1]:
                continue
            target = 1
            for p in range(ell - 1):
                if source & (1 << p) and digit == word[p]:
                    target |= 1 << (p + 1)
            matrix[index[source]][index[target]] += 1
    return states, matrix


def forbidden_count_kmp(word: str, length: int) -> int:
    """Independent longest-prefix DP count of words avoiding the forbidden word."""
    ell = len(word)
    counts = [0] * ell
    counts[0] = 1
    for _ in range(length):
        following = [0] * ell
        for matched, multiplicity in enumerate(counts):
            if multiplicity == 0:
                continue
            prefix = word[:matched]
            for digit in "0123456789":
                candidate = prefix + digit
                if candidate.endswith(word):
                    continue
                next_match = max(
                    q for q in range(ell) if candidate.endswith(word[:q])
                )
                following[next_match] += multiplicity
        counts = following
    return sum(counts)


def configuration() -> dict[str, object]:
    return {
        "agenda_item": "T18",
        "canonical_statement_sha256": CANONICAL_STATEMENT_SHA256,
        "prefix_length_semantics": "starts n with 0 <= n < N; words may extend beyond N",
        "prefix_lengths": list(PREFIX_LENGTHS),
        "word_lengths_exhaustive": list(WORD_LENGTHS),
        "block_entropy_semantics": "all N+1-L fully-contained length-L blocks",
        "block_scales": list(BLOCK_SCALES),
        "forbidden_words": list(FORBIDDEN_WORDS),
        "matrix_powers": list(MATRIX_POWERS),
        "iid_control": {
            "label": "fixed pseudorandom realization of an iid-uniform model",
            "seed": IID_SEED,
            "generator": "SHA-256 counter blocks; accept bytes <250; digit=byte mod 10",
        },
        "stream_order": ["pi", "iid", "champernowne", "t4_balanced", "t2_sparse_island"],
    }


def generate_outputs(output_dir: Path) -> dict[str, object]:
    output_dir.mkdir(parents=True, exist_ok=True)
    required = max(PREFIX_LENGTHS) + max(WORD_LENGTHS) - 1

    pi_machin = pi_digits_machin(required)
    pi_chudnovsky = pi_digits_chudnovsky(required)
    pi_equal = pi_machin == pi_chudnovsky
    prefix_known = pi_machin.startswith(KNOWN_PI_PREFIX)
    if not pi_equal or not prefix_known:
        raise AssertionError("independent pi computations or known-prefix check failed")

    champernowne = champernowne_digits(required)
    streams = {
        "pi": pi_machin,
        "iid": iid_sha256_digits(required),
        "champernowne": champernowne,
        "t4_balanced": balanced_digits(required, champernowne),
        "t2_sparse_island": sparse_island_digits(required),
    }
    write_json(output_dir / "ranges.json", configuration())

    digit_hashes = {
        "digit_count": required,
        "hash_scope": "ASCII digits after the decimal point, with no newline",
        "pi": {
            "machin_sha256": sha256_bytes(pi_machin.encode("ascii")),
            "chudnovsky_sha256": sha256_bytes(pi_chudnovsky.encode("ascii")),
            "algorithms_equal": pi_equal,
            "known_50_digit_prefix_equal": prefix_known,
            "known_prefix": KNOWN_PI_PREFIX,
        },
        "streams": {
            name: sha256_bytes(digits.encode("ascii")) for name, digits in streams.items()
        },
    }
    write_json(output_dir / "digit_hashes.json", digit_hashes)

    word_count_rows = 0
    counts_by_key: dict[tuple[str, int, str], int] = {}
    with (output_dir / "word_counts.csv").open("w", newline="", encoding="ascii") as handle:
        writer = csv.writer(handle, lineterminator="\n")
        writer.writerow(("stream", "N", "word_length", "word", "count", "denominator"))
        for stream_name, digits in streams.items():
            for n in PREFIX_LENGTHS:
                for width in WORD_LENGTHS:
                    observed = Counter(digits[i : i + width] for i in range(n))
                    for tuple_word in product("0123456789", repeat=width):
                        word = "".join(tuple_word)
                        count = observed[word]
                        counts_by_key[(stream_name, n, word)] = count
                        writer.writerow((stream_name, n, width, word, count, n))
                        word_count_rows += 1

    entropy_rows = 0
    entropy_spectrum_checks = 0
    with (output_dir / "block_entropies.csv").open("w", newline="", encoding="ascii") as handle:
        writer = csv.writer(handle, lineterminator="\n")
        writer.writerow((
            "stream", "N", "L", "sample_size", "support_size", "max_count",
            "sum_squared_counts", "collision_pairs", "count_spectrum",
            "exact_entropy_expression", "entropy_nats", "entropy_nats_per_digit",
            "normalized_entropy_H_over_L_log10",
        ))
        for stream_name, digits in streams.items():
            for n in PREFIX_LENGTHS:
                for width in BLOCK_SCALES:
                    counts = contained_word_counter(digits, n, width)
                    total = n + 1 - width
                    spectrum = Counter(counts.values())
                    sum_squares = sum(count * count for count in counts.values())
                    collision_pairs = sum(count * (count - 1) // 2 for count in counts.values())
                    spectrum_mass = sum(
                        count * multiplicity for count, multiplicity in spectrum.items()
                    )
                    if spectrum_mass != total or sum(counts.values()) != total:
                        raise AssertionError("exact block-count spectrum mass failed")
                    entropy_spectrum_checks += 1
                    expression, entropy, per_digit, normalized = decimal_entropy_from_spectrum(
                        total, width, spectrum
                    )
                    spectrum_text = ";".join(
                        f"{count}:{multiplicity}" for count, multiplicity in sorted(spectrum.items())
                    )
                    writer.writerow((
                        stream_name, n, width, total, len(counts), max(counts.values()),
                        sum_squares, collision_pairs, spectrum_text, expression, entropy,
                        per_digit, normalized,
                    ))
                    entropy_rows += 1

    forbidden_rows = 0
    contamination_checks = 0
    with (output_dir / "forbidden_calibration.csv").open(
        "w", newline="", encoding="ascii"
    ) as handle:
        writer = csv.writer(handle, lineterminator="\n")
        writer.writerow((
            "stream", "N", "L", "forbidden_word", "word_count_N", "frequency_denominator",
            "contained_sample_size", "contaminated_starts", "t15_integer_bound",
            "bound_holds", "forbidden_starts", "contamination_fraction",
        ))
        for stream_name, digits in streams.items():
            for n in PREFIX_LENGTHS:
                for width in BLOCK_SCALES:
                    sample_size = n + 1 - width
                    blocks = [digits[i : i + width] for i in range(sample_size)]
                    for word in FORBIDDEN_WORDS:
                        word_count = counts_by_key[(stream_name, n, word)]
                        contaminated = sum(word in block for block in blocks)
                        bound = (width + 1) * word_count
                        bound_holds = contaminated <= bound
                        if not bound_holds:
                            raise AssertionError("T15 integer contamination bound failed")
                        contamination_checks += 1
                        writer.writerow((
                            stream_name, n, width, word, word_count, n, sample_size,
                            contaminated, bound, str(bound_holds).lower(),
                            sample_size - contaminated, f"{contaminated}/{sample_size}",
                        ))
                        forbidden_rows += 1

    automata: dict[str, object] = {}
    automaton_identity_checks = 0
    for word in FORBIDDEN_WORDS:
        states, matrix = prefix_subset_automaton(word)
        initial_index = states.index(1)
        power_records: dict[str, object] = {}
        for exponent in MATRIX_POWERS:
            power = matrix_power(matrix, exponent)
            row_sums = [sum(row) for row in power]
            direct = forbidden_count_kmp(word, exponent)
            initial = row_sums[initial_index]
            maximum = max(row_sums)
            checks = {
                "initial_row_sum_eq_direct_forbidden_count": initial == direct,
                "max_row_sum_eq_initial_row_sum": maximum == initial,
                "all_rows_le_initial_row": all(value <= initial for value in row_sums),
            }
            if not all(checks.values()):
                raise AssertionError(f"automaton identity failed for {word!r}, power {exponent}")
            automaton_identity_checks += len(checks)
            power_records[str(exponent)] = {
                "matrix_power": power,
                "row_sums": row_sums,
                "initial_row_sum": initial,
                "max_row_sum": maximum,
                "independent_kmp_forbidden_count": direct,
                "checks": checks,
            }
        automata[word] = {
            "state_encoding": "bit mask of active proper-prefix lengths; bit 0 is always set",
            "states": states,
            "initial_state_mask": 1,
            "matrix_orientation": "source rows, destination columns; entries count digit labels",
            "transition_matrix": matrix,
            "powers": power_records,
        }
    write_json(output_dir / "automaton_certificates.json", automata)

    zero_zero_fixture = automata["00"]
    fixture_matrix_ok = zero_zero_fixture["transition_matrix"] == [[9, 1], [9, 0]]
    fixture_count_ok = forbidden_count_kmp("00", 4) == 9720
    total_count_checks = len(streams) * len(PREFIX_LENGTHS) * sum(10**k for k in WORD_LENGTHS)
    count_mass_checks = 0
    for stream_name in streams:
        for n in PREFIX_LENGTHS:
            for width in WORD_LENGTHS:
                mass = sum(
                    counts_by_key[(stream_name, n, "".join(word))]
                    for word in product("0123456789", repeat=width)
                )
                if mass != n:
                    raise AssertionError("exhaustive word counts do not sum to N")
                count_mass_checks += 1

    checks = {
        "all_checks_pass": True,
        "pi_algorithms_equal": pi_equal,
        "pi_known_prefix_equal": prefix_known,
        "zero_zero_matrix_fixture": fixture_matrix_ok,
        "zero_zero_length4_count_9720": fixture_count_ok,
        "word_count_rows": word_count_rows,
        "expected_word_count_rows": total_count_checks,
        "block_entropy_rows": entropy_rows,
        "block_entropy_spectrum_mass_checks": entropy_spectrum_checks,
        "forbidden_calibration_rows": forbidden_rows,
        "word_count_mass_checks": count_mass_checks,
        "t15_contamination_bound_checks": contamination_checks,
        "automaton_matrix_identity_checks": automaton_identity_checks,
        "integer_invariants": {
            "word_count_mass": "for each stream,N,k: sum_w count(w,N)=N",
            "block_spectrum_mass": "sum multiplicity*count=N+1-L",
            "t15_bound": "contaminated_starts <= (L+1)*word_count_N",
            "t14_identity": "initial row sum of M^r = independent KMP avoidance count",
            "t16_identity": "maximum row sum of M^r = initial row sum",
        },
    }
    if not fixture_matrix_ok or not fixture_count_ok or word_count_rows != total_count_checks:
        raise AssertionError("global certificate fixture or row count failed")
    write_json(output_dir / "certificate_checks.json", checks)
    return {"digit_hashes": digit_hashes, "checks": checks}


def write_expected_results(base: Path) -> None:
    summary = generate_outputs(base)
    expected = {
        "format_version": 1,
        "generated_file_sha256": {name: sha256_file(base / name) for name in GENERATED_FILES},
        "pi_digit_sha256": summary["digit_hashes"]["pi"]["machin_sha256"],
        "all_checks_pass": summary["checks"]["all_checks_pass"],
    }
    write_json(base / "expected_results.json", expected)


def verify(base: Path) -> None:
    expected_path = base / "expected_results.json"
    if not expected_path.is_file():
        raise SystemExit("missing co-located expected_results.json")
    expected = json.loads(expected_path.read_text(encoding="ascii"))
    missing = [name for name in GENERATED_FILES if not (base / name).is_file()]
    if missing:
        raise SystemExit(f"missing co-located generated files: {', '.join(missing)}")
    with tempfile.TemporaryDirectory(prefix="t18-reproduce-") as temporary:
        reproduced = Path(temporary)
        summary = generate_outputs(reproduced)
        actual_hashes = {name: sha256_file(reproduced / name) for name in GENERATED_FILES}
        retained_hashes = {name: sha256_file(base / name) for name in GENERATED_FILES}
    expected_hashes = expected["generated_file_sha256"]
    if actual_hashes != expected_hashes:
        raise SystemExit("reproduced hashes differ from expected_results.json")
    if retained_hashes != expected_hashes:
        raise SystemExit("retained raw artifacts differ from expected_results.json")
    if summary["digit_hashes"]["pi"]["machin_sha256"] != expected["pi_digit_sha256"]:
        raise SystemExit("reproduced pi digit hash differs from expected_results.json")
    if not summary["checks"]["all_checks_pass"]:
        raise SystemExit("one or more semantic certificate checks failed")
    print(json.dumps({
        "status": "REPRODUCED_OK",
        "pi_digit_sha256": expected["pi_digit_sha256"],
        "generated_file_sha256": actual_hashes,
        "checks": summary["checks"],
    }, indent=2, sort_keys=True))


def main() -> None:
    parser = argparse.ArgumentParser()
    modes = parser.add_mutually_exclusive_group(required=True)
    modes.add_argument("--write", action="store_true", help="regenerate retained outputs")
    modes.add_argument("--verify", action="store_true", help="reproduce in temp and compare exactly")
    args = parser.parse_args()
    base = Path(__file__).resolve().parent
    if args.write:
        write_expected_results(base)
        print(f"wrote deterministic T18 outputs under {base}")
    else:
        verify(base)


if __name__ == "__main__":
    main()
