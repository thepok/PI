#!/usr/bin/env python3
"""Exact finite replay for T98's digit-block analogue of the T56 statistic.

The stream is generated only by concatenating str(1), str(2), ... .  For a
fixed n, L = 10**(n//2), H = 10**n//2, and b_j is the length-n decimal block
at stream start j (leading zeroes are retained by its fixed length).  The
strict circular block cutoff is

  min(|b_i-b_j|, 10**n-|b_i-b_j|) < 1.

Since its left side is a nonnegative integer, this is precisely b_i = b_j.
The resulting ordered, diagonal-inclusive count is decomposed exactly as
L + 2 sum_{1 <= r < L} #{0 <= j < L-r : b_j = b_{j+r}}.

This is a digit-block analogue, not a claim that equality of blocks is the
same as T56's real-circle condition for pi or for the infinite Champernowne
suffixes.  The T56 endpoints and strictness are retained deliberately.
"""

import bisect
import collections
import hashlib
import json
import pathlib
import sys


BASE = 10
MIN_N = 2
MAX_N = 12
CANONICAL_SHA256 = "a70dd741b27595aeb3dfc902b5e201579fed6bae24e2191f58c5ac64a22939e6"


def sha256(path: pathlib.Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def champernowne_prefix(length: int) -> tuple[str, list[int]]:
    """Return exactly `length` stream digits and all positive block boundaries."""
    pieces: list[str] = []
    boundaries: list[int] = []
    total = 0
    integer = 1
    while total < length:
        piece = str(integer)
        pieces.append(piece)
        total += len(piece)
        boundaries.append(total)
        integer += 1
    return "".join(pieces)[:length], boundaries


def fixed_length_block_codes(stream: str, n: int, starts: int) -> list[int]:
    """Code all overlapping n-digit blocks, retaining leading-zero blocks."""
    assert len(stream) >= starts + n - 1
    codes = [int(stream[:n])]
    modulus = BASE**n
    leading = BASE ** (n - 1)
    for j in range(1, starts):
        codes.append((codes[-1] - int(stream[j - 1]) * leading) * BASE + int(stream[j + n - 1]))
        assert 0 <= codes[-1] < modulus
    return codes


def crosses_integer_boundary(boundaries: list[int], start: int, n: int) -> bool:
    """Whether a length-n block contains an internal concatenation boundary."""
    next_boundary = bisect.bisect_right(boundaries, start)
    return next_boundary < len(boundaries) and boundaries[next_boundary] < start + n


def row(n: int) -> dict[str, object]:
    sample_length = BASE ** (n // 2)
    bandwidth = BASE**n // 2
    stream, boundaries = champernowne_prefix(sample_length + n - 1)
    codes = fixed_length_block_codes(stream, n, sample_length)
    positions: dict[int, list[int]] = collections.defaultdict(list)
    for j, code in enumerate(codes):
        positions[code].append(j)

    # This is the T56 positive-lag triangle: 1 <= r < L and 0 <= j < L-r.
    lag_counts: dict[int, int] = collections.defaultdict(int)
    for occurrences in positions.values():
        for left_index, left in enumerate(occurrences):
            for right in occurrences[left_index + 1 :]:
                lag_counts[right - left] += 1

    diagonal = sample_length
    positive_lag_total = sum(lag_counts.values())
    ordered_count = diagonal + 2 * positive_lag_total
    direct_ordered_count = sum(len(occurrences) ** 2 for occurrences in positions.values())
    assert ordered_count == direct_ordered_count
    assert all(1 <= lag < sample_length for lag in lag_counts)

    modulus = BASE**n
    # Strict integer cutoff below one is exactly block equality.  The direct
    # frequency calculation above is its ordered-pair count without O(L^2).
    assert all(0 <= code < modulus for code in codes)
    assert direct_ordered_count == sum(len(v) * len(v) for v in positions.values())

    boundary_starts = sum(
        crosses_integer_boundary(boundaries, j, n) for j in range(sample_length)
    )
    witnesses = [[lag, lag_counts[lag]] for lag in sorted(lag_counts)[:5]]
    return {
        "n": n,
        "L_n": sample_length,
        "H_n": bandwidth,
        "strict_cutoff": "min(|b_i-b_j|,10^n-|b_i-b_j|)<1",
        "lag_range": "1 <= r < L_n",
        "start_range": "0 <= j < L_n-r",
        "ordered_pair_convention": "diagonal plus both orientations",
        "triangular_identity": {
            "diagonal": diagonal,
            "positive_lag_total": positive_lag_total,
            "ordered_count": ordered_count,
        },
        "distinct_n_blocks": len(positions),
        "max_block_multiplicity": max(map(len, positions.values())),
        "nonzero_positive_lags": len(lag_counts),
        "first_nonzero_lag_witnesses": witnesses,
        "boundary_crossing_starts": boundary_starts,
        "all_starts_cross_a_concatenation_boundary": boundary_starts == sample_length,
    }


def main() -> None:
    here = pathlib.Path(__file__).resolve().parent
    statement = here / "pi-positive-decimal-factor-entropy.txt"
    assert sha256(statement) == CANONICAL_SHA256
    results = [row(n) for n in range(MIN_N, MAX_N + 1)]
    result = {
        "replay": "T98 base-10 Champernowne literal block-collision analogue",
        "canonical_statement_sha256": CANONICAL_SHA256,
        "definitions": {
            "stream": "123456789101112... from concatenation of consecutive positive integers",
            "L_n": "10^(n//2), natural-number division",
            "H_n": "10^n/2, natural-number division",
            "block": "b_j is the fixed-length base-10 code of stream[j:j+n]",
            "strict_cutoff": "circular integer block distance < 1",
            "complete_C7_band": "all integer h with |h| < H_n, weight 1-|h|/H_n; not evaluated by this block-count replay",
        },
        "rows": results,
        "scope": "finite deterministic digit-block counts only; not a result about pi, C7, C2, or C1",
    }
    json.dump(result, sys.stdout, indent=2, sort_keys=True)
    sys.stdout.write("\n")


if __name__ == "__main__":
    main()
