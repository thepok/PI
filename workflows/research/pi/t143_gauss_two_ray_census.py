#!/usr/bin/env python3
"""Exact finite census for the T143 Gauss two-ray second moment.

The output retains E as formal integer coefficients of log(p)log(p').  It
does not numerically evaluate logarithms and is finite experimental evidence.
"""

from collections import Counter
from math import comb
import json


def central_coefficient(r: int) -> int:
    """[z^r](z^2+2z+2)^r, in exact closed form."""
    return sum(
        comb(r, 2 * c) * comb(2 * c, c) * 2 ** (r - c)
        for c in range(r // 2 + 1)
    )


def primes_through(limit: int) -> list[int]:
    sieve = bytearray(b"\x01") * (limit + 1)
    sieve[0:2] = b"\x00\x00"
    p = 2
    while p * p <= limit:
        if sieve[p]:
            sieve[p * p:limit + 1:p] = b"\x00" * (
                (limit - p * p) // p + 1
            )
        p += 1
    return [p for p in range(3, limit + 1, 2) if sieve[p]]


CAP_X = 1024
PRIMES = primes_through(2 * CAP_X)
A = [central_coefficient(r) for r in range(CAP_X // 2 + 1)]
assert A[0:3] == [1, 2, 8]


def records(n: int) -> list[tuple[int, int, str]]:
    """Duplicate-free delta=1/12 records (p,r,type) at the given n."""
    out = []
    for p in PRIMES:
        # Exact n/2 < p < n, without floating point.
        if not (n < 2 * p and p < n):
            continue
        t = n - p
        u = 2 * p - n - 1
        r = min(t, u)
        # n/12 <= r <= n/4.
        if 12 * r < n or 4 * r > n:
            continue
        if A[r] % p != 0:
            continue
        kind = "D" if t <= u else "R"  # the tie is direct
        out.append((p, r, kind))
    return out


EXPECTED = {
    32: (5, {"DD": 4, "DR": 0, "RD": 0, "RR": 1}, 5, 0),
    64: (6, {"DD": 6, "DR": 0, "RD": 0, "RR": 2}, 6, 2),
    128: (15, {"DD": 11, "DR": 0, "RD": 0, "RR": 8}, 15, 4),
    256: (26, {"DD": 19, "DR": 1, "RD": 1, "RR": 11}, 26, 6),
    512: (24, {"DD": 14, "DR": 1, "RD": 1, "RR": 10}, 24, 2),
    1024: (66, {"DD": 36, "DR": 2, "RD": 2, "RR": 32}, 66, 6),
}

summaries = []
for x in EXPECTED:
    record_rows = []
    pair_types: Counter[str] = Counter()
    coefficients: Counter[tuple[int, int]] = Counter()
    off_diagonal = []
    diagonal_count = 0

    for n in range(x + 1, 2 * x + 1):
        current = records(n)
        record_rows.extend((n, *record) for record in current)
        for left in current:
            for right in current:
                p, r, left_kind = left
                pp, rr, right_kind = right
                pair_types[left_kind + right_kind] += 1
                coefficients[(p, pp)] += 1
                if left == right:
                    diagonal_count += 1
                else:
                    off_diagonal.append((n, left, right))

                # Independently check the appropriate eliminated-n equation.
                if left_kind + right_kind == "DD":
                    assert p + r == pp + rr
                elif left_kind + right_kind == "DR":
                    assert p + r == 2 * pp - 1 - rr
                elif left_kind + right_kind == "RD":
                    assert 2 * p - 1 - r == pp + rr
                else:
                    assert 2 * p - r == 2 * pp - rr

    types = {kind: pair_types[kind] for kind in ("DD", "DR", "RD", "RR")}
    observed = (len(record_rows), types, diagonal_count, len(off_diagonal))
    assert observed == EXPECTED[x]
    assert types["DR"] == types["RD"]

    summaries.append({
        "X": x,
        "records": record_rows,
        "record_count": len(record_rows),
        "pair_types": types,
        "diagonal": diagonal_count,
        "off_diagonal": off_diagonal,
        "formal_E_coefficients": [
            {"p": p, "p_prime": pp, "coefficient": coefficient}
            for (p, pp), coefficient in sorted(coefficients.items())
        ],
    })

print(json.dumps({
    "status": "experiment",
    "delta": {"numerator": 1, "denominator": 12},
    "normalization": {"A_2": A[2]},
    "blocks": summaries,
}, sort_keys=True, separators=(",", ":")))
