#!/usr/bin/env python3
"""Exact finite replay for T154; finite checks are experiments, not proofs."""

from fractions import Fraction
from hashlib import sha256
from itertools import combinations
from math import ceil, isqrt
from pathlib import Path
import json


ROOT = Path(__file__).resolve().parent
EXPECTED = {
    "canonical_statement.txt": "cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8",
    "prior-T135-REPORT.md": "4439850a49ee2fa7351d85daf366eba4b2b4a55e756a15bf7c431d92fb195e21",
    "prior-T144-REPORT.md": "96c685692710b05035208ca459e4536f992bef2a69c030cc318625c5de00da7a",
    "prior-T147-REPORT.md": "d1af43d8b2c21c6b3106a4c75e8e38467146e7c09f219adf240ee83a9250a909",
    "prior-T150-REPORT.md": "937a6a9c23ba6c319de2f7f2457d33b163f67005e0651f6c199d0453902d5907",
    "prior-T152-REPORT.md": "01ae77f2f125d70d31e5ae774fb2c7adb8f741b04bb9fbec6e19cdc1fc497171",
    "active-items-snapshot.json": "d27d73c06c7db942e3a632b57918ad179c82f8d6258b0b0f8f3245320bf33b4b",
}


def digest(name):
    return sha256((ROOT / name).read_bytes()).hexdigest()


def h(m):
    r = isqrt(m)
    return r if r * r == m else r + 1


def incidence(N, k, m, q):
    lo = max(0, q - m + 1)
    hi = min(N - 1, q)
    return max(0, hi - lo + 1)


def rank(matrix):
    a = [list(map(Fraction, row)) for row in matrix]
    if not a:
        return 0
    rows, cols, r = len(a), len(a[0]), 0
    for c in range(cols):
        pivot = next((i for i in range(r, rows) if a[i][c]), None)
        if pivot is None:
            continue
        a[r], a[pivot] = a[pivot], a[r]
        z = a[r][c]
        a[r] = [v / z for v in a[r]]
        for i in range(rows):
            if i != r and a[i][c]:
                z = a[i][c]
                a[i] = [a[i][j] - z * a[r][j] for j in range(cols)]
        r += 1
        if r == rows:
            break
    return r


def solve_square(matrix, rhs):
    n = len(matrix)
    a = [list(map(Fraction, matrix[i])) + [Fraction(rhs[i])] for i in range(n)]
    for c in range(n):
        pivot = next((i for i in range(c, n) if a[i][c]), None)
        if pivot is None:
            return None
        a[c], a[pivot] = a[pivot], a[c]
        z = a[c][c]
        a[c] = [v / z for v in a[c]]
        for i in range(n):
            if i != c and a[i][c]:
                z = a[i][c]
                a[i] = [a[i][j] - z * a[c][j] for j in range(n + 1)]
    return [a[i][-1] for i in range(n)]


def primal_optimum(N, k, depths):
    """Enumerate primal vertices for small exact-rational instances."""
    L, n = N + k - 1, len(depths)
    rows = []
    rhs = []
    for q in range(L):
        rows.append([Fraction(incidence(N, k, m, q)) for m in depths])
        rhs.append(Fraction(1))
    for j in range(n):
        row = [Fraction(0)] * n
        row[j] = Fraction(1)
        rows.append(row)
        rhs.append(Fraction(0))
    c = [Fraction(N * m, 100 * h(m)) for m in depths]
    best = Fraction(0)
    for chosen in combinations(range(len(rows)), n):
        matrix = [rows[i] for i in chosen]
        if rank(matrix) != n:
            continue
        x = solve_square(matrix, [rhs[i] for i in chosen])
        if x is None or any(v < 0 for v in x):
            continue
        if any(sum(row[j] * x[j] for j in range(n)) > b for row, b in zip(rows[:L], rhs[:L])):
            continue
        best = max(best, sum(c[j] * x[j] for j in range(n)))
    return best


def dual_optimum(N, k, depths):
    """Enumerate sparse dual vertices for small exact-rational instances."""
    L, r = N + k - 1, len(depths)
    # A dual vertex has at most r positive coordinates. Enumerate their support,
    # then active depth constraints. This is complete for the bounded test sizes.
    best = None
    requirements = [Fraction(N * m, 100 * h(m)) for m in depths]
    for size in range(1, r + 1):
        for support in combinations(range(L), size):
            for active in combinations(range(r), size):
                matrix = [
                    [Fraction(incidence(N, k, depths[j], q)) for q in support]
                    for j in active
                ]
                if rank(matrix) != size:
                    continue
                y = solve_square(matrix, [requirements[j] for j in active])
                if y is None or any(v < 0 for v in y):
                    continue
                if any(
                    sum(Fraction(incidence(N, k, m, q)) * y[z] for z, q in enumerate(support)) < req
                    for m, req in zip(depths, requirements)
                ):
                    continue
                value = sum(y)
                if best is None or value < best:
                    best = value
    assert best is not None
    return best


def check_instance(N, k, depths):
    L = N + k - 1
    assert depths and min(depths) >= (k + 1) // 2 and max(depths) <= k
    for m in depths:
        assert (N - 1) + (m - 1) <= L - 1
        ds = [incidence(N, k, m, q) for q in range(L)]
        assert min(ds) >= 0 and max(ds) <= m and sum(ds) == N * m

    m0 = min(depths)
    t = {m: Fraction(1, m0) if m == m0 else Fraction(0) for m in depths}
    assert all(sum(Fraction(incidence(N, k, m, q)) * t[m] for m in depths) <= 1 for q in range(L))
    lower = Fraction(N, 100 * h(m0))

    uniform = [Fraction(1, 100 * h(m0))] * L
    for m in depths:
        assert sum(Fraction(incidence(N, k, m, q)) * uniform[q] for q in range(L)) >= Fraction(N * m, 100 * h(m))
    center = k - 1
    assert all(incidence(N, k, m, center) == m for m in depths)
    exact_dual = [Fraction(N, 100 * h(m0)) if q == center else Fraction(0) for q in range(L)]
    for m in depths:
        assert sum(Fraction(incidence(N, k, m, q)) * exact_dual[q] for q in range(L)) >= Fraction(N * m, 100 * h(m))
    upper = sum(exact_dual)

    a = (k + 1) // 2
    R = isqrt((N * N) // a)
    while a * R * R < N * N:
        R += 1
    B = R + k - 1
    assert B <= L and L - B == N - R
    pref = [Fraction(N, 100 * R * h(a)) if q < B else Fraction(0) for q in range(L)]
    for m in depths:
        assert (R - 1) + (m - 1) <= B - 1
        assert sum(Fraction(incidence(N, k, m, q)) * pref[q] for q in range(L)) >= Fraction(N * m, 100 * h(m))

    p_opt = primal_optimum(N, k, depths)
    d_opt = dual_optimum(N, k, depths)
    assert lower == p_opt == d_opt == upper
    return lower, p_opt, upper, R, B, sum(pref)


def main():
    for name, expected in EXPECTED.items():
        assert digest(name) == expected, name
    snapshot = json.loads((ROOT / "active-items-snapshot.json").read_text())
    leases = snapshot["ledger_export"]["resources"]["leases"]
    t153 = [x for x in leases if x["node_id"].endswith(":t153")]
    assert len(t153) == 1 and t153[0]["generation"] == 1

    report = (ROOT / "REPORT.md").read_text()
    assert report.count("TERMINAL VERDICT (1/1):") == 1
    assert "TERMINAL VERDICT (1/1): **PROVED MATCHING RATE.**" in report
    assert "ADDITIONAL UNPROVED\nFIXED-PI PREMISE; NOT ASSERTED" in report
    for marker in ["FIXED_PI_CLAIM: none", "A1_CLAIM: none", "C1_CLAIM: none", "C2_CLAIM: none"]:
        assert report.count(marker) == 1

    cases = [
        (12, 4, (2,)),
        (12, 4, (2, 3, 4)),
        (15, 5, (3, 5)),
        (18, 6, (3, 4, 6)),
    ]
    print("T154_EXACT_RATIONAL_REPLAY")
    print("FINITE_COMPUTATION_LABEL: experiment, not asymptotic proof")
    print("HASHES_OK:", len(EXPECTED))
    print("T153_STATUS: active generation-1 lease; no mathematical artifact in snapshot")
    for N, k, depths in cases:
        lower, optimum, upper, R, B, prefix_cost = check_instance(N, k, depths)
        print(
            f"CASE N={N} k={k} S={','.join(map(str, depths))} "
            f"lower={lower} optimum={optimum} upper={upper} "
            f"R={R} B={B} prefix_dual={prefix_cost}"
        )
    print("ENDPOINTS_CAPACITIES_DUALS_OK")
    print("FINITE_STRONG_DUALITY_TESTS_OK")
    print("TERMINAL_VERDICT_COUNT: 1")
    print("FIXED_PI_A1_C1_C2_CLAIMS: none")


if __name__ == "__main__":
    main()
