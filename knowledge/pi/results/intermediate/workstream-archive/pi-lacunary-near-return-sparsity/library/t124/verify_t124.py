#!/usr/bin/env python3
"""Self-contained structural and arithmetic replay for the T124 note."""

from __future__ import annotations

import hashlib
import math
from pathlib import Path


ROOT = Path(__file__).resolve().parent

EXPECTED_HASHES = {
    "canonical_statement.txt": "cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8",
    "baake-grimm-0809.0580.pdf": "31106ba1771edc9b4abc961007f12c00ca1d22e0bce9e2310fbe58e8f6e1f824",
    "baker-banaji-2401.01241v2.pdf": "f07b9e579360cff6843fccb526086d27ea454925d6ed46d297fff274ca5689e6",
    "bourgain-chang-2006.pdf": "a4c130e401ff03a5b91fbd20339f06021f26bf871ca2bb375f2ce25e3ee5d1d7",
    "bourgain-varju-1006.3365.pdf": "4cca2184078d800609defec5ed4dcc5be736180d9a7c02924690d98babdd0356",
    "erdelyi-1406.2233.pdf": "413d8d38ebfe2d99394886f096ed38b8466308fdc61738b700d02e41a9285c40",
    "konieczny-1611.09985v2.pdf": "92cc1e1f37a924d89bb2788d883670eba2604c2d56a029d94c750803e78c2360",
    "salehi-golsefidy-varju-1108.4900v3.pdf": "3d64af888a107edb190dcd713b3f82584d2b55426bca7e93bd5dfa5058179d68",
    "singh-venkataramana-1208.6460v2.pdf": "edc121df43a7921658c4e5ab4d728ad3021de746f9712ba5f92db933d0b0c1b3",
}


def sha256(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1 << 20), b""):
            h.update(block)
    return h.hexdigest()


def matmul(a: list[list[int]], b: list[list[int]]) -> list[list[int]]:
    return [
        [sum(a[i][k] * b[k][j] for k in range(len(b))) for j in range(len(b[0]))]
        for i in range(len(a))
    ]


def identity(n: int) -> list[list[int]]:
    return [[int(i == j) for j in range(n)] for i in range(n)]


def determinant(a: list[list[int]]) -> int:
    if len(a) == 1:
        return a[0][0]
    return sum(
        (-1) ** j
        * a[0][j]
        * determinant([row[:j] + row[j + 1 :] for row in a[1:]])
        for j in range(len(a))
    )


def is_squarefree(n: int) -> bool:
    p = 2
    while p * p <= n:
        if n % (p * p) == 0:
            return False
        p += 1
    return True


def check_hashes() -> None:
    for name, expected in EXPECTED_HASHES.items():
        actual = sha256(ROOT / name)
        assert actual == expected, (name, actual, expected)
        print(f"HASH OK {name} {actual}")


def check_report_contract() -> None:
    report = (ROOT / "REPORT.md").read_text(encoding="utf-8")
    assert report.count("PRIMARY_SOURCE_COUNT: 8") == 1
    assert report.count("RETAINED_CANDIDATE_COUNT: 3") == 1
    for candidate in ("Candidate H1", "Candidate H2", "Candidate M1"):
        assert report.count(candidate) == 1
    for comparator in (
        "Semantic obstruction memory",
        "T63 audit",
        "T78 note",
        "T79 note",
        "T104 note",
        "T105 note",
        "T112 note",
        "T114 note",
        "T115 note",
        "T117 note",
        "T118 note",
        "Rejected T119",
        "T120 note",
        "T121 note",
        "Active T122",
        "Active T123",
    ):
        assert comparator in report, comparator
    assert report.count("**Verdict:") == 1
    assert "**Verdict: hold as model.**" in report
    assert report.count("**Bounded successor (one):**") == 1
    assert report.count("PI-MON-T") >= 2
    assert "This note establishes no property of the fixed decimal orbit" in report
    print("CONTRACT OK 8 sources, 3 candidates, 1 verdict, 1 successor")


def check_h1_matrices() -> None:
    a = [[0, -1], [1, 1]]
    b = [[0, -1], [1, 2]]
    ainv = [[1, 1], [-1, 0]]
    t = [[1, 1], [0, 1]]
    tinv = [[1, -1], [0, 1]]
    s = [[0, -1], [1, 0]]
    assert determinant(a) == determinant(b) == 1
    assert matmul(ainv, a) == identity(2)
    assert matmul(ainv, b) == t
    assert matmul(a, tinv) == s
    for m in range(1, 9):
        q = 10**m
        group_size = 72 * 10 ** (3 * m - 2)
        fiber_size = 72 * 10 ** (2 * m - 2)
        assert group_size == q * fiber_size
    print("H1 OK companion matrices and balanced-fiber divisibility m=1..8")


def check_h2_matrices() -> None:
    a = [
        [0, 0, 0, -1],
        [1, 0, 0, 4],
        [0, 1, 0, -6],
        [0, 0, 1, 4],
    ]
    b = [
        [0, 0, 0, -1],
        [1, 0, 0, 2],
        [0, 1, 0, -3],
        [0, 0, 1, 2],
    ]
    c = [
        [1, 0, 0, -2],
        [0, 1, 0, 3],
        [0, 0, 1, -2],
        [0, 0, 0, 1],
    ]
    assert determinant(a) == determinant(b) == 1
    assert matmul(a, c) == b
    assert all(is_squarefree(10**m) == (m == 1) for m in range(1, 9))
    print("H2 OK companion matrices; only q=10 in the decimal tower is squarefree")


def rudin_state(m: int, steps: int) -> tuple[int, int, int]:
    modulus = 10**m
    p, q, e = 1, 1, 10 % modulus
    for _ in range(steps):
        p, q, e = (p + e * q) % modulus, (p - e * q) % modulus, e * e % modulus
    return p, q, e


def check_m1_freeze() -> None:
    for m in range(1, 33):
        s0 = math.ceil(math.log2(m)) if m > 1 else 0
        p, q, e = rudin_state(m, s0)
        assert e == 0
        p1, q1, e1 = rudin_state(m, s0 + 1)
        p2, q2, e2 = rudin_state(m, s0 + 2)
        assert p1 == q1 and e1 == 0
        assert (p1, q1, e1) == (p2, q2, e2)
    print("M1 OK decimal specialization freezes by ceil(log2(m))+1 for m=1..32")


def check_threshold() -> None:
    constant = 131072
    assert constant == 2**17
    assert 2 * constant**2 == 2**35 == 34359738368
    for a in (1, 2, 5):
        for n in (1, 3, 9):
            j = 2 * constant**2 * a**4 * n**4
            assert 2 * j * (constant * a**2 * n**2) ** 2 <= j**2
    print("T10 BUDGET OK J >= 2^35 A^4 n^4 implies sqrt(2J) <= J/(2^17 A^2 n^2)")


def main() -> None:
    check_hashes()
    check_report_contract()
    check_h1_matrices()
    check_h2_matrices()
    check_m1_freeze()
    check_threshold()
    print("T124 REPLAY PASS")


if __name__ == "__main__":
    main()
