#!/usr/bin/env python3
"""Network-free replay for T149 hashes and finite identities.

The computations are experiments. The universal counterfamily arguments are
the proofs in REPORT.md, not finite enumeration.
"""

from collections import Counter
from fractions import Fraction
from hashlib import sha256
from pathlib import Path
import tarfile


ROOT = Path(__file__).resolve().parent

EXPECTED = {
    "canonical_statement.txt": "cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8",
    "gijswijt-schijver-tanaka-2006.pdf": "ff8dd592069b95aaa1e5eba07e82a667641b31405e5a7cdb4b9b308235fc4983",
    "gijswijt-schijver-tanaka-2006.txt": "f218bb3eb1b699528439435825490e32dd4e67db8131e957565f3c85ba841b4f",
    "gijswijt-0910.4515v1.pdf": "b7554d0e58abc6b32f4f1aef6bcfd689f5add8d2c56de99bd48b67ff00c71d28",
    "gijswijt-0910.4515v1.txt": "932c043893872891f8fdb9ccacbe10ef0b7732e58d87731e099a699bee8571e9",
    "baker-khalil-sahlsten-2407.16699v3.pdf": "95f0cc2e23c1c46438b51a331dcc69922cff0c1a266d646e47e2e16c78b8b0a0",
    "baker-khalil-sahlsten-2407.16699v3.txt": "418b7a5bff7b1f2aec6bacf1ee525f0cfed66f48044a081de452e129bd0d65d1",
    "montgomery-vaughan-1973.pdf": "ba1d6ec4ee264e25eb4f0ca05fede6f582c416e36566f94a5db03693b37838e5",
    "montgomery-vaughan-1973.txt": "c1be79a7b3f13f6496aff93727b19bfbb2b63e1226ee5c352524e56beb631c31",
    "prior_evidence.tar.gz": "1f1607b4accb32262c9decde945efab5a85d09391f988d4a8f5376ee1235df7a",
}

PRIOR_MEMBERS = {
    "knowledge_library/t110/REPORT.md": "4eaa088ecb7ea8936d5c35d1eefb66027b376a020c8e76f4a2b91c012a3cb668",
    "knowledge_library/t130/prior-t119-REPORT.md": "72b10e921761874158893bb9cbb7454094bcbc59bbdfc787f33bbf355b63f23a",
    "knowledge_library/t121/REPORT.md": "01b97953941608b41b0fcd12cc5be0047f447be28d7cd26f8bae6506717e6cf2",
    "knowledge_library/t125/REPORT.md": "1ce372d3a99323eae9460a4dbc25b329b93b66e0a356aa3284f1fc9c543f461a",
    "knowledge_library/t132/REPORT.md": "1d1aa950f21bb35697a5301cd3dbcacb27fec50a70d98009f1bb9f6179fe23bd",
    "knowledge_library/t135/REPORT.md": "4439850a49ee2fa7351d85daf366eba4b2b4a55e756a15bf7c431d92fb195e21",
    "knowledge_library/t140/REPORT.md": "ff05177ccaaebfd56d41467f2f74dce085aae3b855be95f6d1c458526541f35c",
    "knowledge_library/notes/t144/REPORT.md": "96c685692710b05035208ca459e4536f992bef2a69c030cc318625c5de00da7a",
    "orchestrator-input.json": "6fa4544725bb497cf2c6b744b31210718dd7e28a9759c89a7983224272ba17d5",
}

ANCHORS = {
    "gijswijt-schijver-tanaka-2006.txt": [
        "Proposition 8. The matrix R0 is given by",
        "Proposition 9.",
        "are positive semidefinite.",
    ],
    "gijswijt-0910.4515v1.txt": [
        "Theorem 6. The map",
        "Theorem 8. The map",
        "Terwilliger algebra of the nonbinary Hamming scheme",
    ],
    "baker-khalil-sahlsten-2407.16699v3.txt": [
        "Definition 1.1.",
        "Theorem 1.5.",
        "polylogarithmic Fourier decay",
    ],
    "montgomery-vaughan-1973.txt": ["THEOREM 1.", "(1.4)"],
}


def digest(name):
    return sha256((ROOT / name).read_bytes()).hexdigest()


def blocks(period, m, M):
    digits = [period[i % len(period)] for i in range(M + m - 1)]
    return [tuple(digits[i : i + m]) for i in range(M)]


def energy(words):
    counts = Counter(words)
    return sum(value * value for value in counts.values()), counts


def weighted_balance(digits, m, M, weights):
    left = Counter()
    right = Counter()
    rhs = Counter()
    for i in range(M):
        word = tuple(digits[i : i + m])
        left[word[:-1]] += weights[i]
        right[word[1:]] += weights[i]
    empty = Fraction(0)
    u0 = tuple(digits[0 : m - 1])
    uM = tuple(digits[M : M + m - 1])
    rhs[u0] += weights[0]
    rhs[uM] -= weights[M - 1]
    for j in range(1, M):
        uj = tuple(digits[j : j + m - 1])
        rhs[uj] += weights[j] - weights[j - 1]
    keys = set(left) | set(right) | set(rhs)
    return all(left.get(k, empty) - right.get(k, empty) == rhs.get(k, empty) for k in keys)


def de_bruijn(q, n):
    """FKM construction of a cyclic q-ary de Bruijn sequence of order n."""
    a = [0] * (q * n + 1)
    sequence = []

    def db(t, p):
        if t > n:
            if n % p == 0:
                sequence.extend(a[1 : p + 1])
        else:
            a[t] = a[t - p]
            db(t + 1, p)
            for j in range(a[t - p] + 1, q):
                a[t] = j
                db(t + 1, t)

    db(1, 1)
    return sequence


def hamming_type(x, y, z):
    i = sum(a != b for a, b in zip(x, y))
    j = sum(a != c for a, c in zip(x, z))
    u = sum(a != b and a != c for a, b, c in zip(x, y, z))
    v = sum(a != b and b == c for a, b, c in zip(x, y, z))
    assert sum(b != c for b, c in zip(y, z)) == i + j - u - v
    return i, j, u, v


def check_triples(counts):
    lambdas = Counter()
    for x, cx in counts.items():
        for y, cy in counts.items():
            for z, cz in counts.items():
                lambdas[hamming_type(x, y, z)] += cx * cy * cz
    total = sum(counts.values())
    return sum(lambdas.values()) == total**3


def main():
    for name, expected in EXPECTED.items():
        actual = digest(name)
        assert actual == expected, (name, actual, expected)
        print(f"HASH {actual}  {name}")

    for name, anchors in ANCHORS.items():
        text = (ROOT / name).read_text(encoding="utf-8", errors="replace")
        for anchor in anchors:
            assert anchor in text, (name, anchor)
        print(f"ANCHORS_OK {name} count={len(anchors)}")

    with tarfile.open(ROOT / "prior_evidence.tar.gz", "r:gz") as archive:
        members = {member.name: member for member in archive.getmembers() if member.isfile()}
        assert set(members) == set(PRIOR_MEMBERS)
        for name, expected in PRIOR_MEMBERS.items():
            stream = archive.extractfile(members[name])
            assert stream is not None
            actual = sha256(stream.read()).hexdigest()
            assert actual == expected, (name, actual, expected)
    print(f"PRIOR_EVIDENCE_OK members={len(PRIOR_MEMBERS)}")

    # Formula (2.4), including nonconstant rational start weights.
    digits = [0, 1, 0, 2, 0, 1, 2, 2]
    weights = [Fraction(1, 2), Fraction(2, 3), Fraction(3, 5), Fraction(5, 7)]
    assert weighted_balance(digits, 5, 4, weights)
    print("WEIGHTED_BALANCE_OK m=5 M=4")

    # Constant obstruction.
    m, M = 7, 35
    e, counts = energy(blocks([0], m, M))
    assert e == M * M and check_triples(counts)
    print(f"CONSTANT_OK m={m} M={M} E={e}")

    # Arbitrary primitive-period obstruction, with no wrapping among starts.
    p, m, M = 17, 31, 170
    primitive_period = [0] * (p - 1) + [1]
    words = blocks(primitive_period, m, M)
    e, counts = energy(words)
    assert len(counts) == p and set(counts.values()) == {M // p}
    assert e == M * M // p and m > p and check_triples(counts)
    print(f"PERIOD_OK p={p} m={m} M={M} E={e}")

    # Base-10 repeated de Bruijn obstruction. All local laws through r are
    # uniform; the tested m exceeds the period, so E=M^2/10^r > M^2/m.
    q, r, k, m = 10, 2, 3, 201
    period = de_bruijn(q, r)
    period_size = q**r
    M = k * period_size
    assert len(period) == period_size
    for ell in range(1, r + 1):
        local = Counter(blocks(period, ell, period_size))
        assert len(local) == q**ell
        assert set(local.values()) == {q ** (r - ell)}
    words = blocks(period, m, M)
    e, counts = energy(words)
    assert len(counts) == period_size and set(counts.values()) == {k}
    assert e == M * M // period_size
    assert e > Fraction(M * M, m)
    assert check_triples(counts)
    print(f"DEBRUIJN_OK q={q} r={r} m={m} M={M} E={e}")

    # The explicit non-universal atom-cap implication (4.1).
    synthetic = Counter({("a",): 4, ("b",): 3, ("c",): 3})
    total = sum(synthetic.values())
    cap = max(synthetic.values())
    e = sum(v * v for v in synthetic.values())
    assert e <= total * cap
    print(f"ATOM_CAP_IDENTITY_OK M={total} max={cap} E={e}")

    report = (ROOT / "REPORT.md").read_text(encoding="ascii")
    assert report.count("**CLOSE:**") == 1
    assert "SUCCESSOR_COUNT: 0" in report
    assert "FIXED_PI_CLAIM: none" in report
    print("REPORT_SENTINELS_OK verdict=1 successors=0")
    print("ALL_T149_CHECKS_PASSED")


if __name__ == "__main__":
    main()
