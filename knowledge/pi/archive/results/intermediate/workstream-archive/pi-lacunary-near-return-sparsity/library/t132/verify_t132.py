#!/usr/bin/env python3
"""Self-contained replay for the finite and provenance checks in T132."""

from collections import defaultdict
from fractions import Fraction
from hashlib import sha256
from pathlib import Path
import re
import subprocess
import tarfile


ROOT = Path(__file__).resolve().parent

EXPECTED = {
    "canonical_statement.txt": "cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8",
    "gallagher-1971.pdf": "3e9adb3a74d10ab8988b6bdd35c612f3581b1e713988ba78d909b7a1dd040943",
    "montgomery-vaughan-1973.pdf": "ba1d6ec4ee264e25eb4f0ca05fede6f582c416e36566f94a5db03693b37838e5",
    "baier-zhao-0512271.pdf": "b0c9932adfd8ed7e48f22a84020d60f27c54def60c36f0dd2b478fbdb17280c4",
    "cicalese-gargano-vaccaro-1901.07530v1.pdf": "90880656635f596a65f51b329f5cdfeacf19278d4239b9db82d783ebc3c98ba3",
    "yadav-shkel-2605.09655v2.pdf": "3d569caf7cf50701d593a2dd57f1824f98243bdcdcfb3c98c83d6074d7007624",
    "konieczny-1611.09985v2.pdf": "92cc1e1f37a924d89bb2788d883670eba2604c2d56a029d94c750803e78c2360",
    "fan-konieczny-1806.04267v2.pdf": "e5fdb01f5f1c717cd5733158edcb97cf70d2f4a18f423c9ab6fd8476fb67f114",
    "prior_evidence.tar.gz": "e21239cfda1d2ba118634056f38811dc24e259793b021606462d50b1e47294e0",
}

COMPARATOR_HASHES = {
    "prior-t130-REPORT.md": "c130b2c8790dce80080367201e56efb3847f8262189af57f2ce756aacb6a893c",
    "prior-t131-REPORT.md": "ed2229ceedcff357f80121fbdc31ffbb8e3582717f487a3a85368eabe64790db",
}


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


def frac(x):
    return x - x.numerator // x.denominator


def block(x, i, m):
    y = frac((10**i) * x)
    z = (10**m) * y
    return z.numerator // z.denominator


def exact_energy(labels, weights):
    fibers = defaultdict(Fraction)
    for label, weight in zip(labels, weights):
        fibers[label] += weight
    return sum(value * value for value in fibers.values())


def residue_energy(labels, weights, q):
    fibers = defaultdict(Fraction)
    for label, weight in zip(labels, weights):
        fibers[label % q] += weight
    return sum(value * value for value in fibers.values())


def ordered_energy(labels, weights):
    total = Fraction(0)
    diagonal = Fraction(0)
    for i in range(len(labels)):
        diagonal += weights[i] * weights[i]
        for j in range(len(labels)):
            if labels[i] == labels[j]:
                total += weights[i] * weights[j]
    return total, diagonal


def circle_distance(x):
    y = frac(x)
    return min(y, 1 - y)


def near_return_count(x, m, n):
    cutoff = Fraction(1, 10**m)
    return sum(
        circle_distance(((10**i) - (10**j)) * x) < cutoff
        for i in range(n)
        for j in range(n)
    )


def sorted_profile(labels, weights, q):
    fibers = defaultdict(Fraction)
    total = sum(weights)
    for label, weight in zip(labels, weights):
        fibers[label % q] += weight
    return sorted((fibers[r] / total for r in range(q)), reverse=True)


def meet(profiles):
    width = max(map(len, profiles))
    padded = [p + [Fraction(0)] * (width - len(p)) for p in profiles]
    cumulative = []
    for k in range(1, width + 1):
        cumulative.append(min(sum(p[:k]) for p in padded))
    result = [cumulative[0]]
    result.extend(cumulative[k] - cumulative[k - 1] for k in range(1, width))
    assert result == sorted(result, reverse=True)
    assert sum(result) == 1
    return result


def report_counter(report, name):
    match = re.search(rf"^{name}: ([0-9]+)$", report, re.MULTILINE)
    assert match, name
    return int(match.group(1))


def main():
    print("T132 self-contained replay")

    for name, wanted in EXPECTED.items():
        got = digest(ROOT / name)
        assert got == wanted, (name, got, wanted)
    print(f"hashes: ok ({len(EXPECTED)} pinned inputs)")

    report = (ROOT / "REPORT.md").read_text(encoding="utf-8")
    assert report_counter(report, "SEARCHED_DOMAIN_COUNT") == 3
    assert report_counter(report, "SEARCHED_DOMAIN_CAP") == 3
    assert report_counter(report, "PRIMARY_SOURCE_COUNT") == 7
    assert report_counter(report, "PRIMARY_SOURCE_CAP") == 8
    assert report_counter(report, "RETAINED_CANDIDATE_COUNT") == 2
    assert report_counter(report, "RETAINED_CANDIDATE_CAP") == 2
    assert report_counter(report, "SURVIVOR_COUNT") == 1
    assert report_counter(report, "TERMINAL_VERDICT_COUNT") == 1
    assert report_counter(report, "SUCCESSOR_COUNT") == 0
    assert report.count("VERDICT:") == 1
    assert "VERDICT: hold as model" in report
    assert "FIXED_PI_CLAIM: none" in report
    assert "C1_CLAIM: none" in report
    assert "C2_CLAIM: none" in report
    assert "PI-MEET (conjecture; unproved)" in report
    assert "T130 active boundary" not in report
    assert "T131 active boundary" not in report
    assert "prior-t130-REPORT.md" in report
    assert "prior-t131-REPORT.md" in report
    print("caps and scope markers: ok")

    source_pins = (ROOT / "SOURCE_PINS.md").read_text(encoding="utf-8")
    assert "Anuj Kumar Yadav and Yanina Y. Shkel" in source_pins
    assert "Aditya Kumar Yadav" not in source_pins
    assert "PDF p. 7, Theorem 3 and equation (36)" in source_pins
    metadata = subprocess.run(
        ["pdfinfo", str(ROOT / "yadav-shkel-2605.09655v2.pdf")],
        check=True,
        capture_output=True,
        text=True,
    ).stdout
    assert "Anuj Kumar Yadav; Yanina Y. Shkel" in metadata
    page7 = subprocess.run(
        [
            "pdftotext",
            "-f",
            "7",
            "-l",
            "7",
            "-layout",
            str(ROOT / "yadav-shkel-2605.09655v2.pdf"),
            "-",
        ],
        check=True,
        capture_output=True,
        text=True,
    ).stdout
    assert "Theorem 3." in page7 and "(36)" in page7
    print("S5 author and PDF-page locator: ok")

    with tarfile.open(ROOT / "prior_evidence.tar.gz", "r:gz") as archive:
        members = {
            Path(member.name).name: member
            for member in archive.getmembers()
            if member.isfile()
        }
        required = {
            "prior-t117-REPORT.md",
            "prior-t118-REPORT.md",
            "prior-t121-REPORT.md",
            "prior-t124-UNVERIFIED-REPORT.md",
            "prior-t130-REPORT.md",
            "prior-t131-REPORT.md",
        }
        assert required <= members.keys()
        for name, wanted in COMPARATOR_HASHES.items():
            payload = archive.extractfile(members[name]).read()
            assert sha256(payload).hexdigest() == wanted
    print("prior comparator bundle: ok")

    # Half-open endpoints and literal floor labels.
    for m in range(1, 4):
        scale = 10**m
        for b in range(scale):
            y = Fraction(b, scale)
            assert (scale * y).numerator // (scale * y).denominator == b
            if b + 1 < scale:
                right = Fraction(b + 1, scale)
                assert (scale * right).numerator // (scale * right).denominator == b + 1
    print("half-open endpoint convention: ok")

    # The exact floor/carry decomposition, including terminating rationals.
    xs = [Fraction(1, 7), Fraction(13, 97), Fraction(1, 10), Fraction(123, 1000)]
    for x in xs:
        for i in range(6):
            for m in range(2, 6):
                for ell in range(1, m):
                    lhs = block(x, i, m)
                    rhs = (10**ell) * block(x, i, m - ell) + block(x, i + m - ell, ell)
                    assert lhs == rhs
                    assert lhs % (10**ell) == block(x, i + m - ell, ell)
    print("floor/carry and power-of-ten projection identities: ok")

    # Weighted ordered-pair identity, diagonal, and C <= E_q.
    labels = [0, 0, 2, 5, 5]
    weights = list(map(Fraction, [2, 3, 1, 4, 2]))
    energy = exact_energy(labels, weights)
    ordered, diagonal = ordered_energy(labels, weights)
    assert energy == ordered
    assert diagonal == sum(w * w for w in weights)
    for q in range(1, 10):
        assert energy <= residue_energy(labels, weights, q)
    print("weighted multiplicity, ordered pairs, diagonal, C<=E_q: ok")

    # Strict factor-three comparison for literal orbit examples.
    for x in xs:
        for m in range(1, 4):
            for n in range(1, 9):
                labels = [block(x, i, m) for i in range(n)]
                c = exact_energy(labels, [Fraction(1)] * n)
                qx = near_return_count(x, m, n)
                assert c <= qx <= 3 * c
                assert qx >= n
    print("factor-three near-return comparison: ok")

    # Actual residue profiles with strict majorization-meet gain.
    labels = list(range(6))
    weights = list(map(Fraction, [3, 1, 1, 3, 1, 1]))
    c = exact_energy(labels, weights)
    e2 = residue_energy(labels, weights, 2)
    e3 = residue_energy(labels, weights, 3)
    p2 = sorted_profile(labels, weights, 2)
    p3 = sorted_profile(labels, weights, 3)
    w = meet([p2, p3])
    n = sum(weights)
    g = n * n * sum(value * value for value in w)
    joint = exact_energy([(b % 2, b % 3) for b in labels], weights)
    assert (c, e2, e3) == (22, 50, 44)
    assert p2 == [Fraction(1, 2), Fraction(1, 2)]
    assert p3 == [Fraction(3, 5), Fraction(1, 5), Fraction(1, 5)]
    assert w == [Fraction(1, 2), Fraction(3, 10), Fraction(1, 5)]
    assert c <= joint <= g == 38
    assert g < min(e2, e3) < (e2 + e3) / 2
    print("C-MEET strict gain: C=22, G=38, min=44, average=47")

    # The displayed single-modulus parameter implication.
    a, m, n, q, delta = 2, 3, 120, 40, Fraction(300)
    assert q >= 6 * a * m and q < 10**m
    assert delta <= Fraction(n * n, 6 * a * m)
    eq = Fraction(n * n, q) + delta
    assert eq <= Fraction(n * n, 3 * a * m)
    assert a * m * 3 * eq <= n * n
    assert n >= 3 * a * m
    print("parameter screen: ok (A=2,m=3,N=120,q=40,Delta=300)")

    print("all T132 replay checks passed")


if __name__ == "__main__":
    main()
