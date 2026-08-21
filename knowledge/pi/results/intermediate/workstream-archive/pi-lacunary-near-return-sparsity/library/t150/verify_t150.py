#!/usr/bin/env python3
"""Finite transcription and falsification checks for the T150 audit."""

from fractions import Fraction
from hashlib import sha256
from itertools import product
from math import ceil, log, sqrt
from pathlib import Path
import re
import subprocess
import tarfile
import tempfile


ROOT = Path(__file__).resolve().parent

EXPECTED = {
    "canonical_statement.txt": "cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8",
    "bkl-2002.00576v3.pdf": "33559640a83bb96b9e8d07f75959a83d913f74d3d8794f6d3daa0d482683285f",
    "chazottes-gabrielli-math0406083.pdf": "a15f64613f8df0f6e25fdb0410c4e85037ab87736f02c93e1679e97301c5c89b",
    "chazottes-gouezel-1111.0849.pdf": "030d9857555fb5cdb680977ab55f89ad897e897f326f9468c38d9118a776de99",
    "varandas-zhao-1203.4409v3.pdf": "68f52ce21d382cd13eed68ea70a13a883e3f2d2834e63096379b3efdd9c736ce",
    "eichelsbacher-schmock-2002.pdf": "d47f732342d197bd0bc46e6fbf1b2e613f35e09425794bf76ff7fa36eb38c800",
    "sahlsten-stevens-2009.01703.pdf": "ba4878034d08a46c0e5cad13b4028922ba1ae058f0a55d11f111c4d8706693bf",
}

COMPARATORS = {
    "prior-T140-REPORT.md": "ff05177ccaaebfd56d41467f2f74dce085aae3b855be95f6d1c458526541f35c",
    "prior-T144-REPORT.md": "96c685692710b05035208ca459e4536f992bef2a69c030cc318625c5de00da7a",
    "prior-T147-REPORT.md": "d1af43d8b2c21c6b3106a4c75e8e38467146e7c09f219adf240ee83a9250a909",
}

ANCHORS = {
    "bkl-2002.00576v3.pdf": [
        r"Theorem A \(Variational principle\)",
        r"abundance of ergodic measures",
    ],
    "chazottes-gabrielli-math0406083.pdf": [
        r"Theorem 3\.1 \(Large deviation principles for empirical entropies\)",
        r"k\(n\).*log n",
    ],
    "chazottes-gouezel-1111.0849.pdf": [
        r"Theorem 2\.1\. The system",
        r"exponential concentration inequality",
    ],
    "varandas-zhao-1203.4409v3.pdf": [
        r"Theorem B\. Assume that",
        r"weak Gibbs measure",
        r"sub-additive family of potentials",
    ],
    "eichelsbacher-schmock-2002.pdf": [
        r"HEOREM 1\.7",
        r"HEOREM 1\.10",
        r"Strong Cramer condition|Strong Cram.r condition",
    ],
    "sahlsten-stevens-2009.01703.pdf": [
        r"Theorem 1\.1\. Suppose",
        r"Theorem 2\.1 \(Large.*deviations\)",
        r"Lemma 5\.6 \(Non-concentration\)",
    ],
}


def digest(data):
    return sha256(data).hexdigest()


def assert_hashes():
    for name, wanted in EXPECTED.items():
        got = digest((ROOT / name).read_bytes())
        assert got == wanted, (name, got, wanted)


def assert_comparator_archive():
    with tarfile.open(ROOT / "PRIOR_EVIDENCE.tar", "r") as archive:
        names = sorted(member.name for member in archive.getmembers() if member.isfile())
        assert names == sorted(COMPARATORS)
        for name, wanted in COMPARATORS.items():
            handle = archive.extractfile(name)
            assert handle is not None
            assert digest(handle.read()) == wanted


def assert_pdf_anchors():
    with tempfile.TemporaryDirectory() as directory:
        for name, patterns in ANCHORS.items():
            output = Path(directory) / (name + ".txt")
            subprocess.run(
                ["pdftotext", "-layout", str(ROOT / name), str(output)],
                check=True,
                stdout=subprocess.DEVNULL,
                stderr=subprocess.DEVNULL,
            )
            text = " ".join(output.read_text(errors="replace").split())
            for pattern in patterns:
                assert re.search(pattern, text, re.IGNORECASE), (name, pattern)


def blocks(word, m, starts):
    return [tuple(word[i : i + m]) for i in range(starts)]


def energy(word, m, starts):
    counts = {}
    for block in blocks(word, m, starts):
        counts[block] = counts.get(block, 0) + 1
    return sum(value * value for value in counts.values())


def pair_energy(word, m, starts):
    values = blocks(word, m, starts)
    return sum(values[i] == values[j] for i in range(starts) for j in range(starts))


def joint_statistic(word, starts, depths):
    return min(Fraction(m * energy(word, m, starts), starts * starts) for m in depths)


def assert_energy_and_expectation():
    sample = (0, 1, 0, 1, 0)
    for m in (1, 2, 3):
        assert energy(sample, m, 3) == pair_energy(sample, m, 3)

    # Exact uniform decimal expectation with N=2 starts, m=2, L=3.
    total = sum(energy(word, 2, 2) for word in product(range(10), repeat=3))
    mean_c = Fraction(total, 10**3 * 2**2)
    expected = Fraction(1, 2) + Fraction(1, 2 * 10**2)
    assert mean_c == expected


def assert_oscillation_bound():
    starts, k = 4, 2
    depths = (1, 2)
    bound = Fraction(4 * k * k, starts)
    maximum = Fraction(0)
    for word in product(range(2), repeat=starts + k - 1):
        old = joint_statistic(word, starts, depths)
        for coordinate in range(len(word)):
            changed = list(word)
            changed[coordinate] = 1 - changed[coordinate]
            delta = abs(old - joint_statistic(changed, starts, depths))
            maximum = max(maximum, delta)
            assert delta <= bound
    return maximum, bound


def debruijn(alphabet_size, order):
    a = [0] * (alphabet_size * order)
    sequence = []

    def visit(t, period):
        if t > order:
            if order % period == 0:
                sequence.extend(a[1 : period + 1])
            return
        a[t] = a[t - period]
        visit(t + 1, period)
        for value in range(a[t - period] + 1, alphabet_size):
            a[t] = value
            visit(t + 1, t)

    visit(1, 1)
    return sequence


def assert_counterfamilies():
    starts, k = 50, 4
    a = ceil(k / 2)
    depths = range(a, k + 1)
    r = ceil(starts / sqrt(a))
    shared = [0] * (r + k - 1) + [digit % 10 for digit in range(starts - r)]
    assert len(shared) == starts + k - 1
    assert all(energy(shared, m, starts) * m >= starts * starts for m in depths)

    for digit in range(10):
        constant = [digit] * (starts + k - 1)
        assert all(energy(constant, m, starts) * m >= starts * starts for m in depths)

    periodic = [i % 2 for i in range(starts + k - 1)]
    assert all(energy(periodic, m, starts) * m >= starts * starts for m in depths)

    order = 2
    cycle = debruijn(10, order)
    assert len(cycle) == 10**order
    db_starts = 10**order
    repeated = cycle + cycle[: order - 1]
    db_energy = energy(repeated, order, db_starts)
    assert db_energy == db_starts * db_starts // (10**order)
    assert db_energy * order < db_starts * db_starts
    return r, db_energy


def assert_t147_compatibility_scale():
    # The ratio of the JC-150 saving (C=1, L~N) to the shared-prefix cost
    # is asymptotic to 1/(64 log(10) k^(7/2)); these checks only illustrate it.
    ratios = [1 / (64 * log(10) * k ** 3.5) for k in (10, 100, 1000, 8000)]
    assert all(ratios[i + 1] < ratios[i] for i in range(len(ratios) - 1))
    return ratios


def assert_report_structure():
    report = (ROOT / "REPORT.md").read_text()
    required = [
        "PRIMARY_SOURCE_COUNT: 6",
        "PRIMARY_SOURCE_CAP: 8",
        "DOMAIN_COUNT: 4",
        "THEOREM_CANDIDATE_COUNT: 3",
        "THEOREM_CANDIDATE_CAP: 3",
        "SCOPED_VERDICT_COUNT: 1",
        "SUCCESSOR_COUNT: 1",
        "SCOPED_VERDICT (1/1): **develop**",
        "SUCCESSOR (1/1):",
        "PI-T107-TRANSFER-T150",
        "UNPROVED PI-SPECIFIC TRANSFER PREMISE",
        "FIXED_PI_CLAIM: none",
        "A1_CLAIM: none",
        "C1_CLAIM: none",
        "C2_CLAIM: none",
        "#J_(N,k)",
        "(JC-150)",
        "T140",
        "T144",
        "T147",
        "Constant words",
        "Periodic words",
        "Repeated de Bruijn words",
    ]
    for marker in required:
        assert marker in report, marker
    assert report.count("SCOPED_VERDICT (1/1):") == 1
    assert report.count("SUCCESSOR (1/1):") == 1


def main():
    assert_hashes()
    assert_comparator_archive()
    assert_pdf_anchors()
    assert_energy_and_expectation()
    maximum, bound = assert_oscillation_bound()
    prefix_length, db_energy = assert_counterfamilies()
    ratios = assert_t147_compatibility_scale()
    assert_report_structure()
    print("T150 REPLAY: PASS")
    print("primary_sources=6 cap=8")
    print("domains=4 minimum=3")
    print("theorem_candidates=3 cap=3")
    print("candidate_results=P:inapplicable,H:inapplicable,C:survives-related-model")
    print(f"oscillation_max={maximum} bound={bound}")
    print(f"shared_prefix_test_R={prefix_length}")
    print(f"debruijn_order2_energy={db_energy}")
    print("compatibility_ratios_C1=" + ",".join(f"{value:.3e}" for value in ratios))
    print("scoped_verdict=develop")
    print("successor_count=1")
    print("fixed_pi_claim=none A1_claim=none C1_claim=none C2_claim=none")
    print("labels=literature-checked,proof sketch,experiment,related-model,conjecture")


if __name__ == "__main__":
    main()
