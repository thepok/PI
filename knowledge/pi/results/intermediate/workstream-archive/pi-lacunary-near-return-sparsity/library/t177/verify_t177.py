#!/usr/bin/env python3
"""Self-contained finite replay for the T177 proof-sketch artifact."""

from __future__ import annotations

import csv
import hashlib
import itertools
import math
from pathlib import Path


ROOT = Path(__file__).resolve().parent
CANONICAL_SHA = "cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8"
SOURCE_SHA = {
    "hoyrup-rojas-0709.0907v2.pdf": "23172258a7b9f47356972c4e3f49e0d151ff8ba9a1d7ec190f45bbbdcd4c5b7d",
    "hoyrup-rojas-0709.0907v2.txt": "587d18c2d49c3d44b7d262ea37da32793bb8094902470829d649da49bc90e026",
    "calude-dinneen-shu-nlin0112022v3.pdf": "16c9df9719783f40aac25730c802c92c3a8459c3a40d4343f6342911f18302de",
    "calude-dinneen-shu-nlin0112022v3.txt": "6f50684f9907bfcd381c03e55cd49cce788d498ad28bc420f404ff8db06ac1cb",
    "lyons-peres-2020-corrected.pdf": "3ba07bc0fb0397dc256610b328c869983d7ab4f709c78952d86646e25a15d043",
    "lyons-peres-2020-corrected.txt": "3f734a0413e5250be19bb227bcae28aec26350eb878101d03ba1496954aaad7a",
    "calude-jurgensen-1994-base-invariance.ps.gz": "4ba7ed65b5f0870d634759844da244f04d686795f65b0bb16e43288b512a31ed",
    "calude-jurgensen-1994-base-invariance.ps": "40452522a63b3b8253832849648270426d40301af39777d9fac5163445ccaa2c",
}


def digest(name: str) -> str:
    return hashlib.sha256((ROOT / name).read_bytes()).hexdigest()


def energy(word: tuple[int, ...], n_starts: int, m: int) -> int:
    blocks = [word[i : i + m] for i in range(n_starts)]
    return sum(a == b for a in blocks for b in blocks)


def m0(a: int) -> int:
    return math.ceil(2 * math.log10(4 * a))


def d_cutoff(a: int) -> int:
    return 2 * math.ceil(math.log2(8 * a))


def r_cutoff(a: int) -> int:
    n = 9
    while 2**n < 16 * a * a * n**6:
        n += 1
    return n


def check_hashes() -> None:
    assert digest("canonical_statement.txt") == CANONICAL_SHA
    for name, expected in SOURCE_SHA.items():
        assert digest(name) == expected, name


def check_ledger() -> None:
    with (ROOT / "SOURCE_LEDGER.csv").open(newline="", encoding="utf-8") as handle:
        rows = list(csv.DictReader(handle))
    assert [row["id"] for row in rows] == ["S1", "S2", "S3", "S4", "S5", "S6"]
    for row in rows:
        if row["pinned_file"]:
            assert digest(row["pinned_file"]) == row["sha256"]


def check_source_locators() -> None:
    hoyrup = (ROOT / "hoyrup-rojas-0709.0907v2.txt").read_text(encoding="utf-8")
    for marker in (
        "Definition 6.1.1",
        "Proposition 6.2.1",
        "Corollary 6.2.1",
        "Corollary 6.2.2",
        "preserve randomness",
    ):
        assert marker in hoyrup
    calude = (ROOT / "calude-dinneen-shu-nlin0112022v3.txt").read_text(encoding="utf-8")
    for marker in (
        "Theorem 2 If U is a universal machine",
        "HALT instruction appears only once",
        "construction is universal in the sense of",
        "compressed programs",
        "prefix-free set",
    ):
        assert marker in calude
    lyons = (ROOT / "lyons-peres-2020-corrected.txt").read_text(encoding="utf-8")
    assert "Theorem 13.35. (Bounded-Di" in lyons
    assert "independent random vari" in lyons
    base_ps = (ROOT / "calude-jurgensen-1994-base-invariance.ps").read_text(encoding="latin-1")
    assert "F23(6.1.)" in base_ps
    assert "(main)S" in base_ps and "(result)S" in base_ps
    assert "(randomness)S" in base_ps and "(represen)S" in base_ps


def check_lag_counts() -> None:
    # Alphabet sizes 2 and 3 test the general graph count q^h/q^(m+h)=q^-m.
    cases = 0
    for q in (2, 3):
        for m in range(1, 6):
            for h in range(1, 7):
                total = q ** (m + h)
                good = 0
                for word in itertools.product(range(q), repeat=m + h):
                    good += word[:m] == word[h : h + m]
                assert good == q**h
                assert good * q**m == total
                cases += 1
    assert cases == 60


def check_expectation() -> None:
    # Exact exhaustive expectation over a small binary product space.
    q, n_starts, m = 2, 4, 3
    values = [energy(word, n_starts, m) for word in itertools.product(range(q), repeat=n_starts + m - 1)]
    lhs = sum(values)
    count = q ** (n_starts + m - 1)
    # Compare as integers: mean = N + N(N-1)q^-m.
    assert lhs * q**m == count * (n_starts * q**m + n_starts * (n_starts - 1))


def check_sensitivity() -> None:
    # Exhaustive replacement checks; the report's 2*m*N bound is deliberately coarse.
    checks = 0
    q = 2
    for n_starts in range(1, 6):
        for m in range(1, 5):
            length = n_starts + m - 1
            for word in itertools.product(range(q), repeat=length):
                e0 = energy(word, n_starts, m)
                for t in range(length):
                    changed = list(word)
                    changed[t] = 1 - changed[t]
                    delta = abs(energy(tuple(changed), n_starts, m) - e0)
                    r_t = sum(i <= t <= i + m - 1 for i in range(n_starts))
                    assert delta <= 2 * r_t * n_starts - r_t * r_t - r_t
                    assert delta <= 2 * m * n_starts
                    checks += 1
    assert checks > 5_000


def check_constants() -> tuple[int, int]:
    max_r = 0
    checked = 0
    for a in range(1, 201):
        s = m0(a)
        assert 10**s >= 4 * a * s
        for m in range(s, s + 30):
            assert 10**m >= 4 * a * m
        d = d_cutoff(a)
        assert 2**d >= 4 * a * d
        r = r_cutoff(a)
        max_r = max(max_r, r)
        assert r >= 9 and 2**r >= 16 * a * a * r**6
        for n in range(max(d, r), max(d, r) + 30):
            assert 2**n >= 4 * a * n
            assert 2**n >= 16 * a * a * n**6
            assert n * math.exp(-(n**2)) <= 2 ** (-n)
        assert 2 ** (-max(d, r) + 1) <= 1 / (32 * a * a)
        checked += 1
    return checked, max_r


def check_report_guards() -> None:
    report = (ROOT / "REPORT.md").read_text(encoding="utf-8")
    assert report.count("SCOPED VERDICT:") == 1
    assert report.count("HOLD AS MODEL") == 1
    assert "unproved pi-transfer" in report
    assert "FIXED_PI_CLAIM: none" in report
    assert "A1_CLAIM: none" in report
    assert "C1_CLAIM: none" in report
    assert "C2_CLAIM: none" in report
    for item in ("T2", "T72", "T74", "T144", "T152"):
        assert item in report
    for item in range(159, 173):
        # The range heading plus explicit fingerprints covers all items; require each ID
        # either literally or via the grouped sentences in the comparison paragraph.
        assert f"T{item}" in report


def check_manifest() -> None:
    manifest = ROOT / "SHA256SUMS"
    if not manifest.exists():
        return
    for line in manifest.read_text(encoding="ascii").splitlines():
        expected, name = line.split("  ", 1)
        assert name != "SHA256SUMS"
        assert digest(name) == expected, name


def main() -> None:
    check_hashes()
    check_ledger()
    check_source_locators()
    check_lag_counts()
    check_expectation()
    check_sensitivity()
    checked, max_r = check_constants()
    check_report_guards()
    check_manifest()
    print("T177 finite replay")
    print(f"canonical_sha256={CANONICAL_SHA}")
    print("source_hashes=8 passed")
    print("source_locators=passed")
    print("lag_probability_cases=60 passed")
    print("expectation_identity=passed")
    print("bounded_difference_exhaustive_checks=>5000 passed")
    print(f"constant_parameter_A_cases={checked} passed")
    print(f"largest_r_cutoff_in_sweep={max_r}")
    print("report_scope_guards=passed")
    print("manifest=passed_or_not_yet_present")
    print("label=experiment_not_proof")


if __name__ == "__main__":
    main()
