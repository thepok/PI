#!/usr/bin/env python3
"""Deterministic replay for the source pins and elementary T88 identities."""

from fractions import Fraction
from hashlib import sha256
from pathlib import Path
import cmath


ROOT = Path(__file__).resolve().parent

EXPECTED = {
    "REPORT.md": "ca481e2d235955cbb137dc752a846a6de510cde1416cd0a2af308bb5a382b066",
    "SOURCE_PINS.md": "12e486cdd42796a65ada7f611b5b85bf73a2edaf0c5e07ce2f6d57be3de33902",
    "canonical_statement.txt": "cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8",
    "T55SignedMultiplierTenPairing.lean": "025f3f7095f18bc542797113073d2bb20921895582dd49eb553b415952f31ffd",
    "T61DirectLabelAdjacentPhaseVariance.lean": "2eaecb2df11027d6ed5911a16fe571b042afbe42e18daf57eaaffc668f74dbdb",
    "T67TerminalRayStrength.lean": "e9fc18166d2b31c52adbfe73bfcbb10ccd8d93c785fb39144b88db75ed493dff",
    "cuny-eisner-farkas-1701.00101v6.pdf": "fdcc0b42f7f1472acfd9d8a984a1f061ab5f1eaf2db6abebe6705137d6d4e237",
    "cuny-eisner-farkas-1701.00101v6.txt": "ee8aafd40cdb6b08c4c63833fba96b15806d27ba7b32742d8dd9f9d722233d6a",
    "hagelstein-herden-stokolos-1910.09054v1.pdf": "cbae98a5eed652c00907d8f302a62daef2b8cdede915bc0f0029ba3e04d93d30",
    "birkhoff-1931-p656.png": "f210435ec22628da76e7e90060c2ef66c7cd1816079fd63f4640ea2c2b569d57",
    "birkhoff-1931-p657.png": "ae8a4d9876372fa894825f68e9a1670d8bf54edb2d347fefebdf89291c62754d",
    "birkhoff-1931-p658.png": "caa684d81e50aa85198c2ca99104c4a05172d2b869bc026a7fc1edeaf8899fe4",
    "birkhoff-1931-p659.png": "992675f218240fa1746da28d5f1d894f62678d8202b2e75304667ac55071b33f",
    "birkhoff-1931-p660.png": "1f8d14bcee2880570ffee8a34c6184fecbd531bcd633116fc9ea8bc7e0dffefb",
}


def digest(path: Path) -> str:
    return sha256(path.read_bytes()).hexdigest()


def check_hashes() -> None:
    for name, expected in EXPECTED.items():
        actual = digest(ROOT / name)
        assert actual == expected, (name, expected, actual)


def check_source_locators() -> None:
    cef = (ROOT / "cuny-eisner-farkas-1701.00101v6.txt").read_text()
    assert "Theorem 1.1 (Wiener" in cef
    assert "Let µ be a complex Borel measure" in cef
    assert "one can replace here" in cef

    t55 = (ROOT / "T55SignedMultiplierTenPairing.lean").read_text()
    assert "def triangularWeight (R u : ℕ) : ℝ :=" in t55
    assert "def terminalShell (R : ℕ) : Finset ℕ :=" in t55

    t61 = (ROOT / "T61DirectLabelAdjacentPhaseVariance.lean").read_text()
    assert "def directFrequency (ell u j : ℕ) : ℤ :=" in t61
    assert "def directTerminalMass (ell R : ℕ) : ℝ :=" in t61

    t67 = (ROOT / "T67TerminalRayStrength.lean").read_text()
    required = [
        "def finiteEmpiricalFourier",
        "def primitiveDecimalBases",
        "def primitiveDecimalRayShell",
        "def exactRemainderMargin",
        "def T61QualifiedUPRID",
        "directTerminalMass ell R * eta ^ 2 <",
        "∀ u ∈ terminalShell R, ∀ j ∈ range ell",
        "(ell : ℝ) / (4 * (R : ℝ) * delta ^ 2) <",
        "def abstractTerminalMeanSquare",
        "def abstractTriangularMeanSquare",
        "theorem abstract_sparseRay_separator_exact",
        "theorem abstract_bulkShell_separator_exact",
    ]
    for text in required:
        assert text in t67, text


def check_bernoulli_and_shell_arithmetic() -> None:
    probabilities = [Fraction(2, 11)] + [Fraction(1, 11)] * 9
    assert sum(probabilities) == 1
    assert max(probabilities) == Fraction(2, 11) < 1
    assert probabilities[0] != Fraction(1, 10)

    zeta = cmath.exp(2j * cmath.pi / 10)
    first_factor = sum(float(probabilities[d]) * zeta**d for d in range(10))
    assert abs(first_factor - (1 / 11)) < 1e-12

    for r in range(1, 10):
        u = 10**r
        H = 2 * u + 1
        R = H + 1
        assert H // 10 < u <= H
        assert H % 10 != 0
        assert 1 % 10 != 0
        assert u == 10**r * 1
        weight = Fraction(1) - Fraction(u, R)
        assert weight == Fraction(u + 2, 2 * u + 2)
        assert weight > Fraction(1, 2)

        weight_sum = Fraction(H) - Fraction(H * (H + 1), 2 * (H + 1))
        assert weight_sum == Fraction(H, 2)
        assert H - H // 10 > 0

        if r <= 3:
            weights = [Fraction(1) - Fraction(h, H + 1) for h in range(1, H + 1)]
            assert sum(weights) == weight_sum
            shell = list(range(H // 10 + 1, H + 1))
            assert len(shell) == H - H // 10


def check_finite_shift_bound() -> None:
    # The list identity is exact for arbitrary unit-modulus values and r may exceed J.
    for J in range(1, 15):
        for r in range(0, 20):
            values = [cmath.exp(2j * cmath.pi * (k * k + 3) / 37) for k in range(J + r)]
            shifted = sum(values[r : J + r])
            base = sum(values[:J])
            endpoint = sum(values[J : J + r]) - sum(values[:r])
            assert abs((shifted - base) - endpoint) < 1e-12
            assert abs(shifted - base) <= 2 * r + 1e-12


def check_report_terminal_verdict() -> None:
    report = (ROOT / "REPORT.md").read_text().splitlines()
    nonempty = [line for line in report if line.strip()]
    report_text = "\n".join(report)
    assert nonempty[-1] == "SEPARATOR PROVED"
    assert "ITERATED-LIMIT SEPARATOR ONLY" not in report_text
    assert "T67 STATISTIC MISMATCH" not in report_text
    assert "Scope of terminal verdict:" in report_text
    assert "does not instantiate" in report_text


def main() -> None:
    check_hashes()
    check_source_locators()
    check_bernoulli_and_shell_arithmetic()
    check_finite_shift_bound()
    check_report_terminal_verdict()
    print("T88 replay passed: pinned hashes, source tokens, and elementary identities")


if __name__ == "__main__":
    main()
