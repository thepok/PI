#!/usr/bin/env python3
"""Self-contained integrity and exact-arithmetic replay for T115.

Finite checks validate transcription and displayed algebra only.  They do not
prove source theorems, asymptotic statements, or any assertion about pi.
"""

from fractions import Fraction
from functools import lru_cache
from hashlib import sha256
from pathlib import Path
import math


ROOT = Path(__file__).resolve().parent

EXPECTED_HASHES = {
    "canonical_statement.txt": "cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8",
    "baake-gahler-grimm-1201.1423v1.pdf": "9c6aa8e9a860389480b070e9b2afb4c361895f9e5c0431ebdfe62d9c27b2314c",
    "baake-gahler-grimm-1201.1423v1.txt": "f4ed4ec05ba30a104600b135efc06416706fa147d84a6390377a5c261f65011e",
    "marshall-maldonado-2210.11982v2.pdf": "f3674b8d7a8d16fc0017334aaf8eec1e75cb83fb021446c95bdd73d46d5f8807",
    "marshall-maldonado-2210.11982v2.txt": "8b08c5ed18ae1549464f1a27465b1c9bb9696213c6aa77fdc507d1668058d1b5",
    "baake-grimm-1007.0707v1.pdf": "a4fa3da0734c750ff3a886c4517745d1745abfc3e0aa93a461ad37bf2bddb6a1",
    "baake-grimm-1007.0707v1.txt": "05ab63fce0792ce51941a453cbdecbebaad2b20c37bff5f107739f2603958e32",
    "baake-grimm-0809.0580v1.pdf": "45ba6ad3033c25b5032ebcf353711e43cd54186222104bfbe304890cc337ce03",
    "baake-grimm-0809.0580v1.txt": "d7896bc0ef970179a98512d13431577495f517c0cd9f990555e669cc6b0a3d14",
}


def digest(path: Path) -> str:
    return sha256(path.read_bytes()).hexdigest()


for name, expected in EXPECTED_HASHES.items():
    actual = digest(ROOT / name)
    assert actual == expected, (name, actual, expected)

anchors = {
    "baake-gahler-grimm-1201.1423v1.txt": [
        "A family of generalised Thue-Morse sequences",
        "Lemma 1. Consider the gTM sequence",
        "Proposition 3. The distribution function",
        "fn+1 (z) =",
    ],
    "marshall-maldonado-2210.11982v2.txt": [
        "Lemma 2.16",
        "Theorem 3.5",
        "almost all",
    ],
    "baake-grimm-1007.0707v1.txt": [
        "The period doubling sequence",
        "This implies a recursion for the autocorrelation",
    ],
    "baake-grimm-0809.0580v1.txt": [
        "THE SINGULAR CONTINUOUS DIFFRACTION MEASURE",
        "Riesz product",
    ],
}
for name, markers in anchors.items():
    text = (ROOT / name).read_text(errors="replace")
    for marker in markers:
        assert marker in text, (name, marker)


def alpha(s: int) -> int:
    assert 0 <= s < 10
    return 10 - s - 2 * min(5, 5, s, 10 - s)


assert alpha(0) == 10
assert alpha(1) == 7
assert alpha(9) == -1

theta_hat = {0: Fraction(1)}
for s in range(1, 10):
    theta_hat[s] = Fraction(alpha(s), 10)
    theta_hat[-s] = Fraction(alpha(s), 10)


@lru_cache(maxsize=None)
def coeff(n: int, m: int) -> Fraction:
    """Coefficient c_n(m) from the exact finite mask recursion."""
    assert n >= 0
    if n == 0:
        return Fraction(int(m == 0))
    total = Fraction(0)
    for a, value in theta_hat.items():
        if (m - a) % 10 == 0:
            total += value * coeff(n - 1, (m - a) // 10)
    return total


for n in range(21):
    assert coeff(n, 0) == 1
    expected = Fraction(7, 11) * (1 - Fraction(-1, 10) ** n)
    assert coeff(n, 1) == expected, (n, coeff(n, 1), expected)

for h in range(-7, 8):
    for r in range(0, 8):
        for extra in range(0, 7):
            n = r + extra
            assert coeff(n, h * 10**r) == coeff(extra, h)

for r in range(0, 16):
    assert coeff(r + 1, 10**r) == Fraction(7, 10)
    for n in range(r + 1, r + 8):
        assert abs(coeff(n, 10**r)) >= Fraction(63, 100)

# Literal T67 shell schedule and exact contribution bounds.
for r in range(1, 13):
    ten_r = 10**r
    H = 2 * ten_r + 1
    R = H + 1
    u = ten_r
    assert H // 10 == 2 * 10 ** (r - 1)
    assert H // 10 < u <= H
    assert u == 10**r * 1 and 1 % 10 != 0
    shell_card = H - H // 10
    assert shell_card == 18 * 10 ** (r - 1) + 1
    weight = 1 - Fraction(u, R)
    assert weight == Fraction(ten_r + 2, 2 * ten_r + 2)
    assert weight > Fraction(1, 2)
    spike_sq = Fraction(49, 100)
    terminal_lower = spike_sq / shell_card
    triangular_lower = weight * spike_sq / Fraction(H, 2)
    assert triangular_lower > spike_sq / H
    assert terminal_lower > 0

# Screened period-doubling closed form follows its displayed recursion.
eta_pd = Fraction(-1, 3)
for valuation in range(0, 16):
    expected = 1 - Fraction(4, 3 * 2**valuation)
    assert eta_pd == expected
    eta_pd = Fraction(1, 2) * (1 + eta_pd)

# T107 threshold is positive and decreases on the sampled literal levels.
thresholds = []
for ell in range(1, 7):
    q = 10**ell
    w = (2 + math.log(800 * q * q + 1)) ** 2
    w += 0.5 * (2 + math.log(40 * q * q + 1)) ** 2
    epsilon = math.sqrt(0.5 / (160 * q * w))
    assert 0 < epsilon < 1
    thresholds.append(epsilon)
assert all(a > b for a, b in zip(thresholds, thresholds[1:]))

report = (ROOT / "REPORT.md").read_text()
assert "PRIMARY_SOURCE_COUNT: 4" in report
assert "PRIMARY_SOURCE_CAP: 10" in report
assert "CANDIDATE_COUNT: 1" in report
assert "CANDIDATE_CAP: 3" in report
assert "TERMINAL_VERDICT_COUNT: 1" in report
assert "SUCCESSOR_COUNT: 0" in report
assert report.count("VERDICT: close") == 1
assert "VERDICT: develop" not in report
assert "VERDICT: hold as model" not in report
assert report.count("CHEAP_REJECTION_TEST:") == 1

for item in [
    "T88", "T91", "T94", "T97", "T101", "T103", "T104",
    "T110", "T112", "T113", "T114", "terminal memory",
]:
    assert item in report, item

for excluded in [
    "invariant-measure separator",
    "paperfolding",
    "Toeplitz tower",
    "ambient Fourier decay",
    "Gowers",
    "nilsequence",
    "finite carry cocycle",
    "Variable-threshold avoidance",
    "Determinant nonvanishing",
]:
    corpus = report + (ROOT / "SEARCH_LOG.md").read_text()
    assert excluded.lower() in corpus.lower(), excluded

print("T115 deterministic replay: PASS")
print(f"verified fixed hashes: {len(EXPECTED_HASHES)}")
print("primary sources: 4 <= 10")
print("retained candidates: 1 <= 3")
print("finite decimal-ray recursion checks: PASS")
print("T67 shell and weight checks: PASS")
print("screened period-doubling recurrence: PASS")
print("T107 theta=1/2 thresholds:")
for ell, epsilon in enumerate(thresholds, start=1):
    print(f"  ell={ell}: {epsilon:.12e}")
print("unique terminal verdict and zero successors: PASS")
print("scope: experiment; no pi, C1, or C2 claim")
