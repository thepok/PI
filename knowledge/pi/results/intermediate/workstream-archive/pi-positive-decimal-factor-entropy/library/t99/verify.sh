#!/bin/sh
set -eu

sha256sum -c SHA256SUMS

python - <<'PY'
from fractions import Fraction
import math
from pathlib import Path
import subprocess

canonical = Path("pi-positive-decimal-factor-entropy.txt").read_text()
complexity = Path("pi-decimal-factor-complexity.txt").read_text()
t36 = Path("T36DecimalPeriodicWindowGap.lean").read_text()
t2 = Path("T2ExponentialCollisionCriterion.lean").read_text()
zz = Path("zeilberger-zudilin-2020.txt").read_text()
bk = Path("bugeaud-kim-1510.00279v3.txt").read_text()
mp = Path("mignosi-pirillo-1992.txt").read_text()
audit = Path("T99_DELTA_AUDIT.md").read_text()

anchors = [
    ("canonical ENT", "p_pi(n) >= 10^(eta*n)", canonical),
    ("canonical LL", "p_pi(n) >= n+1", complexity),
    ("T36 window theorem", "effectiveIrrationality_periodic_window_gap", t36),
    ("T36 exact bound", "(μ - 1) * a + μ * p + roundingConstant", t36),
    ("T2 C2", "def PiExponentialCollisionC2", t2),
    ("T2 implication", "piExponentialCollisionC2_implies_C1", t2),
    ("ZZ definition", "irrationality measure", zz),
    ("ZZ value", "7.10320533413700172750577342281", zz),
    ("ZZ Proposition 7", "Proposition 7.", zz),
    ("ZZ Proposition 8", "Proposition 8.", zz),
    ("BK Morse-Hedlund", "Theorem 1.1.", bk),
    ("BK r definition", "smallest prefix of x containing", bk),
    ("BK Lemma 2.2", "Lemma 2.2.", bk),
    ("BK periodicity", "Theorem 2.3.", bk),
    ("BK rep", "Definition 3.2.", bk),
    ("BK irrationality bridge", "Theorem 4.2.", bk),
    ("Fibonacci source", "Fibonacci", mp),
    ("single terminal heading", "## 10. Terminal form: negative map", audit),
]
for label, needle, text in anchors:
    if needle not in text:
        raise SystemExit(f"missing anchor: {label}: {needle!r}")

def pdf_page(path, page):
    return subprocess.run(
        ["pdftotext", "-f", str(page), "-l", str(page), "-layout", path, "-"],
        check=True, capture_output=True, text=True
    ).stdout

zz_p2 = pdf_page("zeilberger-zudilin-2020.pdf", 2)
zz_p12 = pdf_page("zeilberger-zudilin-2020.pdf", 12)
zz_p13 = pdf_page("zeilberger-zudilin-2020.pdf", 13)
if "smallest number" not in zz_p2 or "sufficiently large q" not in zz_p2:
    raise SystemExit("ZZ definition is not at retained PDF p. 2")
if "Proposition 7." not in zz_p12 or "Proposition 8." not in zz_p12:
    raise SystemExit("ZZ Propositions 7--8 do not begin at retained PDF p. 12")
if "7.10320533413700172750577342281" not in zz_p13:
    raise SystemExit("ZZ final value is not at retained PDF p. 13")

literal_positions = {
    "NR": audit.find("For every A>=1 and every p>=1"),
    "LL": audit.find("For every integer n>=1, p_x(n)>=n+1"),
    "ENT": audit.find("There exist eta>0 and N>=1 such that"),
}
for label, formula_pos in literal_positions.items():
    if formula_pos < 0 or audit.find(label) < formula_pos:
        raise SystemExit(f"{label} label occurs before its literal formula")

if audit.count("Terminal form:") != 1:
    raise SystemExit("audit must contain exactly one terminal-form heading")
if "ranked novel direction" in audit.lower():
    raise SystemExit("negative map must not contain the alternative terminal form")

M = Fraction(888, 125)
loss = M - 1
rho = Fraction(888, 763)
if loss != Fraction(763, 125):
    raise SystemExit("source loss arithmetic failed")
if rho / (rho - 1) != M:
    raise SystemExit("REP threshold identity failed")

c_nat = 1 / math.log(float(M))
c_ten = 1 / math.log10(float(M))
rho_float = float(rho)
expected = (0.510032854836, 1.174394048484, 1.163826998689)
actual = (c_nat, c_ten, rho_float)
for got, want in zip(actual, expected):
    if abs(got - want) > 5e-13:
        raise SystemExit(f"displayed constant mismatch: {got} vs {want}")

print("T99 replay: hashes, source anchors, terminal form, and thresholds verified")
PY
