#!/usr/bin/env python3
"""Finite replay for the centered-carry literature audit.

All computed output has claim label ``experiment``.  This checker pins the
primary sources and frozen parent audits, checks source locators, and replays
only elementary finite identities.  It does not prove a positive carry
density, an empirical-measure theorem for pi, decimal disjunctivity, or V1.
"""

from __future__ import annotations

from fractions import Fraction
from hashlib import sha256
import json
from math import factorial, floor
from pathlib import Path
import subprocess
import tempfile


ROOT = Path(__file__).resolve().parents[2]

PINS = {
    "problems/local/pi-digits.txt":
        "2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825",
    "work/ultrapi-resume/library/chen-ye-zheng-2604.14036v1.pdf":
        "a17f776537f415e4f0b0508024cf95389b1ed4da05a347efda6b149bb2e4924d",
    "work/ultrapi-resume/library/mahler-1973-digits-multiples.pdf":
        "263facae776cfc081d99eafc3ab93e29ebc4b213482c0a9adc97342aa99b7288",
    "work/ultrapi-resume/library/rivoal-2008-bits-counting.pdf":
        "060032757c32e146078c542e72c793aaaf854b48cf264517493ff7d77a3a690e",
    "work/theory/pi-long-lag-block-collision-decay/library/t47/"
    "zeilberger-zudilin-moscow-2020-9-407.pdf":
        "3b11c4bf3e25927227ac8f7f4e49d7f1d3efeb42beecd7f3b8c64efb162d20b5",
    "work/theory/pi-lacunary-near-return-sparsity/library/t63/"
    "lagarias-math0101055v2.pdf":
        "a2a1171eb9c75c9fa3495ca3c3ceaa33c1d20b722bb56f82adb56d8c308209b9",
    "work/theory/pi-lacunary-near-return-sparsity/library/t63/"
    "bailey-crandall-2001-bcrandom.pdf":
        "701067697e8c1dace60cd8695ef509edae31f9da3bffd64b548624ccc2e4cfa8",
    "work/theory/pi-lacunary-near-return-sparsity/library/t63/"
    "bailey-crandall-2002-bcnormal.pdf":
        "d6cb4c65494b8447428a480ba9c29139fcedfac47dc3fff029ec4a50a0d8db74",
    "work/theory/pi-digits/library/t6/bbp-1997-nasa.pdf":
        "e4e0b97fde01328ec41da5f2cd4d6ffc8bcd2b7bd7516b9d8afc320f6d1916c4",
    "work/ultrapi-resume/bbp_fixed_period_carry_attack_20260813.md":
        "bdc77060ef42a15f8985d70b70cf9777c36070713c940a18e89e05b149734d55",
    "work/ultrapi-resume/bbp_fixed_period_carry_attack_20260813_independent_audit.md":
        "ae7e6c84ca6ec253107c2fa48ed202c5ef4f3aadbee75cbd1bca3d2d03dafe91",
    "work/ultrapi-resume/bbp_empirical_rigidity_attack.md":
        "80fc0a6f9bd159dc36438a78ec10b35c76b433c2bae084750b3c34199d97534c",
    "work/ultrapi-resume/bbp_empirical_rigidity_independent_audit.md":
        "33cf4c1224dffa7d019e38fe82bbd0ed352187ba6b1e4548e1109b459961e1ac",
}

MATHLIB_COMMIT = "c5ea00351c28e24afc9f0f84379aa41082b1188f"


def digest(path: Path) -> str:
    return sha256(path.read_bytes()).hexdigest()


def pdf_text(relative: str) -> str:
    with tempfile.TemporaryDirectory(prefix="pi-carry-literature-") as tmp:
        target = Path(tmp) / "source.txt"
        subprocess.run(
            ["pdftotext", "-layout", str(ROOT / relative), str(target)],
            check=True,
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
        )
        return " ".join(target.read_text(errors="replace").split())


def source_markers() -> dict[str, bool]:
    chen = pdf_text(
        "work/ultrapi-resume/library/chen-ye-zheng-2604.14036v1.pdf"
    )
    mahler = pdf_text(
        "work/ultrapi-resume/library/mahler-1973-digits-multiples.pdf"
    )
    rivoal = pdf_text(
        "work/ultrapi-resume/library/rivoal-2008-bits-counting.pdf"
    )
    zz = pdf_text(
        "work/theory/pi-long-lag-block-collision-decay/library/t47/"
        "zeilberger-zudilin-moscow-2020-9-407.pdf"
    )
    lagarias = pdf_text(
        "work/theory/pi-lacunary-near-return-sparsity/library/t63/"
        "lagarias-math0101055v2.pdf"
    )
    bailey_crandall = pdf_text(
        "work/theory/pi-lacunary-near-return-sparsity/library/t63/"
        "bailey-crandall-2001-bcrandom.pdf"
    )
    bailey_crandall_2002 = pdf_text(
        "work/theory/pi-lacunary-near-return-sparsity/library/t63/"
        "bailey-crandall-2002-bcnormal.pdf"
    )
    bbp = pdf_text("work/theory/pi-digits/library/t6/bbp-1997-nasa.pdf")

    checks = {
        "chen_theorem_1_3": (
            "Theorem 1.3." in chen
            and "set E of limit values" in chen
            and "is an infinite set" in chen
        ),
        "chen_corollary_3_4": (
            "Corollary 3.4." in chen
            and "for every integer M" in chen
            and "not contained in any interval" in chen
        ),
        "chen_reduced_length_locator": "Remark 3.5." in chen,
        "mahler_theorem_2": (
            "THEOREM 2." in mahler
            and "arbitrary positive irrational" in mahler
            and "every possible sequence of N digits occurs infinitely" in mahler
        ),
        "rivoal_logarithmic_bound_context": (
            "ON THE BITS COUNTING FUNCTION OF REAL NUMBERS" in rivoal
            and "finite irrationality exposant" in rivoal
            and "log(n)" in rivoal
        ),
        "zeilberger_zudilin_exponent": (
            "irrationality measure of π is at most 7.103205334137" in zz
        ),
        "lagarias_conditional_boundary": (
            "Weak Dichotomy Hypothesis" in lagarias
            and "Strong Dichotomy Hypothesis" in lagarias
            and "Theorem 4.1" in lagarias
        ),
        "bailey_crandall_hypothesis_a": (
            "Hypothesis A." in bailey_crandall
            and "On Hypothesis A" in bailey_crandall
        ),
        "bailey_crandall_2002_conditional": (
            "Hypothesis A" in bailey_crandall_2002
            and "Theorem 3.2 (Conditional)" in bailey_crandall_2002
        ),
        "bbp_theorem_1": (
            "Theorem 1." in bbp and "The following identity holds" in bbp
        ),
    }
    assert all(checks.values()), checks
    return checks


def mathlib_markers() -> dict[str, object]:
    mathlib = ROOT / ".lake/packages/mathlib"
    commit = subprocess.run(
        ["git", "rev-parse", "HEAD"],
        cwd=mathlib,
        check=True,
        text=True,
        capture_output=True,
    ).stdout.strip()
    assert commit == MATHLIB_COMMIT, (MATHLIB_COMMIT, commit)

    files_and_markers = {
        "Mathlib/NumberTheory/Transcendental/Liouville/LiouvilleWith.lean":
            ("def LiouvilleWith", "theorem mul_int_iff"),
        "Mathlib/NumberTheory/Transcendental/Liouville/Measure.lean":
            ("theorem ae_not_liouvilleWith",),
        "Mathlib/Dynamics/Ergodic/AddCircle.lean":
            ("theorem ergodic_nsmul",),
        "Mathlib/MeasureTheory/Measure/Support.lean":
            ("AbsolutelyContinuous.support_mono",),
    }
    hits = {}
    for relative, markers in files_and_markers.items():
        source = (mathlib / relative).read_text()
        hits[relative] = all(marker in source for marker in markers)
    assert all(hits.values()), hits
    return {"commit": commit, "markers": hits}


def nearest_integer(value: Fraction) -> int:
    return floor(value + Fraction(1, 2))


def centered_carry_replay(max_p: int = 6, max_n: int = 24) -> dict[str, int]:
    # 355/113 is only a boundary-safe rational test input.  It is not used as
    # an approximation premise about pi.
    theta = Fraction(355, 113)
    identity_checks = 0
    threshold_checks = 0

    for period in range(1, max_p + 1):
        multiplier = 10**period - 1
        for index in range(max_n):
            current = multiplier * 10**index * theta
            following = 10 * current
            z_current = nearest_integer(current)
            z_following = nearest_integer(following)
            e_current = current - z_current
            e_following = following - z_following
            carry = z_following - 10 * z_current

            assert Fraction(carry) == 10 * e_current - e_following
            assert -5 <= carry <= 5
            identity_checks += 1

            # If carry were zero, |e_(n+1)| = 10 |e_n| < 1/2.
            if abs(e_current) >= Fraction(1, 20):
                assert carry != 0
                threshold_checks += 1

    assert Fraction(1, 11) > Fraction(1, 20)
    return {
        "identity_checks": identity_checks,
        "forced_nonzero_checks": threshold_checks,
        "chen_limsup_denominator": 11,
        "carry_zero_max_error_denominator": 20,
    }


def sparse_topology_replay(max_stage: int = 12) -> dict[str, object]:
    # Put a progressively finer dyadic-grid enumeration at factorial times and
    # zero elsewhere.  Beyond k >= M, every k! lies in the zero residue class
    # modulo M.  Finite checks illustrate the exact logical separator used in
    # the report: rich progression-wise topological accumulation can live on
    # zero-density times.
    grids_checked = 0
    for stage in range(1, 9):
        grid = {Fraction(j, 2**stage) for j in range(2**stage)}
        assert len(grid) == 2**stage
        assert max(grid) - min(grid) == Fraction(2**stage - 1, 2**stage)
        grids_checked += 1

    sparse_ratios = []
    previous = Fraction(1)
    for stage in range(3, max_stage + 1):
        horizon = factorial(stage)
        exceptional_count = stage
        ratio = Fraction(exceptional_count, horizon)
        assert ratio < previous
        previous = ratio
        sparse_ratios.append(str(ratio))

        for modulus in range(1, stage + 1):
            assert factorial(stage) % modulus == 0

    return {
        "dyadic_grids_checked": grids_checked,
        "last_factorial_exceptional_fraction": sparse_ratios[-1],
        "warning": "finite replay only; the report contains the infinite proof sketch",
    }


def main() -> None:
    pins = {}
    for relative, expected in PINS.items():
        actual = digest(ROOT / relative)
        assert actual == expected, (relative, expected, actual)
        pins[relative] = actual

    result = {
        "status": "PASS",
        "claim_label": "experiment",
        "source_pins": pins,
        "source_markers": source_markers(),
        "mathlib": mathlib_markers(),
        "centered_carry_replay": centered_carry_replay(),
        "sparse_topology_replay": sparse_topology_replay(),
        "asserts_linear_carry_density": False,
        "asserts_empirical_infinite_support": False,
        "asserts_v1": False,
    }
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
