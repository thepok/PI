#!/usr/bin/env python3
"""Self-contained hash, locator, algebra, and report-contract checks for T47."""

from fractions import Fraction
from hashlib import sha256
from pathlib import Path


ROOT = Path(__file__).resolve().parent

EXPECTED = {
    "canonical_statement.txt": "cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8",
    "T14CoherentSuccessorSplitting.lean": "bbc5c0323aaa0213e1d86dd4ec711e5f1a9d5421c7d946c88c56ee0f017bf833",
    "T37ArtificialStreamObstruction.lean": "aa0979b629131c6e30c2d8a8dc8c70499ff03d98cd35b2f49841f7669585116c",
}


def digest(name: str) -> str:
    return sha256((ROOT / name).read_bytes()).hexdigest()


def check_hashes() -> None:
    for name, expected in EXPECTED.items():
        actual = digest(name)
        assert actual == expected, (name, actual, expected)

    manifest = (ROOT / "DEPENDENCIES.sha256").read_text().splitlines()
    assert len(manifest) == len(EXPECTED)
    for line in manifest:
        expected, name = line.split(maxsplit=1)
        assert name in EXPECTED, name
        assert expected == EXPECTED[name], (name, expected)


def check_kernel_locators() -> None:
    canonical = (ROOT / "canonical_statement.txt").read_text()
    assert "pairs are ordered and the diagonal is included" in canonical
    assert "for every integer A >= 1" in canonical

    t14 = (ROOT / "T14CoherentSuccessorSplitting.lean").read_text()
    for anchor in (
        "def PiCoherentPositiveDensitySplittingAt",
        "not_piPolynomialSmallBallC2_iff_quantified_splitting_failure",
        "not_piPolynomialSmallBallC2_implies_failure_and_weighted_dominance",
    ):
        assert anchor in t14, anchor
    assert "\u2200 k : \u2115, k0 \u2264 k \u2192 \u2200 m : \u2115, m0 \u2264 m \u2192 m \u2264 k \u2192" in t14

    t37 = (ROOT / "T37ArtificialStreamObstruction.lean").read_text()
    for anchor in (
        "def artificialStream : Stream := concatStream stageBlock",
        "def sampledCheckpoint",
        "def inspectionCheckpoint",
        "theorem stageCoreCount_eq_coreSize_mul_pow",
        "theorem sum_stageErrorCount_all_words",
        "theorem normalizedStageLeakage_tendsto_zero",
        "theorem no_original_halfDominant_branch_explicit",
    ):
        assert anchor in t37, anchor


def check_finite_algebra() -> None:
    # Exact identities and inequalities used in Sections 7, 9, and 10.
    for m in range(1, 10):
        for b_error in range(1, 30):
            repetitions = m**3 * (b_error + 1) + 3
            segment_length = repetitions * m
            core = segment_length - 2 * m
            assert core == m**4 * (b_error + 1) + m
            assert m * b_error <= core
            assert Fraction(b_error, core) <= Fraction(1, m**4)

            sample = 10**m * core + b_error
            assert Fraction(b_error, sample) <= Fraction(1, 1 + m * 10**m)

            # Worst-case parent/child bounds at every shallow level.
            for level in range(m):
                parent_upper = core * 10 ** (m - level) + b_error
                child_lower = core * 10 ** (m - level - 1)
                assert parent_upper <= 20 * child_lower

            # Root mass and energy-share inequalities for all possible e_0.
            for root_error in range(b_error + 1):
                root_count = core + root_error
                root_mass = Fraction(root_count, sample)
                beta = Fraction(b_error, core)
                assert Fraction(1, 10**m + beta) <= root_mass
                assert root_mass <= Fraction(1 + beta, 10**m + beta)

                energy_lower = 10**m * core**2 + 2 * core * b_error
                energy_upper = energy_lower + b_error**2
                share_lower = Fraction(core**2, energy_upper)
                share_upper = Fraction((core + b_error) ** 2, energy_lower)
                assert share_lower <= Fraction(root_count**2, energy_upper)
                assert Fraction(root_count**2, energy_lower) <= share_upper


def check_report_contract() -> None:
    report = (ROOT / "REPORT.md").read_text()
    last_line = report.rstrip().splitlines()[-1]
    assert last_line.startswith("BOUNDARY FAILS AT \\(")
    assert "\\forall\\mu,\\eta,d,B\\in\\mathbb R" in last_line
    assert "\\forall M:\\mathbb N\\to\\mathbb N" in last_line
    assert "\\forall\\nu\\in\\operatorname{Prob}(\\mathbb R/\\mathbb Z)" in last_line
    assert "\\exists k\\in\\mathbb N,\\ k_0\\leq k" in last_line
    assert "\\exists m\\in\\mathbb N,\\ m_0\\leq m\\wedge m\\leq k" in last_line
    assert "\\operatorname{SplitCount}_s" in last_line

    for required in (
        "S_q:=\\operatorname{sampledCheckpoint}(q)",
        "I_q:=\\operatorname{inspectionCheckpoint}(q)",
        "x_s:=\\sum_{j=0}^{\\infty}s_j10^{-(j+1)}",
        "Its literal negation",
        "m\leq k",
        "p_q\\longrightarrow0",
        "\\rho_q\\longrightarrow0",
        "no_original_halfDominant_branch_explicit",
        "This is not canonical C2",
    ):
        assert required in report, required

    forbidden_claims = (
        "canonical C2 holds",
        "canonical C1 holds",
        "canonical A1 holds",
        "C2 for pi holds",
    )
    for forbidden in forbidden_claims:
        assert forbidden not in report, forbidden


def main() -> None:
    check_hashes()
    check_kernel_locators()
    check_finite_algebra()
    check_report_contract()
    print("T47 verification passed: hashes, locators, finite algebra, and report contract")


if __name__ == "__main__":
    main()
