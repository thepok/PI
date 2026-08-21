#!/usr/bin/env python3
"""Self-contained hash, locator, and finite-algebra checks for T46."""

from fractions import Fraction
from hashlib import sha256
from pathlib import Path


ROOT = Path(__file__).resolve().parent

EXPECTED = {
    "canonical_statement.txt": "cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8",
    "T26SharedResonanceChain.lean": "7278999f1ff89d11e7ee408b21e5a300fbdc3e78cf5a6776a2274fc9a761f1c2",
    "T38FixedStratumFejerSpike.lean": "853f10a83b0dbf91955f7587c07cd4651e5954b19f78942703df15073456a014",
    "zeilberger-zudilin-2020.pdf": "3b11c4bf3e25927227ac8f7f4e49d7f1d3efeb42beecd7f3b8c64efb162d20b5",
    "zeilberger-zudilin-2020.txt": "49ca4907538e4ccea23cee27f051f5b33832ed2cf3e3093b4aab58a13c814a68",
}


def digest(name: str) -> str:
    return sha256((ROOT / name).read_bytes()).hexdigest()


def weight(r: int, u: int) -> Fraction:
    if abs(u) >= r:
        return Fraction(0)
    return Fraction(r - abs(u), r)


def autocorrelation_direct(r: int, d: int) -> Fraction:
    return sum((weight(r, u) * weight(r, u + d)
                for u in range(-r + 1, r)), Fraction(0))


def autocorrelation_formula(r: int, d: int) -> Fraction:
    if d == 0:
        return Fraction(2 * r * r + 1, 3 * r)
    if 1 <= d <= r - 1:
        numerator = (4 * r**3 + 2 * r - 6 * r * d**2
                     + 3 * d**3 - 3 * d)
        return Fraction(numerator, 6 * r**2)
    if r <= d <= 2 * r - 2:
        n = 2 * r - d
        return Fraction(n**3 - n, 6 * r**2)
    return Fraction(0)


def check_hashes() -> None:
    for name, expected in EXPECTED.items():
        actual = digest(name)
        assert actual == expected, (name, actual, expected)


def check_locators() -> None:
    canonical = (ROOT / "canonical_statement.txt").read_text()
    assert "pairs are ordered and the diagonal is included" in canonical
    assert "for every integer A >= 1" in canonical

    t26 = (ROOT / "T26SharedResonanceChain.lean").read_text()
    for anchor in (
        "def chainLengthRequest (D d : \u2115)",
        "def initialDensity (A n : \u2115)",
        "N = 16 * A * n * L",
        "literal_not_A1_implies_shared_chain_necessaryOnly",
    ):
        assert anchor in t26

    t38 = (ROOT / "T38FixedStratumFejerSpike.lean").read_text()
    for anchor in (
        "def denominatorStratum",
        "def stratumDelta",
        "def stratumOrder",
        "def FSFS",
        "def lacunaryExpansion",
        "stratumFejerSum_eq_lacunaryExpansion",
    ):
        assert anchor in t38

    source = (ROOT / "zeilberger-zudilin-2020.txt").read_text()
    assert "smallest number" in source
    assert "7.10320533413700172750577342281" in source
    assert (ROOT / "zeilberger-zudilin-2020.pdf").read_bytes().startswith(b"%PDF-")


def check_weighted_algebra() -> None:
    for r in range(2, 201):
        values = []
        for d in range(0, 2 * r - 1):
            direct = autocorrelation_direct(r, d)
            formula = autocorrelation_formula(r, d)
            assert direct == formula, (r, d, direct, formula)
            values.append(formula)
        assert all(values[d] > values[d + 1]
                   for d in range(len(values) - 1))
        total = values[0] + 2 * sum(values[1:], Fraction(0))
        assert total == r * r, (r, total)
        assert values[0] == Fraction(2 * r * r + 1, 3 * r)

        # Complete difference multiplicity on the signed support.
        support = range(-r + 1, r)
        for signed_d in range(-2 * r + 2, 2 * r - 1):
            count = sum(1 for u in support
                        if -r + 1 <= u - signed_d <= r - 1)
            assert count == 2 * r - 1 - abs(signed_d)


def check_valuation_partition() -> None:
    for r in range(2, 201):
        recovered = []
        max_d = 2 * r - 2
        power = 1
        while power <= max_d:
            for m in range(1, max_d // power + 1):
                if m % 10 != 0:
                    recovered.append(power * m)
            power *= 10
        assert sorted(recovered) == list(range(1, max_d + 1))


def check_report_contract() -> None:
    report = (ROOT / "REPORT.md").read_text()
    assert report.rstrip().endswith("INSUFFICIENT")
    for required in (
        "(9C)^7<=20U",
        "T^2=\\frac{R^2}{16}=25U^2",
        "T40 and T43 are not premises",
        "no unconditional FSFS",
        "Q_8",
        "B_{46}",
    ):
        assert required in report, required


def main() -> None:
    check_hashes()
    check_locators()
    check_weighted_algebra()
    check_valuation_partition()
    check_report_contract()
    print("T46 verification passed: hashes, locators, multiplicities, and report contract")


if __name__ == "__main__":
    main()
