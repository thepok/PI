#!/usr/bin/env python3
"""Independent finite replay for the BBP empirical-rigidity audit.

Every computed output has claim status ``experiment``.  This checker pins the
audited artifacts and primary sources, rederives the exact BBP coefficient,
tail majorants, decimal/hexadecimal recurrences, moving-coordinate identity,
and all numerical constants used in the Wasserstein couplings.  It does not
prove an infinite empirical-limit hypothesis, fixed-sixteen return, or V1.
"""

from __future__ import annotations

from fractions import Fraction
from hashlib import sha256
import json
from pathlib import Path
import subprocess
import tempfile


ROOT = Path(__file__).resolve().parents[2]

PINS = {
    "problems/local/pi-digits.txt":
        "2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825",
    "work/ultrapi-resume/bbp_empirical_rigidity_attack.md":
        "80fc0a6f9bd159dc36438a78ec10b35c76b433c2bae084750b3c34199d97534c",
    "work/ultrapi-resume/bbp_empirical_rigidity_check.py":
        "0b943566c03dc083be1321499b66e6f6cf1766ad7f11d87b657ebf52f6572953",
    "work/theory/pi-digits/library/t6/bbp-1997-nasa.pdf":
        "e4e0b97fde01328ec41da5f2cd4d6ffc8bcd2b7bd7516b9d8afc320f6d1916c4",
    "work/theory/pi-lacunary-near-return-sparsity/library/t63/"
    "lagarias-math0101055v2.pdf":
        "a2a1171eb9c75c9fa3495ca3c3ceaa33c1d20b722bb56f82adb56d8c308209b9",
    "work/theory/pi-digits/library/t44/furstenberg-1967-disjointness.pdf":
        "cd07faa4521080272cf2c303ee4e3a41ee6a3ba9e6aea114604becaca0ba9358",
    "work/theory/pi-digits/library/t44/hochman-2022-host-equidistribution-v2.pdf":
        "2fa94bec2580725a6b2d3e83761af1510f86061a6090528350c44ea785087d0b",
    "work/theory/pi-digits/library/t44/rudolph-1990-times2-times3.pdf":
        "9016e14ea8a3125dbea8532c6f8b2230fb24a33fe5e8818db8bcf0f7a7b57c85",
    "work/theory/pi-digits/library/t12/schmidt-1960-on-normal-numbers.pdf":
        "28f1f9604d4000ada9cf9485c2d68532348065087c6bdc42a4dda982bddeea67",
}


def digest(path: Path) -> str:
    return sha256(path.read_bytes()).hexdigest()


def frac(value: Fraction) -> Fraction:
    return value - value.numerator // value.denominator


def coefficient(index: int) -> Fraction:
    split = (
        Fraction(4, 8 * index + 1)
        - Fraction(2, 8 * index + 4)
        - Fraction(1, 8 * index + 5)
        - Fraction(1, 8 * index + 6)
    )
    combined = Fraction(
        120 * index**2 + 151 * index + 47,
        (2 * index + 1)
        * (4 * index + 3)
        * (8 * index + 1)
        * (8 * index + 5),
    )
    assert split == combined > 0
    return combined


def source_text(relative: str) -> str:
    with tempfile.TemporaryDirectory(prefix="bbp-empirical-independent-") as tmp:
        target = Path(tmp) / "source.txt"
        subprocess.run(
            ["pdftotext", "-layout", str(ROOT / relative), str(target)],
            check=True,
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
        )
        return " ".join(target.read_text(errors="replace").split())


def source_checks() -> dict[str, bool]:
    bbp = source_text("work/theory/pi-digits/library/t6/bbp-1997-nasa.pdf")
    lagarias = source_text(
        "work/theory/pi-lacunary-near-return-sparsity/library/t63/"
        "lagarias-math0101055v2.pdf"
    )
    furstenberg = source_text(
        "work/theory/pi-digits/library/t44/furstenberg-1967-disjointness.pdf"
    )
    hochman = source_text(
        "work/theory/pi-digits/library/t44/"
        "hochman-2022-host-equidistribution-v2.pdf"
    )
    rudolph = source_text(
        "work/theory/pi-digits/library/t44/rudolph-1990-times2-times3.pdf"
    )
    schmidt = source_text(
        "work/theory/pi-digits/library/t12/schmidt-1960-on-normal-numbers.pdf"
    )

    checks = {
        "bbp_exact_identity": (
            "Theorem 1." in bbp and "The following identity holds" in bbp
        ),
        "lagarias_shadow_and_infinite_limit_set": (
            "Theorem 3.1" in lagarias
            and "asymptotically approach each other" in lagarias
            and "Theorem 3.3" in lagarias
            and "have finitely many limit points" in lagarias
        ),
        "furstenberg_nonlacunary_orbit": (
            "T H E O R E M IV. 1" in furstenberg
            and "non-lacunary semigroup" in furstenberg
            and "irrational" in furstenberg
            and "dense in K" in furstenberg
        ),
        "hochman_exact_hypotheses": (
            "Theorem 1.1" in hochman
            and "invariant, ergodic and has positive entropy" in hochman
            and "multiplicatively independent" in hochman
        ),
        "rudolph_cofinite_extension": (
            "COROLLARY 4.11" in rudolph
            and "cofinite subgroup" in rudolph
            and "Theorem 4.9 holds for p and q" in rudolph
        ),
        "schmidt_cantor_normality": (
            "THEOREM 2." in schmidt
            and "Thus" in schmidt
            and "normal to base r for almost all" in schmidt
            and "Cantor set" in schmidt
        ),
    }
    assert all(checks.values()), checks
    return checks


def exact_replay(depth: int = 96, extra_tail: int = 24) -> dict[str, object]:
    # The displayed polynomial is exactly denominator - k^2*numerator.
    for index in range(1, depth + extra_tail + 1):
        denominator = (
            (2 * index + 1)
            * (4 * index + 3)
            * (8 * index + 1)
            * (8 * index + 5)
        )
        numerator = 120 * index**2 + 151 * index + 47
        difference = denominator - index**2 * numerator
        asserted = (
            392 * index**4
            + 873 * index**3
            + 665 * index**2
            + 194 * index
            + 15
        )
        assert difference == asserted > 0
        assert coefficient(index) < Fraction(1, index**2)

    partials: list[Fraction] = []
    partial = Fraction()
    for index in range(depth + extra_tail + 1):
        partial += coefficient(index) / 16**index
        partials.append(partial)

    # A rational finite surrogate for pi verifies the moving-conjugacy algebra
    # without importing a floating approximation to pi.
    surrogate = partials[-1]
    diagonal_checks = 0
    hex_checks = 0
    coboundary_checks = 0
    conjugacy_checks = 0
    decimal_coupling_sum = Fraction()
    hex_coupling_sum = Fraction()

    for index in range(depth + 1):
        diagonal = frac(10**index * partials[index])
        hexadecimal = frac(16**index * partials[index])
        decimal_error = 10**index * (surrogate - partials[index])
        hex_error = 16**index * (surrogate - partials[index])
        decimal_coupling_sum += decimal_error
        hex_coupling_sum += hex_error

        assert frac(diagonal + decimal_error) == frac(10**index * surrogate)
        assert frac(hexadecimal + hex_error) == frac(16**index * surrogate)

        if index < depth:
            epsilon = coefficient(index + 1) * Fraction(5, 8) ** (index + 1)
            next_diagonal = frac(10 ** (index + 1) * partials[index + 1])
            next_hex = frac(16 ** (index + 1) * partials[index + 1])
            next_decimal_error = 10 ** (index + 1) * (
                surrogate - partials[index + 1]
            )

            assert next_diagonal == frac(10 * diagonal + epsilon)
            diagonal_checks += 1
            assert next_hex == frac(16 * hexadecimal + coefficient(index + 1))
            hex_checks += 1
            assert epsilon == 10 * decimal_error - next_decimal_error
            coboundary_checks += 1
            assert frac(next_diagonal + next_decimal_error) == frac(
                10 * frac(diagonal + decimal_error)
            )
            conjugacy_checks += 1

    # Constants used in the infinite majorants (not the truncated surrogate).
    geometric_decimal = Fraction(1, 15) / (1 - Fraction(5, 8))
    elementary_zeta2_majorant = Fraction(2, 15)
    assert geometric_decimal == Fraction(8, 45)
    assert geometric_decimal + elementary_zeta2_majorant == Fraction(14, 45)
    assert 16 * geometric_decimal == Fraction(128, 45)

    # Schmidt's digit-code separation: after the first unequal digit, even
    # maximal cancellation by digits 0,...,8 leaves a positive gap.
    code_gaps = {}
    for position in range(1, 13):
        leading = Fraction(1, 10**position)
        maximum_tail = Fraction(8, 9 * 10**position)
        gap = leading - maximum_tail
        assert gap == Fraction(1, 9 * 10**position) > 0
        code_gaps[str(position)] = str(gap)

    # Exponent vectors for 10=2^1*5^1 and 16=2^4*5^0.
    determinant = 1 * 0 - 1 * 4
    assert determinant == -4
    for left_power in range(1, 40):
        for right_power in range(1, 40):
            assert 10**left_power != 16**right_power

    return {
        "claim_label": "experiment",
        "depth": depth,
        "surrogate_tail_depth": depth + extra_tail,
        "diagonal_recurrence_checks": diagonal_checks,
        "hex_recurrence_checks": hex_checks,
        "coboundary_checks": coboundary_checks,
        "moving_conjugacy_checks": conjugacy_checks,
        "truncated_decimal_coupling_sum": str(decimal_coupling_sum),
        "truncated_hex_coupling_sum": str(hex_coupling_sum),
        "decimal_universal_sum_bound": str(geometric_decimal),
        "hex_universal_sum_bound": str(elementary_zeta2_majorant),
        "synchronous_universal_sum_bound": str(
            geometric_decimal + elementary_zeta2_majorant
        ),
        "pushforward_universal_sum_bound": str(16 * geometric_decimal),
        "schmidt_code_gaps": code_gaps,
        "rudolph_exponent_determinant": determinant,
    }


def main() -> None:
    pins = {}
    for relative, expected in PINS.items():
        actual = digest(ROOT / relative)
        assert actual == expected, (relative, expected, actual)
        pins[relative] = actual

    report = (ROOT / "work/ultrapi-resume/bbp_empirical_rigidity_attack.md").read_text()
    assert "Canonical V1 remains a `conjecture`." in report
    assert "No fixed-sixteen return" in report
    assert "no proof that every finite decimal word" in report

    result = {
        "status": "PASS",
        "claim_label": "experiment",
        "pins": pins,
        "source_checks": source_checks(),
        "exact_replay": exact_replay(),
        "asserts_v1": False,
        "asserts_fixed_return": False,
        "warning": (
            "finite exact replay and source-marker checks do not prove "
            "ergodicity, nonatomicity, nonsingularity, a return, or V1"
        ),
    }
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
