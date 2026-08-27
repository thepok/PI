#!/usr/bin/env python3
"""Independent exact replay for the BBP adjacent-shift matching audit.

The script does not import the primary checker.  Its exact arithmetic checks
the displayed BBP coefficient, endpoint correction, adjacent relation,
recurrences, coefficient difference, finite portions of both tail majorants,
and the constants used in the two empirical couplings.  It also checks the
pinned primary-source markers and replays the primary checker as a separate
process.

Every finite diagnostic has claim status ``experiment``.  Nothing here proves
the matching or close-pair hypotheses, a fixed-sixteen return, or V1.
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
    "work/ultrapi-resume/bbp_adjacent_shift_matching_attack.md":
        "2764624665fcb2bd4f7a7f8d4a1c4d1094e9459297e018cb095e0a76ff0feba6",
    "work/ultrapi-resume/bbp_adjacent_shift_matching_check.py":
        "a800bf01ac2149d646481d600500e0b9db4e49d6cb1786c279cfc3406e3c543d",
    "work/theory/pi-digits/library/t6/bbp-1997-nasa.pdf":
        "e4e0b97fde01328ec41da5f2cd4d6ffc8bcd2b7bd7516b9d8afc320f6d1916c4",
    "work/theory/pi-lacunary-near-return-sparsity/library/t63/"
    "lagarias-math0101055v2.pdf":
        "a2a1171eb9c75c9fa3495ca3c3ceaa33c1d20b722bb56f82adb56d8c308209b9",
    "work/theory/pi-digits/library/t44/furstenberg-1967-disjointness.pdf":
        "cd07faa4521080272cf2c303ee4e3a41ee6a3ba9e6aea114604becaca0ba9358",
    "TheoryLib/PiQuantitativeBlockHitting/T69T69FixedSixteenReturn.lean":
        "fb7eb54d99bb904c28da0f49d33f8a40979ffcbf22a4024fcae73de7149886f9",
    "TheoryLib/PiQuantitativeBlockHitting/T70T70EmpiricalRigidityBridge.lean":
        "f8ecbfd2d9f8a13216e75d5ebb3732b98f7844147776b30de7f2666fc7ddec55",
}

DEPTH = 160
SURROGATE_DEPTH = 240


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def digest(path: Path) -> str:
    return sha256(path.read_bytes()).hexdigest()


def fractional(value: Fraction) -> Fraction:
    return value - value.numerator // value.denominator


def circle_distance(left: Fraction, right: Fraction) -> Fraction:
    difference = fractional(left - right)
    return min(difference, 1 - difference)


def coefficient(index: int) -> Fraction:
    require(index >= 0, "coefficient domain")
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
    require(split == combined > 0, f"four-pole coefficient k={index}")
    return combined


def coefficient_difference(index: int) -> Fraction:
    polynomial = (
        40960 * index**5
        + 220672 * index**4
        + 453632 * index**3
        + 443480 * index**2
        + 206712 * index
        + 36903
    )
    denominator = (
        (2 * index + 1)
        * (2 * index + 3)
        * (4 * index + 3)
        * (4 * index + 7)
        * (8 * index + 1)
        * (8 * index + 5)
        * (8 * index + 9)
        * (8 * index + 13)
    )
    return Fraction(-3 * polynomial, denominator)


def source_text(relative: str) -> str:
    with tempfile.TemporaryDirectory(prefix="bbp-adjacent-independent-") as tmp:
        output = Path(tmp) / "source.txt"
        subprocess.run(
            ["pdftotext", "-layout", str(ROOT / relative), str(output)],
            check=True,
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
        )
        return " ".join(output.read_text(errors="replace").split())


def source_checks() -> dict[str, bool]:
    bbp = source_text("work/theory/pi-digits/library/t6/bbp-1997-nasa.pdf")
    lagarias = source_text(
        "work/theory/pi-lacunary-near-return-sparsity/library/t63/"
        "lagarias-math0101055v2.pdf"
    )
    furstenberg = source_text(
        "work/theory/pi-digits/library/t44/furstenberg-1967-disjointness.pdf"
    )
    checks = {
        "bbp_exact_series": (
            "Theorem 1." in bbp
            and "The following identity holds" in bbp
            and "8i+1" in bbp
            and "8i+4" in bbp
            and "8i+5" in bbp
            and "8i+6" in bbp
        ),
        "lagarias_shadow_theorem": (
            "Theorem 3.1" in lagarias
            and "asymptotically approach each other" in lagarias
            and "same sets of limit points" in lagarias
        ),
        "lagarias_finite_limit_set_theorem": (
            "Theorem 3.3" in lagarias
            and "have finitely many limit points" in lagarias
            and "asymptotically approaches a periodic orbit" in lagarias
        ),
        "furstenberg_definition_and_dense_orbit": (
            "Definition IV.1" in furstenberg
            and "non-lacunary" in furstenberg
            and "T H E O R E M IV. 1" in furstenberg
            and "irrational" in furstenberg
            and "dense in K" in furstenberg
        ),
    }
    require(all(checks.values()), f"source marker failure: {checks}")
    return checks


def exact_adjacent_replay() -> dict[str, object]:
    q = Fraction(5, 8)
    endpoint = Fraction(1, 30)
    a0 = coefficient(0)
    require(a0 == Fraction(47, 15), "a(0)=47/15")
    require(16 * a0 - endpoint == Fraction(501, 10), "endpoint 501/10")
    require(endpoint - 16 * a0 == Fraction(-501, 10), "endpoint sign")
    for index in range(1, 25):
        scaled_endpoint = 10**index * (endpoint - 16 * a0)
        require(
            scaled_endpoint.denominator == 1,
            f"endpoint integer at n={index}",
        )
        require(
            scaled_endpoint == -501 * 10 ** (index - 1),
            f"endpoint value at n={index}",
        )
    require((endpoint - 16 * a0).denominator == 10, "endpoint denominator 10")

    coefficient_checks = 0
    difference_checks = 0
    for index in range(SURROGATE_DEPTH + 2):
        current = coefficient(index)
        if index >= 1:
            denominator = (
                (2 * index + 1)
                * (4 * index + 3)
                * (8 * index + 1)
                * (8 * index + 5)
            )
            numerator = 120 * index**2 + 151 * index + 47
            positive_gap = (
                392 * index**4
                + 873 * index**3
                + 665 * index**2
                + 194 * index
                + 15
            )
            require(
                denominator - index**2 * numerator == positive_gap > 0,
                f"coefficient bound polynomial k={index}",
            )
            require(current < Fraction(1, index**2), f"a(k)<k^-2 k={index}")
            coefficient_checks += 2
        require(
            coefficient(index + 1) - current == coefficient_difference(index),
            f"coefficient difference k={index}",
        )
        require(coefficient_difference(index) < 0, f"coefficient decrease k={index}")
        difference_checks += 2

    partials: list[Fraction] = []
    partial = Fraction()
    for index in range(SURROGATE_DEPTH + 2):
        partial += coefficient(index) / 16**index
        partials.append(partial)

    original_states: list[Fraction] = []
    shifted_states: list[Fraction] = []
    recurrence_checks = 0
    adjacent_checks = 0
    finite_tail_checks = 0
    coupling_sum = Fraction()
    shifted_majorant_sum = Fraction()

    for index in range(DEPTH + 1):
        shifted_partial = endpoint + sum(
            (coefficient(k + 1) / 16**k for k in range(index + 1)),
            Fraction(),
        )
        require(
            shifted_partial == endpoint + 16 * (partials[index + 1] - a0),
            f"shifted partial identity n={index}",
        )
        original = fractional(10**index * partials[index])
        shifted = fractional(10**index * shifted_partial)
        original_states.append(original)
        shifted_states.append(shifted)

        if index >= 1:
            displacement = coefficient(index + 1) * q**index
            require(
                shifted == fractional(16 * original + displacement),
                f"adjacent state relation n={index}",
            )
            require(
                circle_distance(shifted, fractional(16 * original))
                <= displacement,
                f"adjacent circle coupling n={index}",
            )
            coupling_sum += displacement
            shifted_majorant_sum += q**index / (15 * (index + 2) ** 2)
            adjacent_checks += 2

        if index >= 1:
            require(
                original_states[index]
                == fractional(
                    10 * original_states[index - 1]
                    + coefficient(index) * q**index
                ),
                f"original recurrence n={index}",
            )
            require(
                shifted_states[index]
                == fractional(
                    10 * shifted_states[index - 1]
                    + coefficient(index + 1) * q**index
                ),
                f"shifted recurrence n={index}",
            )
            recurrence_checks += 2

        if index < DEPTH:
            original_finite_tail = 10**index * sum(
                (
                    coefficient(k) / 16**k
                    for k in range(index + 1, SURROGATE_DEPTH + 1)
                ),
                Fraction(),
            )
            shifted_finite_tail = 10**index * sum(
                (
                    coefficient(k + 1) / 16**k
                    for k in range(index + 1, SURROGATE_DEPTH + 1)
                ),
                Fraction(),
            )
            require(original_finite_tail > 0, f"positive original tail n={index}")
            require(
                original_finite_tail <= q**index / (15 * (index + 1) ** 2),
                f"original tail majorant n={index}",
            )
            require(shifted_finite_tail > 0, f"positive shifted tail n={index}")
            require(
                shifted_finite_tail <= q**index / (15 * (index + 2) ** 2),
                f"shifted tail majorant n={index}",
            )
            finite_tail_checks += 4

    adjacent_geometric_bound = q / (1 - q)
    shifted_geometric_bound = q / (15 * (1 - q))
    require(adjacent_geometric_bound == Fraction(5, 3), "5/3 constant")
    require(shifted_geometric_bound == Fraction(1, 9), "1/9 constant")
    require(coupling_sum < adjacent_geometric_bound, "finite adjacent sum")
    require(shifted_majorant_sum < shifted_geometric_bound, "finite shifted sum")

    return {
        "claim_label": "experiment",
        "depth": DEPTH,
        "surrogate_depth": SURROGATE_DEPTH,
        "coefficient_bound_checks": coefficient_checks,
        "coefficient_difference_checks": difference_checks,
        "recurrence_checks": recurrence_checks,
        "adjacent_relation_checks": adjacent_checks,
        "finite_tail_majorant_checks": finite_tail_checks,
        "endpoint_correction": str(endpoint),
        "endpoint_integer_difference": str(16 * a0 - endpoint),
        "finite_adjacent_coupling_sum_decimal": float(coupling_sum),
        "universal_adjacent_coupling_bound": str(adjacent_geometric_bound),
        "finite_shifted_majorant_sum_decimal": float(shifted_majorant_sum),
        "universal_shifted_empirical_bound": str(shifted_geometric_bound),
    }


def sparse_bad_starts(sample_size: int, window: int) -> tuple[int, int]:
    require(sample_size >= 1 and window >= 1, "sparse count domain")
    powers: list[int] = []
    value = 2
    while value <= sample_size + window:
        powers.append(value)
        value *= 2
    bad = sum(
        any(start < position <= start + window for position in powers)
        for start in range(sample_size)
    )
    floor_log2 = (sample_size + window).bit_length() - 1
    bound = window * (1 + floor_log2)
    require(bad <= bound, f"sparse window bound N={sample_size}, L={window}")
    return bad, bound


def separator_replay() -> dict[str, object]:
    checks: dict[str, object] = {}
    for sample_size in (37, 100, 1_000, 10_000):
        for window in (1, 3, 10, 30):
            bad, bound = sparse_bad_starts(sample_size, window)
            checks[f"N={sample_size},L={window}"] = {
                "bad_starts": bad,
                "bound": bound,
            }

    # A periodic tail of positive period cannot retain exactly the powers of
    # two: for a sufficiently large power, adding the period stays strictly
    # between it and the next power.
    periodicity_checks = 0
    for period in range(1, 257):
        power = 2
        while power <= period:
            power *= 2
        require(power < power + period < 2 * power, f"power gap p={period}")
        require((power + period) & (power + period - 1) != 0, f"not power p={period}")
        periodicity_checks += 2

    return {
        "claim_label": "experiment",
        "sparse_window_checks": checks,
        "finite_periodicity_separator_checks": periodicity_checks,
        "warning": "finite sparse checks are not an irrationality or limit proof",
    }


def report_hygiene() -> dict[str, object]:
    relative = "work/ultrapi-resume/bbp_adjacent_shift_matching_attack.md"
    data = (ROOT / relative).read_bytes()
    text = data.decode("utf-8")
    normalized = " ".join(text.split())
    bad_controls = sorted({byte for byte in data if byte < 32 and byte not in (9, 10, 13)})
    require(not bad_controls, f"control bytes: {bad_controls}")
    required = {
        "quantifier_order": (
            "\\lim_{\\rho\\downarrow0}\\ \\limsup_{j\\to\\infty}" in text
        ),
        "positive_lengths": "positive integers \\(N_j\\to\\infty\\)" in text,
        "nonnegative_deltas": "nonnegative\nreals \\(\\delta_j\\to0\\)" in text,
        "support_pushforward": (
            "\\operatorname{supp}((T_{16})_*\\mu)" in text
            and "=T_{16}(\\operatorname{supp}\\mu)" in text
        ),
        "fourier_integer_domain": "q\\in\\mathbb Z" in text,
        "fourier_shift_bridge": (
            "Equation (12) also makes the Prokhorov" in text
            and "actual two empirical rows" in text
        ),
        "no_fixed_return": "No fixed-sixteen return" in text,
        "v1_conjecture": "Canonical V1 remains a `conjecture`." in text,
        "finite_experiment_label": "only an `experiment`" in text,
        "bounded_search_caveat": (
            "dated, bounded applicability search" in normalized
            and "not an exhaustive absence or novelty claim" in normalized
        ),
    }
    require(all(required.values()), f"report hygiene failure: {required}")
    duplicate_sentence = (
        "and even exact common empirical invariance holds, while the decimal orbit of"
    )
    require(text.count(duplicate_sentence) == 1, "generic separator duplicate")
    return {
        "utf8": True,
        "control_bytes": bad_controls,
        "required_boundaries": required,
        "separator_sentence_count": text.count(duplicate_sentence),
    }


def replay_primary_checker() -> dict[str, object]:
    completed = subprocess.run(
        [
            "python",
            str(
                ROOT
                / "work/ultrapi-resume/bbp_adjacent_shift_matching_check.py"
            ),
        ],
        cwd=ROOT,
        check=True,
        capture_output=True,
        text=True,
    )
    result = json.loads(completed.stdout)
    require(result["status"] == "PASS", "primary checker status")
    for key in (
        "asserts_asymptotic_matching",
        "asserts_collision_anti_concentration",
        "asserts_fixed_return",
        "asserts_v1",
    ):
        require(result[key] is False, f"primary checker overclaim: {key}")
    return {
        "status": result["status"],
        "claim_label": result["claim_label"],
        "asserts_asymptotic_matching": result["asserts_asymptotic_matching"],
        "asserts_collision_anti_concentration": result[
            "asserts_collision_anti_concentration"
        ],
        "asserts_fixed_return": result["asserts_fixed_return"],
        "asserts_v1": result["asserts_v1"],
    }


def main() -> None:
    pins = {}
    for relative, expected in PINS.items():
        actual = digest(ROOT / relative)
        require(actual == expected, f"pin mismatch {relative}: {actual}")
        pins[relative] = actual

    result = {
        "status": "PASS",
        "claim_label": "experiment",
        "pins": pins,
        "source_checks": source_checks(),
        "exact_adjacent_replay": exact_adjacent_replay(),
        "generic_separator_replay": separator_replay(),
        "report_hygiene": report_hygiene(),
        "primary_checker_replay": replay_primary_checker(),
        "asserts_matching_hypothesis": False,
        "asserts_close_pair_hypothesis": False,
        "asserts_fixed_return": False,
        "asserts_v1": False,
        "warning": (
            "exact finite arithmetic and source markers do not prove any "
            "asymptotic hypothesis, fixed return, or decimal universality"
        ),
    }
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
