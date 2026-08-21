#!/usr/bin/env python3
"""Independent deterministic audit for the odd-LCM carry no-go report.

The replay pins and reruns the frozen primary artifacts.  Separate exact
rational checks exercise the q-torsion threshold, zero-block equivalence,
half-open h_P formula, restricted-denominator error identity, and the
sevenfold rational-agreement rate.  Finite rows remain experiments and this
script asserts neither V1 nor a carry-density theorem.
"""

from __future__ import annotations

from fractions import Fraction
from hashlib import sha256
import json
from pathlib import Path
import subprocess


ROOT = Path(__file__).resolve().parents[2]
PRIMARY_REPORT = Path(
    "work/ultrapi-resume/bbp_odd_lcm_carry_no_go_20260813.md"
)
PRIMARY_CHECKER = Path(
    "work/ultrapi-resume/bbp_odd_lcm_carry_no_go_20260813_check.py"
)

PINS = {
    Path("problems/local/pi-digits.txt"):
        "2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825",
    PRIMARY_REPORT:
        "fcea6cb14082ee404fabf14a68215a3b7394d553ed401e51e8f70a333f234bfc",
    PRIMARY_CHECKER:
        "12d9ffef815f60b39d8f4d2f8c946bab10c1e29be94d25f19dfb1039ee15a905",
    Path("work/ultrapi-resume/bbp_fixed_period_carry_attack_20260813.md"):
        "bdc77060ef42a15f8985d70b70cf9777c36070713c940a18e89e05b149734d55",
    Path(
        "work/ultrapi-resume/"
        "bbp_fixed_period_carry_attack_20260813_independent_audit.md"
    ):
        "ae7e6c84ca6ec253107c2fa48ed202c5ef4f3aadbee75cbd1bca3d2d03dafe91",
    Path(
        "work/theory/pi-lacunary-near-return-sparsity/"
        "library/t53/pi_digits.txt"
    ):
        "77eeccb0067283e14c460b33dc230de54ef15c2e825fc2a35c984fb6984bf684",
    Path(
        "work/theory/pi-lacunary-near-return-sparsity/"
        "library/t53/T17_REPORT.md"
    ):
        "f566dd992fa7897797a83022741eec709978bb278c4f247d698d73348999719e",
}


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def digest(relative: Path) -> str:
    return sha256((ROOT / relative).read_bytes()).hexdigest()


def run(command: list[str]) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        command,
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        check=False,
    )


def floor_fraction(value: Fraction) -> int:
    return value.numerator // value.denominator


def nearest(value: Fraction) -> int:
    """floor(value + 1/2), matching the report for signed values."""
    return floor_fraction(value + Fraction(1, 2))


def circle_norm(value: Fraction) -> Fraction:
    residue = value - floor_fraction(value)
    return min(residue, 1 - residue)


def torsion_distance(value: Fraction, q: int) -> Fraction:
    return min(
        circle_norm(value - Fraction(k, q))
        for k in range(q)
    )


def check_torsion_thresholds() -> dict[str, int]:
    rows = 0
    thresholds = 0
    cases = (
        (9, 97, 97),
        (99, 101, 101),
        (999, 103, 41),
    )
    for q, denominator, numerator_stop in cases:
        for numerator in range(numerator_stop):
            value = Fraction(numerator, denominator)
            distance = torsion_distance(value, q)
            norm = circle_norm(q * value)
            require(norm == q * distance,
                    f"q-torsion metric identity q={q}, x={value}")
            rows += 1
            for H in range(1, 7):
                require(
                    (norm < Fraction(1, 2 * 10**H))
                    == (distance < Fraction(1, 2 * q * 10**H)),
                    f"q-torsion threshold q={q}, H={H}, x={value}",
                )
                thresholds += 1
    return {"metric_rows": rows, "threshold_rows": thresholds}


def decimal_log_floor_without_logs(twice_norm: Fraction) -> int:
    """Return floor(-log_10(twice_norm)) away from powers of ten."""
    require(0 < twice_norm < 1, "twice norm must lie in (0,1)")
    exponent = 0
    while twice_norm * 10 ** (exponent + 1) < 1:
        exponent += 1
    require(twice_norm * 10 ** (exponent + 1) != 1,
            "excluded half-cell boundary")
    return exponent


def check_zero_blocks_and_h_formula() -> dict[str, int]:
    zero_block_rows = 0
    h_formula_rows = 0
    restricted_error_rows = 0

    # Odd prime denominators avoid half-integer ties and are coprime to every
    # q and radix used below.  These are algebraic test orbits, not pi data.
    cases = ((9, 97), (99, 101), (999, 103))
    for q, denominator in cases:
        require(denominator % 2 == 1 and denominator % 5 != 0,
                "test denominator convention")
        require(q % denominator != 0, "test orbit must remain nonintegral")
        for numerator in range(1, min(denominator, 33)):
            alpha = Fraction(numerator, denominator)
            for n in range(12):
                Q_n = q * 10**n
                start_value = Q_n * alpha
                start_z = nearest(start_value)
                norm = circle_norm(start_value)
                require(0 < norm < Fraction(1, 2), "nonboundary test state")
                require(
                    abs(alpha - Fraction(start_z, Q_n))
                    == norm / Q_n,
                    f"restricted denominator error identity q={q}, n={n}",
                )
                restricted_error_rows += 1

                carries: list[int] = []
                previous_z = start_z
                for offset in range(1, 17):
                    next_z = nearest(q * 10 ** (n + offset) * alpha)
                    carries.append(next_z - 10 * previous_z)
                    previous_z = next_z

                for H in range(1, 7):
                    all_zero = all(carry == 0 for carry in carries[:H])
                    near_torsion = norm < Fraction(1, 2 * 10**H)
                    require(all_zero == near_torsion,
                            f"zero block iff threshold q={q}, n={n}, H={H}")
                    zero_block_rows += 1

                h_actual = 0
                for carry in carries:
                    if carry != 0:
                        break
                    h_actual += 1
                require(h_actual < len(carries), "finite test zero block")
                h_formula = decimal_log_floor_without_logs(2 * norm)
                require(h_actual == h_formula,
                        f"h formula q={q}, n={n}, alpha={alpha}")
                require(
                    Fraction(1, 2 * 10 ** (h_actual + 1)) < norm
                    < Fraction(1, 2 * 10**h_actual),
                    f"h/norm sandwich q={q}, n={n}, alpha={alpha}",
                )
                h_formula_rows += 1

    return {
        "zero_block_threshold_rows": zero_block_rows,
        "h_formula_rows": h_formula_rows,
        "restricted_denominator_error_rows": restricted_error_rows,
    }


def check_rational_agreement_rate() -> dict[str, object]:
    base = Fraction(10**8, 16**7)
    require(base < 1, "sevenfold oversampling rate")
    onsets: dict[str, int] = {}

    for P in (1, 2, 4, 8):
        q = 10**P - 1

        def ratio(n: int) -> Fraction:
            return (
                Fraction(2**8 * q**8, 15 * (7 * n + 1) ** 2)
                * base**n
            )

        n = 0
        while ratio(n) >= 1:
            n += 1
        require(n == 0 or ratio(n - 1) >= 1,
                f"first comparison onset P={P}")
        for index in range(n, n + 24):
            require(ratio(index + 1) < ratio(index),
                    f"monotone agreement ratio P={P}, n={index}")
            require(ratio(index) < 1,
                    f"persistent agreement comparison P={P}, n={index}")
        onsets[str(P)] = n

    M = Fraction(888, 125)
    require(M - 1 == Fraction(763, 125), "linear slope arithmetic")
    return {
        "rate": f"{base.numerator}/{base.denominator}",
        "tail_boundary_comparison_onsets": onsets,
        "irrationality_exponent": "888/125",
        "linear_slope": "763/125",
    }


def main() -> None:
    observed_pins: dict[str, str] = {}
    for relative, expected in PINS.items():
        actual = digest(relative)
        require(actual == expected,
                f"hash mismatch {relative}: expected {expected}, got {actual}")
        observed_pins[str(relative)] = actual

    report_text = (ROOT / PRIMARY_REPORT).read_text(encoding="utf-8")
    require(PINS[Path("problems/local/pi-digits.txt")] in report_text,
            "canonical source pin absent from report")
    require(PINS[PRIMARY_CHECKER] in report_text,
            "checker pin absent from report")

    primary = run([".venv/bin/python", str(PRIMARY_CHECKER)])
    require(primary.returncode == 0, primary.stdout)
    primary_result = json.loads(primary.stdout)
    require(primary_result["status"] == "PASS", "primary replay status")
    require(primary_result["exact_recurrence_rows"] == 800,
            "primary recurrence count")
    require(primary_result["candidate_independent_congruence_checks"] == 8800,
            "primary congruence count")
    for flag in (
        "asserts_bounded_carry_gaps",
        "asserts_logarithmic_carry_gaps",
        "asserts_positive_carry_density",
        "asserts_v1",
    ):
        require(primary_result[flag] is False, f"primary scope flag {flag}")

    torsion = check_torsion_thresholds()
    zero_blocks = check_zero_blocks_and_h_formula()
    agreement = check_rational_agreement_rate()

    print(json.dumps({
        "status": "PASS",
        "claim_label": "proof sketch audit plus experiment replay",
        "pins": observed_pins,
        "primary_status": primary_result["status"],
        "primary_exact_recurrence_rows":
            primary_result["exact_recurrence_rows"],
        "primary_candidate_independent_congruence_checks":
            primary_result["candidate_independent_congruence_checks"],
        "independent_q_torsion_checks": torsion,
        "independent_zero_block_checks": zero_blocks,
        "rational_agreement_rate": agreement,
        "v1_implies_arbitrarily_late_fixed_P_zero_blocks_audited": True,
        "h_formula_boundary_exception_excluded_by_pi_irrationality": True,
        "restricted_exponent_one_is_not_global_irrationality_exponent": True,
        "asserts_bounded_carry_gaps": False,
        "asserts_logarithmic_carry_gaps": False,
        "asserts_positive_carry_density": False,
        "asserts_v1": False,
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
