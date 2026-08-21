#!/usr/bin/env python3
"""Independent exact replay for the colored zero-carry V1 criterion.

This checker imports no primary code.  It reruns the frozen primary checker,
tests the elementary equivalence on disjoint exact finite families, rebuilds
the common BBP phase through a different route and for new periods, checks a
new fixed-residue collision and the lower boundary color, and samples the
factorial-gap counterexample.  The finite results are experiments and assert
neither V1 nor the colored condition for pi.
"""

from __future__ import annotations

from fractions import Fraction
from hashlib import sha256
import json
from math import factorial, gcd, lcm
from pathlib import Path
import subprocess


ROOT = Path(__file__).resolve().parents[2]
PRIMARY_REPORT = Path(
    "work/ultrapi-resume/bbp_colored_zero_carry_v1_20260813.md"
)
PRIMARY_CHECKER = Path(
    "work/ultrapi-resume/bbp_colored_zero_carry_v1_20260813_check.py"
)

PINS = {
    Path("problems/local/pi-digits.txt"):
        "2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825",
    PRIMARY_REPORT:
        "159ff0d1c94d9fb145790e0ca4f11db571d0af211ef2c588b094201122ff279a",
    PRIMARY_CHECKER:
        "7fbce9df0a4a92831ce7cadc5c0343546be71dd771331f7b5f7270fd4150d916",
    Path("work/ultrapi-resume/bbp_fixed_period_carry_attack_20260813.md"):
        "bdc77060ef42a15f8985d70b70cf9777c36070713c940a18e89e05b149734d55",
    Path("work/ultrapi-resume/bbp_centered_carry_recurrence_20260813.md"):
        "3a357c5b1932b76357259613c338dc6ca49f4bf68baef96730ad31b2a13e69e6",
    Path(
        "work/ultrapi-resume/"
        "bbp_centered_carry_recurrence_20260813_check.py"
    ):
        "b83276cc2aceb61e903e8764424e2a3b9dddec8a5ac16ffff4b8370200316fff",
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

MAX_N = 360
NEW_PERIODS = (5, 6)


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


def coefficient_numerator(k: int) -> int:
    return 120 * k * k + 151 * k + 47


def coefficient_denominator(k: int) -> int:
    return (2 * k + 1) * (4 * k + 3) * (8 * k + 1) * (8 * k + 5)


def nearest(value: Fraction) -> int:
    return (2 * value.numerator + value.denominator) // (2 * value.denominator)


def build_states() -> list[dict[str, object]]:
    """Rebuild endpoints by direct Fraction summation, not primary imports."""
    common = 1
    power = 1
    partial = Fraction(0)
    states: list[dict[str, object]] = []

    for m in range(7 * MAX_N + 1):
        denominator = coefficient_denominator(m)
        common = lcm(common, denominator)
        partial += Fraction(coefficient_numerator(m), power * denominator)

        if m % 7 == 0:
            n = m // 7
            scaled = partial * power * common
            require(scaled.denominator == 1, f"raw numerator at n={n}")
            A = scaled.numerator
            D = 2 ** (27 * n) * common
            V = 5**n * A
            quotient, residue = divmod(V, D)
            require(Fraction(V, D) == 10**n * partial,
                    f"base phase normalization n={n}")
            states.append({
                "n": n,
                "L": common,
                "A": A,
                "B": partial,
                "D": D,
                "V": V,
                "a": quotient,
                "r": residue,
            })

        power *= 16

    require(len(states) == MAX_N + 1, "state count")
    return states


def check_zero_block_equivalence() -> int:
    """Exhaust exact nonboundary errors on an odd rational grid."""
    denominator = 2003
    checks = 0
    for height in range(1, 8):
        threshold = Fraction(1, 2 * 10**height)
        for numerator in range(-(denominator // 2), denominator // 2 + 1):
            error = Fraction(numerator, denominator)
            rounded = [nearest(10**step * error) for step in range(height + 1)]
            carries = [
                rounded[step + 1] - 10 * rounded[step]
                for step in range(height)
            ]
            require(
                all(carry == 0 for carry in carries)
                == (abs(error) < threshold),
                f"zero-block threshold H={height}, numerator={numerator}",
            )
            checks += 1
    return checks


def check_periodic_cylinders() -> dict[str, int]:
    """Use period five, absent from the primary exhaustive period family."""
    period = 5
    q = 10**period - 1
    checks = 0
    for k in range(1, q):
        current = k
        emitted: list[int] = []
        for _ in range(period):
            digit, following = divmod(10 * current, q)
            require(0 <= digit <= 9 and 1 <= following < q,
                    f"period-five orbit range k={k}")
            emitted.append(digit)
            current = following
        require(current == k, f"period-five return k={k}")
        require(emitted == [int(d) for d in f"{k:05d}"],
                f"period-five word k={k}")

        for height in (1, period, period + 3):
            _, remainder = divmod(10**height * k, q)
            require(1 <= remainder < q, "interior cylinder remainder")
            left_margin = Fraction(remainder, q * 10**height)
            right_margin = Fraction(q - remainder, q * 10**height)
            radius = Fraction(1, 2 * q * 10**height)
            require(radius < left_margin and radius < right_margin,
                    "half-radius stays in periodic cylinder")
        checks += 1
    return {"period": period, "interior_colors": checks}


def check_append_one_digit_reduction() -> dict[str, int]:
    """Exhaust every five-digit word via a six-digit interior color."""
    word_length = 5
    period = word_length + 1
    q = 10**period - 1
    checks = 0
    for word_value in range(10**word_length):
        appended_digit = 1 if word_value == 0 else 0
        k = 10 * word_value + appended_digit
        require(1 <= k <= q - 1, "appended color is interior")
        require((10**word_length * k) // q == word_value,
                f"appended periodic prefix a={word_value}")
        quotient, remainder = divmod(10**period * k, q)
        require(quotient == k and remainder == k,
                f"period-six cylinder remainder a={word_value}")
        radius = Fraction(1, 2 * q * 10**period)
        require(
            radius < Fraction(k, q * 10**period)
            and radius < Fraction(q - k, q * 10**period),
            "colored radius remains in appended-word cylinder",
        )
        checks += 1
    return {"word_length": word_length, "words": checks, "period": period}


def check_phase_and_colors(states: list[dict[str, object]]) -> dict[str, object]:
    colors: dict[int, list[int]] = {period: [] for period in NEW_PERIODS}
    phase_checks = 0
    color_checks = 0

    for state in states:
        D = int(state["D"])
        V = int(state["V"])
        a = int(state["a"])
        r = int(state["r"])
        for period in NEW_PERIODS:
            q = 10**period - 1
            color = nearest(Fraction(q * r, D))
            rounded = nearest(Fraction(q * V, D))
            require(0 <= color <= q, "split color range")
            require(rounded == q * a + color,
                    f"color decomposition P={period}, n={state['n']}")
            colors[period].append(color)

    for n in range(MAX_N):
        current = states[n]
        following = states[n + 1]
        L = int(current["L"])
        L_next = int(following["L"])
        A = int(current["A"])
        A_next = int(following["A"])
        D = int(current["D"])
        D_next = int(following["D"])
        V = int(current["V"])
        V_next = int(following["V"])
        r = int(current["r"])
        r_next = int(following["r"])
        a = int(current["a"])
        a_next = int(following["a"])

        require(L_next % L == 0, f"nested L n={n}")
        ratio = L_next // L
        dilation = 2**27 * ratio
        H = A_next - 16**7 * ratio * A
        K = 5 ** (n + 1) * H

        current_B = current["B"]
        following_B = following["B"]
        require(isinstance(current_B, Fraction)
                and isinstance(following_B, Fraction), "B types")
        require(
            following_B - current_B
            == Fraction(H, 16 ** (7 * (n + 1)) * L_next),
            f"independent block increment n={n}",
        )
        require(D_next == dilation * D, f"denominator recurrence n={n}")
        require(V_next == 10 * dilation * V + K,
                f"base numerator recurrence n={n}")

        b, calculated_residue = divmod(10 * dilation * r + K, D_next)
        require(calculated_residue == r_next, f"phase residue n={n}")
        require(a_next == 10 * a + b, f"phase quotient n={n}")
        phase_checks += 1

        for period in NEW_PERIODS:
            q = 10**period - 1
            color = colors[period][n]
            next_color = colors[period][n + 1]
            z = q * a + color
            z_next = q * a_next + next_color
            carry = z_next - 10 * z
            require(carry == q * b + next_color - 10 * color,
                    f"colored carry P={period}, n={n}")
            require(
                (carry == 0) == (q * b + next_color == 10 * color),
                f"zero colored carry P={period}, n={n}",
            )
            if carry == 0 and 1 <= color < q:
                require(next_color == (10 * color) % q,
                        f"periodic color transition P={period}, n={n}")
                digit = (10 * color - next_color) // q
                require(b == digit and 0 <= digit <= 9,
                        f"emitted periodic digit P={period}, n={n}")
            color_checks += 1

    collision_period = 5
    q = 10**collision_period - 1
    seen: dict[int, tuple[int, int]] = {}
    collision: dict[str, object] | None = None
    for n, state in enumerate(states):
        residue_mod_q = int(state["r"]) % q
        color = colors[collision_period][n] % q
        earlier = seen.get(residue_mod_q)
        if earlier is not None and earlier[1] != color:
            collision = {
                "period": collision_period,
                "indices": [earlier[0], n],
                "common_phase_residue": residue_mod_q,
                "colors": [earlier[1], color],
            }
            break
        seen[residue_mod_q] = (n, color)
    require(collision is not None, "new P=5 fixed-residue collision")

    return {
        "periods": list(NEW_PERIODS),
        "depth_range": [0, MAX_N],
        "phase_transitions": phase_checks,
        "colored_transitions": color_checks,
        "new_fixed_residue_collision": collision,
    }


def check_fixed_modulus_absorption() -> list[dict[str, int]]:
    rows: list[dict[str, int]] = []
    for period in (5, 6, 7):
        q = 10**period - 1
        witness = (q - 1) // 2
        onset = (q - 1 + 13) // 14
        require(2 * witness + 1 == q, "linear-factor witness")
        require(coefficient_denominator(witness) % q == 0,
                f"q divides d_j P={period}")
        require(7 * onset >= witness, f"witness included P={period}")
        require(onset == 0 or 7 * (onset - 1) < witness,
                f"minimal coarse onset P={period}")
        rows.append({"period": period, "witness_k": witness, "onset": onset})
    return rows


def check_eventual_transfer_arithmetic() -> list[dict[str, int]]:
    require(10**8 < 16**7, "sevenfold oversampling margin")
    rows: list[dict[str, int]] = []
    for period in NEW_PERIODS:
        q = 10**period - 1
        n = 1
        while True:
            ratio = (
                Fraction(2**8 * q**8, 15 * (7 * n + 1) ** 2)
                * Fraction(10**8, 16**7) ** n
            )
            if ratio < 1:
                break
            n += 1
        require(
            Fraction(2**8 * q**8, 15 * (7 * (n + 1) + 1) ** 2)
            * Fraction(10**8, 16**7) ** (n + 1)
            < ratio,
            "tail/boundary ratio decreases after witnessed onset",
        )

        # Even if (2m+1)/(2q10^n) is unreduced, its odd numerator cannot
        # cancel the 2^(n+1) factor.  These exact samples audit that detail.
        for odd_numerator in (1, 3, 2 * q - 1, 2 * q + 1):
            reduced_denominator = (
                2 * q * 10**n // gcd(odd_numerator, 2 * q * 10**n)
            )
            require(reduced_denominator % 2 ** (n + 1) == 0,
                    "reduced boundary denominator retains dyadic growth")
        rows.append({"period": period, "finite_ratio_below_one_depth": n})
    return rows


def check_lower_boundary_split() -> dict[str, object]:
    """Certify a disjoint all-zero-side block from the pinned pi prefix."""
    digits_path = Path(
        "work/theory/pi-lacunary-near-return-sparsity/"
        "library/t53/pi_digits.txt"
    )
    digits = (ROOT / digits_path).read_text(encoding="ascii").strip()
    q = 9
    positions = [854, 855, 856]
    lookahead = 32
    scale = 10**lookahead
    colors: list[int] = []
    for n in positions:
        prefix = int(digits[n:n + lookahead])
        lower = nearest(Fraction(q * prefix, scale))
        upper = nearest(Fraction(q * (prefix + 1), scale))
        require(lower == upper, f"certified lower color n={n}")
        colors.append(lower)
    require(colors == [0, 0, 0], "new lower split-color witness")
    carries = [
        q * int(digits[n]) + colors[index + 1] - 10 * colors[index]
        for index, n in enumerate(positions[:-1])
    ]
    require(carries == [0, 0], "new lower-side two-zero block")
    return {
        "positions": positions,
        "ordinary_residue": 0,
        "split_color": 0,
        "carries": carries,
    }


def check_sparse_counterexample_samples() -> list[dict[str, int]]:
    rows: list[dict[str, int]] = []
    samples = ((3, 13, 50), (5, 27, 500), (6, 43, 1000))
    for period, height, minimum_n in samples:
        q = 10**period - 1
        j = 2
        while True:
            n = factorial(j)
            gap = factorial(j + 1) - n
            if n >= minimum_n and 20 * q < 9 * 10 ** (gap - height):
                break
            j += 1
        require(gap > height, "factorial gap dominates requested block")
        require(factorial(j + 2) - n > gap,
                "later factorial exponent is beyond first tail exponent")
        rows.append({
            "period": period,
            "height": height,
            "minimum_n": minimum_n,
            "factorial_index": j,
            "n": n,
            "next_gap": gap,
        })
    return rows


def main() -> None:
    observed_pins: dict[str, str] = {}
    for relative, expected in PINS.items():
        actual = digest(relative)
        require(actual == expected,
                f"hash mismatch {relative}: expected {expected}, got {actual}")
        observed_pins[str(relative)] = actual

    primary = run([".venv/bin/python", str(PRIMARY_CHECKER)])
    require(primary.returncode == 0, primary.stdout)
    primary_result = json.loads(primary.stdout)
    require(primary_result["status"] == "PASS", "primary replay")
    require(primary_result["asserts_colored_condition_for_pi"] is False,
            "primary colored-condition scope")
    require(primary_result["asserts_v1"] is False, "primary V1 scope")

    zero_blocks = check_zero_block_equivalence()
    periodic = check_periodic_cylinders()
    appended = check_append_one_digit_reduction()
    states = build_states()
    phases = check_phase_and_colors(states)
    absorption = check_fixed_modulus_absorption()
    transfer = check_eventual_transfer_arithmetic()
    boundary = check_lower_boundary_split()
    sparse = check_sparse_counterexample_samples()

    print(json.dumps({
        "status": "PASS",
        "exact_derivation_label": "proof sketch",
        "finite_replay_label": "experiment",
        "pins": observed_pins,
        "primary_status": primary_result["status"],
        "zero_block_grid_checks": zero_blocks,
        "new_periodic_cylinder_family": periodic,
        "append_one_digit_exhaustion": appended,
        "common_phase_replay": phases,
        "new_fixed_modulus_absorption_witnesses": absorption,
        "eventual_transfer_arithmetic": transfer,
        "new_zero_residue_boundary_side": boundary,
        "new_sparse_counterexample_samples": sparse,
        "asserts_colored_condition_for_pi": False,
        "asserts_v1": False,
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
