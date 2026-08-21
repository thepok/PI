#!/usr/bin/env python3
"""Exact replay for the odd-LCM centered-carry no-go audit.

All BBP assertions below use Python integers or ``fractions.Fraction``.
The certified decimal-window assertion uses an enclosing interval from a
pinned digit source.  Finite checks are experiments, not asymptotic theorems.
This script asserts neither positive carry density nor canonical V1.
"""

from __future__ import annotations

from fractions import Fraction
from hashlib import sha256
import json
from math import gcd, isqrt
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]

PINS = {
    "problems/local/pi-digits.txt":
        "2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825",
    "work/ultrapi-resume/bbp_fixed_period_carry_attack_20260813.md":
        "bdc77060ef42a15f8985d70b70cf9777c36070713c940a18e89e05b149734d55",
    "work/ultrapi-resume/bbp_fixed_period_carry_attack_20260813_independent_audit.md":
        "ae7e6c84ca6ec253107c2fa48ed202c5ef4f3aadbee75cbd1bca3d2d03dafe91",
    "work/theory/pi-lacunary-near-return-sparsity/library/t53/pi_digits.txt":
        "77eeccb0067283e14c460b33dc230de54ef15c2e825fc2a35c984fb6984bf684",
    "work/theory/pi-lacunary-near-return-sparsity/library/t53/T17_REPORT.md":
        "f566dd992fa7897797a83022741eec709978bb278c4f247d698d73348999719e",
}

MAX_N = 800
Q = 9
ZERO_BLOCK = tuple(range(761, 766))

EXPECTED_R_FACTORS = {
    761: (21319, 21323, 42641, 42649, 42677),
    762: (21347, 42689, 42697, 42701, 42709),
    763: (21379, 21383, 21391, 42737, 42773),
    764: (21407, 21419, 42793, 42797, 42821, 42829, 42841),
    765: (42853, 42901),
}


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def digest(path: Path) -> str:
    return sha256(path.read_bytes()).hexdigest()


def numerator(k: int) -> int:
    return 120 * k * k + 151 * k + 47


def denominator(k: int) -> int:
    return (2 * k + 1) * (4 * k + 3) * (8 * k + 1) * (8 * k + 5)


def coefficient(k: int) -> Fraction:
    return Fraction(numerator(k), denominator(k))


def lcm(a: int, b: int) -> int:
    return a // gcd(a, b) * b


def nearest(a: int, b: int) -> int:
    """Return floor(a / b + 1/2), with b positive."""
    require(b > 0, "nearest denominator positive")
    return (2 * a + b) // (2 * b)


def is_prime(n: int) -> bool:
    if n < 2:
        return False
    if n % 2 == 0:
        return n == 2
    for divisor in range(3, isqrt(n) + 1, 2):
        if n % divisor == 0:
            return False
    return True


def build_endpoints() -> list[dict[str, int]]:
    """Build exact L_m,A_m data at m=7n."""
    common = denominator(0)
    scaled = numerator(0)
    endpoints = [{"n": 0, "L": common, "A": scaled, "R": 1, "H": 0}]

    for m in range(1, 7 * MAX_N + 1):
        d = denominator(m)
        next_common = lcm(common, d)
        scaled = (
            16 * (next_common // common) * scaled
            + numerator(m) * (next_common // d)
        )
        common = next_common
        if m % 7 == 0:
            previous = endpoints[-1]
            ratio = common // previous["L"]
            forcing = sum(
                numerator(k)
                * 16 ** (m - k)
                * (common // denominator(k))
                for k in range(m - 6, m + 1)
            )
            require(
                scaled == 16**7 * ratio * previous["A"] + forcing,
                f"sevenfold A recurrence at m={m}",
            )
            endpoints.append(
                {"n": m // 7, "L": common, "A": scaled,
                 "R": ratio, "H": forcing}
            )
    require(len(endpoints) == MAX_N + 1, "endpoint count")
    return endpoints


def build_states(endpoints: list[dict[str, int]]) -> tuple[list[dict[str, int]], list[int]]:
    states: list[dict[str, int]] = []
    carries: list[int] = []
    five_power = 1

    for endpoint in endpoints:
        n = endpoint["n"]
        D = 2 ** (27 * n) * endpoint["L"]
        U = Q * five_power * endpoint["A"]
        z = nearest(U, D)
        S = U - D * z
        require(-D <= 2 * S < D, f"centered interval n={n}")
        states.append({"D": D, "U": U, "z": z, "S": S})

        if n:
            old = states[n - 1]
            R = endpoint["R"]
            alpha = 2**27 * R
            J = Q * five_power * endpoint["H"]
            gamma = z - 10 * old["z"]

            require(D == alpha * old["D"], f"D recurrence n={n - 1}")
            require(U == 10 * alpha * old["U"] + J,
                    f"U recurrence n={n - 1}")
            require(S == 10 * alpha * old["S"] + J - gamma * D,
                    f"S recurrence n={n - 1}")

            # Normalization removes the explicit LCM multiplier alpha.  The
            # seven new coefficients remain in the rational forcing delta.
            delta = Fraction(J, D)
            block = sum(
                coefficient(k) / 16**k
                for k in range(7 * (n - 1) + 1, 7 * n + 1)
            )
            require(delta == Q * 10**n * block,
                    f"normalized forcing identity n={n - 1}")
            require(
                gamma == nearest(10 * old["S"] * D + J * old["D"],
                                 old["D"] * D),
                f"normalized nearest-integer recurrence n={n - 1}",
            )
            require(Fraction(S, D) == 10 * Fraction(old["S"], old["D"]) + delta - gamma,
                    f"normalized centered recurrence n={n - 1}")

            # Every congruence modulo the new odd LCM quotient is independent
            # of the carry candidate, not only of the actual carry.
            require(S % R == J % R, f"new-LCM congruence n={n - 1}")
            for candidate in range(-5, 6):
                candidate_S = 10 * alpha * old["S"] + J - candidate * D
                require(candidate_S % R == J % R,
                        f"candidate-independent congruence n={n - 1}")
            carries.append(gamma)
        five_power *= 5
    return states, carries


def certified_true_window() -> dict[str, object]:
    """Certify the local true P=1 carry window by decimal enclosures."""
    digits = (
        ROOT
        / "work/theory/pi-lacunary-near-return-sparsity/library/t53/pi_digits.txt"
    ).read_text(encoding="ascii").strip()
    require(len(digits) == 1_048_596 and digits.isdigit(), "digit source format")
    lookahead = 40
    scale = 10**lookahead

    def rounded_tail(index: int) -> int:
        prefix = int(digits[index:index + lookahead])
        lower = nearest(Q * prefix, scale)
        upper = nearest(Q * (prefix + 1), scale)
        require(lower == upper, f"rounding enclosure index={index}")
        return lower

    observed = []
    for n in range(710_098, 710_106):
        carry = (
            Q * int(digits[n])
            + rounded_tail(n + 1)
            - 10 * rounded_tail(n)
        )
        observed.append(carry)
    require(observed == [-4, 0, 0, 0, 0, 0, 0, 5],
            "certified six-zero true-carry window")
    return {
        "range": [710_098, 710_105],
        "carries": observed,
        "zero_block_start": 710_099,
        "zero_block_length": 6,
        "claim_label": "experiment",
    }


def replay() -> dict[str, object]:
    for relative, expected in PINS.items():
        path = ROOT / relative
        require(path.is_file(), f"missing pinned input: {relative}")
        require(digest(path) == expected, f"hash mismatch: {relative}")

    for k in range(256):
        direct = (
            Fraction(4, 8 * k + 1)
            - Fraction(2, 8 * k + 4)
            - Fraction(1, 8 * k + 5)
            - Fraction(1, 8 * k + 6)
        )
        require(direct == coefficient(k), f"combined BBP coefficient k={k}")
        require(denominator(k) % 2 == 1, f"odd coefficient denominator k={k}")

    endpoints = build_endpoints()
    states, carries = build_states(endpoints)
    require(carries[755:772] ==
            [5, -1, 0, 2, 1, 5, 0, 0, 0, 0, 0, -1, -5, 4, -4, -3, -2],
            "rational local carry window")

    zero_rows = []
    for n in ZERO_BLOCK:
        endpoint = endpoints[n + 1]
        R = endpoint["R"]
        J = Q * 5 ** (n + 1) * endpoint["H"]
        factors = EXPECTED_R_FACTORS[n]
        require(all(is_prime(prime) for prime in factors), f"prime factors n={n}")
        product = 1
        for prime in factors:
            product *= prime
        require(R == product, f"complete R factorization n={n}")
        require(carries[n] == 0, f"zero carry n={n}")
        require(gcd(J, R) == 1, f"forcing unit modulo R n={n}")
        require(gcd(states[n + 1]["S"], R) == 1,
                f"centered numerator unit modulo R n={n}")
        zero_rows.append({
            "n": n,
            "R": R,
            "R_factors": list(factors),
            "R_bits": R.bit_length(),
            "gcd_J_R": 1,
            "carry": 0,
        })

    no_growth_nonzero = []
    for n in (438, 727):
        require(endpoints[n + 1]["R"] == 1, f"no LCM growth n={n}")
        require(carries[n] != 0, f"nonzero carry n={n}")
        no_growth_nonzero.append({"n": n, "carry": carries[n]})

    true_window = certified_true_window()

    return {
        "status": "PASS",
        "claim_label": "experiment",
        "pinned_inputs": len(PINS),
        "sevenfold_blocks": MAX_N,
        "exact_recurrence_rows": MAX_N,
        "candidate_independent_congruence_checks": 11 * MAX_N,
        "rational_zero_block": {
            "start": ZERO_BLOCK[0],
            "length": len(ZERO_BLOCK),
            "rows": zero_rows,
        },
        "no_growth_nonzero_examples": no_growth_nonzero,
        "certified_true_window": true_window,
        "asserts_bounded_carry_gaps": False,
        "asserts_logarithmic_carry_gaps": False,
        "asserts_positive_carry_density": False,
        "asserts_v1": False,
    }


if __name__ == "__main__":
    print(json.dumps(replay(), indent=2, sort_keys=True))
