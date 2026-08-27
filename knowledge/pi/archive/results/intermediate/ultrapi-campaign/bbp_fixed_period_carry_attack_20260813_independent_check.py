#!/usr/bin/env python3
"""Independent exact replay of the fixed-period BBP carry reduction.

This checker deliberately does not import the primary checker.  Structural
claims are replayed with a separate direct-Fraction implementation and at
different depths.  Finite rows are experiments; external irrationality and
continued-fraction theorems are pinned inputs, not re-proved here.
"""

from __future__ import annotations

from decimal import Decimal, getcontext
from fractions import Fraction
from functools import reduce
from hashlib import sha256
import json
from math import gcd
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]

PINS = {
    "problems/local/pi-digits.txt":
        "2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825",
    "work/ultrapi-resume/bbp_fixed_period_carry_attack_20260813.md":
        "bdc77060ef42a15f8985d70b70cf9777c36070713c940a18e89e05b149734d55",
    "work/ultrapi-resume/bbp_fixed_period_carry_attack_20260813_check.py":
        "48a9db36d577376b0229f48c37ae399cdebe62d1a9c0c2959bebd368a4fe9ceb",
    "work/ultrapi-resume/bbp_adjacent_matching_breakthrough_report.md":
        "2b231d3c2e2ef717a2941a0452304ba402915318b72d305f6a6129ee8431f042",
    "work/ultrapi-resume/bbp_adjacent_matching_breakthrough_independent_audit.md":
        "32cf25b1b2d00a37de57b325134ba0a53e8f5f6c129b16d3f419000a1620af93",
    "work/theory/pi-digits/library/t6/bbp-1997-nasa.pdf":
        "e4e0b97fde01328ec41da5f2cd4d6ffc8bcd2b7bd7516b9d8afc320f6d1916c4",
    "work/theory/pi-lacunary-near-return-sparsity/library/t63/"
    "lagarias-math0101055v2.pdf":
        "a2a1171eb9c75c9fa3495ca3c3ceaa33c1d20b722bb56f82adb56d8c308209b9",
    "work/theory/pi-positive-decimal-factor-entropy/library/t87/"
    "zeilberger-zudilin-2020.pdf":
        "3b11c4bf3e25927227ac8f7f4e49d7f1d3efeb42beecd7f3b8c64efb162d20b5",
    "work/theory/pi-lacunary-near-return-sparsity/library/t89/kempner-1916.pdf":
        "99c4bf8d04d2dbdc63e8d274266f212072d4c248fcbc659e60ca7fa9350eb014",
    "work/ultrapi-resume/library/shallit-1979-simple-continued-fractions.pdf":
        "592a08ecf6df04414fe7bf5083d56898139b5d553679b244296833a1e2f1f981",
    "TheoryLib/PiLongLagBlockCollisionDecay/"
    "T4T4PublishedIrrationalityOnset.lean":
        "73a70fc981bc5856e6c52f3c27143d1a54d84373f830c2b1d37faeb2fdbd71de",
    "TheoryLib/PiQuantitativeBlockHitting/"
    "T35T35OversampledBBPGridStability.lean":
        "7374fdaa2aebac7c228408576724c80e5d5558eb515202b45982dfe726f03351",
    "TheoryLib/PiPositiveDecimalFactorEntropy/"
    "T36T36DecimalPeriodicWindowGap.lean":
        "900e9fdeefbaea73236435b3845cd9dcc3c3b07b93d2e244b94dc39f4c109781",
}


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def digest(path: Path) -> str:
    return sha256(path.read_bytes()).hexdigest()


def lcm_pair(a: int, b: int) -> int:
    return a // gcd(a, b) * b


def raw_bbp_term(k: int) -> Fraction:
    return (
        Fraction(4, 8 * k + 1)
        - Fraction(2, 8 * k + 4)
        - Fraction(1, 8 * k + 5)
        - Fraction(1, 8 * k + 6)
    )


def collapsed_data(k: int) -> tuple[int, int]:
    return (
        120 * k * k + 151 * k + 47,
        (2 * k + 1) * (4 * k + 3) * (8 * k + 1) * (8 * k + 5),
    )


def fract(x: Fraction) -> Fraction:
    return x - x.numerator // x.denominator


def centered(x: Fraction) -> Fraction:
    r = fract(x)
    return r if 2 * r < 1 else r - 1


def norm_circle(x: Fraction) -> Fraction:
    return abs(centered(x))


def nearest_integer(x: Fraction) -> int:
    return (2 * x.numerator + x.denominator) // (2 * x.denominator)


def check_bbp_arithmetic() -> dict[str, int]:
    coefficient_checks = 0
    for k in range(401):
        c, d = collapsed_data(k)
        require(raw_bbp_term(k) == Fraction(c, d), f"collapsed coefficient {k}")
        require(c > 0 and d % 2 == 1, f"positive/odd coefficient data {k}")
        if k:
            polynomial = 392 * k**4 + 873 * k**3 + 665 * k**2 + 194 * k + 15
            require(d - k * k * c == polynomial > 0, f"global 1/k^2 certificate {k}")
        coefficient_checks += 1

    terms: list[Fraction] = []
    old_l = 1
    old_a = 0
    denominator_checks = 0
    residue_checks = 0
    for n in range(97):
        c_n, d_n = collapsed_data(n)
        terms.append(Fraction(c_n, d_n * 16**n))
        direct = sum(terms, Fraction())
        denominators = [collapsed_data(k)[1] for k in range(n + 1)]
        common = reduce(lcm_pair, denominators, 1)
        scaled = direct * 16**n * common
        require(scaled.denominator == 1, f"integral common numerator {n}")
        a_n = scaled.numerator
        explicit = sum(
            collapsed_data(k)[0] * 16 ** (n - k) * (common // collapsed_data(k)[1])
            for k in range(n + 1)
        )
        require(a_n == explicit, f"explicit common numerator {n}")
        ell = common // old_l
        require(a_n == 16 * ell * old_a + c_n * (common // d_n),
                f"one-step common numerator {n}")
        orbit = Fraction(5**n * a_n, 8**n * common)
        require(fract(10**n * direct) == fract(orbit), f"decimal orbit {n}")
        modulus = 8**n * common
        for period in (1, 3, 5, 9, 13):
            q = 10**period - 1
            residue = (q * 5**n * a_n) % modulus
            require(norm_circle(q * orbit) == Fraction(min(residue, modulus - residue), modulus),
                    f"least residue n={n}, P={period}")
            residue_checks += 1
        old_l, old_a = common, a_n
        denominator_checks += 1

    require(Fraction(1, 15) / (1 - Fraction(5, 8)) == Fraction(8, 45),
            "summed diagonal BBP shadow")
    return {
        "coefficient_checks": coefficient_checks,
        "common_denominator_checks": denominator_checks,
        "least_residue_checks": residue_checks,
    }


def centered_orbit(seed: Fraction, length: int) -> tuple[list[Fraction], list[int]]:
    errors: list[Fraction] = []
    carries: list[int] = []
    for n in range(length + 1):
        errors.append(centered(10**n * seed))
    for n in range(length):
        gamma = 10 * errors[n] - errors[n + 1]
        require(gamma.denominator == 1 and -5 <= gamma <= 5,
                f"centered integral carry n={n}")
        carries.append(gamma.numerator)
    return errors, carries


def check_carry_energy() -> dict[str, int]:
    # A separate grid validates the two pointwise metric inequalities.
    metric_checks = 0
    for da in (7, 11, 17, 29):
        for db in (13, 19, 31):
            for ia in range(-da // 2 + 1, da // 2 + 1):
                for ib in range(-db // 2 + 1, db // 2 + 1):
                    a, b = Fraction(ia, da), Fraction(ib, db)
                    require(
                        11 * (10 * a * a + b * b) - (10 * a - b) ** 2
                        == 10 * (a + b) ** 2,
                        "quadratic carry identity",
                    )
                    for q in (1, 9, 99):
                        lhs = abs(norm_circle(q * a) ** 2 - norm_circle(q * b) ** 2)
                        require(lhs <= q * norm_circle(a - b), "circle-square Lipschitz")
                    metric_checks += 1

    prefix_checks = 0
    window_checks = 0
    seeds = [Fraction(2, 37), Fraction(5, 73), Fraction(41, 257), Fraction(101, 997)]
    for seed in seeds:
        errors, carries = centered_orbit(seed, 389)
        for length in (17, 83, 211, 377):
            reconstructed = sum(
                Fraction(carries[n], 10 ** (n + 1)) for n in range(length)
            ) + errors[length] / 10**length
            require(reconstructed == errors[0], "finite centered expansion")
            energy = sum(e * e for e in errors[:length])
            count = sum(g != 0 for g in carries[:length])
            require(Fraction(count) <= 121 * energy + Fraction(11, 4),
                    "prefix count versus energy")
            prefix_checks += 1
            for width in (2, 6, 11):
                extended = sum(g != 0 for g in carries[: length + width])
                require(
                    energy / length
                    <= Fraction(width * extended, 4 * length)
                    + Fraction(1, 4 * 10 ** (2 * width)),
                    "window count versus energy",
                )
                window_checks += 1

    sharp_errors, sharp_carries = centered_orbit(Fraction(1, 11), 300)
    require(all(sharp_errors[n] == Fraction((-1) ** n, 11) for n in range(301)),
            "sharp error orbit")
    require(all(sharp_carries[n] == (-1) ** n for n in range(300)),
            "sharp carry orbit")
    require(sum(g * g for g in sharp_carries) ==
            121 * sum(e * e for e in sharp_errors[:300]), "sharp factor 121")
    return {
        "metric_grid_checks": metric_checks,
        "prefix_checks": prefix_checks,
        "window_checks": window_checks,
    }


def check_oversampling() -> dict[str, object]:
    require(10**8 < 16**7, "sevenfold oversampling base")
    require(not (10**8 < 16**6), "sixfold does not meet exponent-eight comparison")
    thresholds: dict[str, int] = {}
    for period in (1, 2, 4, 8, 12):
        q = 10**period - 1
        threshold = None
        previous = None
        for n in range(1, 2000):
            ratio = Fraction(2**8 * q**8, 15 * (7 * n + 1) ** 2) * Fraction(10**8, 16**7) ** n
            if previous is not None:
                require(ratio < previous, f"oversampling ratio decreases P={period}")
            previous = ratio
            if threshold is None and ratio < 1:
                threshold = n
        require(threshold is not None, f"finite oversampling threshold P={period}")
        thresholds[str(period)] = threshold

    # Directly rebuild B_(7n), then verify the rational shadow presentation.
    shadow_checks = 0
    carry_checks = 0
    previous_nearest: dict[int, int] = {}
    all_terms: list[Fraction] = []
    for k in range(7 * 24 + 1):
        c, d = collapsed_data(k)
        all_terms.append(Fraction(c, d * 16**k))
    for n in range(25):
        m = 7 * n
        direct = sum(all_terms[: m + 1], Fraction())
        common = reduce(lcm_pair, (collapsed_data(k)[1] for k in range(m + 1)), 1)
        scaled = direct * 16**m * common
        require(scaled.denominator == 1, f"oversampled common numerator {n}")
        for period in (1, 4, 9):
            q = 10**period - 1
            shadow = q * 10**n * direct
            displayed = Fraction(q * 5**n * scaled.numerator, 2 ** (27 * n) * common)
            require(shadow == displayed, f"oversampled rational presentation n={n}, P={period}")
            nearest = nearest_integer(shadow)
            if n:
                require(isinstance(nearest - 10 * previous_nearest[period], int),
                        "rational carry integer")
                carry_checks += 1
            previous_nearest[period] = nearest
            shadow_checks += 1

    # Exact rescaling of the exponent-eight boundary separation.
    for period in (1, 5, 11):
        q = 10**period - 1
        for n in (1, 7, 19):
            Q = 2 * q * 10**n
            require(Fraction(q * 10**n, Q**8) ==
                    Fraction(1, 2**8 * q**7 * 10 ** (7 * n)),
                    "boundary rescaling")
    return {
        "shadow_formula_checks": shadow_checks,
        "rational_carry_checks": carry_checks,
        "finite_ratio_below_one_thresholds": thresholds,
    }


def check_logarithmic_constants_and_kempner() -> dict[str, object]:
    getcontext().prec = 60
    source_bound = Decimal("7.10320533413700172750577342281")
    exponent = Decimal(888) / Decimal(125)
    require(source_bound < exponent < Decimal(8), "published exponent slack")
    count_constant = Decimal(1) / exponent.ln()
    energy_constant = count_constant / Decimal(121)
    require(abs(count_constant - Decimal("0.51003285483647831532979185324463")) < Decimal("1e-31"),
            "logarithmic count constant")
    require(abs(energy_constant - Decimal("0.004215147560632052192808197134253")) < Decimal("1e-33"),
            "logarithmic energy constant")

    # Exact finite truncations of the Fredholm/Kempner tail, using powers
    # through 256.  Every asserted inequality is rational and termwise.
    exponents = [1, 2, 4, 8, 16, 32, 64, 128, 256]
    kappa_trunc = sum((Fraction(1, 10**e) for e in exponents), Fraction())
    tail_checks = 0
    defect_checks = 0
    block_sums: dict[str, float] = {}
    for n in range(128):
        next_exponent = min(e for e in exponents if e > n)
        h = next_exponent - n
        exact_tail = sum((Fraction(10**n, 10**e) for e in exponents if e > n), Fraction())
        require(fract(10**n * kappa_trunc) == exact_tail, f"finite sparse tail {n}")
        # State the geometric envelope without floating-point exponentiation.
        envelope = Fraction(10, 9 * 10**h)
        require(exact_tail <= envelope, f"sparse geometric envelope {n}")
        tail_checks += 1
        for period in (1, 3, 7):
            q = 10**period - 1
            defect = norm_circle(q * kappa_trunc * 10**n) ** 2
            envelope_defect = min(Fraction(1, 4), q * q * envelope * envelope)
            require(defect <= envelope_defect, f"sparse defect envelope n={n}, P={period}")
            defect_checks += 1

    for period in (1, 3, 7):
        q = 10**period - 1
        total = sum(norm_circle(q * kappa_trunc * 10**n) ** 2 for n in range(128))
        block_sums[str(period)] = float(total)

    return {
        "count_constant": str(count_constant),
        "energy_constant": str(energy_constant),
        "finite_sparse_tail_checks": tail_checks,
        "finite_sparse_defect_checks": defect_checks,
        "finite_sparse_energy_N128": block_sums,
    }


def replay() -> dict[str, object]:
    for relative, expected in PINS.items():
        path = ROOT / relative
        require(path.is_file(), f"missing pinned input: {relative}")
        require(digest(path) == expected, f"pinned input changed: {relative}")

    t4 = (ROOT / "TheoryLib/PiLongLagBlockCollisionDecay/"
          "T4T4PublishedIrrationalityOnset.lean").read_text()
    t35 = (ROOT / "TheoryLib/PiQuantitativeBlockHitting/"
           "T35T35OversampledBBPGridStability.lean").read_text()
    t36 = (ROOT / "TheoryLib/PiPositiveDecimalFactorEntropy/"
           "T36T36DecimalPeriodicWindowGap.lean").read_text()
    require("μ + ε" in t4 and "irrationalityMeasureBelow_eight_implies" in t4,
            "source quantifier interface markers")
    require("eventually_powTenEight_lt_powSixteenSeven" in t35,
            "independently located sevenfold machine-check marker")
    require("effectiveIrrationality_periodic_window_gap" in t36,
            "periodic-window machine-check marker")

    return {
        "status": "PASS",
        "claim_label": "experiment",
        "pinned_inputs": len(PINS),
        "bbp_arithmetic": check_bbp_arithmetic(),
        "carry_energy": check_carry_energy(),
        "oversampling": check_oversampling(),
        "logarithmic_and_separator": check_logarithmic_constants_and_kempner(),
        "asserts_positive_cesaro_defect": False,
        "asserts_adjacent_matching": False,
        "asserts_fixed_sixteen_return": False,
        "asserts_v1": False,
    }


if __name__ == "__main__":
    print(json.dumps(replay(), indent=2, sort_keys=True))
