#!/usr/bin/env python3
"""Independent finite replay for the all-stratum dyadic-mixing audit.

All bounded computations have claim label ``experiment``.  This checker does
not import the primary checker: for nonnegative arguments it evaluates the BBP
state by the forward recurrence F(x + 1) = 16 F(x) + a(x), starting at F(0)=0.
"""

from __future__ import annotations

from fractions import Fraction
from hashlib import sha256
import json
from math import gcd
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]

PINS = {
    "problems/local/pi-digits.txt":
        "2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825",
    "work/ultrapi-resume/bbp_all_stratum_dyadic_mixing_20260813.md":
        "5089d63f83de1978731c50964c7fce45e7a4cc88e989a29acd99e08b8a9c8360",
    "work/ultrapi-resume/bbp_all_stratum_dyadic_mixing_20260813_check.py":
        "dbbf1cbeba9915f3377ae5dbb4a03026be031b1112bc924ab7211227dccc0fcf",
    "work/ultrapi-resume/bbp_all_depth_two_adic_attack.md":
        "9c1282724c7999fd67133a3f0e756015e564dc6b7a2a1ec44f2efe892b2653d9",
    "work/ultrapi-resume/bbp_high_dyadic_archimedean_separator_20260813.md":
        "d0d975ff9bab6ce456723085cb3e031a3be83a171fa6a94d8656d76d8b0457b3",
    "work/ultrapi-resume/bbp_even_depth_dyadic_mixing_20260813.md":
        "3d47a6a17e759d18b0aafb6215405226eadb99d1d83241a160dc93f6f8a3e623",
    "work/theory/pi-digits/library/t6/bbp-1997-nasa.pdf":
        "e4e0b97fde01328ec41da5f2cd4d6ffc8bcd2b7bd7516b9d8afc320f6d1916c4",
}

MAX_RAW_PRECISION = 10
MAX_STRATUM = 6
MAX_STRATUM_PRECISION = 8
MAX_EXACT_SEVENFOLD_DEPTH = 48


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


def coefficient_mod(k: int, modulus: int) -> int:
    bottom = denominator(k)
    require(bottom % 2 == 1, f"odd coefficient denominator at k={k}")
    return numerator(k) * pow(bottom, -1, modulus) % modulus


def valuation_two(value: int) -> int:
    require(value != 0, "valuation requested at zero")
    value = abs(value)
    return (value & -value).bit_length() - 1


def rational_mod(value: Fraction, exponent: int) -> int:
    require(exponent >= 1, "positive precision required")
    require(value.denominator % 2 == 1, "two-integral rational required")
    modulus = 1 << exponent
    return value.numerator * pow(value.denominator, -1, modulus) % modulus


class ForwardState:
    """Memoized forward recurrence for F on nonnegative integer arguments."""

    def __init__(self) -> None:
        self.tables: dict[int, list[int]] = {}

    def residue(self, x: int, exponent: int) -> int:
        require(x >= 0, "forward F recurrence needs x >= 0")
        require(exponent >= 1, "positive precision required")
        modulus = 1 << exponent
        table = self.tables.setdefault(exponent, [0])
        while len(table) <= x:
            k = len(table) - 1
            table.append(
                (16 * table[-1] + coefficient_mod(k, modulus)) % modulus
            )
        return table[x]


FORWARD = ForwardState()


def reflected_series_residue(x: int, exponent: int) -> int:
    """Independent truncation of sum_j 16^j a(x-1-j) modulo 2^exponent."""
    modulus = 1 << exponent
    total = 0
    for j in range((exponent - 1) // 4 + 1):
        total += pow(16, j, modulus) * coefficient_mod(x - 1 - j, modulus)
    return total % modulus


def z_residue(n: int, exponent: int) -> int:
    require(n >= 0, "selected depth must be nonnegative")
    modulus = 1 << exponent
    return pow(5, n, modulus) * FORWARD.residue(7 * n + 1, exponent) % modulus


def stratum_representative(r: int) -> int:
    modulus = 1 << (r + 1)
    return pow(7, -1, modulus) * ((1 << r) - 1) % modulus


def lcm(first: int, second: int) -> int:
    return first // gcd(first, second) * second


def selected_endpoints() -> dict[int, tuple[int, int]]:
    """Build (L_(7n), A_(7n)) from the rational BBP recurrence."""
    common = denominator(0)
    selected = numerator(0)
    endpoints: dict[int, tuple[int, int]] = {}
    for depth in range(1, 7 * MAX_EXACT_SEVENFOLD_DEPTH + 1):
        new_denominator = denominator(depth)
        new_common = lcm(common, new_denominator)
        selected = (
            16 * selected * (new_common // common)
            + numerator(depth) * (new_common // new_denominator)
        )
        common = new_common
        if depth % 7 == 0:
            endpoints[depth // 7] = (common, selected)
    return endpoints


def replay() -> dict[str, object]:
    for relative, expected in PINS.items():
        path = ROOT / relative
        require(path.is_file(), f"missing pinned input/source: {relative}")
        require(digest(path) == expected, f"hash mismatch: {relative}")

    recurrence_series_cross_checks = 0
    reflected_zero_checks = 0
    for exponent in range(1, 41):
        require(reflected_series_residue(0, exponent) == 0,
                f"reflected null identity modulo 2^{exponent}")
        reflected_zero_checks += 1
        for x in (0, 1, 2, 7, 19, 64):
            require(
                FORWARD.residue(x, exponent)
                == reflected_series_residue(x, exponent),
                f"forward/series agreement x={x}, exponent={exponent}",
            )
            recurrence_series_cross_checks += 1

    lifting_checks = 0
    for distance in range(1, 4097):
        require(
            valuation_two(pow(5, distance) - 1)
            == 2 + valuation_two(distance),
            f"five-power lifting at d={distance}",
        )
        lifting_checks += 1

    raw_bijection_checks = 0
    raw_isometry_checks = 0
    for exponent in range(1, MAX_RAW_PRECISION + 1):
        modulus = 1 << exponent
        values = [z_residue(n, exponent) for n in range(modulus)]
        require(sorted(values) == list(range(modulus)),
                f"raw bijection modulo 2^{exponent}")
        raw_bijection_checks += modulus
        for first in range(modulus):
            for second in range(first):
                require(
                    valuation_two(values[first] - values[second])
                    == valuation_two(first - second),
                    f"raw isometry modulo 2^{exponent}",
                )
                raw_isometry_checks += 1

    zero_endpoint_checks = 0
    orientation_checks = 0
    for base in (0, 1, 17, 257):
        for odd_part in (1, 3, 7, 15):
            for power in range(10):
                distance = odd_part << power
                high = base + distance
                exponent = power + 7
                forward_difference = (
                    z_residue(high, exponent) - z_residue(base, exponent)
                )
                reverse_difference = -forward_difference
                expected = valuation_two(distance)
                require(valuation_two(forward_difference) == expected,
                        f"forward orientation base={base},d={distance}")
                require(valuation_two(reverse_difference) == expected,
                        f"reverse orientation base={base},d={distance}")
                orientation_checks += 2
                if base == 0:
                    zero_endpoint_checks += 2

    representative_checks = 0
    stratum_bijection_checks = 0
    stratum_isometry_checks = 0
    s_one_checks = 0
    low_bit_period_checks = 0
    for r in range(MAX_STRATUM + 1):
        step = 1 << (r + 1)
        representative = stratum_representative(r)
        matches = [
            n for n in range(step)
            if valuation_two(7 * n + 1) == r
        ]
        require(matches == [representative],
                f"explicit exact stratum representative r={r}")
        require((7 * representative + 1) % step == 1 << r,
                f"representative congruence r={r}")
        representative_checks += step + 1

        for exponent in range(1, MAX_STRATUM_PRECISION + 1):
            modulus = 1 << exponent
            period = 1 << (exponent - 1)
            units: list[int] = []
            for m in range(period):
                n = representative + step * m
                raw = z_residue(n, r + exponent)
                require(raw % (1 << r) == 0,
                        f"raw divisibility r={r},m={m}")
                units.append((raw >> r) % modulus)
            require(sorted(units) == list(range(1, modulus, 2)),
                    f"odd-unit bijection r={r},s={exponent}")
            stratum_bijection_checks += period
            if exponent == 1:
                require(period == 1 and units == [1],
                        f"s=1 singleton edge r={r}")
                s_one_checks += 1
            for first in range(period):
                for second in range(first):
                    require(
                        valuation_two(units[first] - units[second])
                        == 1 + valuation_two(first - second),
                        f"reduced-unit isometry r={r},s={exponent}",
                    )
                    stratum_isometry_checks += 1
            for m in range(min(period, 9)):
                n = representative + step * m
                shifted_n = representative + step * (m + period)
                shifted_raw = z_residue(shifted_n, r + exponent)
                require((shifted_raw >> r) % modulus == units[m],
                        f"stratum low-bit period r={r},s={exponent}")
                low_bit_period_checks += 1

    rational_recurrence_checks = 0
    selected_state_checks = 0
    reduced_fraction_checks = 0
    full_precision_checks = 0
    low_bit_actual_w_checks = 0
    for n, (odd_common, selected_numerator) in selected_endpoints().items():
        require(odd_common % 2 == 1, f"odd L_(7n) at n={n}")
        r = valuation_two(7 * n + 1)
        kappa = 27 * n - r
        require(kappa >= 1, f"positive actual precision at n={n}")

        f_value = Fraction(selected_numerator, odd_common)
        raw_selected = 5**n * selected_numerator
        full_denominator = (1 << (27 * n)) * odd_common
        require(
            Fraction(raw_selected, full_denominator)
            == Fraction(10**n * selected_numerator,
                        (1 << (28 * n)) * odd_common),
            f"10^n B_(7n)=V_n/D_n at n={n}",
        )
        rational_recurrence_checks += 1

        require(valuation_two(raw_selected) == r,
                f"exact dyadic cancellation r_n at n={n}")
        common_factor = gcd(raw_selected, full_denominator)
        reduced_top = raw_selected // common_factor
        reduced_bottom = full_denominator // common_factor
        require(valuation_two(reduced_bottom) == kappa,
                f"reduced denominator precision kappa_n at n={n}")
        reduced_odd_bottom = reduced_bottom >> kappa

        modulus = 1 << kappa
        w_from_reduced_fraction = (
            reduced_top * pow(reduced_odd_bottom, -1, modulus) % modulus
        )
        w_from_z = (
            (raw_selected >> r) * pow(odd_common, -1, modulus) % modulus
        )
        require(w_from_reduced_fraction == w_from_z,
                f"actual complete reduced coordinate at n={n}")
        reduced_fraction_checks += 1

        forward_f = FORWARD.residue(7 * n + 1, 27 * n)
        require(
            forward_f == rational_mod(f_value, 27 * n),
            f"rational F identity at full raw precision n={n}",
        )
        require(
            pow(5, n, 1 << (27 * n)) * forward_f % (1 << (27 * n))
            == rational_mod(Fraction(raw_selected, odd_common), 27 * n),
            f"raw selected state at full precision n={n}",
        )
        selected_state_checks += 1
        full_precision_checks += 2

        for low_precision in (1, 2, 3, 5, 8):
            if low_precision > kappa:
                continue
            low_modulus = 1 << low_precision
            low_from_stratum = (
                z_residue(n, r + low_precision) >> r
            ) % low_modulus
            require(low_from_stratum == w_from_z % low_modulus,
                    f"stratum unit equals low actual w bits at n={n}")
            low_bit_actual_w_checks += 1

    return {
        "status": "PASS",
        "finite_claim_label": "experiment",
        "audited_theorem_claim_label": "proof sketch",
        "maximum_raw_precision": MAX_RAW_PRECISION,
        "maximum_stratum": MAX_STRATUM,
        "maximum_stratum_precision": MAX_STRATUM_PRECISION,
        "maximum_exact_sevenfold_depth": MAX_EXACT_SEVENFOLD_DEPTH,
        "reflected_zero_checks": reflected_zero_checks,
        "recurrence_series_cross_checks": recurrence_series_cross_checks,
        "five_power_lifting_checks": lifting_checks,
        "raw_bijection_checks": raw_bijection_checks,
        "raw_isometry_checks": raw_isometry_checks,
        "zero_endpoint_checks": zero_endpoint_checks,
        "orientation_checks": orientation_checks,
        "stratum_representative_checks": representative_checks,
        "stratum_bijection_checks": stratum_bijection_checks,
        "stratum_isometry_checks": stratum_isometry_checks,
        "s_one_checks": s_one_checks,
        "low_bit_period_checks": low_bit_period_checks,
        "rational_recurrence_checks": rational_recurrence_checks,
        "selected_state_checks": selected_state_checks,
        "reduced_fraction_checks": reduced_fraction_checks,
        "full_precision_checks": full_precision_checks,
        "low_bit_actual_w_checks": low_bit_actual_w_checks,
        "asserts_moving_diagonal_mixing": False,
        "asserts_colored_return": False,
        "asserts_v1": False,
    }


if __name__ == "__main__":
    print(json.dumps(replay(), indent=2, sort_keys=True))
