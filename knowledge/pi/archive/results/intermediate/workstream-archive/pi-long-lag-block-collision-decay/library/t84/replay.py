#!/usr/bin/env python3
"""Self-contained certified finite experiment for agenda item T84.

Only Python's standard library is used.  All reported mathematical intervals
are derived from integer or Fraction arithmetic.  Floating point is not used.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import sys
import time
from fractions import Fraction
from pathlib import Path


sys.set_int_max_str_digits(0)

ITEM_ID = "T84"
T_VALUES = tuple(range(6, 17))
N_VALUES = {t: 4 * (2**t) + 1 for t in T_VALUES}
MAX_N = N_VALUES[max(T_VALUES)]
MAX_K = MAX_N - 1

# A phase window has this many certified decimal digits after shifting pi.
TURN_DIGITS = 60
TURN_DEN = 10**TURN_DIGITS
PI_CERT_DIGITS = MAX_K + TURN_DIGITS + 20
PI_SHORT_DIGITS = 70

# Integer fixed-point scale and Taylor depth.  On [0, pi/4], these give a
# deliberately loose but simple component error below BASE_COMPONENT_ERROR.
FIXED_DIGITS = 40
FIXED_ONE = 10**FIXED_DIGITS
TAYLOR_TERMS = 24
DECIMAL_OUTPUT_DIGITS = 24

RANDOM_SEEDS = (
    0x243F6A8885A308D3,
    0x13198A2E03707344,
    0xA4093822299F31D0,
)
MASK64 = (1 << 64) - 1

EXPECTED_INPUT_HASHES = {
    "CANONICAL_STATEMENT.txt": "db1a5656ab93808f9729f08a2e0cae8c7612d5d3225b41ca791f5f381d90a0c3",
}


def sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for block in iter(lambda: f.read(1 << 20), b""):
            h.update(block)
    return h.hexdigest()


def round_nearest(num: int, den: int) -> int:
    """Round num/den to nearest integer, ties away from zero."""
    assert den > 0
    if num >= 0:
        return (2 * num + den) // (2 * den)
    return -((2 * (-num) + den) // (2 * den))


def trunc_zero(num: int, den: int) -> int:
    assert den > 0
    if num >= 0:
        return num // den
    return -((-num) // den)


def decimal_lower(x: Fraction, digits: int = DECIMAL_OUTPUT_DIGITS) -> str:
    scale = 10**digits
    q = (x.numerator * scale) // x.denominator
    return scaled_integer_string(q, digits)


def decimal_upper(x: Fraction, digits: int = DECIMAL_OUTPUT_DIGITS) -> str:
    scale = 10**digits
    q = -((-x.numerator * scale) // x.denominator)
    return scaled_integer_string(q, digits)


def scaled_integer_string(q: int, digits: int) -> str:
    sign = "-" if q < 0 else ""
    s = str(abs(q)).rjust(digits + 1, "0")
    if digits == 0:
        return sign + s
    return sign + s[:-digits] + "." + s[-digits:]


def interval_json(lo: Fraction, hi: Fraction, digits: int = DECIMAL_OUTPUT_DIGITS) -> dict:
    assert lo <= hi
    return {
        "lower": decimal_lower(lo, digits),
        "upper": decimal_upper(hi, digits),
        "endpoint_digits": digits,
    }


def interval_add(a: tuple[Fraction, Fraction], b: tuple[Fraction, Fraction]):
    return a[0] + b[0], a[1] + b[1]


def interval_div_positive(
    numerator: tuple[Fraction, Fraction],
    denominator: tuple[Fraction, Fraction],
) -> tuple[Fraction, Fraction]:
    a, b = numerator
    c, d = denominator
    assert a <= b and 0 < c <= d
    values = (a / c, a / d, b / c, b / d)
    return min(values), max(values)


def bs_chudnovsky(a: int, b: int) -> tuple[int, int, int]:
    """Binary split for terms a,...,b-1 of the Chudnovsky S series."""
    c3_over_24 = 640320**3 // 24
    if b - a == 1:
        if a == 0:
            p = q = 1
        else:
            p = (6 * a - 5) * (2 * a - 1) * (6 * a - 1)
            q = a * a * a * c3_over_24
        t = p * (13591409 + 545140134 * a)
        if a & 1:
            t = -t
        return p, q, t
    m = (a + b) // 2
    p1, q1, t1 = bs_chudnovsky(a, m)
    p2, q2, t2 = bs_chudnovsky(m, b)
    return p1 * p2, q1 * q2, t1 * q2 + p1 * t2


def certified_pi_digits(decimal_digits: int) -> tuple[str, dict]:
    """Return certified common decimal digits and an inspectable certificate.

    The Chudnovsky identity is
      pi = 426880*sqrt(10005)/S,
    where S is the alternating series encoded by bs_chudnovsky.  Its positive
    term magnitudes decrease: the factorial ratio is bounded by 6^6 and the
    linear-factor ratio by (13591409+545140134)/13591409, while the denominator
    contributes 640320^3.  Consecutive partial sums therefore enclose S.
    """
    # Chudnovsky contributes just over 14 decimal digits per term.  The extra
    # terms make the exact next-term comparison comfortably stronger than the
    # requested decimal enclosure.
    terms = (decimal_digits + 43) // 14
    if terms & 1:
        terms += 1  # even: the omitted next term is positive
    p, q, t = bs_chudnovsky(0, terms)
    assert t > 0

    pn = (6 * terms - 5) * (2 * terms - 1) * (6 * terms - 1)
    qn = terms**3 * (640320**3 // 24)
    ln = 13591409 + 545140134 * terms
    next_num = p * pn * ln
    next_den = q * qn

    # Runtime verification of the global decreasing-term estimate used by the
    # alternating-series enclosure.
    assert 6**6 * (13591409 + 545140134) < 640320**3 * 13591409
    assert next_num > 0 and next_num < next_den

    # Use S < T/Q + 10^-R_DIGITS after checking the exact next-term bound.
    remainder_digits = decimal_digits + 10
    remainder_scale = 10**remainder_digits
    assert next_num * remainder_scale < next_den
    # S_low = t/q; S_high = (t*R+q)/(q*R).
    s_hi_num = t * remainder_scale + q
    s_hi_den = q * remainder_scale

    sqrt_digits = decimal_digits + 10
    sqrt_scale = 10**sqrt_digits
    sqrt_lo = math.isqrt(10005 * sqrt_scale * sqrt_scale)
    sqrt_hi = sqrt_lo + 1
    assert sqrt_lo * sqrt_lo <= 10005 * sqrt_scale * sqrt_scale
    assert sqrt_hi * sqrt_hi > 10005 * sqrt_scale * sqrt_scale

    decimal_scale = 10**decimal_digits
    # pi_low = 426880*(sqrt_lo/sqrt_scale)/(S_high)
    low_num = 426880 * sqrt_lo * s_hi_den
    low_den = sqrt_scale * s_hi_num
    # pi_high = 426880*(sqrt_hi/sqrt_scale)/(t/q)
    high_num = 426880 * sqrt_hi * q
    high_den = sqrt_scale * t
    assert low_num * high_den < high_num * low_den

    low_floor = (low_num * decimal_scale) // low_den
    high_floor = (high_num * decimal_scale) // high_den
    if low_floor != high_floor:
        raise RuntimeError("pi enclosure did not certify the requested common digits")

    full = str(low_floor).rjust(decimal_digits + 1, "0")
    assert full[0] == "3"
    fractional_digits = full[1:]
    certificate = {
        "method": "exact-integer Chudnovsky binary splitting with alternating-series remainder",
        "identity": "pi = 426880*sqrt(10005)/sum_(n>=0) (-1)^n (6n)!(13591409+545140134n)/((3n)!(n!)^3*640320^(3n))",
        "terms": terms,
        "certified_fractional_digits": decimal_digits,
        "sqrt_enclosure_scale_digits": sqrt_digits,
        "series_remainder_upper": f"1e-{remainder_digits}",
        "decimal_floor_sha256": hashlib.sha256((full + "\n").encode()).hexdigest(),
        "fractional_digits_sha256": hashlib.sha256((fractional_digits + "\n").encode()).hexdigest(),
        "decimal_enclosure": {
            "lower": f"{full[0]}.{fractional_digits}",
            "upper": f"{full[0]}.{str(low_floor + 1).rjust(decimal_digits + 1, '0')[1:]}",
            "denominator": f"10^{decimal_digits}",
        },
    }
    return fractional_digits, certificate


def fixed_sin_cos(angle_fixed: int) -> tuple[int, int]:
    """Fixed-point cosine and sine Taylor sums at angle_fixed/FIXED_ONE."""
    assert 0 <= angle_fixed <= FIXED_ONE
    a2 = angle_fixed * angle_fixed

    cos_term = FIXED_ONE
    cos_sum = cos_term
    for j in range(1, TAYLOR_TERMS + 1):
        cos_term = trunc_zero(-cos_term * a2, FIXED_ONE * FIXED_ONE * (2 * j - 1) * (2 * j))
        cos_sum += cos_term

    sin_term = angle_fixed
    sin_sum = sin_term
    for j in range(1, TAYLOR_TERMS + 1):
        sin_term = trunc_zero(-sin_term * a2, FIXED_ONE * FIXED_ONE * (2 * j) * (2 * j + 1))
        sin_sum += sin_term
    return cos_sum, sin_sum


TAYLOR_ROUNDING_ERROR = Fraction(TAYLOR_TERMS * (TAYLOR_TERMS + 1) // 2, FIXED_ONE)
TAYLOR_REMAINDER = max(
    Fraction(1, math.factorial(2 * TAYLOR_TERMS + 2)),
    Fraction(1, math.factorial(2 * TAYLOR_TERMS + 3)),
)
# The angle midpoint error is < 1/FIXED_ONE: fixed-point rounding contributes
# 1/(2*FIXED_ONE), the turn window contributes <4*10^-TURN_DIGITS, and the
# short pi interval contributes <1/(8*10^PI_SHORT_DIGITS).
ANGLE_ERROR = Fraction(1, FIXED_ONE)
assert Fraction(1, 2 * FIXED_ONE) + Fraction(4, TURN_DEN) + Fraction(1, 8 * 10**PI_SHORT_DIGITS) < ANGLE_ERROR
BASE_COMPONENT_ERROR = TAYLOR_ROUNDING_ERROR + TAYLOR_REMAINDER + ANGLE_ERROR
# Componentwise complex-power recurrence is bounded by E_(j+1)<=4E_j+4E_1.
# 4^10 E_1 safely dominates that recurrence through h=10.
POWER_COMPONENT_ERROR = 4**10 * BASE_COMPONENT_ERROR


OCTANT_TRANSFORMS = (
    (1, 0, 0, 1),    # ( c,  s)
    (0, 1, 1, 0),    # ( s,  c)
    (0, -1, 1, 0),   # (-s,  c)
    (-1, 0, 0, 1),   # (-c,  s)
    (-1, 0, 0, -1),  # (-c, -s)
    (0, -1, -1, 0),  # (-s, -c)
    (0, 1, -1, 0),   # ( s, -c)
    (1, 0, 0, -1),   # ( c, -s)
)


def base_turn_numerator(y_num: int, y_den: int, octant: int) -> int:
    """Numerator of the reflected base turn a in [0,1/8]."""
    assert y_den % 4 == 0
    if octant == 0:
        return y_num
    if octant == 1:
        return y_den // 4 - y_num
    if octant == 2:
        return y_num - y_den // 4
    if octant == 3:
        return y_den // 2 - y_num
    if octant == 4:
        return y_num - y_den // 2
    if octant == 5:
        return 3 * y_den // 4 - y_num
    if octant == 6:
        return y_num - 3 * y_den // 4
    if octant == 7:
        return y_den - y_num
    raise AssertionError("invalid octant")


def phase_from_turn_midpoint(
    y_num: int,
    y_den: int,
    octant: int,
    pi_short_floor: int,
) -> tuple[int, int]:
    """Approximate exp(2*pi*i*y) at a certified single-octant midpoint."""
    a_num = base_turn_numerator(y_num, y_den, octant)
    assert 0 <= 8 * a_num <= y_den
    pi_mid_num = 2 * pi_short_floor + 1
    pi_mid_den = 2 * 10**PI_SHORT_DIGITS
    # angle = 2*pi*a
    angle_num = 2 * pi_mid_num * a_num
    angle_den = pi_mid_den * y_den
    angle_fixed = round_nearest(angle_num * FIXED_ONE, angle_den)
    c, s = fixed_sin_cos(angle_fixed)
    ar, ai, br, bi = OCTANT_TRANSFORMS[octant]
    return ar * c + ai * s, br * c + bi * s


def complex_mul_fixed(a: tuple[int, int], b: tuple[int, int]) -> tuple[int, int]:
    real_num = a[0] * b[0] - a[1] * b[1]
    imag_num = a[0] * b[1] + a[1] * b[0]
    return round_nearest(real_num, FIXED_ONE), round_nearest(imag_num, FIXED_ONE)


def add_phase_powers(sums: list[list[int]], z: tuple[int, int]) -> None:
    power = z
    for h in range(10):
        sums[h][0] += power[0]
        sums[h][1] += power[1]
        if h != 9:
            power = complex_mul_fixed(power, z)


def x_interval(sum_pair: tuple[int, int] | list[int], n: int) -> tuple[Fraction, Fraction]:
    component_error = n * POWER_COMPONENT_ERROR
    abs_r = Fraction(abs(sum_pair[0]), FIXED_ONE)
    abs_i = Fraction(abs(sum_pair[1]), FIXED_ONE)
    r_lo = max(Fraction(0), abs_r - component_error)
    i_lo = max(Fraction(0), abs_i - component_error)
    r_hi = abs_r + component_error
    i_hi = abs_i + component_error
    lo = r_lo * r_lo + i_lo * i_lo
    hi = r_hi * r_hi + i_hi * i_hi
    return max(Fraction(0), lo), min(Fraction(n * n), hi)


def convex_t63_term_range(xlo: Fraction, xhi: Fraction, n: int) -> tuple[Fraction, Fraction]:
    """Exact range of x^2-4(n-1)x+2n^2-3n on [xlo,xhi]."""
    def p(x: Fraction) -> Fraction:
        return x * x - 4 * (n - 1) * x + 2 * n * n - 3 * n

    critical = Fraction(2 * (n - 1))
    xmin = min(max(critical, xlo), xhi)
    return p(xmin), max(p(xlo), p(xhi))


def sqrt_integer_interval(value: int, digits: int = 50) -> tuple[Fraction, Fraction]:
    scale = 10**digits
    root = math.isqrt(value * scale * scale)
    assert root * root <= value * scale * scale < (root + 1) * (root + 1)
    return Fraction(root, scale), Fraction(root + 1, scale)


def summarize_checkpoint(sums: list[list[int]], n: int) -> tuple[dict, tuple[Fraction, Fraction]]:
    xs = [x_interval(pair, n) for pair in sums]
    f_interval = (
        sum((lo * lo for lo, _ in xs), Fraction(0)),
        sum((hi * hi for _, hi in xs), Fraction(0)),
    )
    g_interval = (
        sum((lo for lo, _ in xs), Fraction(0)),
        sum((hi for _, hi in xs), Fraction(0)),
    )
    linear_interval = (
        -4 * (n - 1) * g_interval[1],
        -4 * (n - 1) * g_interval[0],
    )
    lower_order = Fraction(20 * n * n - 30 * n)
    term_ranges = [convex_t63_term_range(lo, hi, n) for lo, hi in xs]
    numerator = (
        sum((lo for lo, _ in term_ranges), Fraction(0)),
        sum((hi for _, hi in term_ranges), Fraction(0)),
    )
    width = sqrt_integer_interval(n * n - 1)
    contribution = interval_div_positive(numerator, width)
    positive_representative = contribution[0] / 2, contribution[1] / 2

    benchmarks = {}
    rational_r_values = {
        "s=log_10(2)": Fraction(1, 2),
        "s=log_10(5)": Fraction(1, 5),
    }
    for label, r in rational_r_values.items():
        target = Fraction(10) * (n + n * n * r)
        benchmarks[label] = {
            "ten_pow_minus_s": f"{r.numerator}/{r.denominator}",
            "target": interval_json(target, target),
            "two_orientation_ratio": interval_json(contribution[0] / target, contribution[1] / target),
        }

    sqrt10 = sqrt_integer_interval(10, 60)
    invsqrt10 = Fraction(1, 1) / sqrt10[1], Fraction(1, 1) / sqrt10[0]
    half_target = (
        10 * (n + n * n * invsqrt10[0]),
        10 * (n + n * n * invsqrt10[1]),
    )
    benchmarks["s=1/2"] = {
        "ten_pow_minus_s": interval_json(*invsqrt10),
        "target": interval_json(*half_target),
        "two_orientation_ratio": interval_json(*interval_div_positive(contribution, half_target)),
    }

    record = {
        "N": n,
        "X_h_intervals": {str(h + 1): interval_json(*xs[h]) for h in range(10)},
        "F=sum_X_h_squared": interval_json(*f_interval),
        "sum_X_h": interval_json(*g_interval),
        "T63_components": {
            "fourth_moment_F": interval_json(*f_interval),
            "linear_minus_4_N_minus_1_sum_X": interval_json(*linear_interval),
            "lower_order_20_N_squared_minus_30_N": interval_json(lower_order, lower_order),
            "convex_dependency_aware_numerator": interval_json(*numerator),
            "literal_per_h_polynomial": "X_h^2 - 4*(N-1)*X_h + 2*N^2 - 3*N",
        },
        "width_sqrt_N_squared_minus_1": interval_json(*width, digits=30),
        "two_orientation_selected_plus_defect_contribution": interval_json(*contribution),
        "positive_representative_C_contribution": interval_json(*positive_representative),
        "T29_m_equals_1_normalization": {
            "parameterized_target": "10*(N + N^2*10^(-s)), 0<s<1",
            "parameterized_ratio": "two_orientation_selected_plus_defect_contribution / (10*(N + N^2*10^(-s)))",
            "benchmarks": benchmarks,
        },
    }
    return record, f_interval


class XorShift64Star:
    def __init__(self, seed: int):
        assert 0 < seed <= MASK64
        self.state = seed

    def next_u64(self) -> int:
        x = self.state
        x ^= x >> 12
        x ^= (x << 25) & MASK64
        x ^= x >> 27
        self.state = x & MASK64
        return (self.state * 0x2545F4914F6CDD1D) & MASK64


def pi_phase_stream(digits: str, pi_short_floor: int):
    assert len(digits) >= MAX_K + TURN_DIGITS
    window = int(digits[:TURN_DIGITS])
    tail_scale = 10 ** (TURN_DIGITS - 1)
    for k in range(MAX_N):
        # The true turn lies in [window/10^M,(window+1)/10^M).  Certify that
        # this entire half-open interval has one octant before reducing it.
        oct_lo = (8 * window) // TURN_DEN
        oct_hi = (8 * (window + 1) - 1) // TURN_DEN
        if oct_lo != oct_hi:
            raise RuntimeError(f"phase interval crosses an octant boundary at k={k}")
        y_mid_num = 2 * window + 1
        y_mid_den = 2 * TURN_DEN
        yield phase_from_turn_midpoint(y_mid_num, y_mid_den, oct_lo, pi_short_floor)
        if k + 1 < MAX_N:
            next_digit = ord(digits[k + TURN_DIGITS]) - 48
            assert 0 <= next_digit <= 9
            window = (window % tail_scale) * 10 + next_digit


def random_phase_stream(seed: int, pi_short_floor: int):
    rng = XorShift64Star(seed)
    den = 1 << 64
    for _ in range(MAX_N):
        y = rng.next_u64()
        octant = (8 * y) // den
        yield phase_from_turn_midpoint(y, den, octant, pi_short_floor)


def run_stream(stream, include_full_records: bool) -> tuple[dict, dict]:
    sums = [[0, 0] for _ in range(10)]
    checkpoints_by_n = {n: t for t, n in N_VALUES.items()}
    records = {}
    compact = {}
    for count, z in enumerate(stream, start=1):
        add_phase_powers(sums, z)
        if count in checkpoints_by_n:
            t = checkpoints_by_n[count]
            record, f_interval = summarize_checkpoint(sums, count)
            if include_full_records:
                records[str(t)] = record
            compact[str(t)] = {
                "N": count,
                "F_over_N_squared": interval_json(
                    f_interval[0] / (count * count),
                    f_interval[1] / (count * count),
                ),
            }
    assert count == MAX_N
    return records, compact


def build_results(pi_digits: str, pi_certificate: dict) -> dict:
    pi_short_floor = int("3" + pi_digits[:PI_SHORT_DIGITS])
    fixed_records, fixed_compact = run_stream(
        pi_phase_stream(pi_digits, pi_short_floor), include_full_records=True
    )
    controls = []
    for seed in RANDOM_SEEDS:
        _, compact = run_stream(random_phase_stream(seed, pi_short_floor), include_full_records=False)
        controls.append({
            "seed_hex": f"0x{seed:016x}",
            "generator": "xorshift64* with multiplier 0x2545F4914F6CDD1D",
            "interpretation": "heuristic random-phase control only",
            "scales": compact,
        })

    return {
        "schema": "t84-certified-experiment-v1",
        "item_id": ITEM_ID,
        "classification": "experiment",
        "canonical_statement_sha256": EXPECTED_INPUT_HASHES["CANONICAL_STATEMENT.txt"],
        "domains": {
            "t": "integers 6 through 16 inclusive",
            "N_t": "4*2^t+1",
            "h": "integers 1 through 10 inclusive",
            "k": "integers 0 through N_t-1 inclusive",
        },
        "phase": "exp(2*pi*i*h*10^k*pi)",
        "pi_certificate": pi_certificate,
        "arithmetic_certificate": {
            "method": "integer fixed-point Taylor approximation plus explicit rational error bounds",
            "floating_point_used": False,
            "turn_window_decimal_digits": TURN_DIGITS,
            "fixed_point_decimal_digits": FIXED_DIGITS,
            "taylor_terms_after_constant_or_linear_term": TAYLOR_TERMS,
            "base_component_error_upper": decimal_upper(BASE_COMPONENT_ERROR, 45),
            "power_component_error_upper_h_le_10": decimal_upper(POWER_COMPONENT_ERROR, 45),
            "octant_check": "every pi turn interval is required to lie in one rational eighth-turn interval",
        },
        "fixed_pi_scales": fixed_records,
        "fixed_pi_compact_F_over_N_squared": fixed_compact,
        "random_phase_controls": controls,
        "claim_limits": [
            "All fixed-pi and random-phase values are finite-scale experiment results.",
            "The random-phase controls are heuristic evidence only.",
            "These computations neither prove nor refute C2.",
            "These computations neither prove nor refute G10.",
            "These computations neither prove nor refute C1.",
            "These computations neither prove nor refute C3.",
            "The signed T63 selected-plus-defect contribution is not the full nonnegative T29 square function.",
        ],
    }


def verify_manifest(base: Path) -> None:
    manifest = base / "SHA256SUMS"
    if not manifest.exists():
        return
    for line in manifest.read_text(encoding="ascii").splitlines():
        digest, name = line.split("  ", 1)
        actual = sha256_file(base / name)
        if actual != digest:
            raise RuntimeError(f"SHA-256 mismatch for {name}: {actual} != {digest}")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--generate", action="store_true", help="write pi_digits.txt, pi_certificate.json, and results.json")
    parser.add_argument("--verify", action="store_true", help="recompute and compare all certificates/results")
    parser.add_argument("--quick", action="store_true", help="verify only hashes and the stored pi digit-file hash")
    args = parser.parse_args()
    if sum((args.generate, args.verify, args.quick)) != 1:
        parser.error("choose exactly one of --generate, --verify, or --quick")

    base = Path(__file__).resolve().parent
    start = time.monotonic()
    for name, expected in EXPECTED_INPUT_HASHES.items():
        actual = sha256_file(base / name)
        if actual != expected:
            raise RuntimeError(f"pinned input mismatch for {name}: {actual} != {expected}")

    if args.quick:
        verify_manifest(base)
        cert = json.loads((base / "pi_certificate.json").read_text(encoding="ascii"))
        actual = sha256_file(base / "pi_digits.txt")
        expected = cert["fractional_digits_sha256"]
        if actual != expected:
            raise RuntimeError(f"pi digit-file mismatch: {actual} != {expected}")
        print(f"quick verification passed in {time.monotonic() - start:.2f}s")
        return 0

    pi_digits, pi_certificate = certified_pi_digits(PI_CERT_DIGITS)
    if args.generate:
        (base / "pi_digits.txt").write_text(pi_digits + "\n", encoding="ascii")
        (base / "pi_certificate.json").write_text(
            json.dumps(pi_certificate, indent=2, sort_keys=True) + "\n", encoding="ascii"
        )
    else:
        stored_digits = (base / "pi_digits.txt").read_text(encoding="ascii").strip()
        stored_certificate = json.loads((base / "pi_certificate.json").read_text(encoding="ascii"))
        if stored_digits != pi_digits or stored_certificate != pi_certificate:
            raise RuntimeError("stored pi certificate differs from exact regeneration")

    results = build_results(pi_digits, pi_certificate)
    encoded = json.dumps(results, indent=2, sort_keys=True) + "\n"
    if args.generate:
        (base / "results.json").write_text(encoded, encoding="ascii")
    else:
        verify_manifest(base)
        stored = (base / "results.json").read_text(encoding="ascii")
        if stored != encoded:
            raise RuntimeError("stored results differ from certified regeneration")

    elapsed = time.monotonic() - start
    print(f"{args.generate and 'generation' or 'full verification'} passed in {elapsed:.2f}s")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
