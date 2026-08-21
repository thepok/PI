#!/usr/bin/env python3
"""Self-contained replay-certified finite experiment for agenda item T85.

All reported enclosures use integers and fractions. Python floating point is
used only for elapsed-time messages, never for a mathematical result.
"""

from __future__ import annotations

import argparse
import hashlib
import heapq
import json
import math
import sys
import time
from fractions import Fraction
from pathlib import Path


sys.set_int_max_str_digits(0)

ITEM_ID = "T85"
CASES = tuple([(1, 4 * 2**t + 1, t) for t in range(6, 17)] + [
    (2, 11, None), (3, 33, None), (4, 101, None), (5, 317, None),
])
MAX_N = max(n for _, n, _ in CASES)
MAX_K = MAX_N - 1
MAX_H = max(10**m for m, _, _ in CASES)

TURN_DIGITS = 60
TURN_DEN = 10**TURN_DIGITS
PI_CERT_DIGITS = MAX_K + TURN_DIGITS + 20
PI_SHORT_DIGITS = 70
FIXED_DIGITS = 40
FIXED_ONE = 10**FIXED_DIGITS
FIXED_SQUARED = FIXED_ONE**2
TAYLOR_TERMS = 24
DECIMAL_OUTPUT_DIGITS = 18
WIDTH_DIGITS = 50

EXPECTED_INPUT_HASHES = {
    "CANONICAL_STATEMENT.txt": "db1a5656ab93808f9729f08a2e0cae8c7612d5d3225b41ca791f5f381d90a0c3",
    "T22SparseFrequencyCutoff.lean": "73b49990d59e2c446b121eee977a04b9bbb4806f7c47be01c384acb8bf7d1713",
    "T29WidthWeightedSquareFunction.lean": "2f18966e04e00eb657d4a517d31281f9e8eafae4a6365bcf0985b94711e1e358",
    "T49PrimitiveIncidenceAssembly.lean": "65776873b77b51df5639e7546db7319f14ce4b76259d3faa19732744e6e13cdb",
    "T59CompleteSignedPrimitivePartition.lean": "efe26ea7141201081bcaa32d33dfb71688e643ea1a4630ff7beeaf69e47b765c",
    "T63ExactFiniteFourthMoment.lean": "33521ed540153b2483b60d37edea6dd9b250dd304b56b4712d40e132e10ace8e",
    "pi_digits.txt": "3b6fd90e0f3d985de4788cd65318469460ef25379f5ed220aa2ae84172e9bc0c",
    "pi_certificate.json": "0af329268f6120f59edd8d1b8f6bc6a33faabd3d9b94d820df6105adfc85c0a8",
}

Interval = tuple[Fraction, Fraction]
ZERO_INTERVAL: Interval = (Fraction(0), Fraction(0))


def sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for block in iter(lambda: f.read(1 << 20), b""):
            h.update(block)
    return h.hexdigest()


def scaled_integer_string(q: int, digits: int) -> str:
    sign = "-" if q < 0 else ""
    s = str(abs(q)).rjust(digits + 1, "0")
    return sign + (s if digits == 0 else s[:-digits] + "." + s[-digits:])


def decimal_lower(x: Fraction, digits: int = DECIMAL_OUTPUT_DIGITS) -> str:
    scale = 10**digits
    return scaled_integer_string((x.numerator * scale) // x.denominator, digits)


def decimal_upper(x: Fraction, digits: int = DECIMAL_OUTPUT_DIGITS) -> str:
    scale = 10**digits
    return scaled_integer_string(-((-x.numerator * scale) // x.denominator), digits)


def decimal_fraction(s: str) -> Fraction:
    sign = -1 if s.startswith("-") else 1
    text = s[1:] if sign < 0 else s
    whole, frac = text.split(".")
    return sign * Fraction(int(whole + frac), 10 ** len(frac))


def interval_json(lo: Fraction, hi: Fraction, digits: int = DECIMAL_OUTPUT_DIGITS) -> dict:
    assert lo <= hi
    result = {
        "lower": decimal_lower(lo, digits),
        "upper": decimal_upper(hi, digits),
        "endpoint_digits": digits,
    }
    assert decimal_fraction(result["lower"]) <= lo <= hi <= decimal_fraction(result["upper"])
    return result


def iadd(a: Interval, b: Interval) -> Interval:
    return a[0] + b[0], a[1] + b[1]


def isub(a: Interval, b: Interval) -> Interval:
    return a[0] - b[1], a[1] - b[0]


def imul(a: Interval, b: Interval) -> Interval:
    values = (a[0] * b[0], a[0] * b[1], a[1] * b[0], a[1] * b[1])
    return min(values), max(values)


def iscale(a: Interval, c: Fraction) -> Interval:
    return (a[0] * c, a[1] * c) if c >= 0 else (a[1] * c, a[0] * c)


def idiv_positive(a: Interval, b: Interval) -> Interval:
    assert 0 < b[0] <= b[1]
    values = (a[0] / b[0], a[0] / b[1], a[1] / b[0], a[1] / b[1])
    return min(values), max(values)


def iintersect(a: Interval, b: Interval) -> Interval:
    result = max(a[0], b[0]), min(a[1], b[1])
    if result[0] > result[1]:
        raise RuntimeError(f"disjoint certified intervals: {a} and {b}")
    return result


def icontains(outer: Interval, inner: Interval) -> bool:
    return outer[0] <= inner[0] and inner[1] <= outer[1]


def square_real_interval(center: Fraction, error: Fraction) -> Interval:
    assert error >= 0
    lo, hi = center - error, center + error
    minimum = Fraction(0) if lo <= 0 <= hi else min(lo * lo, hi * hi)
    return minimum, max(lo * lo, hi * hi)


def norm_sq_rect(re: Fraction, im: Fraction, error: Fraction) -> Interval:
    return iadd(square_real_interval(re, error), square_real_interval(im, error))


def sqrt_integer_interval(value: int, digits: int = WIDTH_DIGITS) -> Interval:
    scale = 10**digits
    root = math.isqrt(value * scale * scale)
    assert root * root <= value * scale * scale < (root + 1) * (root + 1)
    return Fraction(root, scale), Fraction(root + 1, scale)


def round_nearest(num: int, den: int) -> int:
    assert den > 0
    if num >= 0:
        return (2 * num + den) // (2 * den)
    return -((2 * (-num) + den) // (2 * den))


def trunc_zero(num: int, den: int) -> int:
    assert den > 0
    return num // den if num >= 0 else -((-num) // den)


def bs_chudnovsky(a: int, b: int) -> tuple[int, int, int]:
    c3_over_24 = 640320**3 // 24
    if b - a == 1:
        if a == 0:
            p = q = 1
        else:
            p = (6 * a - 5) * (2 * a - 1) * (6 * a - 1)
            q = a**3 * c3_over_24
        t = p * (13591409 + 545140134 * a)
        return p, q, -t if a & 1 else t
    m = (a + b) // 2
    p1, q1, t1 = bs_chudnovsky(a, m)
    p2, q2, t2 = bs_chudnovsky(m, b)
    return p1 * p2, q1 * q2, t1 * q2 + p1 * t2


def certified_pi_digits(decimal_digits: int) -> tuple[str, dict]:
    terms = (decimal_digits + 43) // 14
    if terms & 1:
        terms += 1
    p, q, t = bs_chudnovsky(0, terms)
    assert t > 0
    pn = (6 * terms - 5) * (2 * terms - 1) * (6 * terms - 1)
    qn = terms**3 * (640320**3 // 24)
    ln = 13591409 + 545140134 * terms
    next_num, next_den = p * pn * ln, q * qn
    assert 6**6 * (13591409 + 545140134) < 640320**3 * 13591409
    assert 0 < next_num < next_den
    remainder_digits = decimal_digits + 10
    remainder_scale = 10**remainder_digits
    assert next_num * remainder_scale < next_den
    s_hi_num, s_hi_den = t * remainder_scale + q, q * remainder_scale
    sqrt_digits = decimal_digits + 10
    sqrt_scale = 10**sqrt_digits
    sqrt_lo = math.isqrt(10005 * sqrt_scale * sqrt_scale)
    sqrt_hi = sqrt_lo + 1
    assert sqrt_lo**2 <= 10005 * sqrt_scale**2 < sqrt_hi**2
    low_num = 426880 * sqrt_lo * s_hi_den
    low_den = sqrt_scale * s_hi_num
    high_num = 426880 * sqrt_hi * q
    high_den = sqrt_scale * t
    decimal_scale = 10**decimal_digits
    low_floor = low_num * decimal_scale // low_den
    high_floor = high_num * decimal_scale // high_den
    if low_floor != high_floor:
        raise RuntimeError("pi enclosure did not certify the requested digits")
    full = str(low_floor).rjust(decimal_digits + 1, "0")
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
    assert 0 <= angle_fixed <= FIXED_ONE
    a2 = angle_fixed * angle_fixed
    cos_term = cos_sum = FIXED_ONE
    for j in range(1, TAYLOR_TERMS + 1):
        cos_term = trunc_zero(-cos_term * a2, FIXED_SQUARED * (2 * j - 1) * (2 * j))
        cos_sum += cos_term
    sin_term = sin_sum = angle_fixed
    for j in range(1, TAYLOR_TERMS + 1):
        sin_term = trunc_zero(-sin_term * a2, FIXED_SQUARED * (2 * j) * (2 * j + 1))
        sin_sum += sin_term
    return cos_sum, sin_sum


TAYLOR_ROUNDING_ERROR = Fraction(TAYLOR_TERMS * (TAYLOR_TERMS + 1) // 2, FIXED_ONE)
TAYLOR_REMAINDER = max(
    Fraction(1, math.factorial(2 * TAYLOR_TERMS + 2)),
    Fraction(1, math.factorial(2 * TAYLOR_TERMS + 3)),
)
ANGLE_ERROR = Fraction(1, FIXED_ONE)
assert (
    Fraction(1, 2 * FIXED_ONE)
    + Fraction(4, TURN_DEN)
    + Fraction(1, 8 * 10**PI_SHORT_DIGITS)
    < ANGLE_ERROR
)
BASE_COMPONENT_ERROR = TAYLOR_ROUNDING_ERROR + TAYLOR_REMAINDER + ANGLE_ERROR
BASE_VECTOR_ERROR = 2 * BASE_COMPONENT_ERROR
MULTIPLICATION_VECTOR_ROUNDING = Fraction(1, FIXED_ONE)

OCTANT_TRANSFORMS = (
    (1, 0, 0, 1), (0, 1, 1, 0), (0, -1, 1, 0), (-1, 0, 0, 1),
    (-1, 0, 0, -1), (0, -1, -1, 0), (0, 1, -1, 0), (1, 0, 0, -1),
)


def base_turn_numerator(y_num: int, y_den: int, octant: int) -> int:
    values = (
        y_num, y_den // 4 - y_num, y_num - y_den // 4,
        y_den // 2 - y_num, y_num - y_den // 2,
        3 * y_den // 4 - y_num, y_num - 3 * y_den // 4, y_den - y_num,
    )
    return values[octant]


def phase_from_turn_midpoint(y_num: int, y_den: int, octant: int, pi_short_floor: int) -> tuple[int, int]:
    a_num = base_turn_numerator(y_num, y_den, octant)
    assert 0 <= 8 * a_num <= y_den
    pi_mid_num = 2 * pi_short_floor + 1
    pi_mid_den = 2 * 10**PI_SHORT_DIGITS
    angle_fixed = round_nearest(2 * pi_mid_num * a_num * FIXED_ONE, pi_mid_den * y_den)
    c, s = fixed_sin_cos(angle_fixed)
    ar, ai, br, bi = OCTANT_TRANSFORMS[octant]
    return ar * c + ai * s, br * c + bi * s


def complex_mul_fixed(a: tuple[int, int], b: tuple[int, int]) -> tuple[int, int]:
    return (
        round_nearest(a[0] * b[0] - a[1] * b[1], FIXED_ONE),
        round_nearest(a[0] * b[1] + a[1] * b[0], FIXED_ONE),
    )


def power_error(h: int) -> Fraction:
    eta = BASE_VECTOR_ERROR + MULTIPLICATION_VECTOR_ROUNDING
    denominator = 1 - h * BASE_VECTOR_ERROR
    assert h >= 1 and denominator > 0
    bound = h * eta / denominator
    if h > 1:
        previous = (h - 1) * eta / (1 - (h - 1) * BASE_VECTOR_ERROR)
        assert bound >= (1 + BASE_VECTOR_ERROR) * previous + eta
    return bound


def pi_phase_table(digits: str, pi_short_floor: int, n: int) -> list[tuple[int, int]]:
    assert len(digits) >= n - 1 + TURN_DIGITS
    result = []
    window = int(digits[:TURN_DIGITS])
    tail_scale = 10 ** (TURN_DIGITS - 1)
    for k in range(n):
        oct_lo = 8 * window // TURN_DEN
        oct_hi = (8 * (window + 1) - 1) // TURN_DEN
        if oct_lo != oct_hi:
            raise RuntimeError(f"pi phase interval crosses an octant boundary at k={k}")
        result.append(phase_from_turn_midpoint(2 * window + 1, 2 * TURN_DEN, oct_lo, pi_short_floor))
        if k + 1 < n:
            next_digit = ord(digits[k + TURN_DIGITS]) - 48
            assert 0 <= next_digit <= 9
            window = (window % tail_scale) * 10 + next_digit
    return result


def canonical_blocks(n: int) -> list[tuple[int, int]]:
    start = 1
    blocks = []
    for level in range((n - 1).bit_length() - 1, -1, -1):
        if (n - 1) >> level & 1:
            finish = start + 2**level
            blocks.append((start, finish))
            start = finish
    assert start == n
    return blocks


def verify_canonical_blocks() -> None:
    for n in range(1, 513):
        blocks = canonical_blocks(n)
        cursor = 1
        levels = []
        for a, b in blocks:
            width = b - a
            assert a == cursor and width > 0 and width & (width - 1) == 0
            level = width.bit_length() - 1
            assert (a - 1) % width == 0
            levels.append(level)
            cursor = b
        assert cursor == n and all(x > y for x, y in zip(levels, levels[1:]))


def record_count(m: int, block: tuple[int, int]) -> int:
    a, b = block
    return 2 * sum(e - m + 1 for e in range(max(a, m), b))


def endpoint_bins(block: tuple[int, int], maximum: int = 16) -> list[tuple[int, int]]:
    a, b = block
    count = min(maximum, b - a)
    return [(a + i * (b - a) // count, a + (i + 1) * (b - a) // count) for i in range(count)]


def frequency_bin_label(h: int) -> str:
    lo = 1
    while lo * 10 <= h:
        lo *= 10
    return f"{lo}-{10 * lo - 1}"


def exclusion_impossible_audit(m: int) -> dict:
    assert 1 <= m <= 5
    q_min = 10**m - 1
    assert q_min**7 > 10**m
    return {
        "m": m,
        "minimum_structured_denominator": q_min,
        "minimum_denominator_power_7": q_min**7,
        "ten_power_m": 10**m,
        "verified_strict_inequality": "(10^m-1)^7 > 10^m",
        "conclusion": "ArithmeticExcluded(8,1,Q0,m,n,r) is false for every Q0 and every r>=m,n>=0",
    }


def convex_t63_range(x: Interval, n: int) -> Interval:
    def p(y: Fraction) -> Fraction:
        return y * y - 4 * (n - 1) * y + 2 * n * n - 3 * n
    critical = Fraction(2 * (n - 1))
    xmin = min(max(critical, x[0]), x[1])
    return p(xmin), max(p(x[0]), p(x[1]))


def target_half_interval(m: int, n: int) -> Interval:
    if m % 2 == 0:
        decay = (Fraction(10) ** (-(m // 2)),) * 2
    else:
        sqrt10 = sqrt_integer_interval(10, 70)
        invsqrt10 = (1 / sqrt10[1], 1 / sqrt10[0])
        decay = iscale(invsqrt10, Fraction(10) ** (-((m - 1) // 2)))
    return iscale(iadd((Fraction(n), Fraction(n)), iscale(decay, Fraction(n * n))), Fraction(10**m))


def row_cancelling_stats(
    powers: list[tuple[int, int]], m: int, block: tuple[int, int]
) -> tuple[int, int, int, int]:
    a, b = block
    pre_re = [0]
    pre_im = [0]
    for re, im in powers[:b]:
        pre_re.append(pre_re[-1] + re)
        pre_im.append(pre_im[-1] + im)
    r_num = 0
    weighted_l1 = 0
    degree_sq = 0
    degree_sum = 0
    for i in range(b):
        low_count = i - m + 1 if a <= i < b and i >= m else 0
        low_re = pre_re[low_count] if low_count else 0
        low_im = pre_im[low_count] if low_count else 0
        high_start = max(a, i + m)
        high_count = b - high_start if high_start < b else 0
        high_re = pre_re[b] - pre_re[high_start] if high_count else 0
        high_im = pre_im[b] - pre_im[high_start] if high_count else 0
        degree = low_count + high_count
        qre, qim = low_re + high_re, low_im + high_im
        r_num += qre * qre + qim * qim
        weighted_l1 += degree * (abs(qre) + abs(qim))
        degree_sq += degree * degree
        degree_sum += degree
    assert degree_sum == record_count(m, block)
    return r_num, weighted_l1, degree_sq, degree_sum


def evaluate_case(
    m: int, n: int, t: int | None, base_phases: list[tuple[int, int]]
) -> tuple[dict, int]:
    h_max = 10**m
    blocks = canonical_blocks(n)
    widths = [sqrt_integer_interval(b * b - a * a) for a, b in blocks]
    counts = [record_count(m, block) for block in blocks]
    powers = list(base_phases[:n])
    common_error = power_error(h_max)
    direct_square_num = [0 for _ in blocks]
    direct_abs_num = [0 for _ in blocks]
    cancelling_square_num = [0 for _ in blocks]
    cancelling_weighted_l1 = [0 for _ in blocks]
    cancelling_degree_sq = [0 for _ in blocks]
    endpoint_ranges = [endpoint_bins(block) for block in blocks]
    endpoint_product_num = [[0 for _ in bins] for bins in endpoint_ranges]
    endpoint_abs_u_num = [[0 for _ in bins] for bins in endpoint_ranges]
    endpoint_abs_v_num = [[0 for _ in bins] for bins in endpoint_ranges]
    frequency_bins: dict[str, Interval] = {}
    top_frequencies: list[tuple[Fraction, int, Interval]] = []
    t63_primitive = ZERO_INTERVAL
    t63_cancelling = ZERO_INTERVAL
    t63_direct = ZERO_INTERVAL
    t63_x = {}

    for h in range(1, h_max + 1):
        error = common_error
        prefix_re = prefix_im = 0
        layers = [0] * n
        for e in range(n):
            if e >= m:
                add_re, add_im = powers[e - m]
                prefix_re += add_re
                prefix_im += add_im
                re, im = powers[e]
                layers[e] = 2 * (re * prefix_re + im * prefix_im)

        frequency_total = ZERO_INTERVAL
        for bi, ((a, b), width, count) in enumerate(zip(blocks, widths, counts)):
            v_num = sum(layers[a:b])
            v_center = Fraction(v_num, FIXED_SQUARED)
            v_error = count * error * (2 + error)
            energy = square_real_interval(v_center, v_error)
            direct_square_num[bi] += v_num * v_num
            direct_abs_num[bi] += abs(v_num)
            frequency_total = iadd(frequency_total, idiv_positive(energy, width))

            r_num, weighted_l1, degree_sq, degree_sum = row_cancelling_stats(powers, m, (a, b))
            assert degree_sum == count
            cancelling_square_num[bi] += r_num
            cancelling_weighted_l1[bi] += weighted_l1
            cancelling_degree_sq[bi] = degree_sq

            for ei, (u, v) in enumerate(endpoint_ranges[bi]):
                u_count = record_count(m, (u, v))
                u_num = sum(layers[u:v])
                endpoint_product_num[bi][ei] += u_num * v_num
                endpoint_abs_u_num[bi][ei] += abs(u_num)
                endpoint_abs_v_num[bi][ei] += abs(v_num)

        label = frequency_bin_label(h)
        frequency_bins[label] = iadd(frequency_bins.get(label, ZERO_INTERVAL), frequency_total)
        candidate = (frequency_total[1], -h, frequency_total)
        if len(top_frequencies) < 20:
            heapq.heappush(top_frequencies, candidate)
        elif candidate[:2] > top_frequencies[0][:2]:
            heapq.heapreplace(top_frequencies, candidate)

        if m == 1:
            orbit_re = Fraction(sum(re for re, _ in powers), FIXED_ONE)
            orbit_im = Fraction(sum(im for _, im in powers), FIXED_ONE)
            x = norm_sq_rect(orbit_re, orbit_im, n * error)
            t63_x[str(h)] = interval_json(*x)
            t63_primitive = iadd(t63_primitive, convex_t63_range(x, n))
            t63_cancelling = iadd(
                t63_cancelling,
                iscale(isub(x, (Fraction(n), Fraction(n))), Fraction(2 * (n - 2))),
            )
            t63_direct = iadd(t63_direct, square_real_interval(
                (x[0] + x[1]) / 2 - n, (x[1] - x[0]) / 2
            ))

        if h != h_max:
            powers = [complex_mul_fixed(powers[k], base_phases[k]) for k in range(n)]

    direct = ZERO_INTERVAL
    cancelling = ZERO_INTERVAL
    mean = ZERO_INTERVAL
    primitive = ZERO_INTERVAL
    block_records = []
    for bi, ((a, b), width, count) in enumerate(zip(blocks, widths, counts)):
        v_error = count * common_error * (2 + common_error)
        direct_center = Fraction(direct_square_num[bi], FIXED_SQUARED**2)
        direct_radius = (
            2 * v_error * Fraction(direct_abs_num[bi], FIXED_SQUARED)
            + h_max * v_error * v_error
        )
        direct_numerator = (max(Fraction(0), direct_center - direct_radius), direct_center + direct_radius)
        cancel_center = Fraction(cancelling_square_num[bi], FIXED_SQUARED)
        cancel_radius = (
            2 * common_error * Fraction(cancelling_weighted_l1[bi], FIXED_ONE)
            + common_error * common_error * h_max * cancelling_degree_sq[bi]
        )
        cancel_rows = (cancel_center - cancel_radius, cancel_center + cancel_radius)
        cancel_numerator = iscale(
            isub(cancel_rows, (Fraction(h_max * count), Fraction(h_max * count))), Fraction(2)
        )
        direct_part = idiv_positive(direct_numerator, width)
        cancel_part = idiv_positive(cancel_numerator, width)
        mean_part = idiv_positive((Fraction(h_max * count), Fraction(h_max * count)), width)
        primitive_part = isub(isub(direct_part, mean_part), cancel_part)
        direct = iadd(direct, direct_part)
        cancelling = iadd(cancelling, cancel_part)
        mean = iadd(mean, mean_part)
        primitive = iadd(primitive, primitive_part)
        block_records.append({
            "block": f"[{a},{b})",
            "length": b - a,
            "oriented_record_count": count,
            "literal_width_sqrt_b2_minus_a2": interval_json(*width, digits=30),
            "direct_contribution": interval_json(*direct_part),
        })

    frequency_sum_certified = ZERO_INTERVAL
    for value in frequency_bins.values():
        frequency_sum_certified = iadd(frequency_sum_certified, value)
    direct = iintersect(direct, frequency_sum_certified)

    reconciliation = {
        "sector_identity": "direct = record_diagonal_mean + primitive_nonattacking + cancelling_shared_coordinate",
    }
    if m == 1:
        one_width = widths[0]
        t63_primitive_q = idiv_positive(t63_primitive, one_width)
        t63_cancelling_q = idiv_positive(t63_cancelling, one_width)
        t63_direct_q = idiv_positive(t63_direct, one_width)
        primitive = iintersect(primitive, t63_primitive_q)
        cancelling = iintersect(cancelling, t63_cancelling_q)
        direct = iintersect(direct, t63_direct_q)
        reconciliation.update({
            "T63_literal_per_frequency_polynomial": "X_h^2 - 4*(N-1)*X_h + 2*N^2 - 3*N",
            "T63_selected_plus_defect_primitive": interval_json(*t63_primitive_q),
            "independent_T63_cancelling_complement": interval_json(*t63_cancelling_q),
            "independent_T63_direct": interval_json(*t63_direct_q),
            "X_h_intervals": t63_x,
            "all_three_intersections_verified_nonempty": True,
        })

    recombined = iadd(iadd(mean, primitive), cancelling)
    if not icontains(recombined, direct):
        raise RuntimeError(f"sector recombination does not enclose direct value for {(m, n)}")

    target = target_half_interval(m, n)
    ratio = idiv_positive(direct, target)
    difference = isub(direct, target)
    if ratio[0] > 1:
        relation = "certified above 1 at this finite case"
    elif ratio[1] < 1:
        relation = "certified below 1 at this finite case"
    else:
        relation = "interval overlaps 1"

    endpoint_output = []
    endpoint_sum = ZERO_INTERVAL
    for bi, ranges in enumerate(endpoint_ranges):
        for ei, (u, v) in enumerate(ranges):
            block_error = counts[bi] * common_error * (2 + common_error)
            bin_error = record_count(m, (u, v)) * common_error * (2 + common_error)
            center = Fraction(endpoint_product_num[bi][ei], FIXED_SQUARED**2)
            radius = (
                block_error * Fraction(endpoint_abs_u_num[bi][ei], FIXED_SQUARED)
                + bin_error * Fraction(endpoint_abs_v_num[bi][ei], FIXED_SQUARED)
                + h_max * block_error * bin_error
            )
            value = idiv_positive((center - radius, center + radius), widths[bi])
            endpoint_sum = iadd(endpoint_sum, value)
            endpoint_output.append({
                "block": f"[{blocks[bi][0]},{blocks[bi][1]})",
                "endpoint_layers": f"[{u},{v})",
                "signed_additive_attribution": interval_json(*value),
            })
    if not icontains(endpoint_sum, direct):
        raise RuntimeError(f"endpoint attribution does not enclose direct value for {(m, n)}")

    frequency_sum = ZERO_INTERVAL
    frequency_output = []
    for label in sorted(frequency_bins, key=lambda x: int(x.split("-")[0])):
        value = frequency_bins[label]
        frequency_sum = iadd(frequency_sum, value)
        frequency_output.append({"frequencies": label, "direct_contribution": interval_json(*value)})
    if not icontains(frequency_sum, direct):
        raise RuntimeError(f"frequency bins do not enclose direct value for {(m, n)}")

    top_output = []
    for _, negative_h, value in sorted(top_frequencies, key=lambda x: (-x[0], -x[1])):
        top_output.append({"h": -negative_h, "direct_contribution": interval_json(*value)})

    record = {
        "m": m,
        "N": n,
        "t": t,
        "inclusive_frequency_range": f"1..{h_max}",
        "canonical_blocks": block_records,
        "direct_T29_width_weighted_square_function": interval_json(*direct),
        "signed_sectors": {
            "record_diagonal_mean": interval_json(*mean),
            "primitive_nonattacking_sector": interval_json(*primitive),
            "cancelling_shared_coordinate_complement": interval_json(*cancelling),
            "complete_complement_to_primitive_mean_plus_cancelling": interval_json(*iadd(mean, cancelling)),
            "recombined_enclosure": interval_json(*recombined),
            "recombined_encloses_direct": True,
        },
        "T63_reconciliation": reconciliation,
        "literal_s_equals_one_half_target": interval_json(*target),
        "direct_minus_target": interval_json(*difference),
        "ratio_to_literal_s_equals_one_half_target": interval_json(*ratio),
        "finite_case_relation_to_one": relation,
        "localization": {
            "frequency_decade_bins": frequency_output,
            "top_20_individual_frequencies": top_output,
            "canonical_block_contributions": block_records,
            "endpoint_layer_ranges_signed_additive": endpoint_output,
            "endpoint_attributions_recombine_to_enclose_direct": True,
        },
    }
    interval_count = count_interval_objects(record)
    return record, interval_count


def brute_force_checks(base_phases: list[tuple[int, int]]) -> list[dict]:
    cases = ((1, 5), (2, 6), (3, 7), (4, 6), (5, 7))
    output = []
    for m, n in cases:
        blocks = canonical_blocks(n)
        powers = list(base_phases[:n])
        for h in range(1, 10**m + 1):
            prefix_re = prefix_im = 0
            layers = [0] * n
            for e in range(n):
                if e >= m:
                    add_re, add_im = powers[e - m]
                    prefix_re += add_re
                    prefix_im += add_im
                    re, im = powers[e]
                    layers[e] = 2 * (re * prefix_re + im * prefix_im)
            for a, b in blocks:
                fast = sum(layers[a:b])
                brute_re = brute_im = 0
                for i in range(n):
                    for j in range(n):
                        if i == j or abs(i - j) < m or not (a <= max(i, j) < b):
                            continue
                        ri, ii = powers[i]
                        rj, ij = powers[j]
                        brute_re += ri * rj + ii * ij
                        brute_im += ii * rj - ri * ij
                assert brute_re == fast and brute_im == 0
            if h != 10**m:
                powers = [complex_mul_fixed(powers[k], base_phases[k]) for k in range(n)]
        output.append({
            "m": m, "N": n, "frequencies_checked": f"1..{10**m}",
            "check": "exact fixed-point equality of fast endpoint recurrence and explicit ordered-record enumeration",
            "passed": True,
        })
    return output


def count_interval_objects(value) -> int:
    if isinstance(value, dict):
        count = int(set(value) == {"lower", "upper", "endpoint_digits"})
        return count + sum(count_interval_objects(v) for v in value.values())
    if isinstance(value, list):
        return sum(count_interval_objects(v) for v in value)
    return 0


def verify_serialized_intervals(value) -> int:
    if isinstance(value, dict):
        if set(value) == {"lower", "upper", "endpoint_digits"}:
            assert decimal_fraction(value["lower"]) <= decimal_fraction(value["upper"])
            assert len(value["lower"].split(".")[1]) == value["endpoint_digits"]
            assert len(value["upper"].split(".")[1]) == value["endpoint_digits"]
            return 1
        return sum(verify_serialized_intervals(v) for v in value.values())
    if isinstance(value, list):
        return sum(verify_serialized_intervals(v) for v in value)
    return 0


def build_results(pi_digits: str, pi_certificate: dict) -> dict:
    verify_canonical_blocks()
    pi_short_floor = int("3" + pi_digits[:PI_SHORT_DIGITS])
    base_phases = pi_phase_table(pi_digits, pi_short_floor, MAX_N)
    brute = brute_force_checks(base_phases)
    records = []
    interval_count = 0
    for m, n, t in CASES:
        print(f"evaluating m={m}, N={n}", file=sys.stderr, flush=True)
        record, count = evaluate_case(m, n, t, base_phases)
        records.append(record)
        interval_count += count
    result = {
        "schema": "t85-certified-complete-t29-experiment-v1",
        "item_id": ITEM_ID,
        "classification": "experiment",
        "canonical_problem_relation": "T29 residual sparse-Fourier sibling A12; not the canonical collision count",
        "parameters": {
            "mu": 8, "c": 1, "Q0_reported": 0,
            "Q0_independence": "verified for every tested m because the second arithmetic-exclusion conjunct is impossible",
            "alpha": "pi",
        },
        "domains": {
            "m_equals_1": "N=4*2^t+1 for every integer 6<=t<=16",
            "transitions": [[2, 11], [3, 33], [4, 101], [5, 317]],
            "frequencies": "inclusive integers 1..10^m",
            "canonical_blocks": "translated binary partition of [1,N)",
            "literal_width": "sqrt(finish^2-start^2)",
        },
        "source_hashes": EXPECTED_INPUT_HASHES,
        "pi_certificate": pi_certificate,
        "arithmetic_certificate": {
            "floating_point_used_for_results": False,
            "fixed_point_decimal_digits": FIXED_DIGITS,
            "turn_window_decimal_digits": TURN_DIGITS,
            "taylor_terms_after_constant_or_linear_term": TAYLOR_TERMS,
            "base_component_error_upper": decimal_upper(BASE_COMPONENT_ERROR, 45),
            "power_error_formula": "E_h = h*(2*base_component_error+10^-40)/(1-2*h*base_component_error)",
            "maximum_power_error_upper": decimal_upper(power_error(MAX_H), 45),
            "every_pi_turn_interval_checked_inside_one_rational_eighth-turn": True,
            "arithmetic_exclusion_audits": [exclusion_impossible_audit(m) for m in range(1, 6)],
        },
        "brute_force_validation": brute,
        "evaluations": records,
        "containment_audit": {
            "reported_interval_objects": interval_count,
            "all_decimal_endpoints_rounded_outward_from_exact_fractions": True,
            "all_frequency_bin_sums_enclose_their_direct_values": True,
            "all_endpoint_attribution_sums_enclose_their_direct_values": True,
            "all_signed_sector_recombinations_enclose_their_direct_values": True,
            "all_m_equals_1_T63_intersections_nonempty": True,
        },
        "claim_limits": [
            "Every reported finite observation is heuristic evidence only.",
            "These finite computations neither prove nor refute C2.",
            "These finite computations neither prove nor refute C1.",
            "These finite computations neither prove nor refute C3.",
            "No finite ratio proves or refutes an all-scale or all-parameter assertion.",
        ],
    }
    actual_count = verify_serialized_intervals(result)
    if actual_count != interval_count:
        raise RuntimeError(f"interval count mismatch: {actual_count} != {interval_count}")
    return result


def verify_inputs(base: Path) -> None:
    for name, expected in EXPECTED_INPUT_HASHES.items():
        actual = sha256_file(base / name)
        if actual != expected:
            raise RuntimeError(f"input SHA-256 mismatch for {name}: {actual} != {expected}")


def verify_manifest(base: Path) -> None:
    for line in (base / "SHA256SUMS").read_text(encoding="ascii").splitlines():
        digest, name = line.split("  ", 1)
        actual = sha256_file(base / name)
        if actual != digest:
            raise RuntimeError(f"manifest SHA-256 mismatch for {name}: {actual} != {digest}")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--generate", action="store_true")
    parser.add_argument("--verify", action="store_true")
    parser.add_argument("--quick", action="store_true")
    args = parser.parse_args()
    if sum((args.generate, args.verify, args.quick)) != 1:
        parser.error("choose exactly one of --generate, --verify, or --quick")
    base = Path(__file__).resolve().parent
    started = time.monotonic()
    verify_inputs(base)
    if args.quick:
        verify_manifest(base)
        print(f"quick verification passed in {time.monotonic() - started:.2f}s")
        return 0

    if args.verify:
        pi_digits, pi_certificate = certified_pi_digits(PI_CERT_DIGITS)
        stored_digits = (base / "pi_digits.txt").read_text(encoding="ascii").strip()
        stored_certificate = json.loads((base / "pi_certificate.json").read_text(encoding="ascii"))
        if stored_digits != pi_digits or stored_certificate != pi_certificate:
            raise RuntimeError("stored pi certificate differs from exact regeneration")
    else:
        pi_digits = (base / "pi_digits.txt").read_text(encoding="ascii").strip()
        pi_certificate = json.loads((base / "pi_certificate.json").read_text(encoding="ascii"))
        if hashlib.sha256((pi_digits + "\n").encode()).hexdigest() != pi_certificate["fractional_digits_sha256"]:
            raise RuntimeError("stored pi digit hash disagrees with certificate")

    results = build_results(pi_digits, pi_certificate)
    encoded = json.dumps(results, indent=2, sort_keys=True) + "\n"
    if args.generate:
        (base / "results.json").write_text(encoded, encoding="ascii")
    else:
        verify_manifest(base)
        if (base / "results.json").read_text(encoding="ascii") != encoded:
            raise RuntimeError("results.json is not byte-identical to certified regeneration")
    print(f"{args.generate and 'generation' or 'full verification'} passed in {time.monotonic() - started:.2f}s")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
