#!/usr/bin/env python3
"""Certified bounded T26/T34/T38 experiment for T50."""

from __future__ import annotations

import argparse
import hashlib
import json
import math
from dataclasses import dataclass
from fractions import Fraction
from functools import lru_cache
from pathlib import Path


@dataclass(frozen=True)
class Interval:
    lo: Fraction
    hi: Fraction

    def __post_init__(self) -> None:
        if self.lo > self.hi:
            raise ValueError("reversed interval")

    @staticmethod
    def point(x: int | Fraction) -> "Interval":
        value = Fraction(x)
        return Interval(value, value)

    def __add__(self, other: "Interval") -> "Interval":
        return Interval(self.lo + other.lo, self.hi + other.hi)

    def __neg__(self) -> "Interval":
        return Interval(-self.hi, -self.lo)

    def __sub__(self, other: "Interval") -> "Interval":
        return self + (-other)

    def __mul__(self, other: "Interval") -> "Interval":
        values = (
            self.lo * other.lo,
            self.lo * other.hi,
            self.hi * other.lo,
            self.hi * other.hi,
        )
        return Interval(min(values), max(values))

    def scale(self, value: int | Fraction) -> "Interval":
        return self * Interval.point(value)

    def reciprocal(self) -> "Interval":
        if self.lo <= 0 <= self.hi:
            raise ValueError("interval reciprocal crosses zero")
        return Interval(Fraction(1, 1) / self.hi, Fraction(1, 1) / self.lo)


ZERO = Interval.point(0)
ONE = Interval.point(1)


def interval_abs(x: Interval) -> Interval:
    if x.lo >= 0:
        return x
    if x.hi <= 0:
        return -x
    return Interval(Fraction(0), max(-x.lo, x.hi))


def interval_square(x: Interval) -> Interval:
    if x.lo <= 0 <= x.hi:
        return Interval(Fraction(0), max(x.lo * x.lo, x.hi * x.hi))
    values = (x.lo * x.lo, x.hi * x.hi)
    return Interval(min(values), max(values))


def interval_pow(x: Interval, exponent: int) -> Interval:
    if exponent < 0:
        return interval_pow(x, -exponent).reciprocal()
    result = ONE
    base = x
    power = exponent
    while power:
        if power & 1:
            result = result * base
        base = base * base
        power >>= 1
    return result


def floor_fraction(x: Fraction) -> int:
    return x.numerator // x.denominator


def ceil_fraction(x: Fraction) -> int:
    return -floor_fraction(-x)


def frac_pair(x: Fraction) -> list[int]:
    return [x.numerator, x.denominator]


def outward_decimal(x: Fraction, places: int, upper: bool) -> str:
    scale = 10**places
    scaled = x * scale
    integer = ceil_fraction(scaled) if upper else floor_fraction(scaled)
    sign = "-" if integer < 0 else ""
    digits = str(abs(integer)).rjust(places + 1, "0")
    return f"{sign}{digits[:-places]}.{digits[-places:]}"


def interval_json(x: Interval, places: int) -> dict[str, str]:
    return {
        "lo": outward_decimal(x.lo, places, False),
        "hi": outward_decimal(x.hi, places, True),
    }


def classify_lt(left: Interval, right: Interval) -> str:
    if left.hi < right.lo:
        return "true"
    if left.lo >= right.hi:
        return "false"
    return "unresolved"


def classify_gt(left: Interval, right: Interval) -> str:
    return classify_lt(right, left)


def classify_positive(x: Interval) -> str:
    return classify_gt(x, ZERO)


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1 << 20), b""):
            digest.update(block)
    return digest.hexdigest()


def atan_reciprocal_interval(q: int, target: Fraction) -> tuple[Interval, int]:
    total = Fraction(0)
    k = 0
    while True:
        term = Fraction(1, (2 * k + 1) * q ** (2 * k + 1))
        total += term if k % 2 == 0 else -term
        next_k = k + 1
        next_term = Fraction(1, (2 * next_k + 1) * q ** (2 * next_k + 1))
        signed_next = next_term if next_k % 2 == 0 else -next_term
        if next_term < target:
            adjacent = total + signed_next
            return Interval(min(total, adjacent), max(total, adjacent)), k + 1
        k += 1


def certify_pi(bits: int) -> tuple[Interval, dict]:
    target = Fraction(1, 2**bits)
    atan5, terms5 = atan_reciprocal_interval(5, target / 32)
    atan239, terms239 = atan_reciprocal_interval(239, target / 8)
    pi = atan5.scale(16) - atan239.scale(4)
    return pi, {
        "method": "Machin_pi_equals_16_atan_1_over_5_minus_4_atan_1_over_239",
        "atan_1_over_5_terms": terms5,
        "atan_1_over_239_terms": terms239,
        "target_bits": bits,
        "endpoint_rationals": {
            "lo": frac_pair(pi.lo),
            "hi": frac_pair(pi.hi),
        },
    }


def intersect_unit_positive(x: Interval) -> Interval:
    return Interval(max(Fraction(0), x.lo), min(Fraction(1), x.hi))


def base_sin_cos(y: Interval, terms: int) -> tuple[Interval, Interval]:
    if y.lo < 0:
        raise ValueError("base angle must be nonnegative")
    cos_value = ZERO
    sin_value = ZERO
    even_power = ONE
    y_squared = y * y
    for k in range(terms + 1):
        cos_term = even_power.scale(Fraction(1, math.factorial(2 * k)))
        sin_term = (even_power * y).scale(Fraction(1, math.factorial(2 * k + 1)))
        cos_value = cos_value + (cos_term if k % 2 == 0 else -cos_term)
        sin_value = sin_value + (sin_term if k % 2 == 0 else -sin_term)
        even_power = even_power * y_squared
    cos_rem = y.hi ** (2 * terms + 1) / math.factorial(2 * terms + 1)
    sin_rem = y.hi ** (2 * terms + 2) / math.factorial(2 * terms + 2)
    cos_value = Interval(cos_value.lo - cos_rem, cos_value.hi + cos_rem)
    sin_value = Interval(sin_value.lo - sin_rem, sin_value.hi + sin_rem)
    return intersect_unit_positive(sin_value), intersect_unit_positive(cos_value)


def reduce_turn(t: Interval) -> Interval:
    if t.lo == t.hi:
        integer = floor_fraction(t.lo)
        return Interval.point(t.lo - integer)
    low_floor = floor_fraction(t.lo)
    high_floor = floor_fraction(t.hi)
    if low_floor != high_floor:
        raise ArithmeticError("phase interval crosses an integer")
    return Interval(t.lo - low_floor, t.hi - low_floor)


@lru_cache(maxsize=None)
def sin_cos_turn(t: Interval, pi: Interval, terms: int) -> tuple[Interval, Interval]:
    fractional = reduce_turn(t)
    if fractional.lo == fractional.hi:
        quadrant = floor_fraction(4 * fractional.lo)
    else:
        quadrant_lo = floor_fraction(4 * fractional.lo)
        quadrant_hi = floor_fraction(4 * fractional.hi)
        if quadrant_lo != quadrant_hi:
            raise ArithmeticError("phase interval crosses a quadrant boundary")
        quadrant = quadrant_lo
    if quadrant == 4 and fractional.lo == fractional.hi == 1:
        quadrant = 0
        fractional = ZERO
    if not 0 <= quadrant <= 3:
        raise ArithmeticError("invalid certified quadrant")
    remainder = fractional - Interval.point(Fraction(quadrant, 4))
    angle = pi.scale(2) * remainder
    sin_base, cos_base = base_sin_cos(angle, terms)
    if quadrant == 0:
        return sin_base, cos_base
    if quadrant == 1:
        return cos_base, -sin_base
    if quadrant == 2:
        return -sin_base, -cos_base
    return -cos_base, sin_base


def phase_turn(t: Interval, pi: Interval, terms: int) -> tuple[Interval, Interval]:
    return sin_cos_turn(t, pi, terms)


def complex_sum_norm_sq(turns: list[Interval], pi: Interval, terms: int) -> Interval:
    real = ZERO
    imag = ZERO
    for turn in turns:
        sin_value, cos_value = phase_turn(turn, pi, terms)
        real = real + cos_value
        imag = imag + sin_value
    return interval_square(real) + interval_square(imag)


def inverse_error_interval(
    tau: Fraction, pi: Interval, terms: int, bisections: int
) -> Interval:
    low = Fraction(0)
    high = Fraction(1, 4)
    tau_interval = Interval.point(tau)
    for _ in range(bisections):
        midpoint = (low + high) / 2
        _sin_value, cos_value = sin_cos_turn(Interval.point(midpoint), pi, terms)
        relation = classify_gt(cos_value, tau_interval)
        if relation == "true":
            low = midpoint
        elif relation == "false":
            high = midpoint
        else:
            raise ArithmeticError("inverse-error bisection was unresolved")
    return Interval(low, high)


def density_denominator(D: int, k: int) -> int:
    value = D
    for _ in range(k):
        value = 8 * value * value
    return value


def selected_minimum(entries: list[tuple[str, Interval]]) -> tuple[Interval, str]:
    for name, candidate in entries:
        if all(candidate.hi < other.lo for other_name, other in entries if other_name != name):
            return candidate, name
    return Interval(min(value.lo for _name, value in entries), min(value.hi for _name, value in entries)), "unresolved"


def certified_order(delta: Interval) -> tuple[int | None, Interval]:
    inverse = delta.reciprocal()
    low_order = ceil_fraction(inverse.lo)
    high_order = ceil_fraction(inverse.hi)
    return (low_order if low_order == high_order else None), inverse


def coefficient_multiplier(h: int, r: int, shifts: list[int], k: int) -> int:
    value = h * (10**r - 1)
    for shift in shifts[:k]:
        value *= 10**shift - 1
    return value


def fejer_interval(
    beta: Interval, denominator: int, R: int, pi: Interval, terms: int
) -> Interval:
    x = beta.scale(denominator)
    if x.lo == x.hi and x.lo.denominator == 1:
        return Interval.point(R)
    numerator_sin, _numerator_cos = sin_cos_turn(x.scale(Fraction(R, 2)), pi, terms)
    denominator_sin, _denominator_cos = sin_cos_turn(x.scale(Fraction(1, 2)), pi, terms)
    denominator_square = interval_square(denominator_sin)
    if denominator_square.lo <= 0:
        raise ArithmeticError("Fejer denominator interval contains zero")
    return interval_square(numerator_sin) * denominator_square.reciprocal().scale(Fraction(1, R))


def integer_candidates(x: Interval, radius: Interval) -> range:
    start = floor_fraction(x.lo - radius.hi) - 1
    stop = ceil_fraction(x.hi + radius.hi) + 2
    return range(start, stop)


def joint_good_pair(
    beta0: Interval,
    beta1: Interval,
    error0: Interval,
    error1: Interval,
    U: int,
    denominator: int,
    places: int,
) -> dict:
    scaled0 = beta0.scale(denominator)
    scaled1 = beta1.scale(denominator)
    unresolved = False
    checked = 0
    for a0 in integer_candidates(scaled0, error0):
        e0 = interval_abs(scaled0 - Interval.point(a0))
        left = classify_lt(e0, error0)
        if left == "false":
            continue
        for a1 in integer_candidates(scaled1, error1):
            checked += 1
            e1 = interval_abs(scaled1 - Interval.point(a1))
            right = classify_lt(e1, error1)
            budget = e1.scale(denominator) + e0.scale(U * denominator)
            budget_status = classify_lt(budget, ONE)
            statuses = (left, right, budget_status)
            if all(status == "true" for status in statuses):
                return {
                    "status": "true",
                    "checked_integer_pairs": checked,
                    "witness": [a0, a1],
                    "e0": interval_json(e0, places),
                    "e1": interval_json(e1, places),
                    "budget": interval_json(budget, places),
                }
            if "unresolved" in statuses and "false" not in statuses:
                unresolved = True
    return {
        "status": "unresolved" if unresolved else "false",
        "checked_integer_pairs": checked,
        "witness": None,
    }


def primitive_contributions(
    beta: Interval,
    ell: int,
    R: int,
    pi: Interval,
    terms: int,
    places: int,
) -> tuple[list[dict], Interval, Fraction]:
    denominators = [10**ell - 10**j for j in range(ell)]
    records: list[dict] = []
    total = ZERO
    total_weight = Fraction(0)
    for m in range(1, R):
        if m % 10 == 0:
            continue
        contribution = ZERO
        class_weight = Fraction(0)
        u = m
        exponents: list[int] = []
        exponent = 0
        while u < R:
            weight = Fraction(R - u, R)
            cosine_sum = ZERO
            for denominator in denominators:
                _sin_value, cosine = phase_turn(beta.scale(u * denominator), pi, terms)
                cosine_sum = cosine_sum + cosine
            contribution = contribution + cosine_sum.scale(weight)
            class_weight += weight
            exponents.append(exponent)
            u *= 10
            exponent += 1
        quarter_margin = contribution - Interval.point(Fraction(ell, 4) * class_weight)
        records.append(
            {
                "m": m,
                "valuation_exponents": exponents,
                "weight": frac_pair(class_weight),
                "contribution": interval_json(contribution, places),
                "quarter_correlation_margin": interval_json(quarter_margin, places),
                "quarter_correlation_status": classify_positive(quarter_margin),
            }
        )
        total = total + contribution
        total_weight += class_weight
    return records, total, total_weight


def build_stratum(
    beta0: Interval,
    beta1: Interval,
    D: int,
    U: int,
    residual0: int,
    residual1: int,
    ell: int,
    pi: Interval,
    error0: Interval,
    error1: Interval,
    terms: int,
    places: int,
) -> dict:
    third_radius = Interval.point(Fraction(1, 2 * U * 10**ell))
    delta, selected = selected_minimum(
        [
            ("left_inverse_error", error0),
            ("right_inverse_error_div_U", error1.scale(Fraction(1, U))),
            ("mixed_budget", third_radius),
        ]
    )
    R, inverse_delta = certified_order(delta)
    if R is None:
        raise ArithmeticError("stratum order unresolved")
    denominators = [10**ell - 10**j for j in range(ell)]
    fejer_terms = [fejer_interval(beta0, q, R, pi, terms) for q in denominators]
    fejer_sum = ZERO
    for value in fejer_terms:
        fejer_sum = fejer_sum + value
    fsfs_threshold = delta.reciprocal()
    fsfs_threshold = interval_square(fsfs_threshold).scale(Fraction(ell, 4 * R))
    fsfs_margin = fejer_sum - fsfs_threshold

    primitive, primitive_total, primitive_weight = primitive_contributions(
        beta0, ell, R, pi, terms, places
    )
    apc_threshold = interval_square(delta.reciprocal()).scale(Fraction(ell, 8 * R)) - Interval.point(Fraction(ell, 2))
    apc_margin = primitive_total - apc_threshold
    regrouping_residual = fejer_sum - (Interval.point(ell) + primitive_total.scale(2))

    common_depth = min(residual0, residual1)
    boundary_total_low = ZERO
    boundary_total_high = ZERO
    boundary_parts = []
    joint_records = []
    for pair_ell in range(1, common_depth):
        part_low = ZERO
        part_high = ZERO
        for j in range(pair_ell):
            s = pair_ell - j
            q = 10**pair_ell - 10**j
            joint = joint_good_pair(beta0, beta1, error0, error1, U, q, places)
            weight = fejer_interval(beta0, q, R, pi, terms) * fejer_interval(beta1, q, R, pi, terms)
            joint_records.append(
                {
                    "j": j,
                    "s": s,
                    "ell": pair_ell,
                    "denominator": q,
                    "domain_predicates": {
                        "j_lt_left_residual": j < residual0,
                        "s_lt_right_residual": s < residual1,
                        "period_positive": 1 <= s,
                        "sum_lt_left_residual": j + s < residual0,
                        "sum_lt_right_residual": j + s < residual1,
                    },
                    "joint_good": joint,
                    "weight": interval_json(weight, places),
                }
            )
            if joint["status"] == "false":
                part_low = part_low + weight
                part_high = part_high + weight
            elif joint["status"] == "unresolved":
                part_high = part_high + weight
        boundary_total_low = boundary_total_low + part_low
        boundary_total_high = boundary_total_high + part_high
        boundary_parts.append(
            {
                "ell": pair_ell,
                "lower": interval_json(part_low, places),
                "upper": interval_json(part_high, places),
            }
        )
    boundary_enclosure = Interval(boundary_total_low.lo, boundary_total_high.hi)
    return {
        "ell": ell,
        "legal_predicates": {
            "D_positive": 1 <= D,
            "ell_positive": 1 <= ell,
            "ell_lt_common_depth": ell < min(residual0, residual1),
        },
        "denominators": denominators,
        "delta": interval_json(delta, places),
        "delta_selected_entry": selected,
        "inverse_delta": interval_json(inverse_delta, places),
        "R": R,
        "fejer_terms": [interval_json(value, places) for value in fejer_terms],
        "fejer_sum": interval_json(fejer_sum, places),
        "fsfs_threshold": interval_json(fsfs_threshold, places),
        "fsfs_margin": interval_json(fsfs_margin, places),
        "fsfs_status": classify_positive(fsfs_margin),
        "primitive_classes": primitive,
        "primitive_weight_sum": frac_pair(primitive_weight),
        "primitive_total": interval_json(primitive_total, places),
        "apc_threshold": interval_json(apc_threshold, places),
        "apc_margin": interval_json(apc_margin, places),
        "apc_status": classify_positive(apc_margin),
        "t43_regrouping_residual": interval_json(regrouping_residual, places),
        "t43_regrouping_interval_contains_zero": regrouping_residual.lo <= 0 <= regrouping_residual.hi,
        "boundary_loss": {
            "cutoffs": [R - 1, R - 1],
            "scope": "full_common_pair_domain_partitioned_by_denominator_stratum",
            "enclosure": interval_json(boundary_enclosure, places),
            "by_stratum": boundary_parts,
            "joint_pairs": joint_records,
        },
    }


def dataset_alpha(name: str, config: dict, pi: Interval) -> tuple[Interval, dict]:
    if name == "pi":
        return pi, {"kind": "fixed_pi_certified_interval"}
    if name == "rational_cycle":
        numerator, denominator = config["controls"]["rational_cycle"]
        return Interval.point(Fraction(numerator, denominator)), {
            "kind": "rational_cycle",
            "value": [numerator, denominator],
        }
    seed = config["controls"]["seeded_random_seed_ascii"].encode("ascii")
    digest = hashlib.sha256(seed).digest()
    numerator = int.from_bytes(digest, "big")
    denominator = 2 ** config["controls"]["seeded_random_denominator_power"]
    return Interval.point(Fraction(numerator, denominator)), {
        "kind": "sha256_seeded_rational_control",
        "seed_sha256": hashlib.sha256(seed).hexdigest(),
        "value": [numerator, denominator],
    }


def build_report(result: dict) -> str:
    lines = [
        "# T50 certified bounded fixed-pi resonance experiment",
        "",
        "Status: `experiment` (finite heuristic evidence only).",
        "",
        "## Scope",
        "",
        "The vendored canonical statement is byte-identical and hash-pinned. Its question",
        "retains `forall A, exists n0, forall n>=n0, exists N`, ordered pairs, the",
        "diagonal, strict circle distance, fixed pi, and base 10. This experiment is the",
        "bounded A14 sibling only. It does not instantiate the failure-derived parameter",
        "provenance of T26; it exhausts the explicitly configured structural",
        "`GeometricResonanceChain` domain.",
        "",
        "## Declared bounds",
        "",
        f"- `M in {result['parameters']['search']['M_values']}`, `D in {result['parameters']['search']['D_values']}`.",
        f"- `r in {result['parameters']['search']['r_values']}`, `h in {result['parameters']['search']['h_values']}`.",
        f"- Depth `{result['parameters']['search']['depth']}`, shifts `{result['parameters']['search']['shift_lists']}`, `B={result['parameters']['search']['B']}`, `K={result['parameters']['search']['K']}`.",
        "- Every legal consecutive node and every `1 <= ell < min(M_k,M_(k+1))` is evaluated.",
        "- Boundary loss uses `H0=H1=R-1` for each target stratum and the full common pair domain.",
        "",
        "## Certification",
        "",
        "Pi is enclosed by exact rational alternating-series bounds in Machin's formula.",
        "Every phase is reduced by certified interval arithmetic, and sine/cosine use",
        "rational Taylor polynomials with explicit derivative remainders. Resonance",
        "comparisons use squared norms. Strict predicates are labeled true only when the",
        "entire left interval is strictly on the required side; overlaps are unresolved.",
        "All T26 list/range predicates and all denominator formulas are exact integers.",
        "",
        "## Results",
        "",
        "| dataset | candidates | witnesses | strata | FSFS true | APC true | unresolved predicates |",
        "|---|---:|---:|---:|---:|---:|---:|",
    ]
    for dataset in result["datasets"]:
        summary = dataset["summary"]
        lines.append(
            f"| {dataset['name']} | {summary['candidate_count']} | {summary['witness_count']} | "
            f"{summary['stratum_count']} | {summary['fsfs_true']} | {summary['apc_true']} | "
            f"{summary['unresolved_predicates']} |"
        )
    lines.extend(
        [
            "",
            "`raw_output.json` contains every candidate, every witness node interval, every",
            "legal denominator stratum, every primitive-class contribution, every common-domain",
            "joint-good classification, and certified boundary-loss/APC/FSFS enclosures.",
            "The primitive regrouping and APC terminology are taken from the unverified T43",
            "note and are used only as an interval-consistency cross-check; T38's Fejer sum is computed",
            "independently through a certified geometric-series identity.",
            "",
            "## Replay",
            "",
            "Run `bash reproduce.sh` from a directory containing only these artifacts.",
            "It hash-checks all pinned inputs, regenerates and byte-compares the JSON and this",
            "report, validates exact table structure, and runs a separate floating-point naive",
            "implementation on all declared `M=3` cases. Requirements are Python 3.11+ and",
            "standard Unix `bash`, `sha256sum`, `cmp`, and `mktemp`; no network is used.",
            "Declared budget: 300 seconds and 2048 MiB.",
            "",
            "## Required limitation",
            "",
            "Every conclusion is finite heuristic evidence. Successes or failures prove neither",
            "FSFS nor its negation beyond the listed tuples, neither adjacent compatibility nor",
            "its negation, neither C1 nor canonical A1, and no asymptotic property of pi.",
            "The rational-cycle and seeded-random rows are controls, not transfers to fixed pi.",
            "",
        ]
    )
    return "\n".join(lines)


def run(config_path: Path, output_path: Path, report_path: Path) -> None:
    config = json.loads(config_path.read_text(encoding="ascii"))
    certification = config["certification"]
    places = certification["output_decimal_places"]
    terms = certification["taylor_terms"]
    pi, pi_certificate = certify_pi(certification["pi_target_bits"])
    error_cache: dict[int, Interval] = {}

    result = {
        "format": "t50-certified-bounded-experiment-output-v1",
        "canonical_statement_sha256": config["canonical_sha256"],
        "parameters": config,
        "pi_certificate": pi_certificate,
        "interval_encoding": f"outward-rounded decimal enclosure with {places} places",
        "datasets": [],
        "claims": {
            "evidence_label": "experiment",
            "finite_heuristic_only": True,
            "proves_FSFS": False,
            "proves_compatibility": False,
            "proves_C1": False,
            "proves_canonical_A1": False,
        },
    }

    for dataset_name in ("pi", "rational_cycle", "seeded_random"):
        alpha, alpha_description = dataset_alpha(dataset_name, config, pi)
        candidates = []
        witnesses = []
        unresolved_count = 0
        for M in config["search"]["M_values"]:
            for D in config["search"]["D_values"]:
                for r in config["search"]["r_values"]:
                    for h in config["search"]["h_values"]:
                        for shifts in config["search"]["shift_lists"]:
                            d = config["search"]["depth"]
                            B = config["search"]["B"]
                            K = config["search"]["K"]
                            discrete = {
                                "length_eq_depth": len(shifts) == d,
                                "nodup": len(set(shifts)) == len(shifts),
                                "shift_lower": all(B <= shift for shift in shifts),
                                "shift_avoids_singleton_r": all(shift != r for shift in shifts),
                                "final_residual": K <= M - sum(shifts),
                            }
                            node_records = []
                            resonance_statuses = []
                            for k in range(d + 1):
                                residual = M - sum(shifts[:k])
                                Dk = density_denominator(D, k)
                                multiplier = coefficient_multiplier(h, r, shifts, k)
                                beta = alpha.scale(multiplier)
                                norm_sq = complex_sum_norm_sq(
                                    [beta.scale(10**j) for j in range(residual)], pi, terms
                                )
                                threshold_sq = Fraction(residual * residual, Dk * Dk)
                                status = classify_gt(norm_sq, Interval.point(threshold_sq))
                                resonance_statuses.append(status)
                                if status == "unresolved":
                                    unresolved_count += 1
                                node_records.append(
                                    {
                                        "k": k,
                                        "residual": residual,
                                        "density_denominator": Dk,
                                        "coefficient_multiplier_of_alpha": multiplier,
                                        "norm_squared": interval_json(norm_sq, places),
                                        "threshold_squared": frac_pair(threshold_sq),
                                        "strict_resonance": status,
                                    }
                                )
                            is_witness = all(discrete.values()) and all(
                                status == "true" for status in resonance_statuses
                            )
                            candidate_id = f"{dataset_name}-M{M}-D{D}-r{r}-h{h}-s{'-'.join(map(str, shifts))}"
                            candidates.append(
                                {
                                    "id": candidate_id,
                                    "M": M,
                                    "N_equals_M_plus_r": M + r,
                                    "D": D,
                                    "r": r,
                                    "h": h,
                                    "shifts": shifts,
                                    "discrete_predicates": discrete,
                                    "nodes": node_records,
                                    "is_witness": is_witness,
                                }
                            )
                            if not is_witness:
                                continue
                            errors = []
                            for k in range(d + 1):
                                Dk = density_denominator(D, k)
                                if Dk not in error_cache:
                                    tau = Fraction(1, 8 * Dk * Dk)
                                    error_cache[Dk] = inverse_error_interval(
                                        tau,
                                        pi,
                                        terms,
                                        certification["inverse_error_bisections"],
                                    )
                                errors.append(error_cache[Dk])
                            beta0 = alpha.scale(coefficient_multiplier(h, r, shifts, 0))
                            beta1 = alpha.scale(coefficient_multiplier(h, r, shifts, 1))
                            residual0 = M
                            residual1 = M - shifts[0]
                            U = 10 ** shifts[0] - 1
                            strata = [
                                build_stratum(
                                    beta0,
                                    beta1,
                                    D,
                                    U,
                                    residual0,
                                    residual1,
                                    ell,
                                    pi,
                                    errors[0],
                                    errors[1],
                                    terms,
                                    places,
                                )
                                for ell in range(1, min(residual0, residual1))
                            ]
                            witnesses.append(
                                {
                                    "candidate_id": candidate_id,
                                    "adjacent_node": 0,
                                    "U": U,
                                    "common_depth": min(residual0, residual1),
                                    "inverse_errors": [interval_json(value, places) for value in errors],
                                    "strata": strata,
                                }
                            )
        all_strata = [stratum for witness in witnesses for stratum in witness["strata"]]
        unresolved_count += sum(
            pair["joint_good"]["status"] == "unresolved"
            for stratum in all_strata
            for pair in stratum["boundary_loss"]["joint_pairs"]
        )
        result["datasets"].append(
            {
                "name": dataset_name,
                "alpha": alpha_description,
                "candidates": candidates,
                "witnesses": witnesses,
                "summary": {
                    "candidate_count": len(candidates),
                    "witness_count": len(witnesses),
                    "stratum_count": len(all_strata),
                    "fsfs_true": sum(s["fsfs_status"] == "true" for s in all_strata),
                    "apc_true": sum(s["apc_status"] == "true" for s in all_strata),
                    "unresolved_predicates": unresolved_count,
                },
            }
        )

    output_path.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n", encoding="ascii")
    report_path.write_text(build_report(result), encoding="ascii")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--config", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--report", type=Path, required=True)
    args = parser.parse_args()
    run(args.config, args.output, args.report)


if __name__ == "__main__":
    main()
