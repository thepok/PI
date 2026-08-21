#!/usr/bin/env python3
"""Exact finite replay for T82's metric signed-residual identities.

All theorem-facing checks use integers or fractions.  The script deliberately
does not numerically evaluate sin, cos, or pi.  Their analytic bounds are
proved in the companion note; this replay checks the resulting rational
envelope and every finite collision identity in the selected cases.
"""

from __future__ import annotations

import argparse
from collections import Counter, defaultdict
from fractions import Fraction
import hashlib
import json
from math import gcd
from pathlib import Path


SCHEMA_VERSION = "t82-symbolic-replay-v1"
STATEMENT_FILE = "pi-positive-decimal-factor-entropy.txt"
STATEMENT_SHA256 = "a70dd741b27595aeb3dfc902b5e201579fed6bae24e2191f58c5ac64a22939e6"
SOURCE_PINS = {
    "T56LagSectorAudit.lean": "41e8ec69c4a113592b8f1de1dc5e02e815726c5a7e541ac7fd57afc6b181f1cc",
    "T58TriangularFejerAudit.lean": "04b3808f208db000284cf369467f4d2ffb907b1af44b30fcada8451b8503016d",
    "T61VaalerAnalytic.lean": "61bf75193b6581ef626fc2b061ea6ba39e4fc164ac9e49b3a0820528dc839993",
}


def require(condition: bool, message: str) -> None:
    """Mandatory check that remains active under python -O."""
    if not condition:
        raise RuntimeError(message)


def sample_length(n: int) -> int:
    return 10 ** (n // 2)


def bandwidth(n: int) -> int:
    return 10**n // 2


def repunit_factor(r: int) -> int:
    return 10**r - 1


def phi(h: int, j: int, r: int) -> int:
    return h * 10**j * repunit_factor(r)


def ten_reduce(h: int) -> tuple[int, int]:
    require(h > 0, "ten_reduce requires a positive integer")
    v = 0
    while h % 10 == 0:
        v += 1
        h //= 10
    return v, h


def residual_labels(n: int, mask: str) -> list[tuple[int, int]]:
    """T61 labels for two exact masks.

    full: no ArithmeticExcluded labels.
    mu2_c1_q1: the exact residual mask for mu=2, c=1, Q0=1;
      ArithmeticExcluded is q <= 10^n, so residual means q > 10^n.
    """
    length = sample_length(n)
    labels: list[tuple[int, int]] = []
    for r in range(1, n):
        if not r < length:
            continue
        for j in range(length - r):
            q = 10**j * repunit_factor(r)
            excluded = Fraction(1, 10**n) <= Fraction(1, q)
            require(excluded == (q <= 10**n), "exact specialized mask reduction failed")
            keep = mask == "full" or (mask == "mu2_c1_q1" and not excluded)
            if keep:
                labels.append((r, j))
    return labels


def canonical_partition(groups: dict[object, list[tuple[int, int, int]]]) -> list[list[list[int]]]:
    fibers = [sorted([list(record) for record in records]) for records in groups.values()]
    return sorted(fibers)


def canonical_json_bytes(value: object) -> bytes:
    return (json.dumps(value, sort_keys=True, indent=2) + "\n").encode("ascii")


def digest(value: object) -> str:
    return hashlib.sha256(canonical_json_bytes(value)).hexdigest()


def frac(value: Fraction) -> str:
    return str(value.numerator) if value.denominator == 1 else f"{value.numerator}/{value.denominator}"


def coefficient_envelope(h: int, h_band: int) -> Fraction:
    # H^-1 [1/3 + 2(1-h/H)]
    return Fraction(1, 3 * h_band) + Fraction(2 * (h_band - h), h_band * h_band)


def evaluate_quadratic(
    polynomial: dict[tuple[int, int], int], weights: dict[int, Fraction]
) -> Fraction:
    return sum(
        (Fraction(coefficient) * weights[h1] * weights[h2]
         for (h1, h2), coefficient in polynomial.items()),
        Fraction(0),
    )


def fiber_evaluation(
    fibers: dict[int, list[tuple[int, int, int]]], weights: dict[int, Fraction]
) -> Fraction:
    total = Fraction(0)
    for records in fibers.values():
        fiber_sum = sum((weights[h] for h, _r, _j in records), Fraction(0))
        total += fiber_sum * fiber_sum
    return total


def gcd_parameter_holds(
    left: tuple[int, int, int], right: tuple[int, int, int]
) -> bool:
    h1, r1, j1 = left
    h2, r2, j2 = right
    v1, u1 = ten_reduce(h1)
    v2, u2 = ten_reduce(h2)
    if v1 + j1 != v2 + j2:
        return False
    common = 10 ** gcd(r1, r2) - 1
    u_factor = repunit_factor(r1) // common
    v_factor = repunit_factor(r2) // common
    if gcd(u_factor, v_factor) != 1:
        return False
    if u1 % v_factor or u2 % u_factor:
        return False
    t1 = u1 // v_factor
    t2 = u2 // u_factor
    if t1 != t2 or t1 <= 0 or t1 % 10 == 0:
        return False
    reconstructed1 = 10**v1 * v_factor * t1
    reconstructed2 = 10**v2 * u_factor * t1
    return (
        reconstructed1 == h1
        and reconstructed2 == h2
    )


def replay_case(n: int, mask: str) -> dict[str, object]:
    require(n >= 1, "replay cases require n>=1")
    length = sample_length(n)
    h_band = bandwidth(n)
    labels = residual_labels(n, mask)
    label_set = set(labels)
    require(len(label_set) == len(labels), "duplicate residual label")

    for r, j in labels:
        require(0 < r < n, "lag endpoint failure")
        require(r < length, "lag exceeds sample length")
        require(0 <= j < length - r, "start endpoint failure")
        if mask == "mu2_c1_q1":
            require(10**j * repunit_factor(r) > 10**n, "residual mask failure")

    records = [
        (h, r, j)
        for h in range(1, h_band)
        for r, j in labels
    ]
    direct: dict[int, list[tuple[int, int, int]]] = defaultdict(list)
    reduced: dict[tuple[int, int], list[tuple[int, int, int]]] = defaultdict(list)
    for record in records:
        h, r, j = record
        direct[phi(h, j, r)].append(record)
        v, primitive = ten_reduce(h)
        reduced[(v + j, primitive * repunit_factor(r))].append(record)

    direct_partition = canonical_partition(direct)
    reduced_partition = canonical_partition(reduced)
    require(direct_partition == reduced_partition, "direct and ten-reduced partitions differ")

    gcd_identity_count = 0
    for r1 in range(1, n):
        for r2 in range(1, n):
            require(
                gcd(repunit_factor(r1), repunit_factor(r2)) == 10 ** gcd(r1, r2) - 1,
                "repunit gcd identity failed",
            )
            gcd_identity_count += 1

    matrix: Counter[tuple[int, int]] = Counter()
    quadratic: Counter[tuple[int, int]] = Counter()
    collision_pair_count = 0
    gcd_parameter_pair_count = 0
    for fiber in direct.values():
        for left in fiber:
            for right in fiber:
                collision_pair_count += 1
                require(gcd_parameter_holds(left, right), "direct collision missed by gcd class")
                gcd_parameter_pair_count += 1
                h1, _r1, _j1 = left
                h2, _r2, _j2 = right
                matrix[(h1, h2)] += 1
                quadratic[(min(h1, h2), max(h1, h2))] += 1

    require(
        gcd_parameter_pair_count == collision_pair_count,
        "direct collision and gcd parameter counts differ",
    )

    # Independently generate every pair satisfying the gcd parameterization.
    # Grouping by the required total ten-exponent avoids a full |I|^2 scan.
    exponent_groups: dict[int, list[tuple[int, int, int]]] = defaultdict(list)
    for record in records:
        h, _r, j = record
        v, _primitive = ten_reduce(h)
        exponent_groups[v + j].append(record)
    gcd_generated_pair_count = 0
    for group in exponent_groups.values():
        for left in group:
            for right in group:
                if gcd_parameter_holds(left, right):
                    gcd_generated_pair_count += 1
                    h1, r1, j1 = left
                    h2, r2, j2 = right
                    require(
                        phi(h1, j1, r1) == phi(h2, j2, r2),
                        "gcd parameter generated a noncollision",
                    )
    require(
        gcd_generated_pair_count == collision_pair_count,
        "gcd generation is not complete",
    )

    require(
        all(matrix[(h1, h2)] == matrix[(h2, h1)] for h1, h2 in matrix),
        "collision matrix is not symmetric",
    )
    require(sum(quadratic.values()) == collision_pair_count, "quadratic lost ordered pairs")

    # Independent coefficientwise construction: square the multiplier-count
    # vector in each frequency fiber, without using the ordered-pair matrix.
    fiber_quadratic: Counter[tuple[int, int]] = Counter()
    for fiber in direct.values():
        h_counts = Counter(h for h, _r, _j in fiber)
        hs = sorted(h_counts)
        for index, h1 in enumerate(hs):
            fiber_quadratic[(h1, h1)] += h_counts[h1] * h_counts[h1]
            for h2 in hs[index + 1 :]:
                fiber_quadratic[(h1, h2)] += 2 * h_counts[h1] * h_counts[h2]
    require(fiber_quadratic == quadratic, "fiber and matrix quadratics differ coefficientwise")

    cosine_orthogonality_equal_frequency = Fraction(1, 2)
    outer_cosine_factor = 2
    real_cosine_l2_factor = outer_cosine_factor**2 * cosine_orthogonality_equal_frequency
    require(real_cosine_l2_factor == 2, "real cosine L2 factor is not 2")

    diagonal_index_pairs = len(records)
    off_diagonal_index_pairs = collision_pair_count - diagonal_index_pairs
    require(off_diagonal_index_pairs >= 0, "negative off-diagonal count")

    multiplicities = Counter(len(fiber) for fiber in direct.values())
    max_multiplicity = max(multiplicities, default=0)
    require(max_multiplicity <= n * (n - 1), "finite fiber exceeds proved bound")
    max_frequency = min(
        (frequency for frequency, fiber in direct.items() if len(fiber) == max_multiplicity),
        default=0,
    )
    max_witnesses = sorted([list(record) for record in direct.get(max_frequency, [])])

    weights_one = {h: Fraction(1) for h in range(1, h_band)}
    weights_triangular = {h: Fraction(h_band - h, h_band) for h in range(1, h_band)}
    weights_alternating = {
        h: (-1 if h % 2 else 1) * Fraction(h_band - h, h_band)
        for h in range(1, h_band)
    }
    substitution_checks: dict[str, str] = {}
    for name, weights in (
        ("ones", weights_one),
        ("triangular", weights_triangular),
        ("alternating_signed_triangular", weights_alternating),
    ):
        polynomial_value = evaluate_quadratic(quadratic, weights)
        fiber_value = fiber_evaluation(direct, weights)
        matrix_value = sum(
            (Fraction(count) * weights[h1] * weights[h2]
             for (h1, h2), count in matrix.items()),
            Fraction(0),
        )
        require(
            polynomial_value == fiber_value == matrix_value,
            f"quadratic substitution mismatch: {name}",
        )
        substitution_checks[name] = frac(polynomial_value)

    envelope_weights = {h: coefficient_envelope(h, h_band) for h in range(1, h_band)}
    envelope_sum = sum(envelope_weights.values(), Fraction(0))
    require(
        envelope_sum == Fraction(4 * (h_band - 1), 3 * h_band),
        "rational envelope sum identity failed",
    )
    require(
        all(value < Fraction(7, 3 * h_band) for value in envelope_weights.values()),
        "rational envelope exceeds 7/(3H)",
    )

    envelope_quadratic = evaluate_quadratic(quadratic, envelope_weights)
    pairwise_envelope = Fraction(49 * collision_pair_count, 9 * h_band * h_band)
    fiber_envelope = Fraction(
        49 * n * (n - 1) * len(records),
        9 * h_band * h_band,
    )
    require(
        envelope_quadratic <= pairwise_envelope <= fiber_envelope,
        "envelope bound chain failed",
    )

    zero_mode = Fraction(2 * len(labels), h_band)
    normalized_zero_mode = zero_mode / length
    per_lag = Counter(r for r, _j in labels)

    if n == 2 and mask == "full":
        expected: Counter[tuple[int, int]] = Counter()
        for h in range(1, 50):
            expected[(h, h)] = 9
        for h in range(1, 5):
            expected[(h, 10 * h)] = 16
        require(quadratic == expected, "n=2 full-mask visible polynomial mismatch")
        visible_formula = (
            "Q=9*sum(h=1..49,c_h^2)+16*(c_1*c_10+c_2*c_20+"
            "c_3*c_30+c_4*c_40); integral(S_2^2)=2*Q"
        )
    elif n == 2 and mask == "mu2_c1_q1":
        expected = Counter()
        for h in range(1, 50):
            expected[(h, h)] = 7
        for h in range(1, 5):
            expected[(h, 10 * h)] = 12
        require(quadratic == expected, "n=2 partial-mask visible polynomial mismatch")
        visible_formula = (
            "Q=7*sum(h=1..49,c_h^2)+12*(c_1*c_10+c_2*c_20+"
            "c_3*c_30+c_4*c_40); integral(S_2^2)=2*Q"
        )
    else:
        visible_formula = "integral(S_n^2)=2*sum_phi(sum_{records in fiber(phi)} c_h)^2"

    return {
        "case_id": f"n{n}-{mask}",
        "parameters": {"n": n, "L_n": length, "H_n": h_band, "mask": mask},
        "mask_definition": (
            "all T61 short-rectangle labels retained"
            if mask == "full"
            else "mu=2,c=1,Q0=1: retain exactly q_(j,r)>10^n"
        ),
        "per_lag_cardinalities": {str(r): per_lag[r] for r in sorted(per_lag)},
        "label_count": len(labels),
        "record_count": len(records),
        "distinct_phi_count": len(direct),
        "direct_partition_sha256": digest(direct_partition),
        "ten_reduced_partition_sha256": digest(reduced_partition),
        "partitions_equal": True,
        "gcd_identity_cases": gcd_identity_count,
        "gcd_parameter_pair_count": gcd_parameter_pair_count,
        "gcd_generated_pair_count": gcd_generated_pair_count,
        "direct_collision_pair_count": collision_pair_count,
        "gcd_pair_counts_equal": True,
        "diagonal_index_pair_count": diagonal_index_pairs,
        "ordered_off_diagonal_pair_count": off_diagonal_index_pairs,
        "multiplicity_histogram": {str(k): multiplicities[k] for k in sorted(multiplicities)},
        "max_multiplicity": max_multiplicity,
        "proved_fiber_bound": n * (n - 1),
        "max_fiber_frequency": max_frequency,
        "max_fiber_witnesses_h_r_j": max_witnesses,
        "matrix_symmetric": True,
        "quadratic_sparse_monomial_count": len(quadratic),
        "quadratic_sha256": digest(
            [[h1, h2, quadratic[(h1, h2)]] for h1, h2 in sorted(quadratic)]
        ),
        "visible_quadratic_formula": visible_formula,
        "rational_substitution_checks": substitution_checks,
        "orthogonality_symbolic_rule": "integral cos(2*pi*k*x)cos(2*pi*l*x)=delta_(k,l)/2",
        "real_cosine_L2_factor": frac(real_cosine_l2_factor),
        "zero_coefficient": frac(Fraction(2, h_band)),
        "summed_zero_mode": frac(zero_mode),
        "normalized_zero_mode_by_L_n": frac(normalized_zero_mode),
        "coefficient_envelope_sum": frac(envelope_sum),
        "coefficient_pointwise_envelope": f"abs(a_(H,h))<7/(3H)={frac(Fraction(7, 3*h_band))}",
        "envelope_quadratic_value": frac(envelope_quadratic),
        "pairwise_envelope_bound": frac(pairwise_envelope),
        "fiber_envelope_bound": frac(fiber_envelope),
        "complete_second_moment_formula": (
            "integral(E_n^2)=(2*label_count/H_n)^2+"
            "2*sum_phi(sum_{records in fiber(phi)} c_h)^2"
        ),
        "checks": {
            "domain_endpoints": True,
            "phi_ten_reduction": True,
            "repunit_gcd": True,
            "gcd_collision_parameterization": True,
            "all_ordered_cross_terms_retained": True,
            "quadratic_coefficientwise_fiber_matrix_equality": True,
            "quadratic_three_substitution_replay": True,
            "zero_mode_normalization": True,
            "rational_envelope_algebra": True,
        },
    }


def build_report() -> dict[str, object]:
    statement_path = Path(__file__).resolve().parent / STATEMENT_FILE
    statement_hash = hashlib.sha256(statement_path.read_bytes()).hexdigest()
    require(statement_hash == STATEMENT_SHA256, "canonical statement hash mismatch")

    cases = [
        replay_case(1, "full"),
        replay_case(2, "full"),
        replay_case(2, "mu2_c1_q1"),
        replay_case(3, "full"),
        replay_case(3, "mu2_c1_q1"),
    ]
    expected_summaries = {
        "n1-full": (0, 0, 0),
        "n2-full": (9, 409, 2),
        "n2-mu2_c1_q1": (7, 319, 2),
        "n3-full": (17, 7375, 5),
        "n3-mu2_c1_q1": (12, 5248, 5),
    }
    for case in cases:
        label_count, distinct_count, max_multiplicity = expected_summaries[case["case_id"]]
        require(case["label_count"] == label_count, "unexpected label count")
        require(case["distinct_phi_count"] == distinct_count, "unexpected frequency count")
        require(case["max_multiplicity"] == max_multiplicity, "unexpected max multiplicity")

    return {
        "schema_version": SCHEMA_VERSION,
        "label": "experiment",
        "canonical_statement_sha256": statement_hash,
        "external_kernel_source_pins_not_vendored": SOURCE_PINS,
        "definitions": {
            "L_n": "10^(n//2)",
            "H_n": "10^n//2",
            "short_labels": "0<r<n, r<L_n, 0<=j<L_n-r, residual mask",
            "positive_frequencies": "1<=h<H_n",
            "phi": "h*10^j*(10^r-1)",
            "zero_mode": "2*label_count/H_n",
        },
        "finite_L2_identity": (
            "integral_0^1 S_n(x)^2 dx=2*sum_{ordered i,i':phi(i)=phi(i')} c_hi*c_hi'"
        ),
        "collision_classes": (
            "v10(h1)+j1=v10(h2)+j2 and primitive(h1)*(10^r1-1)="
            "primitive(h2)*(10^r2-1); equivalently primitive(h1)=V*t, "
            "primitive(h2)=U*t after the repunit gcd split"
        ),
        "prose_global_bound_using_replayed_finite_inequalities": (
            "integral S_n^2 <= (98/9)*n*(n-1)^2*(H_n-1)*L_n/H_n^2 "
            "<=(196/9)*n^3*10^(-ceil(n/2))"
        ),
        "prose_measure_conclusion_not_a_finite_experiment": (
            "The displayed summable bound and Tonelli imply S_n(x)->0 a.e.; "
            "2*label_count/H_n->0, hence E_n(x)->0 a.e."
        ),
        "cases": cases,
        "scope": (
            "Metric sibling only. No estimate for the prescribed seed pi and no conclusion "
            "for C7, C2, or C1."
        ),
        "runtime_check_mode": "mandatory require checks remain active under python -O",
        "all_finite_replay_checks_passed": True,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--write", type=Path, help="write canonical JSON to this path")
    args = parser.parse_args()
    report = build_report()
    payload = canonical_json_bytes(report)
    if args.write is not None:
        args.write.write_bytes(payload)
        print(f"wrote {args.write} sha256={hashlib.sha256(payload).hexdigest()}")
    else:
        print(payload.decode("ascii"), end="")


if __name__ == "__main__":
    main()
