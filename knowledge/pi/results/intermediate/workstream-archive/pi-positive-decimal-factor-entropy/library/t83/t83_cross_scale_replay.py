#!/usr/bin/env python3
"""Exact finite replay for T83's cross-scale algebra.

This is an experiment.  It checks finite domains, integer frequency
collisions, rational coefficient envelopes, exponent comparisons, and an
abstract obstruction.  It does not evaluate pi, sin, or cos, and it does not
prove the pinned irrationality estimate or any fixed-pi covariance estimate.
"""

from __future__ import annotations

import argparse
from collections import Counter, defaultdict
from fractions import Fraction
import hashlib
import json
from math import gcd
from pathlib import Path


SCHEMA_VERSION = "t83-cross-scale-replay-v1"
STATEMENT_FILE = "pi-positive-decimal-factor-entropy.txt"
STATEMENT_SHA256 = "a70dd741b27595aeb3dfc902b5e201579fed6bae24e2191f58c5ac64a22939e6"
T60_NOTE_SHA256 = "2a9aa7628b0611279e4b9d74659e744e8386da5308b196507e3fe47cd164b4ef"
SOURCE_PINS = {
    "T1CanonicalEntropy.lean": "8f424db10d98a42ab0e547b2abdef0db9c5b45443c05a4e01033502a2934dbdf",
    "T2ExponentialCollisionCriterion.lean": "608e959dcbb2114c7102ca7d06ae0b16c8c6309c7f994e25c372c495b00f0fac",
    "T56LagSectorAudit.lean": "41e8ec69c4a113592b8f1de1dc5e02e815726c5a7e541ac7fd57afc6b181f1cc",
    "T58TriangularFejerAudit.lean": "04b3808f208db000284cf369467f4d2ffb907b1af44b30fcada8451b8503016d",
    "T61VaalerAnalytic.lean": "61bf75193b6581ef626fc2b061ea6ba39e4fc164ac9e49b3a0820528dc839993",
}
MU_NUMERATOR = 888
LAMBDA_NUMERATOR = 763
EXPONENT_DENOMINATOR = 125

Record = tuple[int, int, int, int]  # (n,h,r,j)
WeightKey = tuple[int, int]  # (n,h)
Monomial = tuple[WeightKey, WeightKey]


def require(condition: bool, message: str) -> None:
    """Mandatory check, including under python -O."""
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
    require(h > 0, "ten_reduce requires h>0")
    valuation = 0
    while h % 10 == 0:
        valuation += 1
        h //= 10
    return valuation, h


def residual_labels(n: int, mask: str) -> list[tuple[int, int]]:
    """Complete T61 short rectangle for two deterministic replay masks."""
    require(mask in {"full", "mu2_c1_q1"}, "unknown residual mask")
    length = sample_length(n)
    labels: list[tuple[int, int]] = []
    for r in range(1, n):
        if not r < length:
            continue
        for j in range(length - r):
            q = 10**j * repunit_factor(r)
            # For mu=2,c=1,Q0=1, ArithmeticExcluded is exactly q<=10^n.
            excluded = Fraction(1, 10**n) <= Fraction(1, q)
            require(excluded == (q <= 10**n), "specialized mask reduction failed")
            if mask == "full" or not excluded:
                labels.append((r, j))
    return labels


def scale_records(n: int, mask: str) -> list[Record]:
    return [
        (n, h, r, j)
        for h in range(1, bandwidth(n))
        for r, j in residual_labels(n, mask)
    ]


def record_frequency(record: Record) -> int:
    _n, h, r, j = record
    return phi(h, j, r)


def reduced_key(record: Record) -> tuple[int, int]:
    _n, h, r, j = record
    valuation, primitive = ten_reduce(h)
    return valuation + j, primitive * repunit_factor(r)


def gcd_parameter_holds(left: Record, right: Record) -> bool:
    _n1, h1, r1, j1 = left
    _n2, h2, r2, j2 = right
    v1, u1 = ten_reduce(h1)
    v2, u2 = ten_reduce(h2)
    if v1 + j1 != v2 + j2:
        return False
    common = 10 ** gcd(r1, r2) - 1
    u_factor = repunit_factor(r1) // common
    v_factor = repunit_factor(r2) // common
    require(gcd(u_factor, v_factor) == 1, "repunit cofactors are not coprime")
    if u1 % v_factor or u2 % u_factor:
        return False
    t1 = u1 // v_factor
    t2 = u2 // u_factor
    return (
        t1 == t2
        and t1 > 0
        and t1 % 10 != 0
        and h1 == 10**v1 * v_factor * t1
        and h2 == 10**v2 * u_factor * t1
    )


def canonical_json_bytes(value: object) -> bytes:
    return (json.dumps(value, sort_keys=True, indent=2) + "\n").encode("ascii")


def digest(value: object) -> str:
    return hashlib.sha256(canonical_json_bytes(value)).hexdigest()


def frac(value: Fraction) -> str:
    if value.denominator == 1:
        return str(value.numerator)
    return f"{value.numerator}/{value.denominator}"


def canonical_partition(groups: dict[object, list[Record]]) -> list[list[list[int]]]:
    return sorted(sorted([list(record) for record in fiber]) for fiber in groups.values())


def coefficient_envelope(n: int, h: int) -> Fraction:
    h_band = bandwidth(n)
    return Fraction(1, 3 * h_band) + Fraction(2 * (h_band - h), h_band * h_band)


def canonical_monomial(left: WeightKey, right: WeightKey) -> Monomial:
    return (left, right) if left <= right else (right, left)


def evaluate_quadratic(
    polynomial: Counter[Monomial], weights: dict[WeightKey, Fraction]
) -> Fraction:
    return sum(
        (Fraction(count) * weights[left] * weights[right]
         for (left, right), count in polynomial.items()),
        Fraction(0),
    )


def fiber_evaluation(
    fibers: dict[int, list[Record]], weights: dict[WeightKey, Fraction]
) -> Fraction:
    total = Fraction(0)
    for fiber in fibers.values():
        fiber_sum = sum((weights[(n, h)] for n, h, _r, _j in fiber), Fraction(0))
        total += fiber_sum * fiber_sum
    return total


def domain_audit(n: int) -> dict[str, object]:
    length = sample_length(n)
    h_band = bandwidth(n)
    labels = residual_labels(n, "full")
    expected = sum(length - r for r in range(1, n) if r < length)
    require(len(labels) == expected, "full rectangle cardinality failed")
    require(all(0 < r < n and r < length and 0 <= j < length - r for r, j in labels),
            "domain endpoint failed")
    return {
        "n": n,
        "L_n": length,
        "H_n": h_band,
        "full_label_count": len(labels),
        "positive_h_range": [1, h_band - 1],
        "strict_exclusions": ["h=H_n", "r=n", "j=L_n-r"],
    }


def replay_cross_scale_case(scales: tuple[int, ...], mask: str) -> dict[str, object]:
    require(scales == tuple(sorted(set(scales))), "scales must be strictly increasing")
    records = [record for n in scales for record in scale_records(n, mask)]
    direct: dict[int, list[Record]] = defaultdict(list)
    reduced: dict[tuple[int, int], list[Record]] = defaultdict(list)
    for record in records:
        direct[record_frequency(record)].append(record)
        reduced[reduced_key(record)].append(record)
    direct_partition = canonical_partition(direct)
    reduced_partition = canonical_partition(reduced)
    require(direct_partition == reduced_partition, "direct and reduced partitions differ")

    matrix: Counter[tuple[WeightKey, WeightKey]] = Counter()
    quadratic: Counter[Monomial] = Counter()
    cross_quadratic: Counter[Monomial] = Counter()
    categories = Counter()
    by_scale_pair = Counter()
    collision_count = 0
    for fiber in direct.values():
        for left in fiber:
            for right in fiber:
                require(gcd_parameter_holds(left, right), "collision missed by gcd parameterization")
                require(record_frequency(left) == record_frequency(right), "spurious collision")
                collision_count += 1
                n1, h1, r1, j1 = left
                n2, h2, r2, j2 = right
                key1, key2 = (n1, h1), (n2, h2)
                matrix[(key1, key2)] += 1
                quadratic[canonical_monomial(key1, key2)] += 1
                by_scale_pair[(n1, n2)] += 1
                if left == right:
                    categories["same_scale_diagonal"] += 1
                elif n1 == n2:
                    categories["same_scale_nontrivial"] += 1
                elif (h1, r1, j1) == (h2, r2, j2):
                    categories["cross_scale_literal_duplicate"] += 1
                    cross_quadratic[canonical_monomial(key1, key2)] += 1
                else:
                    categories["cross_scale_nontrivial"] += 1
                    cross_quadratic[canonical_monomial(key1, key2)] += 1

    require(sum(quadratic.values()) == collision_count, "quadratic lost ordered pairs")
    require(sum(categories.values()) == collision_count, "collision categories are incomplete")
    require(all(matrix[(a, b)] == matrix[(b, a)] for a, b in matrix),
            "ordered collision matrix is not symmetric")

    # Independent coefficientwise square of each frequency-fiber count vector.
    fiber_quadratic: Counter[Monomial] = Counter()
    for fiber in direct.values():
        counts = Counter((n, h) for n, h, _r, _j in fiber)
        keys = sorted(counts)
        for index, left in enumerate(keys):
            fiber_quadratic[(left, left)] += counts[left] ** 2
            for right in keys[index + 1:]:
                fiber_quadratic[(left, right)] += 2 * counts[left] * counts[right]
    require(fiber_quadratic == quadratic, "matrix and fiber quadratics differ")

    # Every pair satisfying the reduced equality is a literal collision.
    for fiber in reduced.values():
        for left in fiber:
            for right in fiber:
                require(gcd_parameter_holds(left, right), "reduced class missed by gcd split")
                require(record_frequency(left) == record_frequency(right),
                        "gcd/reduced class generated a noncollision")

    # Independently scan all pairs with the necessary common ten exponent.
    # This checks the converse: the gcd predicate never generates a collision
    # outside the direct frequency fibers.
    exponent_groups: dict[int, list[Record]] = defaultdict(list)
    for record in records:
        exponent_groups[reduced_key(record)[0]].append(record)
    gcd_generated_count = 0
    for group in exponent_groups.values():
        for left in group:
            for right in group:
                if gcd_parameter_holds(left, right):
                    gcd_generated_count += 1
                    require(record_frequency(left) == record_frequency(right),
                            "gcd predicate generated a noncollision")
    require(gcd_generated_count == collision_count,
            "gcd predicate and direct collision counts differ")

    weights: dict[str, dict[WeightKey, Fraction]] = {
        "ones": {},
        "triangular": {},
        "scale_signed_triangular": {},
        "envelope": {},
        "cesaro_L_normalized_envelope": {},
    }
    for n in scales:
        h_band = bandwidth(n)
        for h in range(1, h_band):
            key = (n, h)
            triangular = Fraction(h_band - h, h_band)
            envelope = coefficient_envelope(n, h)
            weights["ones"][key] = Fraction(1)
            weights["triangular"][key] = triangular
            weights["scale_signed_triangular"][key] = (-1 if n % 2 else 1) * triangular
            weights["envelope"][key] = envelope
            weights["cesaro_L_normalized_envelope"][key] = (
                envelope / (len(scales) * sample_length(n))
            )

    substitutions: dict[str, str] = {}
    for name, assignment in weights.items():
        polynomial_value = evaluate_quadratic(quadratic, assignment)
        require(polynomial_value == fiber_evaluation(direct, assignment),
                f"quadratic substitution mismatch: {name}")
        matrix_value = sum(
            (Fraction(count) * assignment[left] * assignment[right]
             for (left, right), count in matrix.items()),
            Fraction(0),
        )
        require(polynomial_value == matrix_value, f"matrix substitution mismatch: {name}")
        substitutions[name] = frac(polynomial_value)

    multiplicities = Counter(len(fiber) for fiber in direct.values())
    max_multiplicity = max(multiplicities, default=0)
    max_frequency = min(
        (frequency for frequency, fiber in direct.items() if len(fiber) == max_multiplicity),
        default=0,
    )
    label_sets = {n: set(residual_labels(n, mask)) for n in scales}
    common_labels = set.intersection(*(label_sets[n] for n in scales)) if scales else set()
    per_scale_labels = {n: len(label_sets[n]) for n in scales}
    per_scale_records = {n: len(scale_records(n, mask)) for n in scales}

    encoded_quadratic = [
        [[left[0], left[1]], [right[0], right[1]], quadratic[(left, right)]]
        for left, right in sorted(quadratic)
    ]
    encoded_cross = [
        [[left[0], left[1]], [right[0], right[1]], cross_quadratic[(left, right)]]
        for left, right in sorted(cross_quadratic)
    ]
    coefficient_histogram = Counter(quadratic.values())
    cross_histogram = Counter(cross_quadratic.values())

    return {
        "case_id": f"scales-{'-'.join(map(str, scales))}-{mask}",
        "scales": list(scales),
        "mask": mask,
        "mask_definition": (
            "all T61 short-rectangle labels retained"
            if mask == "full"
            else "mu=2,c=1,Q0=1 replay mask: retain exactly q_(j,r)>10^n"
        ),
        "label_count_by_scale": {str(n): per_scale_labels[n] for n in scales},
        "record_count_by_scale": {str(n): per_scale_records[n] for n in scales},
        "common_label_count": len(common_labels),
        "record_count": len(records),
        "distinct_frequency_count": len(direct),
        "ordered_collision_count": collision_count,
        "gcd_generated_collision_count": gcd_generated_count,
        "ordered_off_diagonal_count": collision_count - len(records),
        "collision_categories": dict(sorted(categories.items())),
        "ordered_collision_count_by_scale_pair": {
            f"{n1},{n2}": by_scale_pair[(n1, n2)] for n1, n2 in sorted(by_scale_pair)
        },
        "max_fiber_size": max_multiplicity,
        "max_fiber_frequency": max_frequency,
        "max_fiber_witnesses_n_h_r_j": [list(x) for x in sorted(direct.get(max_frequency, []))],
        "direct_partition_sha256": digest(direct_partition),
        "reduced_partition_sha256": digest(reduced_partition),
        "quadratic_sparse_monomial_count": len(quadratic),
        "cross_scale_monomial_count": len(cross_quadratic),
        "quadratic_sha256": digest(encoded_quadratic),
        "cross_scale_quadratic_sha256": digest(encoded_cross),
        "coefficient_histogram": {
            str(value): coefficient_histogram[value] for value in sorted(coefficient_histogram)
        },
        "cross_scale_coefficient_histogram": {
            str(value): cross_histogram[value] for value in sorted(cross_histogram)
        },
        "rational_substitution_checks": substitutions,
        "metric_collision_factor_for_sum": "2",
        "metric_collision_factor_for_cesaro_average": frac(Fraction(2, len(scales) ** 2)),
        "fixed_pi_square_warning": (
            "2*Q/K^2 is only the equal-frequency difference-phase term; "
            "all nonzero difference phases and all sum phases remain"
        ),
        "checks": {
            "all_scale_endpoints": True,
            "direct_equals_ten_reduced_partition": True,
            "repunit_gcd_parameterization_sound_and_complete": True,
            "ordered_matrix_equals_fiber_polynomial": True,
            "cross_scale_weight_keys_are_n_h": True,
            "all_collision_categories_retained": True,
        },
    }


def t60_scale_audit(n: int) -> dict[str, object]:
    require(n >= 2, "T60 scale audit requires n>=2")
    length = sample_length(n)
    rectangle = sum(length - r for r in range(1, n))
    require(rectangle == (n - 1) * length - n * (n - 1) // 2,
            "rectangle formula failed")
    eligible = 0
    for r in range(1, n):
        for j in range(length - r):
            q = 10**j * repunit_factor(r)
            if q**LAMBDA_NUMERATOR <= 10 ** (EXPONENT_DENOMINATOR * n):
                eligible += 1
                require(
                    LAMBDA_NUMERATOR * (j + r - 1) <= EXPONENT_DENOMINATOR * n,
                    "coarse exponent implication failed",
                )
            else:
                # Increasing j multiplies q by ten, so no later start is eligible.
                break
    coarse = n * ((EXPONENT_DENOMINATOR * n) // LAMBDA_NUMERATOR + 2)
    require(eligible <= coarse, "eligible count exceeds coarse bound")
    endpoint_q = 9 * 10 ** (length - 2)
    require(endpoint_q**LAMBDA_NUMERATOR > 10 ** (EXPONENT_DENOMINATOR * n),
            "endpoint does not exhibit the pinned exponent loss")
    return {
        "n": n,
        "L_n": length,
        "H_n": bandwidth(n),
        "rectangle_size": rectangle,
        "exponent_eligible_positions": eligible,
        "coarse_bound": coarse,
        "endpoint_q": f"9*10^{length - 2}",
        "endpoint_exact_loss_check": "q^763>10^(125*n)",
    }


def full_rectangle_block_maximum_audit(block_start: int) -> dict[str, object]:
    require(block_start >= 2, "block maximum audit requires N>=2")
    n_star = 2 * block_start - 1
    length = sample_length(n_star)
    h_band = bandwidth(n_star)
    r_star = n_star - 1
    j_star = length - r_star - 1
    require(j_star >= 0, "maximum start is negative")
    q_star = 10**j_star * repunit_factor(r_star)
    m_star = (h_band - 1) * q_star
    # Directly enumerate only n and r maxima, not the enormous h,j rectangles.
    for n in range(block_start, 2 * block_start):
        local_length = sample_length(n)
        local_h = bandwidth(n) - 1
        for r in range(1, n):
            local_q = 10 ** (local_length - r - 1) * repunit_factor(r)
            require(local_h * local_q <= m_star, "claimed block frequency maximum failed")
    return {
        "N": block_start,
        "n_star": n_star,
        "L_star": length,
        "H_star": h_band,
        "r_star": r_star,
        "j_star": j_star,
        "h_star": h_band - 1,
        "q_star_factorization": (
            f"10^({length - 1})*(1-10^(-{r_star}))"
        ),
        "M_star": str(m_star),
        "log10_M_star_exact": (
            f"{length}+{2 * block_start}-2-log10(2)+"
            f"log10(1-2*10^(-{2 * block_start - 1}))+"
            f"log10(1-10^(-{2 * block_start - 2}))"
        ),
        "large_sieve_spacing_loss": "M_star^(763/125)",
        "status": "exact upper bound from the full unmasked rectangle",
    }


def abstract_obstruction(constant: int, scale_count: int) -> dict[str, object]:
    require(constant >= 0 and scale_count >= 1, "invalid obstruction parameters")
    scales = [constant + 2 + s for s in range(scale_count)]
    lengths = [2 * n for n in scales]
    short = [2 * (n - 1) * (length - n) for n, length in zip(scales, lengths)]
    total = [length + value for length, value in zip(lengths, short)]
    for n, length, short_value, total_value in zip(scales, lengths, short, total):
        require(short_value <= 2 * length * n, "retained short budget failed")
        require(total_value == n * length, "abstract total identity failed")
    sum_length = sum(lengths)
    sum_total = sum(total)
    ratio = Fraction(sum_total, sum_length)
    require(ratio > constant, "abstract averaged ratio does not beat constant")
    # Assign globally injective abstract frequencies and signs aligned with
    # abstract phases.  Products are +1 despite both coefficient signs.
    signs = [1 if index % 2 == 0 else -1 for index in range(scale_count)]
    phases = signs[:]
    require(all(sign * phase == 1 for sign, phase in zip(signs, phases)),
            "abstract phase alignment failed")
    require(len(set(range(1, scale_count + 1))) == scale_count,
            "abstract frequencies are not injective")
    return {
        "proposed_constant": constant,
        "scale_count": scale_count,
        "abstract_scales": scales,
        "sum_L": sum_length,
        "sum_total": sum_total,
        "weighted_average_ratio": frac(ratio),
        "globally_injective_abstract_frequencies": True,
        "both_coefficient_signs_present": scale_count >= 2,
        "coefficients_aligned_with_abstract_phases": True,
        "pi_generated": False,
    }


def build_report() -> dict[str, object]:
    root = Path(__file__).resolve().parent
    statement_hash = hashlib.sha256((root / STATEMENT_FILE).read_bytes()).hexdigest()
    t60_hash = hashlib.sha256((root / "T60_VAALER_IRRATIONALITY_FRONTIER.md").read_bytes()).hexdigest()
    require(statement_hash == STATEMENT_SHA256, "canonical statement hash mismatch")
    require(t60_hash == T60_NOTE_SHA256, "T60 inspection-copy hash mismatch")
    require(MU_NUMERATOR - EXPONENT_DENOMINATOR == LAMBDA_NUMERATOR,
            "mu-1 exponent arithmetic failed")

    domain_audits = [domain_audit(n) for n in (1, 2, 3, 4)]
    require([entry["full_label_count"] for entry in domain_audits] == [0, 9, 17, 294],
            "unexpected domain cardinalities")
    cases = [
        replay_cross_scale_case((2, 3), "full"),
        replay_cross_scale_case((2, 3), "mu2_c1_q1"),
    ]
    expected = {
        "scales-2-3-full": (8924, 7375, 14084, 6),
        "scales-2-3-mu2_c1_q1": (6331, 5289, 9779, 6),
    }
    for case in cases:
        record_count, distinct, collisions, max_fiber = expected[case["case_id"]]
        require(case["record_count"] == record_count, "unexpected aggregate record count")
        require(case["distinct_frequency_count"] == distinct, "unexpected frequency count")
        require(case["ordered_collision_count"] == collisions, "unexpected collision count")
        require(case["max_fiber_size"] == max_fiber, "unexpected maximum fiber")

    return {
        "schema_version": SCHEMA_VERSION,
        "label": "experiment",
        "canonical_statement_sha256": statement_hash,
        "source_pins": {
            "kernel_checked_not_vendored": SOURCE_PINS,
            "T60_proof_sketch_inspection_copy": t60_hash,
        },
        "definitions": {
            "scale_block": "N<=n<2N",
            "L_n": "10^(n//2)",
            "H_n": "10^n//2",
            "record": "(n,h,r,j)",
            "ranges": "1<=h<H_n; 0<r<n; r<L_n; 0<=j<L_n-r; residual mask",
            "frequency": "h*10^j*(10^r-1)",
            "weight_key": "(n,h)",
            "cesaro_normalization": "1/N over N scales",
        },
        "exact_cross_scale_expansion": (
            "A_N(pi)^2=(2/N^2)*sum_ordered w_i*w_j*"
            "[cos(2*pi*(Phi_i-Phi_j)*pi)+cos(2*pi*(Phi_i+Phi_j)*pi)]"
        ),
        "metric_collision_term": (
            "integral_0^1 A_N(x)^2 dx=(2/N^2)*"
            "sum_ordered_(Phi_i=Phi_j) w_i*w_j"
        ),
        "collision_classification": (
            "v10(h1)+j1=v10(h2)+j2 and primitive(h1)*(10^r1-1)="
            "primitive(h2)*(10^r2-1); n1,n2 affect membership and weights only"
        ),
        "domain_audits": domain_audits,
        "cross_scale_cases": cases,
        "pinned_irrationality_replay": {
            "mu": "888/125",
            "lambda": "763/125",
            "premise": (
                "exists Q0>=2, forall positive D>=Q0, forall P in Z, "
                "D^(-888/125)<abs(pi-P/D)"
            ),
            "distinct_difference_consequence": (
                "for d>=Q0, ||d*pi||>d^(-763/125)"
            ),
            "numeric_Q0_available": False,
            "Q0_ge_2_without_loss": True,
            "premise_reused_not_proved": True,
            "finite_scales": [t60_scale_audit(n) for n in (2, 3, 6)],
            "full_rectangle_block_upper_bounds": [
                full_rectangle_block_maximum_audit(n) for n in (2, 3)
            ],
        },
        "one_row_spacing_relaxed_dual_large_sieve_test": {
            "inequality": (
                "abs(sum_m b_m*e(m*pi))^2 <= delta_N^(-1)*sum_m abs(b_m)^2"
            ),
            "merged_coefficient": (
                "b_m=(1/N)*sum_(N<=n<2N, Phi=m) a_(H_n,h)/L_n"
            ),
            "eventual_spacing": "delta_N>M_star^(-763/125), with unknown onset",
            "exact_one_row_operator_constant": "card(F_N)",
            "spacing_relaxation": "card(F_N)<=delta_N^(-1)",
            "aggregate_fiber_bound": "R_N=sum_(n=N)^(2N-1)n(n-1)",
            "constant_preserving_bound": (
                "abs(A_N(pi))^2 < (196/(9*N^2))*M_star^(763/125)*R_N*"
                "sum_(n=N)^(2N-1)(n-1)*(H_n-1)/(H_n^2*L_n)"
            ),
            "loss_exponent": (
                "(763/125)*log10(M_star)-N-floor(N/2)+O(log N), "
                "dominated by (763/125)*10^(N-1)"
            ),
            "verdict": (
                "the spacing-relaxed consequence from the audited inputs is worse "
                "than the elementary O(N) normalized residual bound"
            ),
        },
        "abstract_scale_averaging_obstructions": [
            abstract_obstruction(1, 2),
            abstract_obstruction(2, 3),
            abstract_obstruction(4, 4),
        ],
        "uncontrolled_fixed_pi_terms": [
            "cross-scale exact collisions (zero difference)",
            "all nonzero difference-phase covariances",
            "all sum-phase covariances",
        ],
        "scope": {
            "proves_T82_claims": False,
            "proves_pinned_irrationality_estimate": False,
            "proves_fixed_pi_covariance_bound": False,
            "proves_C7": False,
            "proves_C2": False,
            "proves_C1": False,
        },
        "runtime_check_mode": "mandatory require checks remain active under python -O",
        "all_finite_replay_checks_passed": True,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--write", type=Path, help="write canonical JSON report")
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
