#!/usr/bin/env python3
"""Exact finite replay for T85's T61 grouping and square-bound constants.

Finite enumeration is an experiment, not a proof of the universal theorem in
the companion note. All checks remain active under ``python3 -O``.
"""

from __future__ import annotations

from collections import Counter, defaultdict
from fractions import Fraction
from math import gcd
import hashlib
import json


SCHEMA_VERSION = "t85-grouped-square-replay-v1"
STATEMENT_FILE = "pi-positive-decimal-factor-entropy.txt"
STATEMENT_SHA256 = "a70dd741b27595aeb3dfc902b5e201579fed6bae24e2191f58c5ac64a22939e6"
SOURCE_PINS = {
    "T25T25ResidualPairReduction.lean": "86639d8f8adbb5cf54a474fe89760cbeecd243e9f0bcb3768a16a23dab3ee88c",
    "T56LagSectorAudit.lean": "41e8ec69c4a113592b8f1de1dc5e02e815726c5a7e541ac7fd57afc6b181f1cc",
    "T58TriangularFejerAudit.lean": "04b3808f208db000284cf369467f4d2ffb907b1af44b30fcada8451b8503016d",
    "T61VaalerAnalytic.lean": "61bf75193b6581ef626fc2b061ea6ba39e4fc164ac9e49b3a0820528dc839993",
}

Record = tuple[int, int, int, int]  # (n,h,r,j)


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def sample_length(n: int) -> int:
    return 10 ** (n // 2)


def bandwidth(n: int) -> int:
    return 10**n // 2


def repunit(r: int) -> int:
    return 10**r - 1


def denominator(j: int, r: int) -> int:
    return 10**j * repunit(r)


def frequency(record: Record) -> int:
    _n, h, r, j = record
    return h * denominator(j, r)


def ten_reduce(value: int) -> tuple[int, int]:
    require(value > 0, "ten reduction requires a positive integer")
    valuation = 0
    while value % 10 == 0:
        value //= 10
        valuation += 1
    return valuation, value


def reduced_key(record: Record) -> tuple[int, int]:
    _n, h, r, j = record
    valuation, primitive = ten_reduce(h)
    return valuation + j, primitive * repunit(r)


def is_excluded_mu2_c1(n: int, j: int, r: int, q0: int) -> bool:
    """Literal T61/T25 mask at mu=2,c=1, without floating arithmetic."""
    value = denominator(j, r)
    # 10^-n <= value*(1/value^2) iff value <= 10^n.
    return q0 <= value and value <= 10**n


def residual_labels(n: int, q0: int) -> list[tuple[int, int]]:
    length = sample_length(n)
    return [
        (r, j)
        for r in range(1, n)
        if r < length
        for j in range(length - r)
        if not is_excluded_mu2_c1(n, j, r, q0)
    ]


def records(n: int, q0: int) -> list[Record]:
    return [
        (n, h, r, j)
        for h in range(1, bandwidth(n))
        for r, j in residual_labels(n, q0)
    ]


def gcd_parameter_holds(left: Record, right: Record) -> bool:
    _n1, h1, r1, j1 = left
    _n2, h2, r2, j2 = right
    v1, u1 = ten_reduce(h1)
    v2, u2 = ten_reduce(h2)
    if v1 + j1 != v2 + j2:
        return False
    common = 10 ** gcd(r1, r2) - 1
    u_factor = repunit(r1) // common
    v_factor = repunit(r2) // common
    require(gcd(u_factor, v_factor) == 1, "repunit cofactors are not coprime")
    if u1 % v_factor or u2 % u_factor:
        return False
    t1 = u1 // v_factor
    t2 = u2 // u_factor
    return t1 == t2 and t1 > 0 and t1 % 10 != 0


def canonical_partition(groups: dict[object, list[Record]]) -> list[list[list[int]]]:
    return sorted(sorted([list(record) for record in fiber]) for fiber in groups.values())


def canonical_json_bytes(value: object) -> bytes:
    return (json.dumps(value, sort_keys=True, indent=2) + "\n").encode("ascii")


def digest(value: object) -> str:
    return hashlib.sha256(canonical_json_bytes(value)).hexdigest()


def formal_weight(n: int, h: int) -> Fraction:
    """A deterministic signed rational stand-in satisfying |a|<3/H."""
    return Fraction((h % 7) - 3, 10 * bandwidth(n))


def audit_case(scales: tuple[int, ...], q0: int) -> dict[str, object]:
    all_records = [record for n in scales for record in records(n, q0)]
    direct: dict[int, list[Record]] = defaultdict(list)
    reduced: dict[tuple[int, int], list[Record]] = defaultdict(list)
    for record in all_records:
        direct[frequency(record)].append(record)
        reduced[reduced_key(record)].append(record)

    require(
        canonical_partition(direct) == canonical_partition(reduced),
        "direct and ten-reduced partitions differ",
    )

    ordered_collisions = 0
    categories: Counter[str] = Counter()
    for fiber in direct.values():
        ordered_collisions += len(fiber) ** 2
        for left in fiber:
            for right in fiber:
                require(frequency(left) == frequency(right), "fiber contains unequal frequencies")
                require(gcd_parameter_holds(left, right), "gcd parameterization missed collision")
                if left == right:
                    categories["same_scale_diagonal"] += 1
                elif left[0] == right[0]:
                    categories["same_scale_nontrivial"] += 1
                elif left[1:] == right[1:]:
                    categories["cross_scale_literal_duplicate"] += 1
                else:
                    categories["cross_scale_nontrivial"] += 1
    require(sum(categories.values()) == ordered_collisions, "collision categories incomplete")

    # Independently regenerate all ordered pairs allowed by (4.2)-(4.4).
    # For fixed decimal valuation s and ordered lags, one primitive part
    # determines the other, so unrelated record pairs are never scanned.
    signatures: dict[int, Counter[tuple[int, int]]] = defaultdict(Counter)
    for n, h, r, j in all_records:
        _ = n
        valuation, primitive = ten_reduce(h)
        signatures[valuation + j][(primitive, r)] += 1
    gcd_generated_collisions = 0
    for by_primitive_lag in signatures.values():
        lags = sorted({r for _primitive, r in by_primitive_lag})
        for r1 in lags:
            for r2 in lags:
                common = 10 ** gcd(r1, r2) - 1
                u_factor = repunit(r1) // common
                v_factor = repunit(r2) // common
                require(gcd(u_factor, v_factor) == 1, "generated cofactors not coprime")
                for (primitive1, lag1), count1 in by_primitive_lag.items():
                    if lag1 != r1 or primitive1 % v_factor:
                        continue
                    parameter = primitive1 // v_factor
                    if parameter <= 0 or parameter % 10 == 0:
                        continue
                    primitive2 = u_factor * parameter
                    count2 = by_primitive_lag.get((primitive2, r2), 0)
                    if count2:
                        require(
                            primitive1 * repunit(r1) == primitive2 * repunit(r2),
                            "gcd parameters generated unequal frequencies",
                        )
                        gcd_generated_collisions += count1 * count2
    require(
        gcd_generated_collisions == ordered_collisions,
        "gcd-generated and direct ordered collision counts differ",
    )

    # Symbolic grouping records the coefficient of every formal variable a_n(h).
    symbolic: dict[tuple[int, int], Counter[int]] = defaultdict(Counter)
    for q, fiber in direct.items():
        for n, h, _r, _j in fiber:
            symbolic[(n, q)][h] += Fraction(2, sample_length(n))
    for n in scales:
        multiplicities: Counter[tuple[int, int]] = Counter(
            (frequency(record), record[1]) for record in records(n, q0)
        )
        for (q, h), count in multiplicities.items():
            require(
                symbolic[(n, q)][h] == Fraction(2 * count, sample_length(n)),
                "2/L_n symbolic grouping failed",
            )

    grouped_coefficients: dict[tuple[int, int], Fraction] = {}
    for (n, q), by_h in symbolic.items():
        grouped_coefficients[(n, q)] = sum(
            (coefficient * formal_weight(n, h) for h, coefficient in by_h.items()),
            Fraction(0),
        )

    grouped_totals: dict[int, Fraction] = defaultdict(Fraction)
    for (n, q), value in grouped_coefficients.items():
        grouped_totals[q] += value
    grouped_d = sum((value * value for value in grouped_totals.values()), Fraction(0))

    pair_d = Fraction(0)
    for fiber in direct.values():
        for left in fiber:
            for right in fiber:
                n1, h1, _r1, _j1 = left
                n2, h2, _r2, _j2 = right
                pair_d += (
                    Fraction(4, sample_length(n1) * sample_length(n2))
                    * formal_weight(n1, h1)
                    * formal_weight(n2, h2)
                )
    require(grouped_d == pair_d, "grouped D_N and ordered-pair expansion differ")

    one_scale = []
    for n in scales:
        scale_records = records(n, q0)
        scale_groups: dict[int, list[Record]] = defaultdict(list)
        for record in scale_records:
            scale_groups[frequency(record)].append(record)
        max_fiber = max((len(fiber) for fiber in scale_groups.values()), default=0)
        label_count = len(residual_labels(n, q0))
        tuple_bound = (bandwidth(n) - 1) * (n - 1) * sample_length(n)
        require(label_count <= (n - 1) * sample_length(n), "label bound failed")
        require(len(scale_records) <= tuple_bound, "tuple bound failed")
        require(max_fiber <= n * (n - 1), "frequency fiber bound failed")

        energy = sum(
            (grouped_coefficients.get((n, q), Fraction(0)) ** 2 for q in scale_groups),
            Fraction(0),
        )
        theorem_bound = Fraction(36 * n**3, bandwidth(n) * sample_length(n))
        require(energy < theorem_bound, "finite energy exceeds universal theorem bound")
        one_scale.append(
            {
                "n": n,
                "labels": label_count,
                "records": len(scale_records),
                "max_fiber": max_fiber,
                "fiber_bound": n * (n - 1),
                "formal_energy": str(energy),
                "theorem_bound": str(theorem_bound),
            }
        )

    encoded_symbolic = [
        [n, str(q), [[h, str(value)] for h, value in sorted(by_h.items())]]
        for (n, q), by_h in sorted(symbolic.items())
    ]
    return {
        "scales": list(scales),
        "q0": str(q0),
        "mask": "T61 ArithmeticExcluded with mu=2,c=1",
        "records": len(all_records),
        "distinct_frequencies": len(direct),
        "ordered_collision_count": ordered_collisions,
        "gcd_generated_collision_count": gcd_generated_collisions,
        "collision_categories": dict(sorted(categories.items())),
        "direct_partition_sha256": digest(canonical_partition(direct)),
        "reduced_partition_sha256": digest(canonical_partition(reduced)),
        "symbolic_grouping_sha256": digest(encoded_symbolic),
        "formal_grouped_D": str(grouped_d),
        "formal_pair_expansion_D": str(pair_d),
        "one_scale": one_scale,
        "checks": {
            "literal_ranges_and_mask": True,
            "B_normalization_is_2_over_L_n": True,
            "direct_equals_ten_reduced_partition": True,
            "repunit_gcd_parameterization_sound_and_complete": True,
            "ordered_pair_D_identity": True,
            "one_scale_bounds": True,
        },
    }


def constant_audit() -> dict[str, object]:
    sum_from_two = Fraction(43, 160)
    norm_bound = 24 * sum_from_two
    square_bound = norm_bound**2
    require(Fraction(15, 32) - Fraction(1, 5) == sum_from_two, "series tail failed")
    require(norm_bound == Fraction(129, 20), "norm constant failed")
    require(square_bound == Fraction(16641, 400), "square constant failed")
    require(square_bound < 42, "explicit constant 42 failed")
    require(10 < 2**4, "10^(1/4)<2 certificate failed")
    require(5**4 < 10**3, "10^(-3/4)<1/5 certificate failed")
    return {
        "sum_n_ge_2_n2_over_5n": str(sum_from_two),
        "norm_bound": str(norm_bound),
        "square_bound": str(square_bound),
        "linear_constant": 42,
        "fourth_power_certificates": {"10<2^4": True, "5^4<10^3": True},
    }


def build_report() -> dict[str, object]:
    with open(STATEMENT_FILE, "rb") as handle:
        statement_digest = hashlib.sha256(handle.read()).hexdigest()
    require(statement_digest == STATEMENT_SHA256, "canonical statement hash mismatch")

    full_q0 = 10**100
    return {
        "schema_version": SCHEMA_VERSION,
        "label": "experiment",
        "canonical_statement_sha256": statement_digest,
        "source_pins": SOURCE_PINS,
        "definitions": {
            "L_n": "10^(n//2)",
            "H_n": "10^n//2",
            "tuple_ranges": "1<=h<H_n; 0<r<n; r<L_n; 0<=j<L_n-r; exact mask",
            "frequency": "h*10^j*(10^r-1)",
            "B_n(q)": "(2/L_n)*sum of literal signed a_n(h) over the exact fiber",
            "B_0(q)": "0",
            "D_N": "sum_q abs(sum_(0<=n<=N) B_n(q))^2 over finite union support",
        },
        "grouping_cases": [audit_case((2, 3), full_q0), audit_case((2, 3), 1)],
        "constant_audit": constant_audit(),
        "universal_claim_source": "Steps 1-6 of T85_GROUPED_SQUARE_BOUND.md",
        "finite_replay_is_not_universal_proof": True,
        "scope": {
            "uses_T83_as_premise": False,
            "uses_T84_as_premise": False,
            "proves_fixed_pi_estimate": False,
            "proves_C7": False,
            "proves_C2": False,
            "proves_C1": False,
        },
        "all_finite_replay_checks_passed": True,
    }


if __name__ == "__main__":
    print(json.dumps(build_report(), sort_keys=True, indent=2))
