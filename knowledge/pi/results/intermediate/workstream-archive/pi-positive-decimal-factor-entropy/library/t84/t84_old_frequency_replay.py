#!/usr/bin/env python3
"""Exact finite replay for T84 grouping, collisions, and counterfamily.

This is a finite experiment. Universal divergence is proved in the companion
note, not inferred from these examples. All mandatory checks remain active
under ``python3 -O``.
"""

from __future__ import annotations

from collections import Counter, defaultdict
from fractions import Fraction
from math import gcd
import hashlib
import json


SCHEMA_VERSION = "t84-old-frequency-replay-v1"
STATEMENT_FILE = "pi-positive-decimal-factor-entropy.txt"
STATEMENT_SHA256 = "a70dd741b27595aeb3dfc902b5e201579fed6bae24e2191f58c5ac64a22939e6"
SOURCE_PINS = {
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


def frequency(h: int, j: int, r: int) -> int:
    return h * denominator(j, r)


def ten_reduce(value: int) -> tuple[int, int]:
    require(value > 0, "ten reduction requires a positive integer")
    valuation = 0
    while value % 10 == 0:
        valuation += 1
        value //= 10
    return valuation, value


def is_excluded_mu2_c1(n: int, j: int, r: int, q0: int) -> bool:
    """Exact T61 mask for mu=2 and c=1, with no floating arithmetic."""
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


def record_frequency(record: Record) -> int:
    _n, h, r, j = record
    return frequency(h, j, r)


def reduced_key(record: Record) -> tuple[int, int]:
    _n, h, r, j = record
    valuation, primitive = ten_reduce(h)
    return valuation + j, primitive * repunit(r)


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
    require(gcd(u_factor, v_factor) == 1, "repunit cofactors not coprime")
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


def formal_grouping(scales: tuple[int, ...], q0: int) -> dict[str, object]:
    all_records = [record for n in scales for record in records(n, q0)]
    direct: dict[int, list[Record]] = defaultdict(list)
    reduced: dict[tuple[int, int], list[Record]] = defaultdict(list)
    ungrouped: Counter[tuple[int, int, int]] = Counter()
    for record in all_records:
        q = record_frequency(record)
        direct[q].append(record)
        reduced[reduced_key(record)].append(record)
        n, h, _r, _j = record
        ungrouped[(q, n, h)] += 1

    require(canonical_partition(direct) == canonical_partition(reduced),
            "direct and ten-reduced partitions differ")

    grouped_formal: dict[tuple[int, int], Counter[int]] = defaultdict(Counter)
    for q, fiber in direct.items():
        for n, h, _r, _j in fiber:
            grouped_formal[(n, q)][h] += Fraction(2, sample_length(n))

    for (q, n, h), multiplicity in ungrouped.items():
        expected = Fraction(2 * multiplicity, sample_length(n))
        require(grouped_formal[(n, q)][h] == expected,
                "formal B_n coefficient grouping failed")
    require(sum(len(fiber) for fiber in direct.values()) == len(all_records),
            "grouping lost a tuple")

    ordered_collision_count = sum(len(fiber) ** 2 for fiber in direct.values())
    categories = Counter()
    for fiber in direct.values():
        for left in fiber:
            for right in fiber:
                require(gcd_parameter_holds(left, right),
                        "direct collision missed by gcd parameterization")
                require(record_frequency(left) == record_frequency(right),
                        "gcd parameterization accepted a noncollision")
                n1, h1, r1, j1 = left
                n2, h2, r2, j2 = right
                if left == right:
                    categories["same_scale_diagonal"] += 1
                elif n1 == n2:
                    categories["same_scale_nontrivial"] += 1
                elif (h1, r1, j1) == (h2, r2, j2):
                    categories["cross_scale_literal_duplicate"] += 1
                else:
                    categories["cross_scale_nontrivial"] += 1
    require(sum(categories.values()) == ordered_collision_count,
            "ordered collision categories are incomplete")

    # Independently generate every ordered pair allowed by the repunit-gcd
    # parameters. A record's relevant signature is (s,u,r), where s=v10(h)+j
    # and u is the ten-primitive part of h. For fixed ordered lags, (4.2)
    # determines u2 from u1, so this avoids scanning unrelated record pairs.
    signature_groups: dict[int, Counter[tuple[int, int]]] = defaultdict(Counter)
    for n, h, r, j in all_records:
        valuation, primitive = ten_reduce(h)
        signature_groups[valuation + j][(primitive, r)] += 1
    gcd_generated_collision_count = 0
    for signatures in signature_groups.values():
        lags = sorted({r for _primitive, r in signatures})
        for r1 in lags:
            for r2 in lags:
                common = 10 ** gcd(r1, r2) - 1
                u_factor = repunit(r1) // common
                v_factor = repunit(r2) // common
                require(gcd(u_factor, v_factor) == 1,
                        "generated repunit cofactors not coprime")
                for (primitive1, lag1), count1 in signatures.items():
                    if lag1 != r1 or primitive1 % v_factor:
                        continue
                    parameter = primitive1 // v_factor
                    if parameter <= 0 or parameter % 10 == 0:
                        continue
                    primitive2 = u_factor * parameter
                    count2 = signatures.get((primitive2, r2), 0)
                    if count2:
                        require(primitive1 * repunit(r1) == primitive2 * repunit(r2),
                                "gcd parameters generated unequal reduced frequencies")
                        gcd_generated_collision_count += count1 * count2
    require(gcd_generated_collision_count == ordered_collision_count,
            "gcd-generated and direct ordered collision counts differ")

    encoded_grouping = [
        [
            n,
            str(q),
            [[h, str(value)] for h, value in sorted(grouped_formal[(n, q)].items())],
        ]
        for n, q in sorted(grouped_formal)
    ]
    old_at_last = set(direct)
    last = scales[-1]
    last_frequencies = {record_frequency(record) for record in records(last, q0)}
    earlier_frequencies = {
        record_frequency(record)
        for n in scales[:-1]
        for record in records(n, q0)
    }
    old_at_last = last_frequencies & earlier_frequencies
    return {
        "scales": list(scales),
        "q0": str(q0),
        "mask": "T61 ArithmeticExcluded with mu=2,c=1",
        "records": len(all_records),
        "distinct_frequencies": len(direct),
        "old_frequencies_at_last_scale": len(old_at_last),
        "ordered_collision_count": ordered_collision_count,
        "gcd_generated_collision_count": gcd_generated_collision_count,
        "collision_categories": dict(sorted(categories.items())),
        "direct_partition_sha256": digest(canonical_partition(direct)),
        "reduced_partition_sha256": digest(canonical_partition(reduced)),
        "formal_grouping_sha256": digest(encoded_grouping),
        "checks": {
            "all_tuples_grouped_once": True,
            "B_normalization_is_2_over_L_n": True,
            "direct_equals_ten_reduced_partition": True,
            "repunit_gcd_parameterization_sound_and_complete": True,
            "ordered_fiber_square_identity": True,
            "old_frequency_intersection_replayed": True,
        },
    }


def all_representations(n: int, q: int, q0: int) -> list[tuple[int, int, int]]:
    """Exhaust every legal (h,r,j) representation without scanning all h."""
    length = sample_length(n)
    h_band = bandwidth(n)
    q_valuation, _primitive = ten_reduce(q)
    result: list[tuple[int, int, int]] = []
    for r in range(1, n):
        if r >= length:
            continue
        for j in range(min(q_valuation, length - r - 1) + 1):
            value = denominator(j, r)
            if q % value:
                continue
            h = q // value
            if 1 <= h < h_band and not is_excluded_mu2_c1(n, j, r, q0):
                result.append((h, r, j))
    return sorted(result)


def admissible_multipliers(n: int) -> list[int]:
    a = bandwidth(n - 1) // 10
    return [
        h
        for h in range(a, 2 * a)
        if h % 10 != 0
        and all(h % (repunit(r) // 9) != 0 for r in range(2, n))
    ]


def counterfamily_case(n: int, q0: int = 1) -> dict[str, object]:
    require(n >= 4, "finite counterfamily audit starts at n=4")
    a = bandwidth(n - 1) // 10
    multipliers = admissible_multipliers(n)
    starts = list(range(sample_length(n - 1) // 2, sample_length(n - 1) - 1))
    require(len(multipliers) >= a // 2, "multiplier lower count failed")
    require(len(starts) >= sample_length(n - 1) // 4, "start lower count failed")

    seen: set[int] = set()
    for h in multipliers:
        for start in starts:
            q = 9 * h * 10**start
            require(q not in seen, "selected frequencies are not distinct")
            seen.add(q)
            current = all_representations(n, q, q0)
            earlier = all_representations(n - 1, q, q0)
            require(current == [(h, 1, start), (10 * h, 1, start - 1)],
                    "current selected fiber is not exactly the predicted pair")
            require(earlier == [(h, 1, start)],
                    "earlier selected fiber is not the predicted literal duplicate")
            require(Fraction(h, bandwidth(n)) < Fraction(1, 5),
                    "first current coefficient is outside positive zone")
            require(Fraction(10 * h, bandwidth(n)) < Fraction(1, 5),
                    "second current coefficient is outside positive zone")

    count = len(multipliers) * len(starts)
    lower_mass = Fraction(16 * count, 5 * sample_length(n) * bandwidth(n))
    upper_mass = Fraction(28 * count, 3 * sample_length(n) * bandwidth(n))
    parity_lower = Fraction(1, 2500 if n % 2 == 0 else 250)
    require(lower_mass >= parity_lower, "finite family misses universal lower constant")
    require(upper_mass <= Fraction(7, 150), "finite family upper constant failed")
    return {
        "n": n,
        "L_previous": sample_length(n - 1),
        "L_current": sample_length(n),
        "H_previous": bandwidth(n - 1),
        "H_current": bandwidth(n),
        "A_n": a,
        "multiplier_count": len(multipliers),
        "start_count": len(starts),
        "selected_distinct_old_frequencies": count,
        "fiber_shape": "current=[(h,1,J),(10h,1,J-1)]; previous=[(h,1,J)]",
        "proved_symbolic_lower_mass": str(lower_mass),
        "proved_symbolic_upper_mass": str(upper_mass),
        "parity_uniform_lower_bound": str(parity_lower),
        "all_selected_fibers_exhausted": True,
    }


def build_report() -> dict[str, object]:
    with open(STATEMENT_FILE, "rb") as handle:
        statement_digest = hashlib.sha256(handle.read()).hexdigest()
    require(statement_digest == STATEMENT_SHA256, "canonical statement hash mismatch")

    # Q0=1 gives the nontrivial exact mask D>10^n. The huge Q0 makes the
    # first mask conjunct false throughout these finite scales, replaying the
    # complete unmasked rectangle using the literal T61 predicate.
    full_q0 = 10**100
    grouping_cases = [
        formal_grouping((2, 3), full_q0),
        formal_grouping((2, 3), 1),
    ]
    family_cases = [counterfamily_case(n) for n in (4, 5)]
    return {
        "schema_version": SCHEMA_VERSION,
        "label": "experiment",
        "canonical_statement_sha256": statement_digest,
        "source_pins": SOURCE_PINS,
        "definitions": {
            "L_n": "10^(n//2)",
            "H_n": "10^n//2",
            "tuple_ranges": "1<=h<H_n; 0<r<n; 0<=j<L_n-r; exact residual mask",
            "frequency": "h*10^j*(10^r-1)",
            "B_n(q)": "(2/L_n)*sum of signed a_n(h) over the frequency fiber",
            "Old_n": "current tuple frequencies intersect all earlier tuple frequencies",
            "V_n": "sum over Old_n of abs(B_n(q))",
        },
        "grouping_cases": grouping_cases,
        "counterfamily_cases": family_cases,
        "universal_claim_source": "numbered proof in T84_OLD_FREQUENCY_MASS.md",
        "finite_replay_is_not_universal_proof": True,
        "scope": {
            "proves_fixed_pi_estimate": False,
            "proves_C7": False,
            "proves_C2": False,
            "proves_C1": False,
            "uses_T83_as_premise": False,
        },
        "all_finite_replay_checks_passed": True,
    }


if __name__ == "__main__":
    print(json.dumps(build_report(), sort_keys=True, indent=2))
