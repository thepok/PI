#!/usr/bin/env python3
"""Exact finite transfer checks for positive-density reduced precision.

This script checks actual integer encodings, the fixed low progression,
the determinant/carry transfer, and the explicit binary deletion. One
admissible high word is chosen so that its low progression really meets
the first exceptional binary class. Phase equidistribution and eventual
signs are proved in the note; they are not inferred from this audit.
"""

from fractions import Fraction
import argparse
import json
from pathlib import Path


TRANSITIONS = (
    (0, 0, 2, 3, 5), (0, 1, 2, 3, 5), (0, 1, 2, 4, 5),
    (0, 1, 3, 4, 5), (0, 2, 3, 4, 5), (0, 2, 3, 5, 5),
)
COST = (0, 1, 2, -1, 0, 1)
CARRY = (1, 0, 0, 1, 1, 0)
SCORE = (0, 0, 1, -1, 0, 0)
MODULUS, RESIDUE = 4096, 1981
DELTA = Fraction(1, 1 << 1043) / (1 - Fraction(1, 1 << 2048))


def trace(word, state=1):
    score = cost = carry = 0
    for digit in word:
        state = TRANSITIONS[state][digit]
        score += SCORE[state]
        cost += COST[state]
        carry += CARRY[state]
    return state, score, cost, carry


def value(word):
    answer = 0
    for digit in reversed(word):
        answer = 5 * answer + digit
    return answer


def digits(integer, length=None):
    result = []
    while integer:
        integer, digit = divmod(integer, 5)
        result.append(digit)
    if length is not None:
        assert len(result) <= length
        result += [0] * (length - len(result))
    return result


def floorlog5(integer):
    assert integer > 0
    result = 0
    while integer >= 5:
        integer //= 5
        result += 1
    return result


def low_length(length):
    k, power = 0, 1
    while power < length * length:
        k += 1
        power *= 5
    assert length * length <= power < 5 * length * length
    return k


def v5(integer):
    assert integer
    result = 0
    while integer % 5 == 0:
        result += 1
        integer //= 5
    return result


def factorial_v5(integer):
    result = 0
    while integer:
        integer //= 5
        result += integer
    return result


def casoratian_v5(n):
    polynomial = (559455 * n**4 + 3399916 * n**3 + 7651391 * n**2
                  + 7554302 * n + 2760952)
    f = factorial_v5
    return (2 + v5(polynomial) + f(2*n) + f(2*n+2) + 2*f(2*n+4)
            + f(n+1) - 2*f(n+2) - f(4*n+8) - f(3*n+5))


def carry_count(n, length):
    quotient, residue, power, result = 2*n, 0, 1, 0
    for _ in range(length):
        quotient, digit = divmod(quotient, 5)
        residue += digit * power
        power *= 5
        result += residue < (power + 1) // 2
    return result


def possible_a(y):
    cap = ((2*y).bit_length() - 1 + 7) // 32
    return range(33, cap + 1, 64)


def exceptional_a(m):
    return [a for a in possible_a(m)
            if (m+a) % (1 << (32*a-7)) == 0]


def progression_bad_positions(m0, count):
    """Exact union of exceptional positions in a finite low progression."""
    y = m0 + 8000*(count-1)
    assert m0 > 0 and m0 % 64 == 31
    bad = set()
    classes = []
    for a in possible_a(y):
        modulus = 1 << (32*a-13)
        residue = (-(m0+a)//64 * pow(125, -1, modulus)) % modulus
        positions = list(range(residue, count, modulus))
        assert len(positions) <= Fraction(count, modulus) + 1
        for position in positions:
            assert a in exceptional_a(m0 + 8000*position)
        bad.update(positions)
        classes.append({"a": a, "modulus_exponent": 32*a-13,
                        "positions": positions})
    assert len(bad) <= DELTA*count + 1 + (2*y).bit_length()-1
    return bad, classes


def run():
    counts = {"high_pairs": 0, "fixed_low_progressions": 0,
              "full_triple_transfers": 0, "direct_witness_memberships": 0,
              "actual_admissible_exception_witnesses": 0}
    rows = []
    seen = set()

    def check_pair(length, reset, high, witness_n=None):
        k, N = low_length(length), len(high)
        assert N == length-k-7 and reset in (0, 4)
        raw = high if reset == 0 else [4-a for a in high]
        raw_score = trace(raw, state=0)[1]
        assert (raw_score > 0) == (reset == 0)
        assert 16*raw_score**2 >= N
        high_score = trace(high, state=0 if reset == 0 else 5)[1]
        assert high_score == abs(raw_score)
        n0 = 36 + 125*(5**k*reset + 5**(k+1)*value(high)
                       + 2*5**(k+N+2) + 5**(k+N+3))
        first = (RESIDUE-n0)*pow(125, -1, MODULUS) % MODULUS
        count = 1 + (5**k-1-first)//MODULUS
        assert count > 0
        assert 5**k//MODULUS <= count <= 5**k//MODULUS+1
        first_n = n0+125*first
        m0 = (first_n+3)//64
        assert first_n == 64*m0-3 and m0 % 64 == 31
        assert 125*MODULUS//64 == 8000
        bad, classes = progression_bad_positions(m0, count)
        positions = {0, count//2, count-1}
        if witness_n is not None:
            assert witness_n >= first_n
            position, remainder = divmod(witness_n-first_n, 125*MODULUS)
            assert remainder == 0 and 0 <= position < count
            assert position in bad
            positions.add(position)
            for u in range(count):
                assert (u in bad) == bool(exceptional_a(m0+8000*u))
                counts["direct_witness_memberships"] += 1
            counts["actual_admissible_exception_witnesses"] += 1

        row = {"L": length, "k": k, "N": N, "reset": reset,
               "raw_score": raw_score, "low_AP_first": first,
               "low_AP_count": count, "exception_classes": classes,
               "deleted_positions": sorted(bad), "samples": []}
        for position in sorted(positions):
            U = first+MODULUS*position
            n = n0+125*U
            assert n not in seen
            seen.add(n)
            appended = digits(U, k) + [reset] + high + [0, 2, 1]
            assert n == 36+125*value(appended)
            assert len(appended) == length-3
            state, score, cost, carry = trace(appended)
            assert state == 1
            assert score == cost+carry-(length-3)
            assert score >= abs(raw_score)-k+1
            assert length-carry >= score+3
            assert 36+125*U+2 < 125*5**k
            assert 5**length < 4*n and 3*n < 5**length
            assert [floorlog5(4*(n+r)) for r in range(3)] == [length]*3
            assert [carry_count(n+r, length) for r in range(3)] == [carry+1, carry, carry+2]
            assert casoratian_v5(n) == -1-cost
            shallow = floorlog5(2*length+1)
            assert length-carry >= max(1, shallow)
            third_bound = 1-length+carry
            assert casoratian_v5(n)-third_bound == 1-score
            assert (n+3)//64 == m0+8000*position
            m = (n+3)//64
            assert m % 64 == 31 and n % MODULUS == RESIDUE
            assert bool(exceptional_a(m)) == (position in bad)
            binary_weight = (3*m).bit_count()
            for r, order in enumerate((binary_weight+2, binary_weight, binary_weight)):
                assert order <= (n+r).bit_length()-1
            counts["full_triple_transfers"] += 1
            row["samples"].append({"n": n, "U": U,
                "position": position, "total_score": score,
                "casoratian_v5": -1-cost,
                "common_shifted_column_bound": third_bound,
                "forced_reduced_five_depth": max(0, score-1),
                "deleted_by_binary_sieve": position in bad,
                "binary_weight": binary_weight})
        rows.append(row)
        counts["high_pairs"] += 1
        counts["fixed_low_progressions"] += 1

    for length in (64, 256, 1024, 4096):
        N = length-low_length(length)-7
        raw_words = ([2]*N, [3]+[2]*(N-1),
                     ([2, 1]*((N+1)//2))[:N],
                     ([3, 2]*((N+1)//2))[:N])
        for raw in raw_words:
            raw_score = trace(raw, state=0)[1]
            reset = 0 if raw_score > 0 else 4
            high = raw if reset == 0 else [4-a for a in raw]
            check_pair(length, reset, high)

    # This explicit index is simultaneously in the literal digit family
    # and the first sufficient deletion class m == -33 mod 2^1049.
    witness = (1 << 1055)*308632-2115
    word = digits(witness)
    length = len(word)
    k = low_length(length)
    assert length == 463 and k == 8
    assert word[:3] == [1, 2, 1] and word[-3:] == [0, 2, 1]
    reset, high = word[k+3], word[k+4:-3]
    assert reset == 4 and trace(high, state=5)[1] == 38
    assert exceptional_a((witness+3)//64) == [33]
    check_pair(length, reset, high, witness_n=witness)

    assert DELTA < Fraction(1, 1 << 1042)
    count_constant = Fraction(1, 192*MODULUS*5**7)*Fraction(3, 10)
    assert count_constant == Fraction(1, (1 << 19)*5**8)
    assert Fraction(2, 5)-DELTA > Fraction(1, 3)
    return {"schema": "salikhov-positive-density-precision-v1",
            "status": "passed", "finite_evidence_only": True,
            "counts": counts, "distinct_sample_bases": len(seen),
            "fixed_modulus": MODULUS, "fixed_base_residue": RESIDUE,
            "conditional_deleted_density_bound": "2^(-1042)",
            "eventual_index_count_constant": "1/(2^19*5^8)",
            "actual_exception_witness_multiple": 308632,
            "grids": rows,
            "scope": "Exact finite transfer arithmetic, including an admissible high word whose low progression meets the first exceptional class. No asymptotic sign, phase rate, or density onset is inferred from the finite grids."}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json", type=Path)
    args = parser.parse_args()
    result = run()
    path = args.json or Path(__file__).with_name("certificate.json")
    path.write_text(json.dumps(result, indent=2, sort_keys=True)+"\n")
    print(json.dumps({"status": result["status"], **result["counts"],
                      "certificate": str(path)}, sort_keys=True))


if __name__ == "__main__":
    main()
