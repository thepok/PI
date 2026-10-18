#!/usr/bin/env python3
"""Exact finite audit of the Salikhov score martingale and return injection.

Uses rational conditional moments and complete integer state/score counts.
The accompanying note proves the estimates for every positive length.
"""
from __future__ import annotations

import argparse
from collections import defaultdict
from fractions import Fraction as F
from itertools import product
import json
from pathlib import Path


SCORE = (0, 0, 1, -1, 0, 0)
CARRY = (1, 0, 0, 1, 1, 0)
ENDPOINTS = (F(0), F(1, 4), F(1, 3), F(1, 2),
             F(2, 3), F(3, 4), F(1))
TRANSITIONS = (
    (0, 0, 2, 3, 5), (0, 1, 2, 3, 5),
    (0, 1, 2, 4, 5), (0, 1, 3, 4, 5),
    (0, 2, 3, 4, 5), (0, 2, 3, 5, 5),
)


def interval_transition_certificate() -> dict:
    """Certify each full open-interval image under x -> (x+digit)/5."""
    rows = []
    for state, targets in enumerate(TRANSITIONS):
        assert SCORE[state] <= 1-CARRY[state]
        left, right = ENDPOINTS[state:state+2]
        for digit, target in enumerate(targets):
            image_left, image_right = (left+digit)/5, (right+digit)/5
            assert (ENDPOINTS[target] <= image_left < image_right
                    <= ENDPOINTS[target+1])
            rows.append({"state": state, "digit": digit, "target": target,
                         "image_open_interval": [str(image_left), str(image_right)]})
    return {"rational_interval_inclusions": len(rows), "rows": rows,
            "score_le_one_minus_carry_in_all_states": True}


def trace(digits, start: int = 0) -> tuple[int, int]:
    state, score = start, 0
    for digit in digits:
        state = TRANSITIONS[state][digit]
        score += SCORE[state]
    return state, score


def block_integer(digits) -> int:
    value, power = 0, 1
    for digit in digits:
        value += power*digit
        power *= 5
    return value


def conditional_moment_certificate() -> dict:
    rows = []
    for state, targets in enumerate(TRANSITIONS):
        z = SCORE[state]
        assert sum(SCORE[target] for target in targets) == z
        increments = [F(5*SCORE[target]-z, 4) for target in targets]
        moments = [sum(value**k for value in increments)/5 for k in range(1, 5)]
        expected = [F(0), F(5, 8) if z == 0 else F(1, 4),
                    F(3*z, 16), F(125, 128) if z == 0 else F(13, 64)]
        assert moments == expected
        assert max(abs(value) for value in increments) <= F(5, 4)
        assert sum(SCORE[target] != 0 for target in targets) == (2 if z == 0 else 1)
        assert TRANSITIONS[state][0] == 0 and TRANSITIONS[state][4] == 5
        assert trace((0, 2, 1), start=state) == (1, 1)
        for digit in range(5):
            assert TRANSITIONS[5-state][4-digit] == 5-TRANSITIONS[state][digit]
        assert SCORE[5-state] == -z
        rows.append({"state": state, "score": z,
                     "increments": [str(value) for value in increments],
                     "conditional_moments_1_through_4": [str(value) for value in moments]})
    return {"exact_transition_rows": 6, "rows": rows,
            "universal_return_word": [0, 2, 1]}


def exact_path_moment_certificate() -> dict:
    counts = {(0, 0): 1}
    rows = []
    for N in range(1, 101):
        updated = defaultdict(int)
        for (state, score), count in counts.items():
            for target in TRANSITIONS[state]:
                updated[target, score+SCORE[target]] += count
        counts = dict(updated)
        total = 5**N
        assert sum(counts.values()) == total
        nonzero_probability = F(sum(count for (state, score), count in counts.items()
                                    if SCORE[state] != 0), total)
        expected_nonzero = (1-(-F(1, 5))**N)/3
        assert nonzero_probability == expected_nonzero
        # Four times the martingale value is exactly 4*S_N+g(X_N).
        second = F(sum(count*(4*score+SCORE[state])**2
                       for (state, score), count in counts.items()), 16*total)
        fourth = F(sum(count*(4*score+SCORE[state])**4
                       for (state, score), count in counts.items()), 256*total)
        expected_second = F(N, 2)+F(5, 48)*(1-(-F(1, 5))**N)
        fourth_bound = F(165*N*N+8*N, 128)
        assert second == expected_second
        assert F(N, 2) <= second <= F(5*N, 8)
        assert fourth <= fourth_bound < 2*N*N
        tail_count = sum(count for (state, score), count in counts.items()
                         if 16*score*score >= N)
        assert 32*tail_count >= total
        if N in (1, 2, 3, 5, 10, 25, 50, 100):
            rows.append({"length": N, "total_words": total,
                         "nonzero_score_state_probability": str(nonzero_probability),
                         "martingale_second_moment": str(second),
                         "martingale_fourth_moment": str(fourth),
                         "proved_fourth_moment_upper_bound": str(fourth_bound),
                         "score_tail_words": tail_count,
                         "tail_probability_lower_bound": "1/32"})
    return {"complete_state_score_lengths_checked": 100, "checkpoints": rows}


def return_injection_certificate() -> dict:
    rows = []
    for N in range(1, 7):
        images, tail_words = set(), 0
        for word in product(range(5), repeat=N):
            raw_score = trace(word)[1]
            if 16*raw_score*raw_score < N:
                continue
            tail_words += 1
            if raw_score >= 0:
                output = (0, *word, 0, 2, 1)
            else:
                complement = tuple(4-digit for digit in word)
                assert trace(complement, start=5)[1] == -raw_score
                output = (4, *complement, 0, 2, 1)
            assert len(output) == N+4
            final_state, total_score = trace(output, start=1)
            assert final_state == 1 and total_score == abs(raw_score)+1
            assert 16*(total_score-1)**2 >= N
            images.add(block_integer(output))
        assert len(images) == tail_words
        assert 32*tail_words >= 5**N
        rows.append({"raw_length": N, "raw_words": 5**N,
                     "tail_words": tail_words,
                     "distinct_positive_score_return_words": len(images)})
    return {"complete_raw_words_checked": sum(row["raw_words"] for row in rows),
            "rows": rows}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json", type=Path)
    args = parser.parse_args()
    certificate = {
        "schema": "salikhov-score-moments-v1",
        "interval_transitions": interval_transition_certificate(),
        "conditional_moments": conditional_moment_certificate(),
        "exact_path_moments": exact_path_moment_certificate(),
        "return_injection": return_injection_certificate(),
    }
    if args.json:
        args.json.write_text(json.dumps(certificate, indent=2, sort_keys=True)+"\n")
    print(json.dumps({
        "status": "passed", "exact_conditional_moment_rows": 6,
        "rational_interval_inclusions": 30,
        "complete_state_score_lengths_checked": 100,
        "complete_return_injection_raw_words": certificate["return_injection"]["complete_raw_words_checked"],
        "proved_score_tail_fraction": "1/32",
    }, sort_keys=True))


if __name__ == "__main__":
    main()
