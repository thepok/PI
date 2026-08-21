#!/usr/bin/env python3
"""Exact finite checks for the T31 triangular count-tree counterexample."""

from fractions import Fraction
from itertools import product


DIGITS = tuple(range(10))
ALPHA = Fraction(1, 2)


def block_start(height: int) -> int:
    assert height >= 1
    return (height - 1) * (height + 2) // 2


def separator(height: int) -> int:
    return block_start(height) + height


def separator_levels(max_level: int) -> set[int]:
    result: set[int] = set()
    height = 1
    while separator(height) <= max_level:
        result.add(separator(height))
        height += 1
    return result


def is_separator(level: int) -> bool:
    height = 1
    while separator(height) < level:
        height += 1
    return separator(height) == level


def count(word: tuple[int, ...]) -> Fraction:
    value = Fraction(1)
    for level, digit in enumerate(word):
        if is_separator(level):
            value /= 10
        elif digit != 0:
            return Fraction(0)
    return value


def words(level: int):
    return product(DIGITS, repeat=level)


def positive_words(level: int):
    choices = [DIGITS if is_separator(n) else (0,) for n in range(level)]
    return product(*choices)


def energy(level: int) -> Fraction:
    return sum((count(word) ** 2 for word in positive_words(level)), Fraction(0))


def retained_energy(level: int) -> Fraction:
    total = Fraction(0)
    for word in positive_words(level):
        parent = count(word)
        assert parent > 0
        qualifying = [
            word + (digit,)
            for digit in DIGITS
            if count(word + (digit,)) >= ALPHA * parent
        ]
        if qualifying:
            chosen = max(qualifying, key=count)
            total += count(chosen) ** 2
    return total


def check_partition(max_height: int) -> None:
    covered: list[int] = []
    for height in range(1, max_height + 1):
        start = block_start(height)
        stop = separator(height)
        assert stop == block_start(height + 1) - 1
        covered.extend(range(start, stop))
        covered.append(stop)
    assert covered == list(range(separator(max_height) + 1))


def check_tree(max_height: int) -> None:
    max_level = separator(max_height)
    separators = separator_levels(max_level)
    for level in range(max_level + 1):
        for word in positive_words(level):
            parent = count(word)
            children = [count(word + (digit,)) for digit in DIGITS]
            assert parent >= 0
            assert sum(children, Fraction(0)) == parent
            if parent > 0 and level in separators:
                assert all(child == parent / 10 for child in children)
                assert all(child < ALPHA * parent for child in children)
            if parent > 0 and level not in separators:
                assert children[0] == parent
                assert all(child == 0 for child in children[1:])


def check_blocks(max_height: int) -> None:
    previous_start = -1
    for height in range(1, max_height + 1):
        start = block_start(height)
        assert start > previous_start
        previous_start = start
        root = (0,) * start
        assert count(root) > 0

        for offset in range(height):
            level = start + offset
            assert not is_separator(level)
            assert retained_energy(level) == energy(level)
            assert energy(level) - retained_energy(level) == 0
            parent = root + (0,) * offset
            child = parent + (0,)
            assert count(child) == count(parent)
            assert count(child) >= ALPHA * count(parent)

        assert is_separator(start + height)


def check_tangent_windows(max_height: int) -> None:
    for height in range(1, max_height + 1):
        root = (0,) * block_start(height)
        root_count = count(root)
        for depth in range(height + 1):
            for suffix in words(depth):
                profile = count(root + suffix) / root_count
                expected = Fraction(1) if all(digit == 0 for digit in suffix) else 0
                assert profile == expected


def check_no_branch_window(max_start: int) -> None:
    for start in range(max_start + 1):
        height = 1
        while separator(height) < start:
            height += 1
        obstruction = separator(height)
        assert obstruction >= start
        assert is_separator(obstruction)
        # Any path from level start must cross this edge level, and every
        # positive parent there has no 1/2-dominant child.
        for word in positive_words(obstruction):
            parent = count(word)
            assert parent > 0
            assert all(
                count(word + (digit,)) < ALPHA * parent for digit in DIGITS
            )


if __name__ == "__main__":
    # Only positive-support words are enumerated at deep absolute levels.
    # The report's formulas prove the claims for every height.
    check_partition(4)
    check_tree(4)
    check_blocks(4)
    check_tangent_windows(4)
    check_no_branch_window(8)
    print("T31 exact counterexample checks passed")
