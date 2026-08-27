#!/usr/bin/env python3
"""Exact checks for the two finite count trees in T27 REPORT.md."""

from fractions import Fraction
from itertools import product
from math import isqrt


DIGITS = tuple(str(i) for i in range(10))


def child(word: str, digit: int) -> str:
    return word + str(digit)


def count(counts: dict[str, int], word: str) -> int:
    return counts.get(word, 0)


def level_words(_counts: dict[str, int], level: int) -> set[str]:
    return {"".join(word) for word in product(DIGITS, repeat=level)}


def check_conservation(counts: dict[str, int], depth: int) -> None:
    assert all(
        isinstance(value, int) and value >= 0 for value in counts.values()
    )
    assert all(
        len(word) <= depth and all(digit in DIGITS for digit in word)
        for word in counts
    )
    for level in range(depth):
        for word in level_words(counts, level):
            assert count(counts, word) == sum(
                count(counts, child(word, digit)) for digit in range(10)
            ), word


def energy(counts: dict[str, int], level: int) -> int:
    return sum(count(counts, word) ** 2 for word in level_words(counts, level))


def positive_words(counts: dict[str, int], level: int) -> set[str]:
    return {word for word in level_words(counts, level) if count(counts, word) > 0}


def qualifying_children(
    counts: dict[str, int], word: str, threshold: Fraction
) -> list[str]:
    return [
        child(word, digit)
        for digit in range(10)
        if Fraction(count(counts, child(word, digit)))
        >= threshold * count(counts, word)
    ]


def dominant_words(
    counts: dict[str, int], level: int, alpha: Fraction
) -> set[str]:
    return {
        word
        for word in positive_words(counts, level)
        if qualifying_children(counts, word, alpha)
    }


def split_words(counts: dict[str, int], level: int, eta: Fraction) -> set[str]:
    return {
        word
        for word in level_words(counts, level)
        if len(qualifying_children(counts, word, eta)) >= 2
    }


def selected_child(counts: dict[str, int], word: str, alpha: Fraction) -> str:
    choices = qualifying_children(counts, word, alpha)
    assert choices
    return max(choices, key=lambda item: (count(counts, item), -int(item[-1])))


def retained_energy(counts: dict[str, int], level: int, alpha: Fraction) -> int:
    return sum(
        count(counts, selected_child(counts, word, alpha)) ** 2
        for word in dominant_words(counts, level, alpha)
    )


def has_coherent_path(counts: dict[str, int], alphas: list[Fraction]) -> bool:
    survivors = positive_words(counts, 0)
    for level, alpha in enumerate(alphas):
        good = dominant_words(counts, level, alpha)
        survivors = {
            selected_child(counts, word, alpha) for word in survivors & good
        }
    return bool(survivors)


def positive_example() -> None:
    counts = {
        "": 12,
        "0": 9,
        "1": 3,
        "00": 8,
        "01": 1,
        "10": 3,
    }
    alphas = [Fraction(3, 4), Fraction(8, 9)]
    check_conservation(counts, 2)
    energies = [energy(counts, level) for level in range(3)]
    assert energies == [144, 90, 74]
    retained = [
        retained_energy(counts, level, alpha)
        for level, alpha in enumerate(alphas)
    ]
    assert retained == [81, 73]
    leakages = [energies[level] - retained[level] for level in range(2)]
    assert leakages == [63, 17]
    assert Fraction(leakages[0], energies[0]) == Fraction(7, 16)
    assert Fraction(leakages[1], energies[1]) == Fraction(17, 90)
    q_value = energies[0] - sum(leakages)
    assert q_value == 64
    assert isqrt(q_value) ** 2 == q_value
    assert has_coherent_path(counts, alphas)
    assert count(counts, "00") == 8
    assert alphas[0] * alphas[1] * count(counts, "") == 8


def migration_counterexample() -> None:
    counts = {"": 12, "0": 6}
    counts.update({str(i): 1 for i in range(1, 7)})
    counts.update({f"0{a}": 1 for a in range(6)})
    counts.update({f"{i}0": 1 for i in range(1, 7)})
    eta = Fraction(1, 11)
    alpha = 1 - 9 * eta
    mu = Fraction(9, 10)
    assert alpha == Fraction(2, 11)
    check_conservation(counts, 2)
    energies = [energy(counts, level) for level in range(3)]
    assert energies == [144, 42, 12]

    split0 = split_words(counts, 0, eta)
    split1 = split_words(counts, 1, eta)
    assert split0 == set()
    # T9 regards a zero parent as split because every zero child meets the
    # zero threshold. Those parents contribute zero collision energy.
    assert split1 == {"0", "7", "8", "9"}
    split_energy = [
        sum(count(counts, word) ** 2 for word in split0),
        sum(count(counts, word) ** 2 for word in split1),
    ]
    assert split_energy == [0, 36]
    assert split_energy[0] < mu * energies[0] == Fraction(648, 5)
    assert split_energy[1] < mu * energies[1] == Fraction(189, 5)

    good0 = dominant_words(counts, 0, alpha)
    good1 = dominant_words(counts, 1, alpha)
    assert good0 == {""}
    assert good1 == {str(i) for i in range(1, 7)}
    dominant_energy = [
        sum(count(counts, word) ** 2 for word in good0),
        sum(count(counts, word) ** 2 for word in good1),
    ]
    assert dominant_energy == [144, 6]
    assert (1 - mu) * energies[0] == Fraction(72, 5) < dominant_energy[0]
    assert (1 - mu) * energies[1] == Fraction(21, 5) < dominant_energy[1]

    retained = [retained_energy(counts, level, alpha) for level in range(2)]
    assert retained == [36, 6]
    leakages = [energies[level] - retained[level] for level in range(2)]
    assert leakages == [108, 36]
    assert Fraction(leakages[0], energies[0]) == Fraction(3, 4)
    assert Fraction(leakages[1], energies[1]) == Fraction(6, 7)
    assert Fraction(3, 4) + Fraction(6, 7) == Fraction(45, 28) > 1
    assert Fraction(sum(leakages), energies[0]) == 1
    assert energies[0] - sum(leakages) == 0
    assert not has_coherent_path(counts, [alpha, alpha])

    delta = 1 - (1 - mu) * alpha**2
    assert delta == Fraction(603, 605)
    assert Fraction(3, 4) < delta
    assert Fraction(6, 7) < delta


if __name__ == "__main__":
    positive_example()
    migration_counterexample()
    print("T27 exact checks passed")
