#!/usr/bin/env python3
"""Independent exact checks for the 2026-08-13 G-function/SFT audit.

Claim status: ``experiment``.  This program was written without importing the
parent checker.  It verifies finite instances and exact algebraic identities;
it neither reads digits of pi nor proves the canonical V1 conjecture.
"""

from __future__ import annotations

from decimal import Decimal, getcontext
from fractions import Fraction
from hashlib import sha256
from itertools import product
from math import gcd
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
PARENT_REPORT = ROOT / "work/ultrapi-resume/gfunction_subshift_entropy_attack_20260813.md"
PARENT_CHECKER = ROOT / "work/ultrapi-resume/gfunction_subshift_entropy_attack_20260813_check.py"
INHERITED_SOURCE_INDEX = ROOT / "work/ultrapi-resume/subshift_log_algebraic_bridge.md"

FROZEN = {
    ROOT / "problems/local/pi-digits.txt":
        "2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825",
    PARENT_REPORT:
        "3fe1e0639411421cef5b28786190717e41bdde1d893fe15fb6bd7e0600efb3b9",
    PARENT_CHECKER:
        "c150a72f596794655ed00d911def69db88b92c578c69a463cb7ea05086baa6d7",
    INHERITED_SOURCE_INDEX:
        "b4e4fb05397f75e1e4af7bbd6d4d32e80d489893fead9773de51a57a28aca896",
}

PRIMARY_SOURCE_PINS = {
    "Fischler--Rivoal corrected G-function PDF":
        "4e6954c62da62ab760181f9204a7f0fec50afaea6089004b874723b6dedc4d40",
    "Adamczewski--Bugeaud math/0511674":
        "e3bd2934800e94dd27930d43d47abc44f760de7e90320d1d014b372b681be9a0",
    "Adamczewski 1205.0961":
        "28ed9d10ddcadc20e103a0ff177c19d2d8c80b5b264441baa071ce5f13e4a7e3",
    "Bell--Chen 1606.04986":
        "9550237fb012dea45349573f50ef19aa0adbbe9d4e68121255206756851da1db",
    "Bell--Coons--Rowland 1210.2070":
        "30481c3b4cf0ae925bb7bf11b908e00d3df0a77779090c615ebdfa82bd764aa0",
    "Bell--Chen--Nguyen--Zannier 2306.02590v1":
        "2d50018f9c9f255d3886814fb4875dacc7f3c7e936fc31ed0c2bab2bd8a4ac05",
    "Bugeaud--Kaneko--Kim 2510.17177v3":
        "c825aac435e48f4668d8d1a496869c8c1e86ff1d18cea407e2c0156ece1bdd01",
    "Zeilberger--Zudilin 1912.06345":
        "b922ee68a427ad5b74617bd2ac6b6a549824eb2d5a8c97eed0d34b2de984155f",
    "Adamczewski Mahler survey":
        "2862813f5fc24f3a4e5d4af48603053c2657bb4722d9583c5af9f477a3ea55b0",
    "Cijsouw 1974":
        "fc31f7cf4ce0177a46966c0ef41b05c6252c0d4f3abb762d50c2e43e7f48a46a",
    "Bugeaud Thue--Morse Numdam PDF":
        "6d7607e8a70e8524630daa45001192113487d9af1f1588c96556283445c7460c",
    "Adamczewski--Faverjon 2604.08208v1":
        "c428a9a555b8d7abeb25f3e8a02c8f7880c640e7fe6a2f85c411ca1b68f1945c",
    "Fischler--Rivoal Math. Ann. 2026":
        "86669c0103d2a589c9a45970734a9ebac47c737382c015fa026b546960c0301d",
    "Nguyen 2605.30606v2":
        "2cfb651d65a9960bc0385a2658005752dd899bb4a8919b08d91c8319a18a87b2",
}


def digest(path: Path) -> str:
    return sha256(path.read_bytes()).hexdigest()


def suffix_transition(pattern: tuple[int, ...], state: int, symbol: int) -> int:
    """Return the new proper-prefix state, or -1 after completing pattern."""
    history = pattern[:state] + (symbol,)
    width = len(pattern)
    if len(history) >= width and history[-width:] == pattern:
        return -1
    for candidate in range(min(width - 1, len(history)), 0, -1):
        if history[-candidate:] == pattern[:candidate]:
            return candidate
    return 0


def transition_table(pattern: tuple[int, ...], base: int) -> list[list[int]]:
    return [
        [suffix_transition(pattern, state, digit) for digit in range(base)]
        for state in range(len(pattern))
    ]


def counts_through(pattern: tuple[int, ...], stop: int, base: int = 10) -> list[int]:
    table = transition_table(pattern, base)
    vector = [1] + [0] * (len(pattern) - 1)
    totals = [1]
    for _ in range(stop):
        following = [0] * len(pattern)
        for state, multiplicity in enumerate(vector):
            for target in table[state]:
                if target >= 0:
                    following[target] += multiplicity
        vector = following
        totals.append(sum(vector))
    return totals


def brute_count(pattern: tuple[int, ...], length: int, base: int) -> int:
    width = len(pattern)
    answer = 0
    for word in product(range(base), repeat=length):
        if not any(word[start : start + width] == pattern
                   for start in range(length - width + 1)):
            answer += 1
    return answer


def lcm(a: int, b: int) -> int:
    return a // gcd(a, b) * b


def poly_mul(left: list[int], right: list[int]) -> list[int]:
    answer = [0] * (len(left) + len(right) - 1)
    for i, a in enumerate(left):
        for j, b in enumerate(right):
            answer[i + j] += a * b
    return answer


def poly_eval(coefficients: list[int], x: Fraction) -> Fraction:
    answer = Fraction(0)
    for coefficient in reversed(coefficients):
        answer = answer * x + coefficient
    return answer


Gaussian = tuple[Fraction, Fraction]


def g_add(x: Gaussian, y: Gaussian) -> Gaussian:
    return x[0] + y[0], x[1] + y[1]


def g_mul(x: Gaussian, y: Gaussian) -> Gaussian:
    return x[0] * y[0] - x[1] * y[1], x[0] * y[1] + x[1] * y[0]


def g_div(x: Gaussian, y: Gaussian) -> Gaussian:
    norm = y[0] * y[0] + y[1] * y[1]
    return g_mul(x, (y[0] / norm, -y[1] / norm))


def g_pow(x: Gaussian, exponent: int) -> Gaussian:
    answer: Gaussian = (Fraction(1), Fraction(0))
    for _ in range(exponent):
        answer = g_mul(answer, x)
    return answer


def substitution_thue_morse(minimum_length: int) -> tuple[int, ...]:
    word = (0,)
    while len(word) < minimum_length:
        word = tuple(symbol for bit in word for symbol in (bit, 1 - bit))
    return word


def cijsouw_symmetrization(coefficients: list[int]) -> list[int]:
    """Coefficients of P(-iY)P(iY), verified to be real integers."""
    degree = len(coefficients) - 1
    powers_i: list[Gaussian] = [(Fraction(1), Fraction(0))]
    for _ in range(2 * degree):
        powers_i.append(g_mul(powers_i[-1], (Fraction(0), Fraction(1))))
    gaussian_answer: list[Gaussian] = [
        (Fraction(0), Fraction(0)) for _ in range(2 * degree + 1)
    ]
    for j, a in enumerate(coefficients):
        for k, b in enumerate(coefficients):
            minus_i_j = powers_i[j]
            if j % 2:
                minus_i_j = (-minus_i_j[0], -minus_i_j[1])
            term = g_mul(minus_i_j, powers_i[k])
            scaled = (Fraction(a * b) * term[0], Fraction(a * b) * term[1])
            gaussian_answer[j + k] = g_add(gaussian_answer[j + k], scaled)
    answer = []
    for real, imaginary in gaussian_answer:
        assert imaginary == 0
        assert real.denominator == 1
        answer.append(real.numerator)
    while len(answer) > 1 and answer[-1] == 0:
        answer.pop()
    return answer


def main() -> None:
    for path, expected in FROZEN.items():
        assert digest(path) == expected, path
    report_text = PARENT_REPORT.read_text(encoding="utf-8")
    source_index_text = INHERITED_SOURCE_INDEX.read_text(encoding="utf-8")
    for source_hash in PRIMARY_SOURCE_PINS.values():
        assert source_hash in report_text + source_index_text

    # Independent automaton versus exhaustive enumeration.
    brute_cases = 0
    for base in (2, 3):
        for width in range(1, 4):
            for pattern in product(range(base), repeat=width):
                totals = counts_through(pattern, 8, base)
                for length, exact in enumerate(totals):
                    assert exact == brute_count(pattern, length, base)
                    brute_cases += 1

    # Exhaust every decimal forbidden word through width four.  All comparisons
    # here are integer-exact, including the aligned-block entropy bound.
    decimal_patterns = 0
    bound_checks = 0
    submultiplicativity_checks = 0
    samples: dict[str, int] = {}
    for width in range(1, 5):
        for pattern in product(range(10), repeat=width):
            decimal_patterns += 1
            totals = counts_through(pattern, 12)
            for length, exact in enumerate(totals):
                blocks, remainder = divmod(length, width)
                lower = 9**length
                upper = 10**remainder * (10**width - 1) ** blocks
                assert lower <= exact <= upper <= 10**length
                bound_checks += 3
                if width == 1:
                    assert exact == lower
            for left in range(13):
                for right in range(13 - left):
                    assert totals[left + right] <= totals[left] * totals[right]
                    submultiplicativity_checks += 1
            if pattern in ((0,), (1, 2), (1, 0, 1), (0, 0, 0, 0)):
                samples["".join(map(str, pattern))] = totals[12]

    # Overlap-heavy and border-free longer patterns stress failure transitions.
    stress_patterns = (
        (0, 0, 0, 0, 0),
        (1, 0, 1, 0, 1, 0),
        (1, 2, 3, 4, 5, 6, 7),
        (9, 9, 0, 9, 9, 0, 9, 9),
    )
    for pattern in stress_patterns:
        totals = counts_through(pattern, 60)
        for length, exact in enumerate(totals):
            blocks, remainder = divmod(length, len(pattern))
            assert 9**length <= exact
            assert exact <= 10**remainder * (10**len(pattern) - 1) ** blocks

    # Finite cylinder witnesses for the embedded nine-shift.  Half-open
    # decimal prefix intervals have pairwise distinct integer addresses.
    cylinder_checks = 0
    for omitted in range(10):
        alphabet = tuple(digit for digit in range(10) if digit != omitted)
        for depth in (1, 2, 3):
            addresses = {
                sum(digit * 10 ** (depth - index - 1) for index, digit in enumerate(word))
                for word in product(alphabet, repeat=depth)
            }
            assert len(addresses) == 9**depth
            assert min(addresses) >= 0 and max(addresses) < 10**depth
            cylinder_checks += len(addresses)

    # Decimal entropy deficits, evaluated stably at high precision for display.
    getcontext().prec = 180
    entropy_rows: list[tuple[int, Decimal]] = []
    for width in (1, 2, 3, 4, 10, 100):
        exact_numerator = 10**width - 1
        assert 0 < exact_numerator < 10**width
        deficit = -(Decimal(1) - (Decimal(10) ** (-width))).ln() / Decimal(width)
        assert deficit > 0
        entropy_rows.append((width, deficit))

    # Thue--Morse built by substitution, not by the parent's popcount method.
    tm = substitution_thue_morse(8192)
    for n in range(4096):
        assert tm[2 * n] == tm[n]
        assert tm[2 * n + 1] == 1 - tm[n]
    for coefficient in range(4096):
        right = 0
        if coefficient % 2 == 0:
            right += tm[coefficient // 2]
        else:
            right -= tm[(coefficient - 1) // 2]
            right += 1
        assert tm[coefficient] == right

    mapped_survivors = 0
    for width in range(1, 5):
        for pattern in product(range(10), repeat=width):
            omitted = pattern[-1]
            available = [digit for digit in range(10) if digit != omitted]
            a, b = available[0], available[-1]
            assert a < b
            mapped = tuple(a + (b - a) * bit for bit in tm[:512])
            assert set(mapped) <= {a, b}
            assert omitted not in mapped and omitted in pattern
            assert all(
                mapped[start : start + width] != pattern
                for start in range(len(mapped) - width + 1)
            )
            mapped_survivors += 1

    # Exact finite affine-series identity and the shift between Bugeaud's
    # sum t_n 10^{-n} and the report's tau_10.
    prefix_length = 120
    a, b = 2, 9
    tau_prefix = sum(
        (Fraction(bit, 10 ** (n + 1)) for n, bit in enumerate(tm[:prefix_length])),
        Fraction(0),
    )
    xi_prefix = sum(
        (Fraction(bit, 10**n) for n, bit in enumerate(tm[:prefix_length])),
        Fraction(0),
    )
    constant_prefix = sum(
        (Fraction(a, 10 ** (n + 1)) for n in range(prefix_length)),
        Fraction(0),
    )
    mapped_prefix = sum(
        (Fraction(a + (b - a) * bit, 10 ** (n + 1))
         for n, bit in enumerate(tm[:prefix_length])),
        Fraction(0),
    )
    assert xi_prefix == 10 * tau_prefix
    assert mapped_prefix == constant_prefix + (b - a) * tau_prefix

    # Machin's identity as an exact Gaussian-rational phase identity:
    # exp(2i arctan(1/q)) = (q+i)/(q-i).
    phase_fifth = g_div((Fraction(5), Fraction(1)), (Fraction(5), Fraction(-1)))
    inverse_phase_239 = g_div(
        (Fraction(239), Fraction(-1)), (Fraction(239), Fraction(1))
    )
    machin_phase = g_mul(g_pow(phase_fifth, 4), inverse_phase_239)
    assert machin_phase == (Fraction(0), Fraction(1))

    # H'(z)=32/(1+4z^2)-9560/(57121+100z^2).  The second
    # denominator is nonzero at the first denominator's roots.
    pole_square = Fraction(-1, 4)
    assert 1 + 4 * pole_square == 0
    assert 57121 + 100 * pole_square == 57096
    assert 32 != 0

    # Finite coefficient-denominator audit for H.  This supports, but does
    # not replace, the standard G-function denominator proof.
    common_denominator = 1
    odd_lcm = 1
    for k in range(31):
        coefficient = (
            Fraction(16 * ((-1) ** k) * 2 ** (2 * k + 1), 2 * k + 1)
            - Fraction(4 * ((-1) ** k) * 10 ** (2 * k + 1),
                       (2 * k + 1) * 239 ** (2 * k + 1))
        )
        common_denominator = lcm(common_denominator, coefficient.denominator)
        odd_lcm = lcm(odd_lcm, 2 * k + 1)
        advertised_multiple = odd_lcm * 239 ** (2 * k + 1)
        assert advertised_multiple % common_denominator == 0

    # A fully expanded all-prefix language polynomial in an independent base.
    base = 4
    pattern = (1, 2)
    length = 3
    scale = base**length
    allowed = []
    for integer in range(scale):
        digits = tuple((integer // base**power) % base for power in reversed(range(length)))
        if not any(digits[start : start + len(pattern)] == pattern
                   for start in range(length - len(pattern) + 1)):
            allowed.append(integer)
    polynomial = [1]
    for integer in allowed:
        polynomial = poly_mul(polynomial, [-(3 * scale + integer), scale])
    assert len(allowed) == counts_through(pattern, length, base)[-1] == 56
    assert len(polynomial) - 1 == len(allowed)
    assert polynomial[-1] == scale ** len(allowed)
    assert max(map(abs, polynomial)) >= polynomial[-1]
    selected = allowed[len(allowed) // 2]
    fractional_tail = Fraction(1, 3)
    x = Fraction(3) + Fraction(selected, scale) + fractional_tail / scale
    direct_value = Fraction(1)
    for integer in allowed:
        direct_value *= scale * (x - 3) - integer
    assert poly_eval(polynomial, x) == direct_value
    assert 0 < abs(direct_value) < scale ** (len(allowed) - 1)

    # The report's factor norm 30*t^2 has harmless slack: the exact maximum
    # over 0 <= A < 4t is 25*t^2-5*t, hence at most 25*t^2.
    tail_factor_checks = 0
    for n in range(1, 61):
        t = 10**n
        maximum_a = 4 * t - 1
        maximum_l1 = (
            t * t + t * (1 + 2 * maximum_a) + maximum_a * (1 + maximum_a)
        )
        assert maximum_l1 == 25 * t * t - 5 * t
        assert maximum_l1 <= 25 * t * t <= 30 * t * t
        tail_factor_checks += 1

    # Verify the exact symmetrization used to transfer Cijsouw's theorem.
    cijsouw_checks = 0
    for coefficients in ([1, 2], [3, -1, 4], [-2, 0, 5, 1], [7, -3, 2, -4, 1]):
        q = cijsouw_symmetrization(list(coefficients))
        p_minus = [coefficient * ((-1) ** degree)
                   for degree, coefficient in enumerate(coefficients)]
        product_pm = poly_mul(list(coefficients), p_minus)
        q_at_i = [0] * len(q)
        for degree, coefficient in enumerate(q):
            assert degree % 2 == 0 or coefficient == 0
            if degree % 2 == 0:
                q_at_i[degree] = coefficient * ((-1) ** (degree // 2))
        assert q_at_i == product_pm
        degree = len(coefficients) - 1
        height = max(map(abs, coefficients))
        assert len(q) - 1 <= 2 * degree
        assert max(map(abs, q)) <= (degree + 1) * height * height
        cijsouw_checks += 1

    print("claim_status=experiment")
    print("canonical_v1=conjecture; independent checker is not a proof")
    print(f"frozen_artifacts={len(FROZEN)}")
    print(f"primary_source_pins_present={len(PRIMARY_SOURCE_PINS)}")
    print(f"brute_force_cross_checks={brute_cases}")
    print(f"decimal_patterns_exhausted={decimal_patterns}")
    print(f"integer_bound_checks={bound_checks}")
    print(f"submultiplicativity_checks={submultiplicativity_checks}")
    print(f"embedded_nine_shift_cylinders_checked={cylinder_checks}")
    print(f"mapped_thue_morse_survivors={mapped_survivors}")
    print("mahler_coefficients_checked=4096")
    print("machin_gaussian_identity=exact")
    print(f"selected_tail_factor_bounds={tail_factor_checks}")
    print(f"cijsouw_symmetrizations={cijsouw_checks}")
    for word, count in samples.items():
        print(f"avoid[{word}]_length_12={count}")
    for width, deficit in entropy_rows:
        print(f"entropy_deficit[m={width}]={deficit}")


if __name__ == "__main__":
    main()
