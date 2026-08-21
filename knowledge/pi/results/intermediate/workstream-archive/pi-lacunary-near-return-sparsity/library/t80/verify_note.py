#!/usr/bin/env python3
"""Self-contained exact-arithmetic replay for the T80 Ramanujan audit.

Finite calculations below are sanity checks for the universal arguments in
REPORT.md. They are not evidence for C1, C2, or the canonical question.
"""

from fractions import Fraction
from hashlib import sha256
from math import factorial, gcd
from pathlib import Path


ROOT = Path(__file__).resolve().parent

EXPECTED_HASHES = {
    "canonical_statement.txt":
        "cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8",
    "ramanujan-1914-modular-equations.pdf":
        "478e2643fd7ca8a2dbbba23b60ae35608845c21d29019bb9d8dd9b0af27710a1",
    "ramanujan-1914-modular-equations.txt":
        "f80754fa22cd1dadfd58a36a686224a392a7dd9ec9fdb0ee6ca1d43bf25fa73b",
    "ramanujan-collected-papers-1927-scan.pdf":
        "858af6247df93916a2ef7cedfe774782e95acbb9c06fe40a876c06ff0add41a7",
    "ramanujan-collected-papers-1927-scan.txt":
        "7fc153f0f5dd44fbd91b583fe3d5ad9e15e6df37987b2b3ed75156eadad4e4a0",
}


def file_hash(name: str) -> str:
    return sha256((ROOT / name).read_bytes()).hexdigest()


def ramanujan_term(k: int) -> Fraction:
    return Fraction(
        factorial(4 * k) * (1103 + 26390 * k),
        factorial(k) ** 4 * 396 ** (4 * k),
    )


def pochhammer(a: Fraction, k: int) -> Fraction:
    out = Fraction(1)
    for j in range(k):
        out *= a + j
    return out


def common_partial_sum(k_terms: int) -> tuple[int, int, Fraction]:
    """Return the displayed common numerator/denominator and reduced sum."""
    assert k_terms >= 1
    top = k_terms - 1
    denominator = factorial(top) ** 4 * 396 ** (4 * top)
    numerator = 0
    for k in range(k_terms):
        numerator += (
            factorial(4 * k)
            * (1103 + 26390 * k)
            * (factorial(top) // factorial(k)) ** 4
            * 396 ** (4 * (top - k))
        )
    reduced = Fraction(numerator, denominator)
    return numerator, denominator, reduced


def pi_coefficient(k_terms: int) -> Fraction:
    """c where the reciprocal truncation pi_K equals c*sqrt(2)."""
    _, _, partial = common_partial_sum(k_terms)
    return Fraction(9801 * partial.denominator, 4 * partial.numerator)


def valuation(n: int, p: int) -> tuple[int, int]:
    exponent = 0
    while n % p == 0:
        exponent += 1
        n //= p
    return exponent, n


def collision_formula(n: int, transient: int, order: int) -> int:
    early = min(n, transient)
    tail = max(n - transient, 0)
    counts = [0] * order
    for s in range(tail):
        counts[s % order] += 1
    return early + sum(c * c for c in counts)


# Exact values were independently factored once. The replay verifies each
# factorization and proves the stated order from its prime divisors.
TABLE = [
    {
        "K": 1,
        "a": 9801,
        "b": 4412,
        "alpha": 2,
        "beta": 0,
        "m_factors": {1103: 1},
        "order": 1102,
        "order_factors": {2: 1, 19: 1, 29: 1},
    },
    {
        "K": 2,
        "a": 2510613731736,
        "b": 1130173253125,
        "alpha": 0,
        "beta": 5,
        "m_factors": {7: 1, 4423: 1, 11681: 1},
        "order": 12912240,
        "order_factors": {2: 4, 3: 1, 5: 1, 11: 1, 67: 1, 73: 1},
    },
    {
        "K": 3,
        "a": 2286635172367940241408,
        "b": 1029347477390786609545,
        "alpha": 0,
        "beta": 1,
        "m_factors": {7: 2, 4789: 1, 10111: 1, 106859: 1, 811981: 1},
        "order": 1944481966883820,
        "order_factors": {
            2: 2, 3: 2, 5: 1, 7: 1, 13: 1, 19: 1,
            23: 2, 101: 1, 337: 1, 347: 1,
        },
    },
    {
        "K": 4,
        "a": 17252765328978109815564789153792,
        "b": 7766473062254307011793347201855,
        "alpha": 0,
        "beta": 1,
        "m_factors": {
            7: 1, 13: 1, 967: 1, 12899: 1, 113537: 1,
            2780801: 1, 4334336261: 1,
        },
        "order": 333008626063235355784320,
        "order_factors": {
            2: 7, 3: 1, 5: 1, 7: 1, 11: 1, 23: 1,
            79: 1, 163: 1, 191: 1, 887: 1, 6449: 1, 6961: 1,
        },
    },
]


def product(factors: dict[int, int]) -> int:
    value = 1
    for prime, exponent in factors.items():
        value *= prime ** exponent
    return value


def is_prime(n: int) -> bool:
    if n < 2:
        return False
    if n in (2, 3):
        return True
    if n % 2 == 0 or n % 3 == 0:
        return False
    divisor = 5
    while divisor * divisor <= n:
        if n % divisor == 0 or n % (divisor + 2) == 0:
            return False
        divisor += 6
    return True


def verify_manifest() -> None:
    manifest = ROOT / "SHA256SUMS"
    listed = {}
    for line in manifest.read_text(encoding="ascii").splitlines():
        digest, name = line.split("  ", 1)
        assert name not in listed
        listed[name] = digest
    delivered = {
        path.name for path in ROOT.iterdir()
        if path.is_file() and path.name != "SHA256SUMS"
    }
    assert set(listed) == delivered, (set(listed), delivered)
    for name, expected in listed.items():
        assert file_hash(name) == expected, name


def main() -> None:
    for name, expected in EXPECTED_HASHES.items():
        actual = file_hash(name)
        assert actual == expected, (name, expected, actual)

    extracted = (ROOT / "ramanujan-1914-modular-equations.txt").read_text(
        encoding="utf-8"
    )
    assert "1103" in extracted
    assert "27493" in extracted
    assert "53883" in extracted
    assert "The last series (44) is extremely rapidly convergent" in extracted

    # The modern factorial coefficient is exactly the product coefficient in
    # Ramanujan's equation (44).
    for k in range(21):
        product_form = (
            pochhammer(Fraction(1, 4), k)
            * pochhammer(Fraction(1, 2), k)
            * pochhammer(Fraction(3, 4), k)
            / factorial(k) ** 3
        )
        factorial_form = Fraction(factorial(4 * k), 256 ** k * factorial(k) ** 4)
        assert product_form == factorial_form
        original_term = Fraction(
            1103 + 26390 * k, 99 ** (4 * k + 2)
        ) * product_form
        modern_term = ramanujan_term(k) / 9801
        assert original_term == modern_term
    assert [1103 + 26390 * k for k in range(3)] == [1103, 27493, 53883]
    assert 99 ** 2 == 9801
    assert 4 * 99 == 396

    q = Fraction(1, 3_000_000)
    assert Fraction(25, 99 ** 4) < q
    for k in range(50):
        assert ramanujan_term(k + 1) / ramanujan_term(k) < q

    rows = []
    for expected in TABLE:
        k_terms = expected["K"]
        numerator, denominator, partial = common_partial_sum(k_terms)
        assert Fraction(numerator, denominator) == partial
        coefficient = pi_coefficient(k_terms)
        assert coefficient.numerator == expected["a"]
        assert coefficient.denominator == expected["b"]
        assert gcd(coefficient.numerator, coefficient.denominator) == 1

        alpha, after_two = valuation(coefficient.denominator, 2)
        beta, m = valuation(after_two, 5)
        assert alpha == expected["alpha"]
        assert beta == expected["beta"]
        assert product(expected["m_factors"]) == m
        assert gcd(m, 10) == 1

        order = expected["order"]
        assert all(is_prime(prime) for prime in expected["m_factors"])
        assert all(is_prime(prime) for prime in expected["order_factors"])
        assert product(expected["order_factors"]) == order
        assert pow(10, order, m) == 1
        for prime in expected["order_factors"]:
            assert pow(10, order // prime, m) != 1

        # Denominator ideal d((a/b)sqrt(2)) has lattice basis
        # b and (b/gcd(b,2))*sqrt(2), hence this index.
        ideal_index = coefficient.denominator ** 2 // gcd(coefficient.denominator, 2)

        rows.append(
            (
                k_terms,
                coefficient.numerator,
                coefficient.denominator,
                alpha,
                beta,
                m,
                order,
                ideal_index,
            )
        )

    # Exhaustively check the exact coefficient-collision criterion for K=1.
    first = rows[0]
    _, a, b, alpha, beta, m, order, _ = first
    transient = max(alpha, beta)
    n = 2500
    residues = [(a * pow(10, i, b)) % b for i in range(n)]
    brute = sum(1 for x in residues for y in residues if x == y)
    formula = collision_formula(n, transient, order)
    assert brute == formula

    # Before the transient there are no coefficient collisions; afterward the
    # order criterion is exact. The corresponding circle differences remain
    # nonzero rational multiples of sqrt(2), hence are never integers.
    for i in range(40):
        for j in range(i + 1, 80):
            coefficient_collision = (a * (10 ** j - 10 ** i)) % b == 0
            criterion = i >= transient and (j - i) % order == 0
            assert coefficient_collision == criterion
            assert Fraction(a * (10 ** j - 10 ** i), b) != 0

    verify_manifest()

    print("T80 exact-arithmetic replay: PASS")
    print("canonical/source/artifact hashes: PASS")
    print("equation (44) modernization, k=0..20: PASS")
    print("term-ratio sanity, k=0..49: PASS")
    print("K | a | b | v2(b) | v5(b) | m | ord_m(10) | ideal norm")
    for row in rows:
        print(" | ".join(str(value) for value in row))
    print(f"K=1, N={n} coefficient collisions: {formula}")
    print(f"K=1, N={n} literal circle collisions: {n} (diagonal only, by irrationality)")
    print("Finite checks are sanity checks only; no C1 or C2 claim is made.")


if __name__ == "__main__":
    main()
