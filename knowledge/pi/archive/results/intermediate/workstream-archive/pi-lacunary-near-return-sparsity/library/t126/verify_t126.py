#!/usr/bin/env python3
"""Self-contained finite replay for the T126 proof-sketch note.

All bounded calculations printed by this script are experiments. Universal
claims in REPORT.md rest on their displayed proofs, not on this replay.
"""

from __future__ import annotations

from collections import Counter
from fractions import Fraction
import hashlib
import math
from pathlib import Path


ROOT = Path(__file__).resolve().parent

EXPECTED_HASHES = {
    "canonical_statement.txt": "cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8",
    "singh-venkataramana-1208.6460v2.pdf": "edc121df43a7921658c4e5ab4d728ad3021de746f9712ba5f92db933d0b0c1b3",
    "prior-T79-REPORT.md": "7fb415a8140597f5a061b945df08eacc122e693d4998fafca98ff98aa641d800",
    "prior-T85-REPORT.md": "06fc459ab48d1d3cbe78a3038bdc76e20591ee86b7d243cba4a879a1e1fce2c7",
    "prior-T112-REPORT.md": "72884fc7d8d594cfd2f380cafde121c541c1aa316badf054ac143bb102abcefa",
    "prior-T118-REPORT.md": "2ed7a176bedb2f3a1627dffd4002f6b6141f078fe5c73798041b4fba90c7410e",
    "prior-T121-REPORT.md": "01b97953941608b41b0fcd12cc5be0047f447be28d7cd26f8bae6506717e6cf2",
    "prior-T123-REPORT.md": "3eed848437e5ade5cfc0ac5c8f8fabf5968ff156262b74ea2d947413b74fecb2",
}


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1 << 20), b""):
            digest.update(block)
    return digest.hexdigest()


def valuation(value: int, prime: int) -> int:
    assert value > 0 and prime >= 2
    result = 0
    while value % prime == 0:
        value //= prime
        result += 1
    return result


def factorial_valuation(n: int, prime: int) -> int:
    result = 0
    power = prime
    while power <= n:
        result += n // power
        power *= prime
    return result


def digit_sum(n: int, base: int) -> int:
    result = 0
    while n:
        n, digit = divmod(n, base)
        result += digit
    return result


def coefficient_factor(n: int) -> int:
    return (6 * n - 5) * (6 * n - 1)


def cleared_coefficient(n: int) -> int:
    result = 1
    for k in range(1, n + 1):
        result *= coefficient_factor(k)
    return result


def coefficient(n: int) -> Fraction:
    return Fraction(cleared_coefficient(n), 36**n * math.factorial(n) ** 2)


def roots_mod_prime_power(q: int) -> tuple[int, int]:
    residue = q % 6
    if residue == 1:
        return (5 * q + 1) // 6, (q + 5) // 6
    assert residue == 5
    return (q + 1) // 6, (5 * q + 5) // 6


def floor_valuation_residues(n: int, prime: int) -> int:
    if prime in (2, 3):
        return 0
    result = 0
    q = prime
    while q <= 6 * n - 1:
        r1, r5 = roots_mod_prime_power(q)
        result += (n + q - r1) // q + (n + q - r5) // q
        q *= prime
    return result


def floor_valuation_factorial(n: int, prime: int) -> int:
    if prime in (2, 3):
        return 0
    result = 0
    q = prime
    while q <= 6 * n:
        result += 6 * n // q - 3 * n // q - 2 * n // q + n // q
        q *= prime
    return result


def alpha(n: int) -> int:
    return 2 * n + 2 * factorial_valuation(n, 2)


def beta(n: int) -> int:
    return 2 * n + 2 * factorial_valuation(n, 3)


def order_10_mod_3_power(exponent: int) -> int:
    return 1 if exponent <= 2 else 3 ** (exponent - 2)


def occupancy_formula(n: int, prefix: int) -> int:
    transient = alpha(n)
    if prefix <= transient:
        return prefix
    length = prefix - transient
    order = order_10_mod_3_power(beta(n))
    quotient, remainder = divmod(length, order)
    tail_collision = remainder * (quotient + 1) ** 2
    tail_collision += (order - remainder) * quotient**2
    return transient + tail_collision


def direct_collision(n: int, prefix: int) -> tuple[int, Counter[int]]:
    value = coefficient(n)
    denominator = value.denominator
    numerator = value.numerator
    labels = [(numerator * pow(10, j, denominator)) % denominator for j in range(prefix)]
    fibers = Counter(labels)
    return sum(count * count for count in fibers.values()), fibers


def check_hashes() -> None:
    for name, expected in EXPECTED_HASHES.items():
        actual = sha256(ROOT / name)
        assert actual == expected, (name, actual, expected)
        print(f"HASH OK {name} {actual}")
    assert (ROOT / "singh-venkataramana-1208.6460v2.pdf").read_bytes()[:4] == b"%PDF"
    print("SOURCE PDF MAGIC OK")


def check_report_contract() -> None:
    report = (ROOT / "REPORT.md").read_text(encoding="utf-8")
    assert report.rstrip().endswith("DEVELOP")
    assert report.count("## 11. Scoped verdict") == 1
    assert "`PI-H1-COLL` (`conjecture`; unproved additional premise)" in report
    assert "This report makes no fixed-pi, C1, or C2 claim." in report
    for item in ("T79", "T85", "T112", "T118", "T121", "T123", "T125"):
        assert item in report
    print("REPORT CONTRACT OK one scoped verdict, separate premise, all comparisons")


def check_recurrence_and_valuations() -> None:
    primes = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31)
    previous = Fraction(1)
    for n in range(1, 81):
        current = coefficient(n)
        assert 36 * n * n * current == coefficient_factor(n) * previous
        u = cleared_coefficient(n)
        for prime in primes:
            actual = valuation(u, prime)
            assert actual == floor_valuation_residues(n, prime)
            assert actual == floor_valuation_factorial(n, prime)
        previous = current
    print("RECURRENCE/VALUATIONS OK n=1..80, p<=31")


def check_five_adic_bound() -> None:
    for n in range(1, 10001):
        u5 = floor_valuation_residues(n, 5)
        levels = int(math.log(6 * n - 1, 5))
        while 5 ** (levels + 1) <= 6 * n - 1:
            levels += 1
        while 5**levels > 6 * n - 1:
            levels -= 1
        deviation = Fraction(u5) - Fraction(n, 2)
        assert deviation > -2 * levels - Fraction(1, 2)
        assert deviation < 2 * levels
    print("5-ADIC EXPLICIT BOUND OK n=1..10000 (experiment)")


def check_reduced_denominators() -> None:
    for n in range(1, 31):
        value = coefficient(n)
        expected_alpha = 4 * n - 2 * digit_sum(n, 2)
        expected_beta = 3 * n - digit_sum(n, 3)
        assert alpha(n) == expected_alpha
        assert beta(n) == expected_beta
        assert value.denominator == 2**expected_alpha * 3**expected_beta
        assert math.gcd(value.numerator, 6) == 1
        for j in range(0, expected_alpha + 6):
            reduced = value * 10**j
            expected = 2 ** max(expected_alpha - j, 0) * 3**expected_beta
            assert reduced.denominator == expected
    print("REDUCED MODULI OK n=1..30 and decimal times through alpha+5")


def check_orders_and_occupancies() -> None:
    for n in range(1, 6):
        a = alpha(n)
        b = beta(n)
        order = order_10_mod_3_power(b)
        modulus = 3**b
        assert pow(10, order, modulus) == 1
        if order > 1:
            assert pow(10, order // 3, modulus) != 1
        prefix = a + order
        direct, fibers = direct_collision(n, prefix)
        assert direct == occupancy_formula(n, prefix) == prefix
        assert max(fibers.values()) == 1
        longer = a + 2 * order + min(7, order)
        direct_longer, _ = direct_collision(n, longer)
        assert direct_longer == occupancy_formula(n, longer)
        print(
            f"ORBIT EXPERIMENT n={n} alpha={a} beta={b} "
            f"order={order} one-period-collisions={direct}"
        )
    print("ORDER/OCCUPANCY FORMULA OK finite n=1..5")


def check_logarithmic_substitution() -> None:
    for agenda_a in (1, 2, 5, 10, 25):
        for n in range(max(agenda_a, 2), max(agenda_a, 2) + 20):
            orbit_order = order_10_mod_3_power(beta(n))
            block = agenda_a * n
            prefix = alpha(n) + block
            assert block <= n * n <= 9 ** (n - 1) <= orbit_order
            collision = occupancy_formula(n, prefix)
            assert collision == prefix
            assert agenda_a * n * collision <= prefix * prefix
            assert prefix <= (agenda_a + 4) * n
            assert 4**n <= coefficient(n).denominator
    print("LOG-DEPTH SUBSTITUTION OK A in {1,2,5,10,25}, 20 n-values each")


def main() -> None:
    print("All finite calculations below are EXPERIMENT checks, not universal proofs.")
    check_hashes()
    check_report_contract()
    check_recurrence_and_valuations()
    check_five_adic_bound()
    check_reduced_denominators()
    check_orders_and_occupancies()
    check_logarithmic_substitution()
    print("T126 REPLAY PASS")


if __name__ == "__main__":
    main()
