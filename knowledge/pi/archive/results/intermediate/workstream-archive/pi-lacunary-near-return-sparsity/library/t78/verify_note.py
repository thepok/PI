#!/usr/bin/env python3
"""Self-contained replay checks for T78.

All bounded mathematical checks are sanity checks only. They do not prove the
universal statements in REPORT.md; those are supported by displayed proofs.
"""

from fractions import Fraction
from hashlib import sha256
from math import ceil, factorial, gcd, lcm, pi
from pathlib import Path


ROOT = Path(__file__).resolve().parent

if not __debug__:
    raise RuntimeError("Run verify_note.py without Python -O so checks stay enabled")

PINNED_HASHES = {
    "canonical_statement.txt": "cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8",
    "euler-e212-1755.pdf": "c3de459c5ecf84eca7c43dcbf9b846f3c010c9b527b46d44ec0269935b405a40",
    "euler-e212-1755.txt": "2907d73d35fe0c6f18a65f28c56aee2330cdf0f4aa263bb718d3a8606ec45c68",
    "euler-e212-1755-p295.png": "3990269603c272b2338cf3bcdd699f574357f644a74b6052243319dccb94ab0e",
    "li-e854-monthly-1949.pdf": "cb15101243c771c5478a3d19eca8b1630fff342f7dfd0166f045e1e5a83a7603",
    "li-e854-monthly-1949.txt": "0255a930605df68e48d44980b5ac6cc17e796deac4cc0ec69b3e44cd558dad91",
    "rabinowitz-wagon-spigot-1995.pdf": "09d968fb257e79df68e6f54e746353e346e628fdc999bfaaaa0bbf7cb114db1b",
    "rabinowitz-wagon-spigot-1995.txt": "a40a2b1a1ec27ad055619a81cab1c055791a4fdfa13343a99ee468a592f17500",
    "zeilberger-zudilin-2020.pdf": "3b11c4bf3e25927227ac8f7f4e49d7f1d3efeb42beecd7f3b8c64efb162d20b5",
    "zeilberger-zudilin-2020.txt": "49ca4907538e4ccea23cee27f051f5b33832ed2cf3e3093b4aab58a13c814a68",
    "bailey-crandall-2002.pdf": "d6cb4c65494b8447428a480ba9c29139fcedfac47dc3fff029ec4a50a0d8db74",
    "bailey-crandall-2002.txt": "bab7d90671a8c5384d4251b0516c4282554062cc4bd5cdcdc9d12dc02dafec47",
}

REVIEWED_TEXT_HASHES = {
    "REPORT.md": "26cc36a18ea585d85d5e7f2c23e40df61bbb1ca94639541736531feb8074af4b",
    "SOURCE_PINS.md": "0c7a81793cd9528034708e8c1a7f252dc58dfd66b05c4730b9721e19311a3ffd",
}


def digest(path: Path) -> str:
    h = sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1 << 20), b""):
            h.update(block)
    return h.hexdigest()


def check_hashes() -> None:
    for name, expected in (PINNED_HASHES | REVIEWED_TEXT_HASHES).items():
        actual = digest(ROOT / name)
        assert actual == expected, (name, expected, actual)


def check_text_anchors() -> None:
    anchors = {
        "li-e854-monthly-1949.txt": [
            "A Series for x",
            "Using the beta function",
            "Using Euler’s transformation",
        ],
        "rabinowitz-wagon-spigot-1995.txt": [
            "moderately well-known series",
            "Euler’s transform",
            "(2i +  1)!!",
        ],
        "zeilberger-zudilin-2020.txt": [
            "irrationality measure µ",
            "7.10320533413700172750577342281",
        ],
        "bailey-crandall-2002.txt": [
            "Theorem 4.6",
            "pure power",
            "gcd(H, cn )",
        ],
    }
    for name, required in anchors.items():
        text = (ROOT / name).read_text(encoding="utf-8")
        for fragment in required:
            assert fragment in text, (name, fragment)


def term(k: int) -> Fraction:
    return Fraction(2 ** (k + 1) * factorial(k) ** 2, factorial(2 * k + 1))


def partial_sum(k_count: int) -> Fraction:
    return sum((term(k) for k in range(k_count)), Fraction())


def odd_lcm(k_count: int) -> int:
    value = 1
    for odd in range(1, 2 * k_count, 2):
        value = lcm(value, odd)
    return value


def valuation(value: int, prime: int) -> int:
    if value == 0:
        raise ValueError("valuation of zero is not needed")
    result = 0
    while value % prime == 0:
        value //= prime
        result += 1
    return result


def primes_through(limit: int) -> list[int]:
    result = []
    for candidate in range(2, limit + 1):
        if all(candidate % p for p in result if p * p <= candidate):
            result.append(candidate)
    return result


def alpha(prime: int, k_count: int) -> int:
    result = 0
    power = prime
    while power <= 2 * k_count - 1:
        result += 1
        power *= prime
    return result


def five_split(q: int) -> tuple[int, int]:
    exponent = 0
    while q % 5 == 0:
        q //= 5
        exponent += 1
    return exponent, q


def multiplicative_order_10(modulus: int) -> int:
    if modulus == 1:
        return 1
    assert gcd(10, modulus) == 1
    residue = 10 % modulus
    order = 1
    while residue != 1:
        residue = residue * 10 % modulus
        order += 1
        assert order <= modulus
    return order


def circle_distance(value: Fraction) -> Fraction:
    residue = value.numerator % value.denominator
    return min(Fraction(residue, value.denominator),
               Fraction(value.denominator - residue, value.denominator))


def rational_count(s: Fraction, n_points: int, rho: Fraction) -> int:
    return sum(
        circle_distance((10 ** i - 10 ** j) * s) < rho
        for i in range(n_points)
        for j in range(n_points)
    )


def exact_equal_count(s: Fraction, n_points: int) -> int:
    return sum(
        ((10 ** i - 10 ** j) * s).denominator == 1
        for i in range(n_points)
        for j in range(n_points)
    )


def formula_data(s: Fraction, n_points: int):
    p, q = s.numerator, s.denominator
    e, m = five_split(q)
    tau = multiplicative_order_10(m)
    e0 = min(e, n_points)
    length = max(n_points - e, 0)
    quotient, remainder = divmod(length, tau)
    equal = e0 + (tau - remainder) * quotient ** 2
    equal += remainder * (quotient + 1) ** 2
    u = p * 2 ** e % m if m > 1 else 0
    y = [(u * pow(10, r, m)) % m if m > 1 else 0
         for r in range(tau)]
    weights = [quotient + (r < remainder) for r in range(tau)]
    return p, q, e, m, tau, e0, length, equal, y, weights


def formula_short_arc_count(s: Fraction, n_points: int,
                            rho: Fraction) -> int:
    p, q, _e, m, tau, e0, _length, _equal, y, weights = formula_data(
        s, n_points
    )
    transient = sum(
        circle_distance(Fraction(p * (10 ** i - 10 ** j), q)) < rho
        for i in range(e0)
        for j in range(e0)
    )
    active = [r for r in range(tau) if weights[r]]
    cross = 2 * sum(
        weights[r] * (
            circle_distance(Fraction(p * 10 ** i, q) - Fraction(y[r], m))
            < rho
        )
        for i in range(e0)
        for r in active
    )
    cycle = sum(
        weights[r] * weights[t] * (
            circle_distance(Fraction(y[r] - y[t], m)) < rho
        )
        for r in active
        for t in active
    )
    return transient + cross + cycle


def ceil_fraction(value: Fraction) -> int:
    return -(-value.numerator // value.denominator)


def occupancy_upper(s: Fraction, n_points: int, rho: Fraction) -> int:
    _p, q, _e, m, tau, e0, length, _equal, _y, _weights = formula_data(
        s, n_points
    )
    hq = min((q - 1) // 2, ceil_fraction(rho * q) - 1)
    hm = min((m - 1) // 2, ceil_fraction(rho * m) - 1)
    max_weight = max(1, ceil_fraction(Fraction(length, tau)))
    result = e0 * min(e0, 2 * hq + 1)
    result += 2 * e0 * max_weight * min(
        tau, ceil_fraction(2 * rho * m)
    )
    result += length * max_weight * min(tau, 2 * hm + 1)
    return result


def check_arithmetic() -> None:
    # Finite sanity checks only.
    for k_count in range(1, 41):
        s = partial_sum(k_count)
        d = odd_lcm(k_count)
        term_lcm = 1
        for k in range(k_count):
            term_lcm = lcm(term_lcm, term(k).denominator)
        assert term_lcm == d
        scaled = s * d
        assert scaled.denominator == 1
        p_common = scaled.numerator
        assert s == Fraction(p_common // gcd(p_common, d),
                             d // gcd(p_common, d))
        for prime in primes_through(2 * k_count - 1):
            if prime == 2:
                assert valuation(s.denominator, prime) == 0
                continue
            expected = alpha(prime, k_count)
            expected -= min(alpha(prime, k_count), valuation(p_common, prime))
            assert valuation(s.denominator, prime) == expected
        e, _m = five_split(s.denominator)
        assert 5 ** e <= 2 * k_count - 1

    for k_count in range(1, 26):
        s = partial_sum(k_count)
        first_omitted = term(k_count)
        tail = pi - float(s)
        assert float(first_omitted) < tail < 2 * float(first_omitted)
        assert 2 * first_omitted <= 2 ** (2 - k_count)


def check_modular_formulas() -> None:
    # Finite sanity checks only.
    thresholds = [
        Fraction(1, 100), Fraction(1, 17), Fraction(1, 7), Fraction(1, 2)
    ]
    # Zero-weight cycle classes are skipped above, keeping larger orders cheap
    # while covering m=1 and power-of-five transients of length at least two.
    for k_count in range(1, 16):
        s = partial_sum(k_count)
        for n_points in range(1, 31):
            data = formula_data(s, n_points)
            assert exact_equal_count(s, n_points) == data[7]
            for rho in thresholds:
                direct = rational_count(s, n_points, rho)
                formula = formula_short_arc_count(s, n_points, rho)
                assert direct == formula, (k_count, n_points, rho)
                assert direct <= occupancy_upper(s, n_points, rho)


def check_report_markers() -> None:
    report = (ROOT / "REPORT.md").read_text(encoding="utf-8")
    required = [
        "Status: `proof sketch`.",
        "## 1. Independent identity proof",
        "## 4. Exact reduced partial sums and valuations",
        "## 5. Uniform phase error for every literal pair",
        "## 9. Exact short-arc occupancy",
        "## 12. Terminal family-specific scale obstruction",
        "No unknown occupancy estimate is an endpoint",
    ]
    for marker in required:
        assert marker in report, marker


def main() -> None:
    check_hashes()
    check_text_anchors()
    check_report_markers()
    check_arithmetic()
    check_modular_formulas()
    print("T78 replay passed: source pins verified; bounded computations are sanity checks only.")


if __name__ == "__main__":
    main()
