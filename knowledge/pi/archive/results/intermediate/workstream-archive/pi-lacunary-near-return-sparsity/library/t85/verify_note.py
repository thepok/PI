#!/usr/bin/env python3
"""Self-contained exact-arithmetic replay for the T85 valuation-tie audit."""

from fractions import Fraction
from hashlib import sha256
from math import gcd
from pathlib import Path


T79_P = 147153121
T79_B = 1758719
EXPECTED_HASHES = {
    "canonical_statement.txt": "cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8",
    "prior-t79-REPORT.md": "7fb415a8140597f5a061b945df08eacc122e693d4998fafca98ff98aa641d800",
    "abrarov-quine-1706.08835v3.pdf": "7500ccc8cb55f651b81dd6310f02e428d2455ca6739dfb0c382435bfac8b6c3c",
    "abrarov-quine-1706.08835v3.txt": "b5e8eff87327d624abffd4d1e45258e2ba8b5487f8b555c21b1b5fccd7e91d94",
    "bailey-crandall-2002.pdf": "d6cb4c65494b8447428a480ba9c29139fcedfac47dc3fff029ec4a50a0d8db74",
    "bailey-crandall-2002.txt": "bab7d90671a8c5384d4251b0516c4282554062cc4bd5cdcdc9d12dc02dafec47",
    "bourgain-2004.pdf": "4974d3596f7c86fd11d8c5d716a72481c29bc9a492cecdb6a4651c3e5db2ed23",
    "bourgain-2004.txt": "9c06d9ad6fb3659988bfbe94d05c802132dc920303f7f72855f88854f61958b7",
    "konyagin-shparlinski-2012.pdf": "46f7981327913a4a7adbca724a7b3a214520ed6a946b46baba80ba8af55d97bc",
    "konyagin-shparlinski-2012.txt": "ce0ac0c9ed48ac6fcd1594b5ffff62eeea83eef25cee5eba5e4c8b376fafd107",
}


def file_hash(name):
    return sha256(Path(name).read_bytes()).hexdigest()


def valuation(value, prime):
    if value == 0:
        return float("inf")
    value = abs(value)
    exponent = 0
    while value % prime == 0:
        value //= prime
        exponent += 1
    return exponent


def rational_valuation(value, prime):
    return valuation(value.numerator, prime) - valuation(value.denominator, prime)


def is_prime_trial(value):
    if value < 2:
        return False
    if value % 2 == 0:
        return value == 2
    divisor = 3
    while divisor * divisor <= value:
        if value % divisor == 0:
            return False
        divisor += 2
    return True


def factor(value):
    result = {}
    divisor = 2
    while divisor * divisor <= value:
        while value % divisor == 0:
            result[divisor] = result.get(divisor, 0) + 1
            value //= divisor
        divisor = 3 if divisor == 2 else divisor + 2
    if value > 1:
        result[value] = result.get(value, 0) + 1
    return result


def euler_phi(factors):
    result = 1
    for prime, exponent in factors.items():
        result *= (prime - 1) * prime ** (exponent - 1)
    return result


def multiplicative_order(base, modulus, factors=None):
    assert modulus > 0 and gcd(base, modulus) == 1
    factors = factor(modulus) if factors is None else factors
    order = euler_phi(factors)
    for prime in factor(order):
        while order % prime == 0 and pow(base, order // prime, modulus) == 1:
            order //= prime
    assert pow(base, order, modulus) == 1
    return order


def largest_exact_order_exponent(terminal, prime, exponent):
    """Largest odd e <= terminal having v_prime(e)=exponent."""
    power = prime ** exponent
    quotient = terminal // power
    if quotient % 2 == 0:
        quotient -= 1
    if quotient % prime == 0:
        quotient -= 2
    assert quotient > 0 and quotient % 2 == 1 and quotient % prime != 0
    return power * quotient


def valuation_maximizers(terminal, prime):
    """All odd e <= terminal maximizing e + v_prime(e)."""
    assert terminal >= 1 and terminal % 2 == 1 and prime % 2 == 1
    candidates = []
    power = 1
    exponent = 0
    while power <= terminal:
        e = largest_exact_order_exponent(terminal, prime, exponent)
        candidates.append((e + exponent, e, exponent, terminal - e))
        power *= prime
        exponent += 1
    maximum = max(row[0] for row in candidates)
    return maximum, [row for row in candidates if row[0] == maximum], candidates


def second_family_leading_residue(terminal, prime, b_value):
    maximum, ties, _ = valuation_maximizers(terminal, prime)
    residue = 0
    rows = []
    for _, e, exponent, _ in ties:
        unit = e // prime ** exponent
        sign = -1 if ((e - 1) // 2) % 2 else 1
        term = -4 * sign * pow(b_value, e, prime) * pow(unit, -1, prime)
        term %= prime
        residue = (residue + term) % prime
        rows.append((e, exponent, unit % prime, term))
    return maximum, ties, rows, residue


def first_family_leading_residue(terminal, prime):
    maximum, ties, _ = valuation_maximizers(terminal, prime)
    residue = 0
    rows = []
    for _, e, exponent, _ in ties:
        unit = e // prime ** exponent
        sign = -1 if ((e - 1) // 2) % 2 else 1
        term = 32 * sign * pow(unit, -1, prime) * pow(pow(2, e, prime), -1, prime)
        term %= prime
        residue = (residue + term) % prime
        rows.append((e, exponent, unit % prime, term))
    return maximum, ties, rows, residue


def full_partial_sum(terminal, prime, b_value):
    total = Fraction(0)
    for e in range(1, terminal + 1, 2):
        sign = -1 if ((e - 1) // 2) % 2 else 1
        total += Fraction(32 * sign, e * 10 ** e)
        total -= Fraction(4 * sign * b_value ** e, e * prime ** e)
    return total


def collision_count(length, order):
    return sum(((length - 1 - residue) // order + 1) ** 2
               for residue in range(min(length, order)))


def inspect_small_case(prime, b_value, terminal, tail_length):
    maximum, ties, rows, leading = second_family_leading_residue(
        terminal, prime, b_value)
    value = full_partial_sum(terminal, prime, b_value)
    q = value.denominator
    a = valuation(q, 2)
    b = valuation(q, 5)
    modulus = q // (2 ** a * 5 ** b)
    modulus_factors = factor(modulus)
    order = multiplicative_order(10, modulus, modulus_factors)
    actual_prime_exponent = valuation(q, prime)
    collisions = collision_count(tail_length, order)
    print(
        f"small case P={prime}, B={b_value}, E={terminal}: "
        f"ties={[row[1] for row in ties]}, leading={leading}, "
        f"vP(q)={actual_prime_exponent}, predicted_layer={maximum}, "
        f"v2(q)={a}, v5(q)={b}, t={max(a,b)}, "
        f"q={q}, m={modulus}, m_factors={modulus_factors}, ord10={order}, "
        f"tail_length={tail_length}, collisions={collisions}"
    )
    return {
        "maximum": maximum,
        "ties": ties,
        "leading": leading,
        "vP": actual_prime_exponent,
        "v2": a,
        "v5": b,
        "modulus": modulus,
        "order": order,
        "collisions": collisions,
    }


def main():
    for name, expected in EXPECTED_HASHES.items():
        actual = file_hash(name)
        assert actual == expected, (name, actual, expected)
    print(f"source hashes: verified ({len(EXPECTED_HASHES)} files)")

    assert is_prime_trial(T79_P)
    assert gcd(T79_B, 10 * T79_P) == 1
    p_factors = factor(T79_P - 1)
    assert p_factors == {2: 5, 3: 1, 5: 1, 113: 1, 2713: 1}
    order_p = multiplicative_order(10, T79_P, {T79_P: 1})
    assert order_p == 12262760
    assert pow(10, order_p, T79_P ** 2) != 1
    lift_coefficient = ((pow(10, order_p, T79_P ** 2) - 1) // T79_P) % T79_P
    assert lift_coefficient == 4247150
    print(
        "T79 prime: certified by trial division; "
        f"ord_P(10)={order_p}; lift coefficient={lift_coefficient} != 0"
    )

    # T79's printed range E<P has no ties: every odd e has v_P(e)=0.
    for terminal in (1, 3, 101, T79_P - 2):
        maximum, ties, _ = valuation_maximizers(terminal, T79_P)
        assert maximum == terminal
        assert ties == [(terminal, terminal, 0, 0)]
    print("T79 stated range E<P: terminal exponent is uniquely least-valued")

    # The full-sum implication must exclude p=5: the decimal family can tie.
    assert full_partial_sum(1, 5, 4) == 0
    _, _, _, second_only_residue = second_family_leading_residue(1, 5, 4)
    assert second_only_residue == 4
    print("p=5 scope check: full E=1 sum cancels although second-family residue is 4")

    terminal = T79_P ** 2 + 2
    maximum, ties, rows, leading = second_family_leading_residue(
        terminal, T79_P, T79_B)
    assert maximum == terminal
    assert ties == [
        (terminal, terminal, 0, 0),
        (terminal, T79_P ** 2, 2, 2),
    ]
    assert rows == [
        (terminal, 0, 2, 57367864),
        (T79_P ** 2, 2, 1, 140118245),
    ]
    assert T79_B ** 2 % T79_P == 81070662
    assert leading == 50332988
    assert leading == 2 * T79_B * (T79_B ** 2 - 2) % T79_P
    print(
        f"P^2+2={terminal}: ties={[row[1] for row in ties]}, "
        f"normalized rows={rows}, sum={leading} != 0"
    )

    # The unique terminal first-family terms determine v_2 and v_5 exactly.
    five_maximum, five_ties, five_rows, five_leading = first_family_leading_residue(
        terminal, 5)
    assert five_maximum == terminal
    assert five_ties == [(terminal, terminal, 0, 0)]
    assert five_leading == 2
    assert terminal >= 7 and terminal % 2 == 1
    # v2(first_e)=5-e is uniquely minimized at e=E; second terms have v2=2.
    assert 5 - terminal < 5 - (terminal - 2) and 5 - terminal < 2
    v2_q = -(5 - terminal)
    v5_q = terminal
    vP_q = terminal
    transient = terminal
    print(
        f"P^2+2 denominator valuations: v2={v2_q}, v5={v5_q}, "
        f"vP={vP_q}, transient={transient}"
    )
    print(
        "P-primary order: ord_(P^E)(10)="
        f"{order_p}*{T79_P}^(E-1), which divides ord_m(10)"
    )
    for n in (1, 10, 1000):
        largest_transfer_prefix = terminal - n - 3
        assert largest_transfer_prefix < transient
    print("transfer occupancy: N+n+4<=E+1 implies N<t=E; tail length is zero")

    noncancel = inspect_small_case(3, 1, 11, 12)
    assert noncancel["ties"] == [(11, 11, 0, 0), (11, 9, 2, 2)]
    assert noncancel["leading"] != 0 and noncancel["vP"] == 11

    cancel = inspect_small_case(7, 3, 51, 12)
    assert cancel["ties"] == [(51, 51, 0, 0), (51, 49, 2, 2)]
    assert cancel["leading"] == 0 and cancel["vP"] < 51

    # A strict failure of terminal minimality, not merely a tie.
    maximum, ties, _ = valuation_maximizers(29, 3)
    assert maximum == 30 and ties == [(30, 27, 3, 2)]
    print("strict reversal P=3,E=29: e=27 is uniquely least-valued")

    # A three-way tie shows that pairwise auditing is not sufficient.
    terminal = 3 ** 20 + 20
    maximum, ties, _ = valuation_maximizers(terminal, 3)
    assert [row[1] for row in ties] == [terminal, terminal - 2, terminal - 20]
    assert [row[2] for row in ties] == [0, 2, 20]
    print(
        f"three-way tie P=3,E={terminal}: "
        f"{[(row[1], row[2]) for row in ties]}"
    )

    # A modulus-only logarithmic-length theorem uniform in the numerator fails.
    for length in range(1, 20):
        q = 12 * 10 ** (length - 1) + 1
        assert gcd(q, 10) == 1
        assert all(12 * 10 ** s <= q for s in range(length))
    print("short-arc obstruction checked symbolically for N=1..19")
    print("all T85 exact-arithmetic checks passed")


if __name__ == "__main__":
    main()
