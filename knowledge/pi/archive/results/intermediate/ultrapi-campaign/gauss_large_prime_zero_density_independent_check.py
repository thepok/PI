#!/usr/bin/env python3
"""Independent exact audit for gauss_large_prime_zero_density_reduction.md.

The proof-relevant assertions use integers and modular arithmetic.  Floating
point logarithms occur only in the explicitly labelled finite statistics.
This file does not import the primary checker.
"""

from __future__ import annotations

from hashlib import sha256
from math import comb, isqrt, log
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
REPORT = ROOT / "work/ultrapi-resume/gauss_large_prime_zero_density_reduction.md"
TARGET = ROOT / "problems/local/pi-digits.txt"
TARGET_SHA256 = "2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825"


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def primes_through(limit: int) -> tuple[list[int], bytearray]:
    sieve = bytearray(b"\x01") * (limit + 1)
    sieve[0:2] = b"\x00\x00"
    for prime in range(2, isqrt(limit) + 1):
        if sieve[prime]:
            sieve[prime * prime : limit + 1 : prime] = b"\x00" * (
                (limit - prime * prime) // prime + 1
            )
    return [n for n in range(2, limit + 1) if sieve[n]], sieve


def a_formula(n: int) -> int:
    """Coefficient [X^n](X^2+2X+2)^n, independently expanded."""

    return sum(
        comb(n, 2 * k) * comb(2 * k, k) * 2 ** (n - k)
        for k in range(n // 2 + 1)
    )


def a_table(last: int) -> list[int]:
    values = [1, 2]
    for n in range(1, last):
        numerator = 2 * (2 * n + 1) * values[n] + 4 * n * values[n - 1]
        require(numerator % (n + 1) == 0, f"A recurrence integrality n={n}")
        values.append(numerator // (n + 1))
    return values[: last + 1]


def legendre_scaled_formula(n: int) -> list[int]:
    """Coefficient list of 2^n P_n(X), from the closed binomial formula."""

    result = [0] * (n + 1)
    for k in range(n // 2 + 1):
        result[n - 2 * k] = (-1) ** k * comb(n, k) * comb(2 * n - 2 * k, n)
    return result


def gaussian_remainder(coefficients: list[int]) -> tuple[int, int]:
    constant = sum(
        (-1) ** (exponent // 2) * coefficient
        for exponent, coefficient in enumerate(coefficients)
        if exponent % 2 == 0
    )
    linear = sum(
        (-1) ** ((exponent - 1) // 2) * coefficient
        for exponent, coefficient in enumerate(coefficients)
        if exponent % 2 == 1
    )
    return constant, linear


def u_block(prime: int) -> list[int]:
    """U_0,...,U_{p-1} modulo p from its normalized recurrence."""

    values = [1, 1]
    for n in range(2, prime):
        values.append(
            (
                (2 * n - 1) * values[n - 1]
                + (n - 1) * values[n - 2]
            )
            * pow(n, -1, prime)
            % prime
        )
    return values[:prime]


def d_power_block(prime: int) -> list[int]:
    """Coefficients of (1-2X-X^2)^((p-1)/2) modulo p."""

    coefficients = [1]
    for _ in range((prime - 1) // 2):
        following = [0] * (len(coefficients) + 2)
        for exponent, coefficient in enumerate(coefficients):
            following[exponent] += coefficient
            following[exponent + 1] -= 2 * coefficient
            following[exponent + 2] -= coefficient
        coefficients = [coefficient % prime for coefficient in following]
    return coefficients


def floor_cuberoot(value: int) -> int:
    lower, upper = 0, 1
    while upper**3 <= value:
        lower, upper = upper, 2 * upper
    while lower + 1 < upper:
        middle = (lower + upper) // 2
        if middle**3 <= value:
            lower = middle
        else:
            upper = middle
    return lower


# File integrity and the corrected quantifier/control-character boundary.
require(sha256(TARGET.read_bytes()).hexdigest() == TARGET_SHA256, "target pin")
report_bytes = REPORT.read_bytes()
require(b"\r" not in report_bytes and b"\x00" not in report_bytes, "report controls")
require(
    not any(byte < 32 and byte not in (9, 10) for byte in report_bytes),
    "unexpected report C0 byte",
)
report_text = report_bytes.decode("utf-8")
require("For an integer \\(B\\ge1\\)" in report_text, "integer-B correction")


# 1. Normalization, Gaussian remainder, resultant, and polynomial iff.
ALGEBRA_LAST = 48
A = a_table(10_000)
for n in range(ALGEBRA_LAST + 1):
    require(A[n] == a_formula(n), f"central coefficient normalization n={n}")
    coefficients = legendre_scaled_formula(n)
    c0, c1 = gaussian_remainder(coefficients)
    expected = (
        ((-1) ** (n // 2) * A[n], 0)
        if n % 2 == 0
        else (0, (-1) ** ((n - 1) // 2) * A[n])
    )
    require((c0, c1) == expected, f"Gaussian remainder n={n}")
    # For a monic quadratic X^2+1, the resultant is the Gaussian norm of
    # the Euclidean remainder c0+c1 X, independently of factorization in F_p.
    require(c0 * c0 + c1 * c1 == A[n] * A[n], f"resultant n={n}")

small_primes, _ = primes_through(251)
irreducible_checks = 0
for prime in small_primes:
    if prime == 2:
        continue
    if prime % 4 == 3:
        irreducible_checks += 1
    for n in range(ALGEBRA_LAST + 1):
        c0, c1 = gaussian_remainder(legendre_scaled_formula(n))
        divides_a = A[n] % prime == 0
        polynomial_divides = c0 % prime == 0 and c1 % prime == 0
        square_divides_resultant = A[n] * A[n] % (prime * prime) == 0
        require(
            divides_a == polynomial_divides == square_divides_resultant,
            f"resultant iff p={prime}, n={n}",
        )
require(irreducible_checks > 0, "p=3 mod 4 cases exercised")


# 2. First-block identity, signed reflection, and zero counts.
PRIME_LAST = 10_000
primes, is_prime = primes_through(PRIME_LAST)
zero_sets: dict[int, frozenset[int]] = {}
max_zero_record = (0, 0, ())
for prime in primes:
    if prime == 2:
        continue
    block = u_block(prime)
    if prime <= 257:
        require(block == d_power_block(prime), f"Frobenius block p={prime}")
    m = (prime - 1) // 2
    require(block[-1] == (-1) ** m % prime, f"last coefficient p={prime}")
    for s in range(prime):
        require(
            block[prime - 1 - s] == (-1) ** (m + s) * block[s] % prime,
            f"signed reflection p={prime}, s={s}",
        )
    zeros = tuple(index for index, value in enumerate(block) if value == 0)
    zero_sets[prime] = frozenset(zeros)
    require(
        all(zeros[i + 1] != zeros[i] + 1 for i in range(len(zeros) - 1)),
        f"consecutive zeros p={prime}",
    )
    require(len(zeros) <= (prime - 1) // 2, f"weight bound p={prime}")
    if len(zeros) > max_zero_record[0]:
        max_zero_record = (len(zeros), prime, zeros)

require(
    max_zero_record
    == (8, 2777, (309, 551, 1286, 1382, 1394, 1490, 2225, 2467)),
    "reported first-block zero record",
)


# 3. Forward selector, exact converse, strict boundaries, and compact bound.
SCAN_LAST = 10_000
selected_pairs: list[list[tuple[int, int, int]]] = [
    [] for _ in range(SCAN_LAST + 1)
]
weights = [0.0] * (SCAN_LAST + 1)
encoded_count = 0
direct_count = reflected_count = central_count = equality_count = 0
for n in range(2, SCAN_LAST + 1):
    for prime in primes:
        if prime == 2 or prime * prime <= n:
            continue
        if prime >= n:
            break
        a, s = divmod(n, prime)
        if s not in zero_sets[prime]:
            continue
        t = min(s, prime - 1 - s)
        require(a >= 1 and a < prime, f"quotient range n={n}, p={prime}")
        require(prime > 2 * t, f"minimal size n={n}, p={prime}")
        require(A[t] % prime == 0, f"reflected divisor n={n}, p={prime}")
        require((2 * a + 1) * t <= n - a, f"triangle n={n}, p={prime}")
        direct = n == a * prime + t
        reflected = n == (a + 1) * prime - 1 - t
        require(direct or reflected, f"selector disjunction n={n}, p={prime}")
        require(
            direct == (prime == (n - t) // a and (n - t) % a == 0),
            f"direct quotient n={n}, p={prime}",
        )
        require(
            reflected
            == (
                prime == (n + 1 + t) // (a + 1)
                and (n + 1 + t) % (a + 1) == 0
            ),
            f"reflected quotient n={n}, p={prime}",
        )
        direct_count += int(direct)
        reflected_count += int(reflected)
        central_count += int(direct and reflected)
        equality_count += int((2 * a + 1) * t == n - a)
        selected_pairs[n].append((prime, a, t))
        weights[n] += log(prime)
        encoded_count += 1

require(encoded_count == 7803, "reported selected-pair count")
require(direct_count > central_count and reflected_count > central_count, "both branches")
require(central_count > 0 and equality_count >= central_count, "central boundary")

# Exhaustively reconstruct the converse at manageable depth from both affine
# selectors.  In particular, p>2t makes the stated quotient a=floor(n/p).
CONVERSE_LAST = 1800
converse_candidates = 0
for n in range(2, CONVERSE_LAST + 1):
    selected_primes = {prime for prime, _, _ in selected_pairs[n]}
    for a in range(1, isqrt(n) + 1):
        for t in range((n - a) // (2 * a + 1) + 1):
            for denominator, numerator in ((a, n - t), (a + 1, n + 1 + t)):
                if numerator % denominator:
                    continue
                prime = numerator // denominator
                if not (
                    2 < prime < n
                    and prime <= PRIME_LAST
                    and is_prime[prime]
                    and prime * prime > n
                    and prime > 2 * t
                    and A[t] % prime == 0
                ):
                    continue
                require(n // prime == a, f"converse quotient n={n}, p={prime}")
                residue = n % prime
                require(
                    t == min(residue, prime - 1 - residue),
                    f"converse minimal index n={n}, p={prime}",
                )
                require(prime in selected_primes, f"converse selection n={n}, p={prime}")
                converse_candidates += 1
require(converse_candidates > 1000, "converse coverage")


# 4. Exact tail premises for many integer B and T, including the advertised
# floor cube-root choice.  The pre-correction real-B inference is also
# explicitly rejected: a>B need not imply a>=B+1 when B is nonintegral.
require(2 > 1.5 and not (2 >= 1.5 + 1), "real-B counterexample")
tail_instances = 0
for n in range(8, 3001):
    b0 = floor_cuberoot(n)
    choices_b = {1, b0, max(1, b0 - 1), b0 + 1, min(isqrt(n), 12)}
    choices_t = {1, 2, 5, b0, b0 + 1}
    for B in choices_b:
        for T in choices_t:
            endpoint_products: dict[int, int] = {}
            categories = 0
            for prime, a, t in selected_pairs[n]:
                if a > B:
                    require(
                        prime <= n // (B + 1),
                        f"tail cutoff n={n}, B={B}, p={prime}",
                    )
                elif t <= T:
                    endpoint_products[t] = endpoint_products.get(t, 1) * prime
                categories += 1
            require(categories == len(selected_pairs[n]), f"partition n={n}")
            for t, product in endpoint_products.items():
                require(A[t] % product == 0, f"endpoint product n={n}, t={t}")
            tail_instances += 1


# 5. Independently reproduce the finite W_n/n statistics (experiment only).
dyadic_statistics = []
for upper in (100, 1000, 10_000):
    lower = upper // 2
    maximizer = max(range(lower, upper + 1), key=lambda n: weights[n] / n)
    mean = sum(weights[n] / n for n in range(lower, upper + 1)) / (
        upper - lower + 1
    )
    dyadic_statistics.append((upper, maximizer, weights[maximizer] / maximizer, mean))

expected_statistics = [
    (100, 68, 0.10771308793159606, 0.018902677932601458),
    (1000, 505, 0.03380773184168008, 0.005139887790901463),
    (10_000, 5009, 0.006701765654129378, 0.0007040017576365069),
]
for actual, expected in zip(dyadic_statistics, expected_statistics):
    require(actual[:2] == expected[:2], f"finite statistic indices {actual}")
    require(abs(actual[2] - expected[2]) < 1e-15, f"finite maximum {actual}")
    require(abs(actual[3] - expected[3]) < 1e-15, f"finite mean {actual}")


print(
    "PASS: independent normalization/resultant/reflection and both selector "
    f"directions on {encoded_count} selected pairs; {converse_candidates} "
    f"converse candidates and {tail_instances} exact tail instances"
)
print(
    "BOUNDARY: X^2+1 divisibility is in F_p[X] and includes p=3 mod 4; "
    "the corrected tail theorem requires integer B"
)
print(
    "EXPERIMENT: first-block zero record and all three reported W_n/n "
    "statistics independently reproduced; no o(n), exceptional-gcd, or V1 claim"
)
