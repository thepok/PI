#!/usr/bin/env python3
"""Finite replay for T152.  Experiments are not proofs of universal claims."""

from fractions import Fraction
from hashlib import sha256
from math import isqrt, log, sqrt
from pathlib import Path


ROOT = Path(__file__).resolve().parent
EXPECTED_CANONICAL = "cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8"


def digest(name):
    return sha256((ROOT / name).read_bytes()).hexdigest()


def blocks(word, n, m):
    return [tuple(word[i : i + m]) for i in range(n)]


def energy(word, n, m):
    counts = {}
    for block in blocks(word, n, m):
        counts[block] = counts.get(block, 0) + 1
    return sum(value * value for value in counts.values()), counts


def coverage(n, k, m):
    length = n + k - 1
    d = []
    for q in range(length):
        d.append(sum(i <= q < i + m for i in range(n)))
    lambdas = [Fraction(1) - Fraction(value, m) for value in d]
    assert all(value >= 0 for value in lambdas)
    assert all(Fraction(value, m) + lam == 1 for value, lam in zip(d, lambdas))
    assert sum(lambdas) == k - 1
    return d, lambdas


def ceil_n_over_sqrt_a(n, a):
    """Return the least integer r with a*r^2 >= n^2, using integers only."""
    r = isqrt((n * n) // a)
    if a * r * r < n * n:
        r += 1
    assert a * (r - 1) * (r - 1) < n * n <= a * r * r
    return r


def de_bruijn(alphabet_size, order):
    a = [0] * (alphabet_size * order)
    sequence = []

    def db(t, p):
        if t > order:
            if order % p == 0:
                sequence.extend(a[1 : p + 1])
            return
        a[t] = a[t - p]
        db(t + 1, p)
        for value in range(a[t - p] + 1, alphabet_size):
            a[t] = value
            db(t + 1, t)

    db(1, 1)
    assert len(sequence) == alphabet_size**order
    return sequence


print("T152 finite replay (experiment, not proof)")
print(f"canonical sha256: {digest('canonical_statement.txt')}")
assert digest("canonical_statement.txt") == EXPECTED_CANONICAL

# Exact endpoints and DLFC weights.
for n, k, m in [(17, 4, 2), (31, 7, 6), (100, 9, 9)]:
    d, lambdas = coverage(n, k, m)
    assert len(d) == n + k - 1
    assert max(d) <= m
    assert (n - 1) + (m - 1) <= n + k - 2
    print(
        f"cover N={n} k={k} m={m}: max_d={max(d)} "
        f"singleton_mass={sum(lambdas)} endpoint={n + m - 2}/{n + k - 2}"
    )

# Constant family.
n, k = 40, 6
constant = [7] * (n + k - 1)
constant_energies = [energy(constant, n, m)[0] for m in range(1, k + 1)]
assert constant_energies == [n * n] * k
print(f"constant: energies={constant_energies} bad_depths={k}")

# Periodic family, including exact Cauchy lower threshold.
p = 3
periodic = [index % p for index in range(n + k - 1)]
periodic_energies = [energy(periodic, n, m)[0] for m in range(1, k + 1)]
for m in range(p, k + 1):
    assert periodic_energies[m - 1] * p >= n * n
    assert periodic_energies[m - 1] * m >= n * n
print(f"periodic p={p}: energies={periodic_energies} bad_depths={k - p + 1}")

# Decimal repeated de Bruijn family of order 3.
k_db = 3
cycle = de_bruijn(10, k_db)
n_db = len(cycle)
db_word = cycle + cycle[: k_db - 1]
db_energies = []
for m in range(1, k_db + 1):
    value, counts = energy(db_word, n_db, m)
    assert len(counts) == 10**m
    assert set(counts.values()) == {n_db // (10**m)}
    assert value == n_db * n_db // (10**m)
    assert value * m < n_db * n_db
    db_energies.append(value)
print(f"deBruijn order={k_db}: energies={db_energies} bad_depths=0")

# Shared-prefix family at finite parameters; cardinality is checked symbolically.
n_sp, k_sp = 100, 4
a_sp = (k_sp + 1) // 2
r_sp = ceil_n_over_sqrt_a(n_sp, a_sp)
fixed = r_sp + k_sp - 1
length = n_sp + k_sp - 1
shared = [0] * fixed + [index % 10 for index in range(length - fixed)]
selected = list(range(a_sp, k_sp + 1))
for m in selected:
    value, counts = energy(shared, n_sp, m)
    assert counts.get((0,) * m, 0) >= r_sp
    assert value * m >= n_sp * n_sp
assert length - fixed == n_sp - r_sp
assert len(selected) == k_sp // 2 + 1 >= (k_sp + 1) // 2
print(
    f"shared-prefix N={n_sp} k={k_sp}: a={a_sp} R={r_sp} "
    f"fixed={fixed} free={length - fixed} selected={selected}"
)

# Type and collision identities on a nontrivial word.
sample = [(7 * index + index * index) % 10 for index in range(29)]
n_type, k_type, m_type = 25, 5, 4
value, counts = energy(sample, n_type, m_type)
assert sum(counts.values()) == n_type
assert sum(Fraction(count, n_type) ** 2 for count in counts.values()) == Fraction(
    value, n_type * n_type
)
ordered = sum(
    blocks(sample, n_type, m_type)[i] == blocks(sample, n_type, m_type)[j]
    for i in range(n_type)
    for j in range(n_type)
)
assert ordered == value
print(f"type identity: total={sum(counts.values())} energy={value} ordered={ordered}")

# Numerical checks of the entropy lemma's displayed one-variable bound.
minimum_margin = float("inf")
for m in range(2, 10001):
    numerator = m * log(10) - log(2 * sqrt(2) * (m ** 1.5)) - 1
    margin = numerator / sqrt(2 * m) - sqrt(m) / 100
    minimum_margin = min(minimum_margin, margin)
    assert margin > 0
print(f"entropy-bound finite sweep m=2..10000: minimum_margin={minimum_margin:.12f}")

# Explicit N=10^16 simplification and a sparse larger sample.
for n_const in [10**16, 10**20, 10**40]:
    # These test values are exact powers of ten, so decimal digit length gives
    # floor((1/4) log_10 N) without floating-point endpoint ambiguity.
    exponent = len(str(n_const)) - 1
    assert n_const == 10**exponent
    k_const = exponent // 4
    type_term = (10**k_const) * log(n_const + 1) + log(k_const)
    saving = n_const / (100 * sqrt(k_const))
    assert k_const >= 4
    assert type_term <= 2 * sqrt(n_const)
    assert 2 * sqrt(n_const) <= n_const / (200 * sqrt(k_const))
    assert -saving + type_term <= -n_const / (200 * sqrt(k_const))
    print(
        f"constant N=1e{exponent}: k={k_const} "
        f"type/saving={type_term / saving:.12e} pure_c=1/200"
    )

for required in [
    "CHARGING_RULE: DLFC-152",
    "TERMINAL ENDPOINT (1/1)",
    "FIXED_PI_CLAIM: none",
    "PI-MEMBERSHIP-EXCLUSION-AND-T107-TRANSFER-T152",
    "T149",
]:
    assert required in (ROOT / "REPORT.md").read_text(encoding="utf-8")

print("markers and claim firewall: PASS")
print("all finite replay checks: PASS")
