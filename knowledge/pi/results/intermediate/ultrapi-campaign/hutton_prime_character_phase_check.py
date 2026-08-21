#!/usr/bin/env python3
"""Exact/finite checks for the Hutton signed prime-reciprocal phase.

The assertions involving Fraction/integer arithmetic are exact.  The binned
phase statistics and logarithms are floating-point experiments and are printed
as such; they are not used as proofs of equidistribution or of a digit hit.
"""

from __future__ import annotations

from fractions import Fraction
from hashlib import sha256
from math import floor, gcd, log, log10, pi, sqrt
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
SOURCE = ROOT / "problems/local/pi-digits.txt"
SOURCE_SHA256 = "2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825"


def sieve(limit: int) -> bytearray:
    prime = bytearray(b"\x01") * (limit + 1)
    prime[0:2] = b"\x00\x00"
    for p in range(2, int(limit**0.5) + 1):
        if prime[p]:
            prime[p * p : limit + 1 : p] = b"\x00" * (((limit - p * p) // p) + 1)
    return prime


def chi4(n: int) -> int:
    assert n % 2 == 1
    return 1 if n % 4 == 1 else -1


def eligible(n: int, prime: bytearray) -> bool:
    return n < len(prime) and bool(prime[n]) and n > 7 and n != 17


def selected_primes(k: int, prime: bytearray) -> list[int]:
    r = 4 * k + 3
    return [p for p in range(r // 2 + 1, r + 1) if eligible(p, prime)]


def phase_data(k: int, prime: bytearray) -> tuple[list[int], int, int, Fraction]:
    ps = selected_primes(k, prime)
    g = 1
    for p in ps:
        g *= p
    s = sum(chi4(p) * (g // p) for p in ps)
    delta = Fraction(s, g) if ps else Fraction(0)
    return ps, g, s, delta


def recurrence_increment(k: int, prime: bytearray) -> Fraction:
    ans = Fraction(0)
    for n, sign in ((4 * k + 5, 1), (4 * k + 7, -1)):
        if eligible(n, prime):
            ans += Fraction(sign, n)
    n = 2 * k + 3
    if eligible(n, prime):
        ans += Fraction((-1) ** k, n)
    return ans


def event_signature(k: int, prime: bytearray) -> tuple[bool, bool, bool]:
    return (
        eligible(4 * k + 5, prime),
        eligible(4 * k + 7, prime),
        eligible(2 * k + 3, prime),
    )


def exact_checks(prime: bytearray) -> tuple[int, int]:
    exact_groups = 0
    logarithmic_checks = 0
    deltas: list[Fraction] = []

    for k in range(2, 601):
        ps, g, s, delta = phase_data(k, prime)
        assert delta == sum((Fraction(chi4(p), p) for p in ps), Fraction(0))
        if ps:
            assert gcd(s, g) == 1

        # F(X) = product (p + chi_4(p) X): F(0)=G and F'(0)=S.
        coefficients = [1]
        for p in ps:
            eps = chi4(p)
            nxt = [0] * (len(coefficients) + 1)
            for j, coefficient in enumerate(coefficients):
                nxt[j] += p * coefficient
                nxt[j + 1] += eps * coefficient
            coefficients = nxt
        assert coefficients[0] == g
        assert (coefficients[1] if len(coefficients) > 1 else 0) == s

        # Every local summand is G (mod 4), so S == #P * G (mod 4).
        assert (s - len(ps) * g) % 4 == 0

        # Symmetric log product.  The inequality is checked numerically here;
        # its proof in the report is the absolutely convergent atanh series.
        if ps:
            a = 1
            c = 1
            error_bound = 0.0
            for p in ps:
                eps = chi4(p)
                a *= p + eps
                c *= p - eps
                error_bound += 1.0 / (3.0 * p * (p * p - 1))
            approximation = 0.5 * log(a / c)
            assert abs(float(delta) - approximation) <= error_bound * (1 + 1e-10)
            logarithmic_checks += 1

        deltas.append(delta)
        exact_groups += 1

    for offset, k in enumerate(range(2, 600)):
        assert deltas[offset + 1] - deltas[offset] == recurrence_increment(k, prime)

    # Exact counterexamples to fixed affine first-order behavior: two distinct
    # plateaus force a=1,c=0, while another adjacent pair changes.
    plateau_values: list[Fraction] = []
    changed = False
    for k in range(2, 599):
        d0 = deltas[k - 2]
        d1 = deltas[k - 1]
        if d0 == d1 and d0 not in plateau_values:
            plateau_values.append(d0)
        if d0 != d1:
            changed = True
    assert len(plateau_values) >= 2 and changed

    # No event-pattern rule depending only on K mod m survives this range.
    for modulus in range(1, 65):
        seen: dict[int, tuple[bool, bool, bool]] = {}
        collision = False
        for k in range(40, 600):
            residue = k % modulus
            signature = event_signature(k, prime)
            if residue in seen and seen[residue] != signature:
                collision = True
                break
            seen[residue] = signature
        assert collision, modulus

    assert any(d < 0 for d in deltas) and any(d > 0 for d in deltas)
    assert any(deltas[i] != deltas[i + 6] for i in range(len(deltas) - 6))
    return exact_groups, logarithmic_checks


def explicit_bounds() -> tuple[float, float, float, float]:
    # Bennett--Martin--O'Bryant--Rechnitzer, Theorem 1.2 and its q=4 table.
    c_theta_pair = 2.0 * 0.0004822
    r_unconditional = 2.0 * 4_800_162_889.0
    ell = log(r_unconditional)
    ell_half = log(r_unconditional / 2.0)
    d_unconditional = c_theta_pair * (
        1.0 / ell_half
        - 1.0 / ell
        + 0.5 / ell**2
        + 1.5 / ell_half**2
    )
    b_unconditional = floor(log(r_unconditional, 5))
    scaled_unconditional = 10.0**b_unconditional * d_unconditional

    # Lee, Corollary 4.4, x0=e^10, q=4; the negative Omega_2 term is dropped.
    r_grh = 2.0 * (2.718281828459045**10)
    lg = log(r_grh)
    lh = log(r_grh / 2.0)
    m = lg**2 / (8.0 * pi) + (log(4.0) / (2.0 * pi) + 9.17523) * lg + 0.78834
    d_grh = m / sqrt(r_grh) * (
        (3.0 * sqrt(2.0) - 1.0) / lh + 2.0 * (sqrt(2.0) - 1.0) / lh**2
    )
    b_grh = floor(log(r_grh, 5))
    scaled_grh = 10.0**b_grh * d_grh
    assert scaled_unconditional > 1.0 and scaled_grh > 1.0
    return d_unconditional, scaled_unconditional, d_grh, scaled_grh


def phase_experiment(prime: bytearray, b: int) -> tuple[int, list[int], float, int]:
    r_lo = 5**b
    r_hi = 5 ** (b + 1)
    k_lo = max(2, (r_lo - 3 + 3) // 4)
    k_hi = (r_hi - 3 + 3) // 4
    prefix = [0.0] * r_hi
    running = 0.0
    for n in range(1, r_hi):
        if eligible(n, prime):
            running += chi4(n) / n
        prefix[n] = running

    bins = [0] * 20
    values: list[float] = []
    repeats = 0
    previous_delta: float | None = None
    multiplier = float(10**b)
    for k in range(k_lo, k_hi):
        r = 4 * k + 3
        if not (r_lo <= r < r_hi):
            continue
        delta = prefix[r] - prefix[r // 2]
        if previous_delta is not None and delta == previous_delta:
            repeats += 1
        previous_delta = delta
        value = (multiplier * delta) % 1.0
        values.append(value)
        bins[min(19, int(20.0 * value))] += 1

    values.sort()
    count = len(values)
    star_discrepancy = max(
        max(abs(value - i / count), abs((i + 1) / count - value))
        for i, value in enumerate(values)
    )
    return count, bins, star_discrepancy, repeats


def orbit_experiment(k: int, prime: bytearray) -> tuple[int, int, int, int]:
    ps, g, s, _ = phase_data(k, prime)
    assert ps and gcd(g, 10) == 1
    r = 4 * k + 3
    b = floor(log(r, 5))
    residue = (pow(10, b, g) * (s % g)) % g
    horizon = floor(0.4 * r)
    cells: set[int] = set()
    for _ in range(horizon + 1):
        cells.add((100 * residue) // g)
        residue = (10 * residue) % g
    return k, r, horizon + 1, len(cells)


def main() -> None:
    digest = sha256(SOURCE.read_bytes()).hexdigest()
    assert digest == SOURCE_SHA256

    limit = 5**9
    prime = sieve(limit)
    exact_groups, logarithmic_checks = exact_checks(prime)
    du, sdu, dg, sdg = explicit_bounds()

    print(f"source sha256: {digest}")
    print(f"exact phase/polynomial/recurrence groups: {exact_groups}")
    print(f"finite symmetric-log inequalities checked: {logarithmic_checks}")
    print("fixed affine, six-periodic, and K-mod-m event rules: falsified")
    print(f"explicit unconditional endpoint: Delta bound={du:.9e}, 10^b bound={sdu:.9e}")
    print(f"explicit GRH endpoint:          Delta bound={dg:.9e}, 10^b bound={sdg:.9e}")

    for b in (7, 8):
        count, bins, discrepancy, repeats = phase_experiment(prime, b)
        print(
            f"experiment b={b}: K-count={count}, adjacent repeats={repeats}, "
            f"20-bin counts={bins}, star-discrepancy={discrepancy:.6g}"
        )

    print("experiment isolated Delta-orbit two-digit coverage (c=0.4):")
    for k in (100, 200, 400, 800):
        kk, r, starts, cells = orbit_experiment(k, prime)
        print(f"  K={kk:4d} R={r:4d} starts={starts:4d} distinct-cells={cells:3d}")
    print("all exact checks passed; distribution rows are experiments only")


if __name__ == "__main__":
    main()
