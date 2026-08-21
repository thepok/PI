#!/usr/bin/env python3
"""Self-contained finite replay for the T118 literature audit.

All factorizations and numerical orbit sums printed here are experiments.  The
universal order and transfer arguments are given in REPORT.md.
"""

from __future__ import annotations

import cmath
from decimal import Decimal, ROUND_HALF_UP, localcontext
from functools import reduce
from hashlib import sha256
from math import gcd, isqrt, log, pi
from pathlib import Path
from random import Random


ROOT = Path(__file__).resolve().parent
EXPECTED = {
    "canonical_statement.txt": "cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8",
    "bailey-crandall-2002.pdf": "d6cb4c65494b8447428a480ba9c29139fcedfac47dc3fff029ec4a50a0d8db74",
    "bailey-crandall-2002.txt": "bab7d90671a8c5384d4251b0516c4282554062cc4bd5cdcdc9d12dc02dafec47",
    "kerr-1302.4170v1.pdf": "9136dc3965da376942f653b2b06de8d92d7e5e997ee536e1257979698b73e4bd",
    "kerr-1302.4170v1.txt": "2a13bcbb1416ceaf783095661282cf08f9834a71b7a71a97f750d7c314d6ea6b",
    "bourgain-2004.pdf": "4974d3596f7c86fd11d8c5d716a72481c29bc9a492cecdb6a4651c3e5db2ed23",
    "bourgain-2004.txt": "9c06d9ad6fb3659988bfbe94d05c802132dc920303f7f72855f88854f61958b7",
    "zeilberger-zudilin-2020.pdf": "3b11c4bf3e25927227ac8f7f4e49d7f1d3efeb42beecd7f3b8c64efb162d20b5",
    "zeilberger-zudilin-2020.txt": "49ca4907538e4ccea23cee27f051f5b33832ed2cf3e3093b4aab58a13c814a68",
    "t116-report.md": "573011bda281022483a113829138112494b73d667323c30aa2a0ef03bba32cd1",
}


def digest(path: Path) -> str:
    return sha256(path.read_bytes()).hexdigest()


def check_pins() -> None:
    for name, expected in EXPECTED.items():
        actual = digest(ROOT / name)
        assert actual == expected, (name, actual, expected)
    canonical = (ROOT / "canonical_statement.txt").read_text()
    assert "pairs are ordered and the diagonal is included" in canonical
    assert "for every integer A >= 1" in canonical
    anchors = {
        "bailey-crandall-2002.txt": ["Lemma 4.5", "Theorem 4.6", "ord(b, c)"],
        "kerr-1302.4170v1.txt": ["Theorem 2. For g", "71/96", "N < t"],
        "bourgain-2004.txt": ["Theorem 3.2", "t > p", "p−δ t"],
        "zeilberger-zudilin-2020.txt": ["irrationality measure", "7.103205334137001"],
        "t116-report.md": [
            "effective finite-scale orbit-avoidance selector",
            "C-RS: computable variable-depth dyadic avoidance tree",
            "PI-RS:",
            "TERMINAL_VERDICT: hold as model",
        ],
    }
    for name, needles in anchors.items():
        text = (ROOT / name).read_text(errors="replace")
        for needle in needles:
            assert needle in text, (name, needle)


def is_prime(n: int) -> bool:
    if n < 2:
        return False
    small = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37)
    for p in small:
        if n % p == 0:
            return n == p
    d, s = n - 1, 0
    while d % 2 == 0:
        s += 1
        d //= 2
    for a in (2, 325, 9375, 28178, 450775, 9780504, 1795265022):
        if a % n == 0:
            continue
        x = pow(a, d, n)
        if x in (1, n - 1):
            continue
        for _ in range(s - 1):
            x = x * x % n
            if x == n - 1:
                break
        else:
            return False
    return True


RNG = Random(118)


def pollard_rho(n: int) -> int:
    if n % 2 == 0:
        return 2
    if n % 3 == 0:
        return 3
    while True:
        c = RNG.randrange(1, n)
        x = RNG.randrange(2, n - 1)
        y, d = x, 1
        while d == 1:
            x = (x * x + c) % n
            y = (y * y + c) % n
            y = (y * y + c) % n
            d = gcd(abs(x - y), n)
        if d != n:
            return d


def factor(n: int, out: list[int] | None = None) -> list[int]:
    if out is None:
        out = []
    if n == 1:
        return out
    if is_prime(n):
        out.append(n)
        return out
    d = pollard_rho(n)
    factor(d, out)
    factor(n // d, out)
    return out


def factor_dict(n: int) -> dict[int, int]:
    ans: dict[int, int] = {}
    for p in sorted(factor(n)):
        ans[p] = ans.get(p, 0) + 1
    return ans


def divisors(n: int) -> list[int]:
    ds = []
    for d in range(1, isqrt(n) + 1):
        if n % d == 0:
            ds.append(d)
            if d * d != n:
                ds.append(n // d)
    return sorted(ds)


def order_from_known_multiple(base: int, modulus: int, multiple: int) -> int:
    assert gcd(base, modulus) == 1
    assert pow(base, multiple, modulus) == 1
    order = multiple
    for prime in factor_dict(multiple):
        while order % prime == 0 and pow(base, order // prime, modulus) == 1:
            order //= prime
    return order


def decimal_pi(precision: int) -> Decimal:
    with localcontext() as ctx:
        ctx.prec = precision + 15
        c = Decimal(426880) * Decimal(10005).sqrt()
        m, ell, x, k = 1, 13591409, 1, 6
        series = Decimal(ell)
        for i in range(1, precision // 14 + 3):
            m = (k**3 - 16 * k) * m // (i**3)
            ell += 545140134
            x *= -262537412640768000
            series += Decimal(m * ell) / Decimal(x)
            k += 12
        ctx.prec = precision
        return +(c / series)


PI_DEC = decimal_pi(100)


def nint_p_pi(p_modulus: int) -> int:
    return int((Decimal(p_modulus) * PI_DEC).to_integral_value(rounding=ROUND_HALF_UP))


def cyclotomic_at_10(r: int, prior: dict[int, int]) -> int:
    value = 10**r - 1
    for d in divisors(r):
        if d < r:
            value //= prior[d]
    return value


def canonical_row(r: int, cyclo: dict[int, int]) -> dict[str, object]:
    n = 10**r - 1
    factors = factor_dict(n)
    private = []
    for p, exponent in factors.items():
        order_p = order_from_known_multiple(10, p, r)
        if order_p == r:
            private.append((p**exponent, p, exponent))
    selected = max(private, default=(1, 1, 0))
    p_power, p, exponent = selected
    phi = cyclotomic_at_10(r, cyclo)
    cyclo[r] = phi
    if p_power == 1:
        return {"r": r, "P": 1, "empty": True}
    assert phi % p_power == 0
    assert order_from_known_multiple(10, p_power, r) == r
    # Bailey-Crandall Lemma 4.3: beta=v_p(10^r-1)=e for this full component.
    c1 = p ** min(exponent, exponent)
    assert c1 == p_power
    length = len(str(p_power))  # ceil(log_10(P)); P is coprime to 10.
    assert length <= r
    a = nint_p_pi(p_power)
    d_a = gcd(a, p_power)
    orbit = sum(
        cmath.exp(2j * pi * ((a * pow(10, j, p_power)) % p_power) / p_power)
        for j in range(length)
    )
    return {
        "r": r,
        "P": p_power,
        "p": p,
        "e": exponent,
        "L": length,
        "a": a,
        "gcd": d_a,
        "sum_abs": abs(orbit),
        "empty": False,
    }


def check_report() -> None:
    report = (ROOT / "REPORT.md").read_text()
    source_pins = (ROOT / "SOURCE_PINS.md").read_text()
    search_log = (ROOT / "SEARCH_LOG.md").read_text()
    assert report.count("SCOPED VERDICT:") == 1
    assert report.count("BOUNDED SUCCESSOR:") == 1
    assert "SCOPED VERDICT: close" in report
    assert "BOUNDED SUCCESSOR: none" in report
    assert "PRIMARY_SOURCE_COUNT: 4" in source_pins
    assert "RETAINED_MECHANISM_COUNT: 3" in source_pins
    for item in ("T63", "T68", "T78", "T79", "T85", "T87", "T104", "T105",
                 "T109", "T113", "T114", "T115", "T116", "T117"):
        assert item in report, item
    for phrase in ("literature-checked", "proof sketch", "experiment", "conjectural transfer"):
        assert phrase in report, phrase
    assert "c1(P_r)=p^min(e,beta)=p^e=P_r" in report
    assert "d_h < P_r/c1(P_r)=1" in report
    assert "SEARCHED_PRIMARY_SOURCE_COUNT: 4" in search_log
    assert "computable variable-depth dyadic avoidance" in report
    assert "supplies no private prime-power modulus" in report
    assert "573011bda281022483a113829138112494b73d667323c30aa2a0ef03bba32cd1" in report
    assert "T116" in search_log and "artificial sibling point" in search_log
    assert "No readable T116" not in report
    assert "No readable T116" not in search_log


def main() -> None:
    check_pins()
    check_report()
    cyclo: dict[int, int] = {}
    rows = [canonical_row(r, cyclo) for r in range(1, 19)]
    print("T118 finite replay (EXPERIMENT ONLY)")
    print("pins: 10/10 exact; source anchors: pass; report constraints: pass")
    print("Bailey-Crandall c1(P_r)=P_r checks: 18/18 pass; gcd hypothesis impossible")
    print("r P_r=p^e ord L_r a_r gcd(a_r,P_r) |S(P_r,a_r,1;0,L_r)|")
    for row in rows:
        if row["empty"]:
            print(f"{row['r']:2d} EMPTY")
        else:
            print(
                f"{row['r']:2d} {row['P']}={row['p']}^{row['e']} {row['r']} "
                f"{row['L']} {row['a']} {row['gcd']} {row['sum_abs']:.9f}"
            )

    # Literal transfer cap with no modular cost, hence maximally optimistic.
    row = rows[-1]
    q, ell, theta, u = 10, 1, 0.5, 0
    h_child = 8000 * q**3
    a_child = 2 + log(800 * q**2 + 1)
    a_parent = 2 + log(40 * q**2 + 1)
    weight = a_child**2 + 0.5 * a_parent**2
    epsilon = (theta / (160 * q * weight)) ** 0.5
    length = int(row["L"])
    cap = 9 * epsilon * length / (2 * pi * h_child * 10**u * (10**length - 1))
    actual_delta = abs(PI_DEC - Decimal(int(row["a"])) / Decimal(int(row["P"])))
    print("optimistic literal transfer test: ell=1 theta=1/2 u=0 B_mod=0")
    print(f"H_child={h_child} epsilon={epsilon:.12e}")
    print(f"required_delta<={cap:.12e} actual_rounding_delta={actual_delta:.12E}")
    print("finite results are experiments, not universal cancellation evidence")


if __name__ == "__main__":
    main()
