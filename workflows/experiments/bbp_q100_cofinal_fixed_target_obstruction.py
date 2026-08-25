#!/usr/bin/env python3
"""Independent exact/directed certificate for the q=100 fixed-target memo.

No repository access is used. BBP partial sums are inclusive: P_M = sum_{m=0}^M.
All finite BBP floor claims use fractions.Fraction. Trigonometric enclosures use
Decimal with directed rounding and a Machin-series rational enclosure for pi.
"""
from __future__ import annotations

from dataclasses import dataclass
from decimal import Context, Decimal, ROUND_CEILING, ROUND_FLOOR
from fractions import Fraction
from functools import lru_cache
import csv
import hashlib
import io
import math

# ---------- Inclusive BBP/T112 exact arithmetic ----------

def bbp_term(m: int) -> Fraction:
    return Fraction(1, 16**m) * (
        Fraction(4, 8*m + 1)
        - Fraction(2, 8*m + 4)
        - Fraction(1, 8*m + 5)
        - Fraction(1, 8*m + 6)
    )


def bbp_partial(M: int) -> Fraction:
    return sum((bbp_term(m) for m in range(M + 1)), Fraction(0))


def selected_q(n: int) -> Fraction:
    return Fraction(10**n) * bbp_partial(7*n)


def selected_y(n: int) -> Fraction:
    qn = selected_q(n)
    return Fraction(qn.numerator % qn.denominator, qn.denominator)


def forcing_f(n: int) -> Fraction:
    # Exactly the seven terms 7n+1,...,7n+7.
    return Fraction(10**(n + 1)) * (bbp_partial(7*n + 7) - bbp_partial(7*n))


def sha_fraction(x: Fraction) -> str:
    return hashlib.sha256(f"{x.numerator}/{x.denominator}".encode()).hexdigest()


# ---------- Rational enclosure of pi ----------

def arctan_inv_bounds(q: int, even_N: int) -> tuple[Fraction, Fraction]:
    assert even_N % 2 == 0
    s = Fraction(0)
    for k in range(even_N + 1):
        term = Fraction(1, (2*k + 1) * q**(2*k + 1))
        s += term if k % 2 == 0 else -term
    upper = s
    k = even_N + 1
    lower = s - Fraction(1, (2*k + 1) * q**(2*k + 1))
    return lower, upper


L5, U5 = arctan_inv_bounds(5, 30)
L239, U239 = arctan_inv_bounds(239, 6)
PI_LO = 16*L5 - 4*U239
PI_HI = 16*U5 - 4*L239

PREC = 50
CTX_LO = Context(prec=PREC, rounding=ROUND_FLOOR)
CTX_HI = Context(prec=PREC, rounding=ROUND_CEILING)


def dec_frac_lo(x: Fraction) -> Decimal:
    return CTX_LO.divide(Decimal(x.numerator), Decimal(x.denominator))


def dec_frac_hi(x: Fraction) -> Decimal:
    return CTX_HI.divide(Decimal(x.numerator), Decimal(x.denominator))


@dataclass(frozen=True)
class DI:
    lo: Decimal
    hi: Decimal

    def __add__(self, other: "DI") -> "DI":
        return DI(CTX_LO.add(self.lo, other.lo), CTX_HI.add(self.hi, other.hi))

    def __sub__(self, other: "DI") -> "DI":
        return DI(CTX_LO.subtract(self.lo, other.hi), CTX_HI.subtract(self.hi, other.lo))

    def __mul__(self, other: "DI") -> "DI":
        low_products = [CTX_LO.multiply(a, b) for a in (self.lo, self.hi) for b in (other.lo, other.hi)]
        high_products = [CTX_HI.multiply(a, b) for a in (self.lo, self.hi) for b in (other.lo, other.hi)]
        return DI(min(low_products), max(high_products))

    def scale_fraction(self, x: Fraction) -> "DI":
        return self * DI(dec_frac_lo(x), dec_frac_hi(x))


ZERO = DI(Decimal(0), Decimal(0))
ONE = DI(Decimal(1), Decimal(1))
PI_DI = DI(dec_frac_lo(PI_LO), dec_frac_hi(PI_HI))


def floor_fraction(x: Fraction) -> int:
    return x.numerator // x.denominator


@lru_cache(maxsize=None)
def cos_pi_r_interval(r: Fraction, M: int = 12) -> DI:
    """Directed enclosure of cos(pi*r), reducing r modulo 2 to [-1,1)."""
    k = floor_fraction((r + 1) / 2)
    rr = r - 2*k
    assert Fraction(-1) <= rr < Fraction(1)
    a = abs(rr)
    x = PI_DI.scale_fraction(a)
    y = x * x

    # Horner evaluation of sum_{k=0}^M (-1)^k x^(2k)/(2k)!.
    p: DI | None = None
    for kk in range(M, -1, -1):
        c = Fraction((-1)**kk, math.factorial(2*kk))
        ci = DI(dec_frac_lo(c), dec_frac_hi(c))
        p = ci if p is None else ci + y*p
    assert p is not None

    # Lagrange remainder after degree 2M; every derivative of cos has norm <= 1.
    rem = CTX_HI.divide(CTX_HI.power(x.hi, 2*M + 1), Decimal(math.factorial(2*M + 1)))
    return DI(CTX_LO.subtract(p.lo, rem), CTX_HI.add(p.hi, rem))


# ---------- q=100 singleton polynomial ----------
Q = 100
J = [j for j in range(1, Q//2 + 1) if j % 10 != 0]
COS_COEFF = cos_pi_r_interval(Fraction(1, Q))
DELTA = ONE - COS_COEFF
COEFF: dict[int, DI] = {}
for j in J:
    base = Fraction(Q - j, 2*Q*Q)
    cubic = Fraction((Q - j)**3 - (Q - j), 6*Q*Q)
    COEFF[j] = DI(dec_frac_lo(base), dec_frac_hi(base)) + DELTA.scale_fraction(cubic)


def phi_node_interval(m: int, A: int, mesh_den: int = 500) -> DI:
    """Enclose Re Phi((u-A-1/2)/100) at u=m/mesh_den."""
    u = Fraction(m, mesh_den)
    total = ZERO
    for j in J:
        h = Q + j
        # 2*pi*h*(u-A-1/2)/Q = pi*r.
        r = Fraction(2*h, Q) * (u - A - Fraction(1, 2))
        total = total + COEFF[j] * cos_pi_r_interval(r)
    return total


REGIONS = [
    # m0, m1, offset B; endpoints are included and overlap harmlessly.
    (0,   135, 0),   # u in [0,.27]
    (135, 210, 1),   # [.27,.42]
    (210, 275, 10),  # [.42,.55]
    (275, 285, 20),  # [.55,.57]
    (285, 365, 99),  # [.57,.73]
    (365, 500, 0),   # [.73,1]
]


def main() -> None:
    # Inclusive-index sanity checks.
    assert bbp_partial(0) == Fraction(47, 15)
    assert selected_y(0) == Fraction(2, 15)
    f0 = forcing_f(0)
    assert f0 == Fraction(42934995690007497849126077, 519836915885323158521118720)
    assert math.floor(10*selected_y(0) + f0) == 1

    y39 = selected_y(39)
    f39 = forcing_f(39)
    assert 100*y39 - 16 > Fraction(9, 10)
    assert 17 - 100*y39 > Fraction(3, 50)
    assert 10*y39 + f39 - 1 > Fraction(69, 100)
    assert 2 - (10*y39 + f39) > Fraction(3, 10)
    assert math.floor(100*y39) == 16
    assert math.floor(10*y39 + f39) == 1

    # Exact coefficient sums used in the analytic interpolation bounds.
    lam0 = sum(Fraction(Q-j, 2*Q*Q) for j in J)
    lam1 = sum(Fraction((Q-j)**3-(Q-j), 6*Q*Q) for j in J)
    h0 = sum(Fraction((Q+j)*(Q-j), 2*Q*Q) for j in J)
    h1 = sum(Fraction((Q+j)*((Q-j)**3-(Q-j)), 6*Q*Q) for j in J)
    assert (lam0, lam1) == (Fraction(27, 160), Fraction(14049, 40))
    assert (h0, h1) == (Fraction(16503, 800), Fraction(10307649, 250))
    j0 = sum(Fraction(j*(Q-j), 2*Q*Q) for j in J)
    j1 = sum(Fraction(j*((Q-j)**3-(Q-j)), 6*Q*Q) for j in J)
    assert (j0, j1) == (Fraction(3003, 800), Fraction(763512, 125))

    # 1-cos(pi/100) < 1/2000, hence Lambda<1 and sum h C_h<42.
    assert Fraction(121, 245000) < Fraction(1, 2000)
    assert lam0 + lam1*Fraction(1, 2000) < 1
    assert h0 + h1*Fraction(1, 2000) < 42
    assert j0 + j1*Fraction(1, 2000) < 7

    # The rational bounds used between mesh nodes and in both tail transfers.
    rho = Fraction(10, 16**7)
    assert PI_HI < Fraction(22, 7)
    assert 2*PI_HI*Fraction(42, 100) < Fraction(66, 25)
    assert 2*PI_HI*10*rho < Fraction(1, 400_000)
    assert rho + Fraction(7, 10) < 1
    assert 2*PI_HI*rho < Fraction(1, 4_000_000)

    # A coarse rational comparison already separates the T139-compatible
    # termwise budget from the certified adverse increment.
    ct139_upper = (Fraction(20001, 2000) - 3) / 6
    assert ct139_upper < Fraction(93429, 40000)

    rows: list[tuple[int, int, int, str, str]] = []
    maxima = []
    for region_id, (m0, m1, B) in enumerate(REGIONS):
        max_hi: Decimal | None = None
        max_m: int | None = None
        for m in range(m0, m1 + 1):
            val = phi_node_interval(m, B)
            rows.append((region_id, B, m, str(val.lo), str(val.hi)))
            if max_hi is None or val.hi > max_hi:
                max_hi, max_m = val.hi, m
        assert max_hi is not None and max_m is not None
        assert max_hi < Decimal(-13) / Decimal(500)
        maxima.append((region_id, B, max_m, max_hi))

    # Recreate the complete certificate in memory.  Its hash pins every
    # directed interval while keeping the generated 59 KiB CSV out of git.
    fh = io.StringIO(newline="")
    w = csv.writer(fh)
    w.writerow(["region", "offset_B", "mesh_index_m", "lower", "upper"])
    w.writerows(rows)
    certificate_sha256 = hashlib.sha256(fh.getvalue().encode()).hexdigest()
    assert certificate_sha256 == (
        "b7e5677908eeadf97ff8750e1953b4f55be5c9aaa10ff0b9510149d94c6a981a"
    )

    # Continuous interpolation and forcing rotation:
    # derivative < 66/25, nearest mesh point distance <=1/1000;
    # forcing rotation error <1/400000.
    continuous_upper = -Fraction(13, 500) + Fraction(66, 25_000) + Fraction(1, 400_000)
    assert continuous_upper == -Fraction(9343, 400_000)
    assert continuous_upper < -Fraction(1, 50)

    print("PASS: inclusive T112 indexing, exact q=100 floors, and directed node certificate")
    print(f"P0={bbp_partial(0)}; y0={selected_y(0)}; b0=1")
    print(f"q39 digest={sha_fraction(selected_q(39))}")
    print(f"y39 digest={sha_fraction(y39)}")
    print(f"f39 digest={sha_fraction(f39)}")
    for region_id, B, max_m, max_hi in maxima:
        print(f"region={region_id} B={B:02d} max_node=m/{500} at m={max_m}: upper={max_hi}")
    print(f"continuous forced upper = {continuous_upper} = {float(continuous_upper):.10f} < -1/50")
    print(f"certificate sha256={certificate_sha256} (501 distinct mesh nodes)")


if __name__ == "__main__":
    main()
