"""Exact finite checks for the scoped Pisot-conjugate ledger calculation.

Standard library only. No sampled pi digits or target-digit assumptions.
The all-index proofs are in ATTEMPT_LEDGER.md, not supplied by this experiment.
The interval check uses the classical Machin identity
pi = 16 arctan(1/5) - 4 arctan(1/239) and exact alternating-series bounds.
"""

from fractions import Fraction as F
from math import lcm


def q(a=0, b=0):
    """a + b sqrt(3)."""
    return F(a), F(b)


def qa(x, y):
    return x[0] + y[0], x[1] + y[1]


def qs(x, c):
    return x[0] * c, x[1] * c


def qm(x, y):
    return x[0] * y[0] + 3 * x[1] * y[1], x[0] * y[1] + x[1] * y[0]


def qi(x):
    norm = x[0] ** 2 - 3 * x[1] ** 2
    assert norm
    return x[0] / norm, -x[1] / norm


def sigma(x):
    return x[0], -x[1]


def trace(x):
    return qa(x, sigma(x))


def integral(x):
    return all(v.denominator == 1 for v in x)


def ca(x, y):
    return qa(x[0], y[0]), qa(x[1], y[1])


def cs(x, c):
    return qs(x[0], c), qs(x[1], c)


def cm(x, y):
    return qa(qm(x[0], y[0]), qs(qm(x[1], y[1]), -1)), qa(
        qm(x[0], y[1]), qm(x[1], y[0])
    )


def ci(x):
    den = qi(qa(qm(x[0], x[0]), qm(x[1], x[1])))
    return qm(x[0], den), qs(qm(x[1], den), -1)


def atan_bounds(inv, terms=80):
    """Exact alternating-series enclosure of arctan(1/inv)."""
    partial = sum((F((-1) ** j, (2 * j + 1) * inv ** (2 * j + 1))
                   for j in range(terms)), F(0))
    other = partial + F((-1) ** terms, (2 * terms + 1) * inv ** (2 * terms + 1))
    return min(partial, other), max(partial, other)


def main():
    one, imag_unit = (q(1), q()), (q(), q(1))
    eps = q(2, 1)
    a = q(F(-1, 4), F(1, 4)), q(F(3, 4), F(-1, 4))
    b = cm(imag_unit, a)
    zeta = q(F(-1, 2)), q(0, F(1, 2))
    assert qm(eps, sigma(eps)) == q(1)
    assert cm(cm(zeta, zeta), zeta) == one
    assert cm(a, a) == tuple(qs(qm(v, sigma(eps)), F(1, 2)) for v in zeta)

    # Endpoint factors: independent exact inversion, not decimal evaluation.
    a_ratio = cm(a, ci(ca(one, a)))
    b_ratio = cm(b, ci(ca(one, b)))
    assert a_ratio == (q(F(1, 2), F(-1, 6)),) * 2
    assert b_ratio == (q(F(1, 2), F(-1, 2)), q(F(-1, 2), F(1, 2)))
    period = []
    zpow = one
    for n in range(6):
        endpoint = cm(zpow, ca(cs(a_ratio, 2), cs(b_ratio, (-1) ** n)))
        value = qs(trace(endpoint[1]), 4)
        assert value[1] == 0 and value[0].denominator == 1
        period.append(int(value[0]))
        zpow = cm(zpow, zeta)
    assert period == [4, -4, 8, 12, -12, -8]

    lo5, hi5 = atan_bounds(5)
    lo239, hi239 = atan_bounds(239)
    pi_lo, pi_hi = 16 * lo5 - 4 * hi239, 16 * hi5 - 4 * lo239
    assert F(3) < pi_lo < pi_hi < F(22, 7)

    power_a = power_b = one
    sum_a = sum_b = (q(), q())
    ep, lcm_j = q(1), 1
    q_prev, q_now = 2, 4
    samples = {}
    for j in range(1, 73):
        power_a, power_b = cm(power_a, a), cm(power_b, b)
        sign_over_j = F((-1) ** (j + 1), j)
        sum_a = ca(sum_a, cs(power_a, sign_over_j))
        sum_b = ca(sum_b, cs(power_b, sign_over_j))
        coefficient = qs(qa(qs(power_a[1], 2), power_b[1]), 4)
        exponent = j // 2 - 1 if j % 2 == 0 else (j - 1) // 2
        assert integral(qs(coefficient, 2 ** max(exponent, 0)))
        lcm_j = lcm(lcm_j, j)
        if j % 2:
            continue
        n = j // 2
        ep = qm(ep, eps)
        s_n = qs(qa(qs(sum_a[1], 2), sum_b[1]), 4)
        assert integral(qs(s_n, 2 ** (n - 1) * lcm_j))
        t_pair = trace(qm(ep, s_n))
        q_pair = trace(ep)
        assert t_pair[1] == q_pair[1] == 0
        t_n, q_n = t_pair[0], q_pair[0]
        assert q_n == q_now and q_n.denominator == 1
        q_prev, q_now = q_now, 4 * q_now - q_prev
        assert int(q_n) % 5 == [2, 4, 4][n % 3]
        d_n = 2 ** n * lcm_j
        assert (d_n * t_n).denominator == 1
        if n >= 2:
            assert (2 ** (n - 2) * lcm_j * t_n).denominator == 1
        else:
            assert t_n == 14

        e_lo, e_hi = q_n * pi_lo - t_n, q_n * pi_hi - t_n
        assert max(abs(e_lo), abs(e_hi)) < F(18, n * 2 ** n)
        # A rigorous, deliberately loose endpoint-remainder envelope.
        scale = (2 * n + 1) * 2 ** n
        residue = period[n % 6]
        remainder_bound = F(144, 2 * n + 2)
        assert max(abs(scale * e_lo - residue), abs(scale * e_hi - residue)) < remainder_bound
        samples[n] = t_n

    assert samples[2] == F(131, 3)
    assert samples[4] == F(256009, 420)
    assert samples[8] == F(68168981831, 576576)
    assert samples[12] == F(1964885998818327049, 85667662080)
    print("PASS: 36 exact traces, coefficient/denominator caps, Pell clocks,")
    print("six endpoint factors and rational Machin error enclosures.")
    print("Finite experiment only; no pi digit occurrence or primitive-denominator claim.")


if __name__ == "__main__":
    main()
