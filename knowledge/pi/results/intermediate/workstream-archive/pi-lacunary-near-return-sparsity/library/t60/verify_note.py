#!/usr/bin/env python3
"""Arithmetic and finite-transform checks supporting the T60 note.

This script uses only Python's standard library and rational arithmetic.
It does not test any assertion about pi.
"""

from fractions import Fraction
import cmath
import math


def valuation_ten(n: int) -> int:
    result = 0
    while n % 10 == 0:
        result += 1
        n //= 10
    return result


def weight(R: int, u: int) -> Fraction:
    return Fraction(R - u, R)


def zero_phase_gamma(R: int, u: int) -> Fraction:
    return sum(
        (weight(R, u // (10**a)) for a in range(valuation_ten(u) + 1)),
        Fraction(0),
    )


def zero_phase_data(R: int, ell: int = 1) -> dict[str, Fraction | int]:
    H = R - 1
    K = H // 10
    direct = ell * sum((weight(R, u) for u in range(K + 1, H + 1)), Fraction(0))
    predecessor = ell * sum(
        (
            sum(
                (weight(R, u // (10**a)) for a in range(1, valuation_ten(u) + 1)),
                Fraction(0),
            )
            for u in range(K + 1, H + 1)
        ),
        Fraction(0),
    )
    endpoint_budget = 2 * sum(
        (zero_phase_gamma(R, u) for u in range(1, K + 1)), Fraction(0)
    )
    terminal = ell * sum(
        (zero_phase_gamma(R, u) for u in range(K + 1, H + 1)), Fraction(0)
    )
    # Both audited examples have delta = 1/R.
    theta = Fraction(ell * R, 4)
    direct_budget_rhs = (
        ell + 2 * direct - 2 * predecessor - 2 * endpoint_budget - theta
    )
    top_shell_rhs = Fraction(ell * R, 8) - Fraction(ell, 2) + endpoint_budget
    return {
        "H": H,
        "K": K,
        "A0": direct,
        "X": predecessor,
        "Bend": endpoint_budget,
        "terminal": terminal,
        "Theta": theta,
        "direct_budget_rhs": direct_budget_rhs,
        "top_shell_rhs": top_shell_rhs,
        "top_shell_margin": terminal - top_shell_rhs,
    }


def check_primitive_ray_partition(R: int) -> None:
    H = R - 1
    top = set(range(H // 10 + 1, H + 1))
    representatives = set()
    label_mass = Fraction(0)
    for q in range(1, H + 1):
        if q % 10 == 0:
            continue
        h = q
        ray = []
        while h <= H:
            ray.append(h)
            h *= 10
        representatives.add(ray[-1])
        label_mass += sum((weight(R, v) for v in ray), Fraction(0))
    assert representatives == top
    assert label_mass == Fraction(H, 2)


def check_walsh_collision_identity() -> None:
    # A nonuniform probability on ten one-digit words.
    p = [Fraction(1, 2), Fraction(1, 2)] + [Fraction(0)] * 8
    q = len(p)
    collision = sum((x * x for x in p), Fraction(0))
    l2_error = sum(((x - Fraction(1, q)) ** 2 for x in p), Fraction(0))
    assert collision == Fraction(1, 2)
    assert l2_error == collision - Fraction(1, q) == Fraction(2, 5)
    assert q * l2_error == q * collision - 1 == 4
    # Independently evaluate the unnormalized one-digit Walsh transform.
    zeta = cmath.exp(2j * math.pi / q)
    walsh = [sum(float(p[a]) * zeta ** (-k * a) for a in range(q)) for k in range(q)]
    nonzero_energy = sum(abs(walsh[k]) ** 2 for k in range(1, q))
    assert abs(nonzero_energy - 4.0) < 1e-12


def density_denominator(D: int, k: int) -> int:
    for _ in range(k):
        D = 8 * D * D
    return D


def check_zero_phase_chain(shifts: list[int], expected_R: int) -> None:
    M, D, B, K, d = 5, 2, 1, 2, 2
    forbidden = {0}
    assert len(shifts) == d
    assert len(set(shifts)) == d
    assert all(s >= B and s not in forbidden for s in shifts)
    assert K <= M - sum(shifts)

    residuals = [M - sum(shifts[:k]) for k in range(d + 1)]
    denominators = [density_denominator(D, k) for k in range(d + 1)]
    assert denominators == [2, 32, 8192]
    assert all(Fraction(residuals[k], denominators[k]) < residuals[k] for k in range(d + 1))

    q, ell = 1, 1
    common_depth = min(residuals[q], residuals[q + 1])
    assert 1 <= ell < common_depth
    adjacent_factor = 10 ** shifts[q] - 1
    delta = Fraction(1, 2 * adjacent_factor * 10**ell)
    # nodeErrorThreshold > 1/6 because nodeTau < 1/2.
    assert Fraction(1, 6) > delta
    assert Fraction(1, 6 * adjacent_factor) > delta
    assert delta == Fraction(1, expected_R)


def main() -> None:
    for R in (2, 10, 180, 1980, 10001):
        check_primitive_ray_partition(R)

    check_zero_phase_chain([2, 1], 180)
    first = zero_phase_data(180)
    assert first == {
        "H": 179,
        "K": 17,
        "A0": Fraction(1467, 20),
        "X": Fraction(323, 20),
        "Bend": Fraction(1543, 45),
        "terminal": Fraction(179, 2),
        "Theta": Fraction(45),
        "direct_budget_rhs": Fraction(82, 45),
        "top_shell_rhs": Fraction(2533, 45),
        "top_shell_margin": Fraction(2989, 90),
    }

    check_zero_phase_chain([1, 2], 1980)
    second = zero_phase_data(1980)
    assert second == {
        "H": 1979,
        "K": 197,
        "A0": Fraction(16047, 20),
        "X": Fraction(3743, 20),
        "Bend": Fraction(204983, 495),
        "terminal": Fraction(1979, 2),
        "Theta": Fraction(495),
        "direct_budget_rhs": Fraction(-45448, 495),
        "top_shell_rhs": Fraction(327248, 495),
        "top_shell_margin": Fraction(325109, 990),
    }

    check_walsh_collision_identity()
    print("T60 support checks passed")


if __name__ == "__main__":
    main()
