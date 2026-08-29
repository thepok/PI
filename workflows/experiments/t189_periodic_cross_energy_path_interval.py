#!/usr/bin/env python3
"""Directed-interval replay of the periodic T189 cross-energy path.

This is a reproducible ``experiment``, not a Lean theorem.  It reuses the
outward-rounded T139 closed-kernel and endpoint implementation from
``t170_signed_parent_334_interval`` on the exact rational orbit ``0.overline(w)``.
The fixed path is

    (10, 6) -> (100, 66) -> (1000, 666) -> (10000, 6666),

with child digit 6 selected before any score is evaluated.
"""

from __future__ import annotations

from concurrent.futures import ProcessPoolExecutor
from dataclasses import dataclass
from decimal import Decimal
from fractions import Fraction
from hashlib import sha256
import os

import t170_signed_parent_334_interval as interval


ORBIT_WINDOW = 145
MAX_WORKERS = min(4, os.cpu_count() or 1)
EXPECTED_WORD_SHA256 = (
    "8e896b260071cfcde983fe89d509cfbf007ef6a0d25d773bf72d3545c346496c"
)


def repeated_prefix(block: str, length: int) -> str:
    return (block * ((length + len(block) - 1) // len(block)))[:length]


WORD = repeated_prefix("6666" + "0" * 64, 1_000) + repeated_prefix(
    "2666" + "0" * 48, 9_000
)
assert len(WORD) == 10_000
assert sha256(WORD.encode("ascii")).hexdigest() == EXPECTED_WORD_SHA256

ORBIT_DENOMINATOR = 10**ORBIT_WINDOW


def periodic_orbit_interval(n: int) -> tuple[Fraction, Fraction]:
    """Enclose ``{10^n * 0.overline(WORD)}`` by adjacent decimal endpoints."""
    block = "".join(WORD[(n + j) % len(WORD)] for j in range(ORBIT_WINDOW))
    numerator = int(block)
    return (
        Fraction(numerator, ORBIT_DENOMINATOR),
        Fraction(numerator + 1, ORBIT_DENOMINATOR),
    )


def configure(q: int, label: int, horizon: int) -> None:
    interval.Q = q
    interval.A = label
    interval.N = horizon
    interval.SUFFIX_DIGITS = ORBIT_WINDOW
    interval.DEN = ORBIT_DENOMINATOR
    interval.orbit_interval = periodic_orbit_interval
    interval._PHASE_CACHE.clear()
    interval.BETA = interval.phase_interval(
        Fraction(1, 2 * q), Fraction(1, 2 * q)
    ).re


def bellman_from_kernel_sum(
    q: int, label: int, horizon: int, kernel_sum: interval.Iv
) -> interval.Iv:
    configure(q, label, horizon)
    alpha_zero = (
        (interval.Iv.point(1) - interval.BETA)
        * Fraction(2 * q**2 + 1, 3 * q)
        - Fraction(1, q)
    )
    primitive_score = (
        (kernel_sum - alpha_zero * horizon) / 2 - interval.endpoint().re
    )
    return primitive_score * q - Fraction(7 * horizon, 3 * q)


def one_bellman(q: int, label: int, horizon: int) -> interval.Iv:
    configure(q, label, horizon)
    kernel_sum = interval.Iv.point(0)
    for n in range(horizon):
        kernel_sum += interval.kernel_at(n)
    return bellman_from_kernel_sum(q, label, horizon, kernel_sum)


def child_bellmans(task: tuple[int, int, int, int]) -> tuple[int, interval.Iv, interval.Iv]:
    parent_q, parent_label, parent_horizon, child = task
    child_q = 10 * parent_q
    child_label = parent_label + child * parent_q
    child_horizon = 10 * parent_horizon
    configure(child_q, child_label, child_horizon)
    kernel_sum = interval.Iv.point(0)
    prefix_sum: interval.Iv | None = None
    for n in range(child_horizon):
        kernel_sum += interval.kernel_at(n)
        if n + 1 == parent_horizon:
            prefix_sum = kernel_sum
    assert prefix_sum is not None
    return (
        child,
        bellman_from_kernel_sum(child_q, child_label, parent_horizon, prefix_sum),
        bellman_from_kernel_sum(child_q, child_label, child_horizon, kernel_sum),
    )


def strict_sign(value: interval.Iv) -> int:
    if value.lo > 0:
        return 1
    if value.hi < 0:
        return -1
    raise AssertionError(f"interval does not have a strict sign: {value}")


def corrected_cross_energy(fresh: list[interval.Iv], final: list[interval.Iv]) -> interval.Iv:
    energy = interval.Iv.point(0)
    for fresh_value, final_value in zip(fresh, final, strict=True):
        fresh_sign = strict_sign(fresh_value)
        final_sign = strict_sign(final_value)
        if fresh_sign == final_sign == -1:
            continue
        energy += fresh_value * final_value
    return energy


@dataclass(frozen=True)
class NodeResult:
    q: int
    label: int
    parent: interval.Iv
    energy: interval.Iv
    fresh_6: interval.Iv
    final_6: interval.Iv
    fmr_digits: frozenset[int]


def evaluate_node(q: int, label: int) -> NodeResult:
    parent = one_bellman(q, label, q)
    tasks = [(q, label, q, child) for child in range(10)]
    with ProcessPoolExecutor(max_workers=MAX_WORKERS) as pool:
        child_rows = sorted(pool.map(child_bellmans, tasks))

    fresh: list[interval.Iv] = []
    final: list[interval.Iv] = []
    for child, child_prefix, child_final in child_rows:
        assert child == len(fresh)
        fresh.append(child_final - child_prefix)
        final.append(child_final - parent)

    fmr_digits = frozenset(
        child
        for child in range(10)
        if strict_sign(fresh[child]) > 0 and strict_sign(final[child]) > 0
    )
    return NodeResult(
        q=q,
        label=label,
        parent=parent,
        energy=corrected_cross_energy(fresh, final),
        fresh_6=fresh[6],
        final_6=final[6],
        fmr_digits=fmr_digits,
    )


def verify_expected(result: NodeResult) -> None:
    if result.q == 10:
        assert result.label == 6
        assert result.parent.lo > Decimal("46")
        assert result.energy.lo > Decimal("204311")
        assert result.fresh_6.lo > Decimal("302")
        assert result.final_6.lo > Decimal("672")
        assert result.fmr_digits == {0, 6}
    elif result.q == 100:
        assert result.label == 66
        assert result.parent.lo > Decimal("719")
        assert result.energy.lo > Decimal("1445101901")
        assert result.fresh_6.lo > Decimal("27759")
        assert result.final_6.lo > Decimal("31562")
        assert result.fmr_digits == {0, 6}
    elif result.q == 1_000:
        assert result.label == 666
        assert result.parent.lo > Decimal("32281.8468558256")
        assert result.energy.lo > Decimal("-3080140823.433565")
        assert result.energy.hi < Decimal("-3080140823.433564")
        assert result.fresh_6.lo > Decimal("42249")
        assert result.final_6.lo > Decimal("10884")
        assert result.fmr_digits == {6}
    else:
        raise AssertionError(result.q)


def show_interval(name: str, value: interval.Iv) -> None:
    print(f"{name}=[{value.lo}, {value.hi}]")


def main() -> None:
    print("status: running directed-interval experiment")
    print(f"word_sha256={EXPECTED_WORD_SHA256}")
    print(
        f"precision={interval.PREC} taylor_terms={interval.TAYLOR_TERMS} "
        f"orbit_window={ORBIT_WINDOW} workers={MAX_WORKERS}"
    )
    for q, label in ((10, 6), (100, 66), (1_000, 666)):
        result = evaluate_node(q, label)
        verify_expected(result)
        print(f"node=(q={q}, A={label}) fmr_digits={sorted(result.fmr_digits)}")
        show_interval("P", result.parent)
        show_interval("E", result.energy)
        show_interval("D_6", result.fresh_6)
        show_interval("F_6", result.final_6)
    print("status: PASS (directed-interval experiment; not a Lean theorem)")


if __name__ == "__main__":
    main()
