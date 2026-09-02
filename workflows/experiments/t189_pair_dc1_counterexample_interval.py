#!/usr/bin/env python3
"""Directed-interval replay of the finite T189 Pair/DC1 counterexample.

This is a reproducible ``experiment``, not a Lean theorem.  It evaluates the
T173 lower endpoint with the machine-checked T139 closed-kernel/endpoint
identity, then adds an explicit bound for the full T173 decimal cylinder.

The paired Fourier margin is computed from the real fresh-gain vector.  Thus
its DFT is conjugate-equivalent to the correct sector pairing

    P_r = C_r + conj(C_(10-r)),    Dhat_r = (q / 2) P_r.

No unpaired ``C_r + C_(10-r)`` normalization is used.
"""

from __future__ import annotations

from concurrent.futures import ProcessPoolExecutor
from decimal import Decimal
from fractions import Fraction
from hashlib import sha256
from pathlib import Path
import os
import re

import t170_signed_parent_334_interval as interval


PARENT_Q = 1_000
PARENT_A = 689
CHILD_Q = 10_000
N = 1_000
H = 10_000
T173_PLACES = 10_015
ORBIT_WINDOW = 120
MAX_WORKERS = min(4, os.cpu_count() or 1)

EXPECTED_DIGIT_FILE_SHA256 = (
    "77eeccb0067283e14c460b33dc230de54ef15c2e825fc2a35c984fb6984bf684"
)

REPO = Path(__file__).resolve().parents[2]
DIGIT_PATH = Path(__file__).resolve().parent / "data" / "pi_digits_1048596.txt"
T173_PATH = (
    REPO
    / "TheoryLib/PiQuantitativeBlockHitting/"
    "T173T173MachinIntegerCertificate10015.lean"
)


def load_and_check_digits() -> str:
    raw = DIGIT_PATH.read_bytes()
    actual_hash = sha256(raw).hexdigest()
    assert actual_hash == EXPECTED_DIGIT_FILE_SHA256, actual_hash
    digits = raw.rstrip(b"\n").decode("ascii")
    assert len(digits) == 1_048_596 and digits.isdigit()

    lean = T173_PATH.read_text(encoding="utf-8")
    match = re.search(
        r"abbrev certifiedPiPrefix : Nat :=\s*(\d+)\s*"
        r"private abbrev piPrefix",
        lean,
    )
    assert match is not None
    assert match.group(1) == "3" + digits[:T173_PLACES]
    return digits


DIGITS = load_and_check_digits()


def t173_lower_orbit_interval(n: int) -> tuple[Fraction, Fraction]:
    """Enclose the orbit of the exact T173 lower rational endpoint.

    At most ``ORBIT_WINDOW`` digits are retained.  Before the certified cutoff
    the discarded suffix is enclosed by the adjacent decimal endpoint; at the
    cutoff the finite lower rational is exact and is padded by zeros.
    """
    if not 0 <= n < T173_PLACES:
        raise ValueError(n)
    stop = min(n + ORBIT_WINDOW, T173_PLACES)
    block = DIGITS[n:stop]
    denominator = 10 ** len(block)
    lower = Fraction(int(block), denominator)
    if stop == T173_PLACES:
        return lower, lower
    return lower, Fraction(int(block) + 1, denominator)


def configure(q: int, label: int) -> None:
    interval.Q = q
    interval.A = label
    interval.SUFFIX_DIGITS = ORBIT_WINDOW
    interval.DEN = 10**ORBIT_WINDOW
    interval.orbit_interval = t173_lower_orbit_interval
    interval._PHASE_CACHE.clear()
    interval.BETA = interval.phase_interval(
        Fraction(1, 2 * q), Fraction(1, 2 * q)
    ).re


def score_from_kernel_sum(q: int, label: int, horizon: int, kernel_sum: interval.Iv) -> interval.Iv:
    configure(q, label)
    alpha_zero = (
        (interval.Iv.point(1) - interval.BETA)
        * Fraction(2 * q**2 + 1, 3 * q)
        - Fraction(1, q)
    )
    interval.N = horizon
    endpoint_re = interval.endpoint().re
    return (kernel_sum - alpha_zero * horizon) / 2 - endpoint_re


def two_scores(task: tuple[int, int]) -> tuple[int, interval.Iv, interval.Iv]:
    q, label = task
    configure(q, label)
    kernel_sum = interval.Iv.point(0)
    kernel_sum_n: interval.Iv | None = None
    for n in range(H):
        kernel_sum += interval.kernel_at(n)
        if n + 1 == N:
            kernel_sum_n = kernel_sum
    assert kernel_sum_n is not None
    score_n = score_from_kernel_sum(q, label, N, kernel_sum_n)
    score_h = score_from_kernel_sum(q, label, H, kernel_sum)
    return label, score_n, score_h


def one_score(q: int, label: int, horizon: int) -> interval.Iv:
    configure(q, label)
    kernel_sum = interval.Iv.point(0)
    for n in range(horizon):
        kernel_sum += interval.kernel_at(n)
    return score_from_kernel_sum(q, label, horizon, kernel_sum)


def t173_score_error(q: int, horizon: int) -> Decimal:
    """Upper bound for |Z(pi)-Z(T173 lower)|.

    The coefficient bounds used in the memo give
    ``sum_h |a_(q,h)| u(h) < 44 q``.  Also ``2*pi < 8`` and

      sum_(n<horizon) 10^(n-10015) < 10^(horizon-10015) / 9.
    """
    geometric = interval.UP.divide(
        Decimal(1).scaleb(horizon - T173_PLACES), Decimal(9)
    )
    return interval.UP.multiply(Decimal(8 * 44 * q), geometric)


def expand(value: interval.Iv, error: Decimal) -> interval.Iv:
    return interval.Iv(
        interval.dsub(value.lo, error),
        interval.dadd(value.hi, error, True),
    )


def signed_surplus(q: int, score: interval.Iv, horizon: int) -> interval.Iv:
    nominal = score * q - Fraction(7 * horizon, 3 * q)
    return expand(nominal, interval.UP.multiply(Decimal(q), t173_score_error(q, horizon)))


def positive_part_of_negative(value: interval.Iv) -> interval.Iv:
    if value.hi < 0:
        return -value
    if 0 < value.lo:
        return interval.Iv.point(0)
    return interval.Iv(Decimal(0), -value.lo)


def complex_sum(values: list[interval.Iv], frequency: int) -> interval.CIv:
    total = interval.CIv.zero()
    for digit, value in enumerate(values):
        root = interval.phase_interval(
            Fraction(frequency * digit, 10), Fraction(frequency * digit, 10)
        )
        total += root * value
    return total * Fraction(1, 10)


def interval_abs(value: interval.Iv) -> tuple[Decimal, Decimal]:
    if value.lo <= 0 <= value.hi:
        lower = Decimal(0)
    else:
        lower = min(abs(value.lo), abs(value.hi))
    upper = max(abs(value.lo), abs(value.hi))
    return lower, upper


def complex_norm(value: interval.CIv) -> interval.Iv:
    re_lo, re_hi = interval_abs(value.re)
    im_lo, im_hi = interval_abs(value.im)
    lower_square = interval.DOWN.add(
        interval.DOWN.multiply(re_lo, re_lo),
        interval.DOWN.multiply(im_lo, im_lo),
    )
    upper_square = interval.UP.add(
        interval.UP.multiply(re_hi, re_hi),
        interval.UP.multiply(im_hi, im_hi),
    )
    return interval.Iv(
        interval.DOWN.sqrt(lower_square), interval.UP.sqrt(upper_square)
    )


def decagon_gauge(value: interval.CIv) -> interval.Iv:
    rho = interval.phase_interval(Fraction(1, 20), Fraction(1, 20)).re
    faces: list[interval.Iv] = []
    for face in range(10):
        normal = interval.phase_interval(
            Fraction(-(2 * face + 1), 20),
            Fraction(-(2 * face + 1), 20),
        )
        faces.append((value * normal).re / rho)
    return interval.Iv(max(face.lo for face in faces), max(face.hi for face in faces))


def show(name: str, value: interval.Iv) -> None:
    print(f"{name}=[{value.lo}, {value.hi}]")


def main() -> None:
    parent_score = one_score(PARENT_Q, PARENT_A, N)
    parent = signed_surplus(PARENT_Q, parent_score, N)
    assert parent.lo > Decimal("80.21738")

    tasks = [(CHILD_Q, PARENT_A + digit * PARENT_Q) for digit in range(10)]
    with ProcessPoolExecutor(max_workers=MAX_WORKERS) as pool:
        child_results = sorted(pool.map(two_scores, tasks))

    gains: list[interval.Iv] = []
    fresh: list[interval.Iv] = []
    final: list[interval.Iv] = []
    for label, score_n, score_h in child_results:
        child_n = signed_surplus(CHILD_Q, score_n, N)
        child_h = signed_surplus(CHILD_Q, score_h, H)
        gains.append(child_n - parent)
        fresh.append(child_h - child_n)
        final.append(child_h - parent)

    fresh_positive = {d for d, value in enumerate(fresh) if value.lo > 0}
    final_positive = {d for d, value in enumerate(final) if value.lo > 0}
    assert all(value.hi < 0 for d, value in enumerate(fresh) if d != 8)
    assert all(value.hi < 0 for d, value in enumerate(final) if d not in {8, 9})
    assert fresh_positive == {8}
    assert final_positive == {8, 9}
    assert fresh[8].lo > Decimal("12295.03615")
    assert final[8].lo > Decimal("11062.69343")

    dbar = sum(fresh, interval.Iv.point(0)) / 10
    pair_margins: list[interval.Iv] = []
    for r in range(1, 6):
        dhat = complex_sum(fresh, r)
        pair_margin = (dbar + complex_norm(dhat)) / PARENT_Q
        assert pair_margin.hi < 0
        pair_margins.append(pair_margin)

    deficits = [positive_part_of_negative(gain) for gain in gains]
    hbar = sum(deficits, interval.Iv.point(0)) / 10
    hhat = complex_sum(deficits, 1)
    dhat = complex_sum(fresh, 1)
    gauge = decagon_gauge(hhat - dhat)
    dc1 = dbar - hbar + gauge
    assert dc1.hi < 0

    compensated = [fresh[d] - deficits[d] for d in range(10)]
    assert compensated[8].lo > Decimal("11062.69343")

    print("status: PASS (directed-interval experiment; not a Lean theorem)")
    print(f"digit_file_sha256={EXPECTED_DIGIT_FILE_SHA256}")
    print("lean_t173_prefix_match=true")
    print(
        f"precision={interval.PREC} taylor_terms={interval.TAYLOR_TERMS} "
        f"orbit_window={ORBIT_WINDOW} workers={MAX_WORKERS}"
    )
    print(
        "t173_child_H_surplus_error_bound="
        f"{interval.UP.multiply(Decimal(CHILD_Q), t173_score_error(CHILD_Q, H))}"
    )
    show("parent_B", parent)
    print("d D_d G_d_plus_D_d")
    for digit in range(10):
        print(
            f"{digit} [{fresh[digit].lo}, {fresh[digit].hi}] "
            f"[{final[digit].lo}, {final[digit].hi}]"
        )
    print(f"fresh_positive={sorted(fresh_positive)}")
    print(f"final_positive={sorted(final_positive)}")
    for r, margin in enumerate(pair_margins, start=1):
        show(f"pair_margin_r{r}", margin)
    show("hbar", hbar)
    show("dc1_gauge", gauge)
    show("dc1_rhs", dc1)
    show("literal_max_Y_lower_witness_d8", compensated[8])


if __name__ == "__main__":
    main()
