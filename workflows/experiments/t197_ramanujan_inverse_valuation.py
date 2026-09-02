#!/usr/bin/env python3
"""Numerically check the Ramanujan 4/pi inverse-series valuation claims.

This is a finite experiment, not a proof.  Coefficients and partial sums use
exact Python integers and ``fractions.Fraction``.  Only comparisons with pi
use mpmath, at 3000 decimal digits.
"""

from __future__ import annotations

from fractions import Fraction
from math import comb
from pathlib import Path

import mpmath as mp


HERE = Path(__file__).resolve().parent
OUTPUT_PATH = HERE / "t197_ramanujan_inverse_valuation.out.md"
MAX_N = 600
MP_DPS = 3_000
IDENTITY_N = 600
ERROR_NS = (100, 300, 600)
EXPECTED_INITIAL_R = (1, -56, 328, -13_120, -249_304, -14_947_264)


def valuation(value: int, prime: int) -> int | None:
    """Return v_prime(value), or None when value is zero."""
    if value == 0:
        return None
    value = abs(value)
    exponent = 0
    while value % prime == 0:
        exponent += 1
        value //= prime
    return exponent


def valuation_10(value: int) -> int | None:
    """Return the number of trailing decimal zeroes, or None at zero."""
    if value == 0:
        return None
    value = abs(value)
    exponent = 0
    while value % 10 == 0:
        exponent += 1
        value //= 10
    return exponent


def exact_radix_partial(coefficients: list[int], n: int, radix: int) -> Fraction:
    """Return sum_{j=0}^n coefficients[j] * radix^(-j) exactly."""
    value = Fraction(0)
    for coefficient in reversed(coefficients[: n + 1]):
        value = coefficient + value / radix
    return value


def as_mpf(value: Fraction) -> mp.mpf:
    return mp.mpf(value.numerator) / value.denominator


def scientific(value: mp.mpf, digits: int = 25) -> str:
    """Format an mpf in normalized scientific notation."""
    if value == 0:
        return "0"
    exponent = int(mp.floor(mp.log10(abs(value))))
    mantissa = value / mp.power(10, exponent)
    return f"{mp.nstr(mantissa, digits)}e{exponent:+d}"


def sign_word(value: mp.mpf) -> str:
    if value > 0:
        return "positive"
    if value < 0:
        return "negative"
    return "zero"


def markdown_table(headers: tuple[str, ...], rows: list[tuple[str, ...]]) -> str:
    lines = ["| " + " | ".join(headers) + " |"]
    lines.append("|" + "|".join("---" for _ in headers) + "|")
    lines.extend("| " + " | ".join(row) + " |" for row in rows)
    return "\n".join(lines)


def failure_section(
    title: str, headers: tuple[str, ...], rows: list[tuple[str, ...]]
) -> str:
    if not rows:
        return f"## {title}\n\nNone."
    return f"## {title}\n\n" + markdown_table(headers, rows)


def main() -> None:
    mp.mp.dps = MP_DPS

    # (a) Generate A_n and the formal inverse coefficients r_n exactly.
    a_values = []
    for n in range(MAX_N + 1):
        central_binomial = comb(2 * n, n)
        a_values.append((6 * n + 1) * central_binomial**3)

    r_values = [1]
    for n in range(1, MAX_N + 1):
        r_values.append(
            -sum(a_values[j] * r_values[n - j] for j in range(1, n + 1))
        )

    inverse_convolution_failures: list[tuple[str, ...]] = []
    for n in range(MAX_N + 1):
        observed = sum(
            a_values[j] * r_values[n - j] for j in range(n + 1)
        )
        expected = 1 if n == 0 else 0
        if observed != expected:
            inverse_convolution_failures.append(
                (str(n), str(expected), str(observed))
            )
    check_a = len(r_values) == MAX_N + 1 and not inverse_convolution_failures

    # (b) Bound the positive tail of F(1/256).  Since C(2n,n) <= 4^n,
    # A_n / 256^n <= (6n+1) / 4^n.  For k=N+1, the resulting geometric-
    # arithmetic tail is sum_{n=k}^infinity (6n+1)/4^n=(8k+4)/4^k.
    f_partial = exact_radix_partial(a_values, IDENTITY_N, 256)
    tail_start = IDENTITY_N + 1
    f_tail_bound = Fraction(8 * tail_start + 4, 4**tail_start)
    four_over_pi = 4 / mp.pi
    f_difference = four_over_pi - as_mpf(f_partial)
    f_tail_bound_mpf = as_mpf(f_tail_bound)
    check_b = (
        f_difference > 0
        and f_difference <= f_tail_bound_mpf
        and f_tail_bound < Fraction(1, 10**200)
    )

    # (c) Check the six claimed initial inverse coefficients.
    initial_rows: list[tuple[str, ...]] = []
    initial_failures: list[tuple[str, ...]] = []
    for n, expected in enumerate(EXPECTED_INITIAL_R):
        observed = r_values[n]
        verdict = "PASS" if observed == expected else "FAIL"
        row = (str(n), str(expected), str(observed), verdict)
        initial_rows.append(row)
        if observed != expected:
            initial_failures.append(row)
    check_c = not initial_failures

    # (d) Check the proposed exact 2-adic valuation law on the finite range.
    valuation_2_failures: list[tuple[str, ...]] = []
    for n in range(1, MAX_N + 1):
        observed = valuation(r_values[n], 2)
        expected = 3 * n.bit_count()
        if observed != expected:
            valuation_2_failures.append(
                (
                    str(n),
                    "undefined (r_n=0)" if observed is None else str(observed),
                    str(expected),
                )
            )
    check_d = not valuation_2_failures

    # (e) Report the requested 5-adic valuations and all zero coefficients in
    # the computed range.  The wording is deliberately finite: this experiment
    # cannot decide whether a later, uncomputed coefficient vanishes.
    zero_indices = [n for n, value in enumerate(r_values) if value == 0]
    valuation_5_entries = [
        "infinity" if (value := valuation(r_values[n], 5)) is None else str(value)
        for n in range(41)
    ]
    valuation_5_rows: list[tuple[str, ...]] = []
    for offset in range(14):
        row: list[str] = []
        for n in (offset, offset + 14, offset + 28):
            if n <= 40:
                row.extend((str(n), valuation_5_entries[n]))
            else:
                row.extend(("", ""))
        valuation_5_rows.append(tuple(row))

    # (f) Compare inverse-series partial sums directly with pi/4.
    inverse_error_rows: list[tuple[str, ...]] = []
    for n in ERROR_NS:
        partial = exact_radix_partial(r_values, n, 256)
        error = mp.pi / 4 - as_mpf(partial)
        inverse_error_rows.append(
            (str(n), sign_word(error), scientific(abs(error), 30))
        )

    # (g) Construct g_{8n} exactly and check its decimal valuation.  The n=0
    # term is the separate leading 4, so the stated law is checked for n>=1.
    valuation_10_failures: list[tuple[str, ...]] = []
    power_5_8n = 1
    factor_5_8 = 5**8
    for n in range(1, MAX_N + 1):
        power_5_8n *= factor_5_8
        g_8n = 4 * r_values[n] * power_5_8n
        observed = valuation_10(g_8n)
        expected = 2 + 3 * n.bit_count()
        if observed != expected:
            valuation_10_failures.append(
                (
                    str(n),
                    "undefined (g_8n=0)" if observed is None else str(observed),
                    str(expected),
                )
            )
    check_g = not valuation_10_failures

    gate_passes = check_a and check_b and check_c and check_d and check_g
    verdict_rows = [
        (
            "(a)",
            "PASS" if check_a else "FAIL",
            f"Computed A_n and r_n exactly for 0<=n<={MAX_N}; checked F(z)R(z)=1 through z^{MAX_N}.",
        ),
        (
            "(b)",
            "PASS" if check_b else "FAIL",
            f"0 < 4/pi-S_{IDENTITY_N} <= explicit tail bound < 10^-200.",
        ),
        (
            "(c)",
            "PASS" if check_c else "FAIL",
            "All six listed coefficients agree exactly.",
        ),
        (
            "(d)",
            "PASS" if check_d else "FAIL",
            f"v_2(r_n)=3*s_2(n) for 1<=n<={MAX_N}.",
        ),
        (
            "(e)",
            "REPORT",
            f"v_5(r_n) tabulated for 0<=n<=40; zero search covers 0<=n<={MAX_N}.",
        ),
        (
            "(f)",
            "REPORT",
            "Signed inverse-series errors reported at N=100, 300, 600.",
        ),
        (
            "(g)",
            "PASS" if check_g else "FAIL",
            f"v_10(g_(8n))=2+3*s_2(n) for 1<=n<={MAX_N}.",
        ),
    ]

    sections = [
        "# T197 Ramanujan inverse-series valuation experiment",
        "Finite numerical verification only; this report is an `experiment`, not a proof.",
        "## Verdicts\n\n"
        + markdown_table(("check", "verdict", "detail"), verdict_rows),
        "## (b) Ramanujan 4/pi identity check\n\n"
        + "\n".join(
            (
                f"- Exact partial sum: `S_{IDENTITY_N}=sum_(n=0)^{IDENTITY_N} A_n/256^n`.",
                f"- `4/pi` (210 significant digits): `{mp.nstr(four_over_pi, 210)}`",
                f"- `S_{IDENTITY_N}` (210 significant digits): `{mp.nstr(as_mpf(f_partial), 210)}`",
                f"- Observed `4/pi-S_{IDENTITY_N}`: `{scientific(f_difference, 30)}`.",
                f"- Explicit bound: using `C(2n,n)<=4^n`, the omitted positive tail is at most `(8k+4)/4^k` for `k={tail_start}`, namely `{scientific(f_tail_bound_mpf, 30)}`.",
                f"- Bound below `10^-200`: {'PASS' if f_tail_bound < Fraction(1, 10**200) else 'FAIL'}.",
            )
        ),
        "## (c) Listed inverse coefficients\n\n"
        + markdown_table(("n", "expected r_n", "observed r_n", "verdict"), initial_rows),
        failure_section(
            "(a) Inverse-convolution failures",
            ("n", "expected coefficient", "observed coefficient"),
            inverse_convolution_failures,
        ),
        failure_section(
            "(d) 2-adic valuation failures",
            ("n", "observed v_2(r_n)", "expected 3*s_2(n)"),
            valuation_2_failures,
        ),
        "## (e) 5-adic valuations\n\n"
        + markdown_table(
            ("n", "v_5(r_n)", "n", "v_5(r_n)", "n", "v_5(r_n)"),
            valuation_5_rows,
        )
        + "\n\n"
        + (
            f"Zero coefficients for `0<=n<={MAX_N}`: "
            + (", ".join(map(str, zero_indices)) if zero_indices else "none")
            + "."
        ),
        "## (f) Inverse-series truncation errors\n\n"
        + "The sign is that of `pi/4-sum_(n=0)^N r_n/256^n`.\n\n"
        + markdown_table(("N", "sign", "absolute error"), inverse_error_rows),
        failure_section(
            "(g) Decimal valuation failures",
            ("n", "observed v_10(g_(8n))", "expected 2+3*s_2(n)"),
            valuation_10_failures,
        ),
        "## Ledger gate\n\n"
        + (
            "PASS: checks (a), (b), (c), (d), and (g) all passed."
            if gate_passes
            else "FAIL: at least one of checks (a), (b), (c), (d), and (g) failed."
        ),
    ]
    report = "\n\n".join(sections)
    OUTPUT_PATH.write_text(report + "\n", encoding="utf-8")
    print(report)


if __name__ == "__main__":
    main()
