#!/usr/bin/env python3
"""Check exact denominator valuations for the Machin 3/7 pi brackets.

This is a finite experiment, not a proof.  All rational calculations use
``fractions.Fraction``; only the comparisons with pi use mpmath at 2000 dps.
"""

from __future__ import annotations

from fractions import Fraction
from pathlib import Path

import mpmath as mp


HERE = Path(__file__).resolve().parent
OUTPUT_PATH = HERE / "t196_machin37_bracket_valuation.out.md"
MAX_M = 400
MP_DPS = 2_000
SAMPLE_MS = (0, 1, 6, 31, 156, 400)


def valuation(value: int, prime: int) -> int:
    """Return the exponent of prime in a positive integer."""
    exponent = 0
    while value % prime == 0:
        exponent += 1
        value //= prime
    return exponent


def floor_log(value: int, base: int) -> int:
    """Return floor(log_base(value)) using integer arithmetic."""
    exponent = 0
    power = 1
    while power * base <= value:
        exponent += 1
        power *= base
    return exponent


def machin_term(j: int, q: int) -> Fraction:
    sign = 1 if j % 2 == 0 else -1
    return Fraction(sign, (2 * j + 1) * q ** (2 * j + 1))


def as_mpf(value: Fraction) -> mp.mpf:
    return mp.mpf(value.numerator) / value.denominator


def markdown_table(headers: tuple[str, ...], rows: list[tuple[str, ...]]) -> str:
    lines = ["| " + " | ".join(headers) + " |"]
    lines.append("|" + "|".join("---" for _ in headers) + "|")
    lines.extend("| " + " | ".join(row) + " |" for row in rows)
    return "\n".join(lines)


def main() -> None:
    mp.mp.dps = MP_DPS
    pi = mp.pi
    s3 = Fraction(0)
    s7 = Fraction(0)
    failures: list[tuple[str, str, str]] = []
    sample_rows: list[tuple[str, ...]] = []
    bracket_passes = 0
    width_passes = 0
    denominator_passes = 0

    for m in range(MAX_M + 1):
        even_j = 2 * m
        s3 += machin_term(even_j, 3)
        s7 += machin_term(even_j, 7)
        upper = 8 * s3 + 4 * s7

        odd_j = even_j + 1
        s3 += machin_term(odd_j, 3)
        s7 += machin_term(odd_j, 7)
        lower = 8 * s3 + 4 * s7

        p_m = 4 * m + 3
        expected_width = Fraction(8, p_m * 3**p_m) + Fraction(
            4, p_m * 7**p_m
        )
        expected_v5 = floor_log(p_m, 5)

        lower_mpf = as_mpf(lower)
        upper_mpf = as_mpf(upper)
        bracket_ok = lower_mpf < pi < upper_mpf
        width_ok = upper - lower == expected_width
        lower_den = lower.denominator
        upper_den = upper.denominator
        lower_v5 = valuation(lower_den, 5)
        upper_v5 = valuation(upper_den, 5)
        denominator_ok = (
            lower_den % 2 == 1
            and upper_den % 2 == 1
            and lower_v5 == expected_v5
            and upper_v5 == expected_v5
        )

        bracket_passes += bracket_ok
        width_passes += width_ok
        denominator_passes += denominator_ok

        failed_claims: list[str] = []
        details: list[str] = []
        if not bracket_ok:
            failed_claims.append("bracket")
            details.append(
                "pi-L="
                + mp.nstr(pi - lower_mpf, 8)
                + ", U-pi="
                + mp.nstr(upper_mpf - pi, 8)
            )
        if not width_ok:
            failed_claims.append("width")
            details.append("U-L differs from the claimed exact width")
        if not denominator_ok:
            failed_claims.append("denominator")
            details.append(
                f"odd(L/U)={lower_den % 2 == 1}/{upper_den % 2 == 1}, "
                f"v5(L/U)={lower_v5}/{upper_v5}, expected={expected_v5}"
            )
        if failed_claims:
            failures.append((str(m), ", ".join(failed_claims), "; ".join(details)))

        if m in SAMPLE_MS:
            sample_rows.append(
                (
                    str(m),
                    str(p_m),
                    f"{valuation(lower_den, 2)}/{valuation(upper_den, 2)}",
                    f"{valuation(lower_den, 3)}/{valuation(upper_den, 3)}",
                    f"{lower_v5}/{upper_v5}",
                    f"{valuation(lower_den, 7)}/{valuation(upper_den, 7)}",
                )
            )

    failure_rows = failures or [("--", "none", "--")]
    total = MAX_M + 1
    sections = [
        "# T196 Machin 3/7 bracket valuation experiment",
        "## Claim failures\n\n"
        + markdown_table(("m", "failed claim(s)", "details"), failure_rows),
        "## Sample denominator valuations\n\n"
        + "Entries are `v_p(den L_m)/v_p(den U_m)`.\n\n"
        + markdown_table(("m", "p_m", "v2", "v3", "v5", "v7"), sample_rows),
        "## Summary\n\n"
        + "\n".join(
            (
                f"- Range: `m=0..{MAX_M}` ({total} cases); exact rational arithmetic; "
                f"`mpmath` pi at {MP_DPS} decimal digits.",
                f"- Brackets `L_m < pi < U_m`: "
                f"{'PASS' if bracket_passes == total else 'FAIL'} "
                f"({bracket_passes}/{total}).",
                f"- Width `U_m-L_m=8/(p_m*3^p_m)+4/(p_m*7^p_m)`: "
                f"{'PASS' if width_passes == total else 'FAIL'} "
                f"({width_passes}/{total}, exact).",
                f"- Odd reduced denominators with "
                f"`v_5=floor(log_5(4m+3))`: "
                f"{'PASS' if denominator_passes == total else 'FAIL'} "
                f"({denominator_passes}/{total}).",
                f"- Failing values of `m`: {len(failures)}.",
            )
        ),
    ]
    report = "\n\n".join(sections)
    OUTPUT_PATH.write_text(report + "\n", encoding="utf-8")
    print(report)


if __name__ == "__main__":
    main()
