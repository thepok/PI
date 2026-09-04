#!/usr/bin/env python3
"""Track B conjecture-mining cycle 2 reconnaissance.

Status: experiment.  This script checks finite decimal data; it proves no
conjecture and no unbounded digit-occurrence statement.

Archive location when copied into PI:
    workflows/experiments/mining_cycle2.py

Default input at that location:
    workflows/experiments/data/pi_digits_1048596.txt

The retained tests are the two orientations of the Machin critical-shell law.
A Ramanujan valuation-budget selector is also reproduced and explicitly marked
REJECTED because T202 supplies no carry/location bridge to decimal digits.
Only Python's standard library is used.
"""

from __future__ import annotations

import argparse
import hashlib
import math
from dataclasses import dataclass, field
from pathlib import Path
from typing import Iterable

EXPECTED_SHA256 = "77eeccb0067283e14c460b33dc230de54ef15c2e825fc2a35c984fb6984bf684"
EXPECTED_DIGITS = 1_048_596
# Known tracked digit files: name -> (sha256, digit count). The 4,700,000-digit
# file was generated with mpmath (Chudnovsky) on 2026-09-04; its first
# 1,048,596 digits are byte-identical to the verified 1,048,596-digit file.
KNOWN_DIGIT_FILES = {
    "pi_digits_1048596.txt": (EXPECTED_SHA256, EXPECTED_DIGITS),
    "pi_digits_4700000.txt": (
        "0a14c71c5e0f093b25707c907bf416edc553153ff7c57c89bff31513889c0a93",
        4_700_000,
    ),
}
SAFETY_DIGITS = 18
NUMERIC_PAD = 5.0e-10

LOG10_2 = math.log10(2.0)
LOG10_3 = math.log10(3.0)
LOG10_5 = math.log10(5.0)
LOG_3_OVER_7 = math.log(3.0 / 7.0)
LOG_10 = math.log(10.0)


@dataclass(frozen=True)
class Hit:
    side: str
    e: int
    m: int
    M: int
    k: int
    n: int
    c: float
    digits: str


@dataclass
class ShellStats:
    e: int
    k: int
    m_start: int
    m_stop: int  # exclusive
    full_expected_per_side: float = 0.0
    tested_expected_per_side: float = 0.0
    tested: int = 0
    zero_hits: int = 0
    nine_hits: int = 0
    zero_ambiguous: int = 0
    nine_ambiguous: int = 0
    first_zero: Hit | None = None
    first_nine: Hit | None = None
    max_tested_n: int | None = None
    min_floor_clearance: float = math.inf

    @property
    def size(self) -> int:
        return self.m_stop - self.m_start

    @property
    def complete(self) -> bool:
        return self.tested == self.size


@dataclass
class RamanujanStats:
    K: int
    n_bound: int
    fully_observed: bool
    eligible: int = 0
    expected_per_side: float = 0.0
    zero_hits: int = 0
    nine_hits: int = 0
    first_zero: tuple[int, int, int, int, str] | None = None
    first_nine: tuple[int, int, int, int, str] | None = None


def ceil_div(a: int, b: int) -> int:
    return -(-a // b)


def shell_bounds(e: int) -> tuple[int, int]:
    """Return [lo, hi) for 5^e <= 4m+3 < 5^(e+1)."""
    lo = ceil_div(5**e - 3, 4)
    hi = ceil_div(5 ** (e + 1) - 3, 4)
    assert hi - lo == 5**e
    return lo, hi


def machin_log10_width(M: int) -> float:
    """Numerically evaluate log10(W_m) from the exact T198 width formula.

    W_m = 8/(M*3^M) + 4/(M*7^M)
        = 8/(M*3^M) * (1 + (1/2)*(3/7)^M).

    In the retained range M >= 627, the correction is below 10^-230, but
    log1p is used while it remains representable.
    """
    exponent = M * LOG_3_OVER_7
    relative = 0.0 if exponent < -745.0 else 0.5 * math.exp(exponent)
    correction = math.log1p(relative) / LOG_10
    return math.log10(8.0) - math.log10(M) - M * LOG10_3 + correction


def machin_scale(e: int, m: int) -> tuple[int, int, int, float, float]:
    """Return (M, k_e, n_m, c_m, floor-clearance).

    h_m = floor(log10(1/W_m)), n_m = h_m-k_e-1, and
    c_m = 10^(n_m+k_e) W_m.  Thus w_m=10^n_m W_m=c_m*10^-k_e.
    """
    M = 4 * m + 3
    if not (5**e <= M < 5 ** (e + 1)):
        raise ValueError("m is outside its claimed five-adic shell")
    k = math.floor(e * LOG10_5)
    if k < 1:
        raise ValueError("k_e is not positive")
    log_width = machin_log10_width(M)
    log_inverse_width = -log_width
    h = math.floor(log_inverse_width)
    n = h - k - 1
    c = 10.0 ** (n + k + log_width)
    floor_clearance = abs(log_inverse_width - round(log_inverse_width))
    if not (0.009999999 <= c <= 0.100000001):
        raise ArithmeticError(f"unexpected matched-width scale c={c}")
    return M, k, n, c, floor_clearance


def load_digits(path: Path) -> str:
    raw = path.read_bytes()
    digest = hashlib.sha256(raw).hexdigest()
    expected_sha, expected_digits = KNOWN_DIGIT_FILES.get(
        path.name, (EXPECTED_SHA256, EXPECTED_DIGITS)
    )
    if digest != expected_sha:
        raise ValueError(f"unexpected SHA-256 for {path}: {digest}")
    line = raw.decode("ascii").strip()
    if len(line) != expected_digits or not line.isdigit():
        raise ValueError(f"expected exactly {expected_digits:,} decimal digits")
    return line


def classify_tail(digits: str, start: int, k: int, c: float) -> tuple[str, str, str]:
    """Classify zero/nine events using an 18-digit tail interval and numeric pad.

    If the first k digits are all zero or all nine, both directed margin events
    reduce to the same condition c < T < 1-c for the fractional tail T after
    those k digits.  The unknown infinite tail lies in [A/10^q,(A+1)/10^q).

    Returns (zero_status, nine_status, displayed_digits), where each status is
    one of HIT, MISS, AMBIGUOUS, or UNAVAILABLE.
    """
    q = SAFETY_DIGITS
    if start < 0 or start + k + q > len(digits):
        return "UNAVAILABLE", "UNAVAILABLE", ""

    block = digits[start : start + k]
    tail_text = digits[start + k : start + k + q]
    tail_units = int(tail_text)
    scale = 10**q
    lo = tail_units / scale
    hi = (tail_units + 1) / scale

    inside = lo > c + NUMERIC_PAD and hi < 1.0 - c - NUMERIC_PAD
    outside = hi <= c - NUMERIC_PAD or lo >= 1.0 - c + NUMERIC_PAD
    tail_status = "HIT" if inside else "MISS" if outside else "AMBIGUOUS"

    def side_status(required: str) -> str:
        if block != required * k:
            return "MISS"
        return tail_status

    shown = digits[start : start + k + q]
    return side_status("0"), side_status("9"), shown


def scan_machin_shells(digits: str, min_e: int = 2) -> list[ShellStats]:
    """Scan through the first shell that is not fully covered by the corpus."""
    output: list[ShellStats] = []
    e = min_e
    while True:
        lo, hi = shell_bounds(e)
        k = math.floor(e * LOG10_5)
        if k < 1:
            e += 1
            continue
        stats = ShellStats(e=e, k=k, m_start=lo, m_stop=hi)

        for m in range(lo, hi):
            M, observed_k, n, c, floor_clearance = machin_scale(e, m)
            assert observed_k == k
            probability = (1.0 - 2.0 * c) * 10.0 ** (-k)
            stats.full_expected_per_side += probability

            zero_status, nine_status, shown = classify_tail(digits, n, k, c)
            if zero_status == "UNAVAILABLE":
                continue

            stats.tested += 1
            stats.tested_expected_per_side += probability
            stats.max_tested_n = n if stats.max_tested_n is None else max(stats.max_tested_n, n)
            stats.min_floor_clearance = min(stats.min_floor_clearance, floor_clearance)

            if zero_status == "HIT":
                stats.zero_hits += 1
                if stats.first_zero is None:
                    stats.first_zero = Hit("0", e, m, M, k, n, c, shown)
            elif zero_status == "AMBIGUOUS":
                stats.zero_ambiguous += 1

            if nine_status == "HIT":
                stats.nine_hits += 1
                if stats.first_nine is None:
                    stats.first_nine = Hit("9", e, m, M, k, n, c, shown)
            elif nine_status == "AMBIGUOUS":
                stats.nine_ambiguous += 1

        output.append(stats)
        if not stats.complete:
            break
        e += 1
    return output


def ramanujan_parameters(n: int) -> tuple[int, int, int, int]:
    """Return s_2(n), lambda_n, p_n, k_n for the rejected T202 selector."""
    s = n.bit_count()
    lam = 12 * n + 4 - 3 * s
    p = math.floor(lam * LOG10_2)
    k = max(1, math.floor(3 * s * LOG10_2))
    return s, lam, p, k


def max_ramanujan_index(digit_count: int) -> int:
    lo, hi = 1, digit_count
    while lo < hi:
        mid = (lo + hi + 1) // 2
        _, _, p, k = ramanujan_parameters(mid)
        if p + k <= digit_count:
            lo = mid
        else:
            hi = mid - 1
    return lo


def scan_rejected_ramanujan(digits: str, max_K: int = 5) -> list[RamanujanStats]:
    """Reproduce the selector that was screened out on admission-test grounds."""
    max_n = max_ramanujan_index(len(digits))
    rows = [
        RamanujanStats(K=K, n_bound=1 << (4 * K + 2), fully_observed=(1 << (4 * K + 2)) - 1 <= max_n)
        for K in range(1, max_K + 1)
    ]

    for n in range(1, max_n + 1):
        s, _lam, p, k = ramanujan_parameters(n)
        block = digits[p : p + k]
        for row in rows:
            if n >= row.n_bound or k < row.K:
                continue
            row.eligible += 1
            row.expected_per_side += 10.0 ** (-k)
            if block == "0" * k:
                row.zero_hits += 1
                if row.first_zero is None:
                    row.first_zero = (n, s, p, k, digits[p : p + max(k, 18)])
            if block == "9" * k:
                row.nine_hits += 1
                if row.first_nine is None:
                    row.first_nine = (n, s, p, k, digits[p : p + max(k, 18)])
    return rows


def markdown_table(headers: Iterable[str], rows: Iterable[Iterable[str]]) -> str:
    headers = list(headers)
    lines = ["| " + " | ".join(headers) + " |"]
    lines.append("|" + "|".join("---" for _ in headers) + "|")
    lines.extend("| " + " | ".join(row) + " |" for row in rows)
    return "\n".join(lines)


def hit_text(hit: Hit | None) -> str:
    if hit is None:
        return "--"
    return f"m={hit.m}, n={hit.n}, c={hit.c:.8f}, digits={hit.digits}"


def render_report(path: Path, shells: list[ShellStats], ramanujan: list[RamanujanStats]) -> str:
    retained = [row for row in shells if row.e >= 4 and row.complete]
    partial = next((row for row in shells if not row.complete), None)

    shell_rows = []
    for row in shells:
        coverage = f"{row.tested:,}/{row.size:,}" + (" full" if row.complete else " partial")
        shell_rows.append(
            [
                str(row.e),
                str(row.k),
                f"[{row.m_start:,},{row.m_stop:,})",
                coverage,
                f"{row.tested_expected_per_side:.6f}",
                f"{row.full_expected_per_side:.6f}",
                str(row.zero_hits),
                str(row.nine_hits),
                f"{row.zero_ambiguous}/{row.nine_ambiguous}",
            ]
        )

    example_rows = []
    for row in retained:
        example_rows.append([str(row.e), "0", hit_text(row.first_zero)])
        example_rows.append([str(row.e), "9", hit_text(row.first_nine)])

    ram_rows = []
    for row in ramanujan:
        ram_rows.append(
            [
                str(row.K),
                f"n<{row.n_bound:,}",
                "full" if row.fully_observed else "partial",
                f"{row.expected_per_side:.6f}",
                str(row.zero_hits),
                str(row.nine_hits),
            ]
        )

    total_expected = sum(row.tested_expected_per_side for row in retained)
    total_zero = sum(row.zero_hits for row in retained)
    total_nine = sum(row.nine_hits for row in retained)
    min_clearance = min(row.min_floor_clearance for row in shells if row.tested)

    lines = [
        "# Conjecture-mining cycle 2 numerical output",
        "",
        "Status: `experiment`; finite reconnaissance only; no theorem is claimed.",
        "",
        f"- input: `{path}`",
        f"- decimal digits: `{EXPECTED_DIGITS}` (zero-based after the point)",
        f"- SHA-256: `{EXPECTED_SHA256}`",
        f"- safety tail: `{SAFETY_DIGITS}` digits",
        "",
        "## Machin matched critical shells",
        "",
        markdown_table(
            ["e", "k_e", "m range", "coverage", "null E tested/side", "null E full/side", "0 hits", "9 hits", "ambig 0/9"],
            shell_rows,
        ),
        "",
        f"Complete retained shells e=4..{retained[-1].e}: expected `{total_expected:.12f}` and observed `{total_zero}` zero-side, `{total_nine}` nine-side hits.",
        f"Closest tested `-log10(W_m)` to an integer: `{min_clearance:.12g}`; numeric pad `{NUMERIC_PAD:g}`.",
        "",
        "### First robust hit in each complete retained shell",
        "",
        markdown_table(["e", "side", "first hit"], example_rows),
        "",
    ]
    if partial is not None:
        lines.extend(
            [
                f"The first incomplete shell is e={partial.e}: `{partial.tested:,}/{partial.size:,}` candidates are observable; zero hits there do not falsify either law.",
                "",
            ]
        )

    lines.extend(
        [
            "## Rejected Ramanujan valuation-budget selector",
            "",
            markdown_table(["K", "horizon", "coverage", "null E/side", "0 hits", "9 hits"], ram_rows),
            "",
            "This selector is reported for reproducibility but rejected: the T202 ramp supplies no wrap-aware decimal carry or target-location mechanism.",
            "",
        ]
    )
    return "\n".join(lines)


def parse_args() -> argparse.Namespace:
    here = Path(__file__).resolve().parent
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--digits",
        type=Path,
        default=here / "data" / "pi_digits_1048596.txt",
        help="path to the tracked newline-terminated decimal digit file",
    )
    parser.add_argument(
        "--output",
        type=Path,
        default=None,
        help="optional path for the generated Markdown output",
    )
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    digits = load_digits(args.digits)
    shells = scan_machin_shells(digits)
    ramanujan = scan_rejected_ramanujan(digits)
    report = render_report(args.digits, shells, ramanujan)
    if args.output is not None:
        args.output.write_text(report + "\n", encoding="utf-8")
    print(report)


if __name__ == "__main__":
    main()
