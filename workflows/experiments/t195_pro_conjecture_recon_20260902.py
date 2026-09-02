#!/usr/bin/env python3
"""Reproduce the T195 ChatGPT Pro conjecture-mining reconnaissance.

This is a finite decimal-digit experiment, not a proof.  It uses the tracked
1,048,596-digit fractional prefix of pi and mpmath only for the constants in
the theta-seven recurrence.
"""

from __future__ import annotations

import hashlib
from pathlib import Path

import mpmath as mp


HERE = Path(__file__).resolve().parent
DIGIT_PATH = HERE / "data" / "pi_digits_1048596.txt"
OUTPUT_PATH = HERE / "t195_pro_conjecture_recon_20260902.out.md"
EXPECTED_SHA256 = "77eeccb0067283e14c460b33dc230de54ef15c2e825fc2a35c984fb6984bf684"
EXPECTED_DIGITS = 1_048_596

EXTREME_DIGITS = 40
SAFETY_DIGITS = 64
MP_DPS = 60


def load_fractional_digits() -> bytes:
    """Load the exact tracked input and normalize its possible pi prefix."""
    raw = DIGIT_PATH.read_bytes()
    digest = hashlib.sha256(raw).hexdigest()
    if digest != EXPECTED_SHA256:
        raise ValueError(f"unexpected input SHA-256: {digest}")
    if raw.count(b"\n") != 1 or not raw.endswith(b"\n"):
        raise ValueError("digit input must be one newline-terminated line")

    line = raw[:-1]
    if line.startswith(b"3."):
        digits = line[2:]
    elif line.startswith(b"314159"):
        digits = line[1:]
    elif line.startswith(b"141592"):
        digits = line
    else:
        raise ValueError("unrecognized decimal-pi prefix")
    if len(digits) != EXPECTED_DIGITS or not digits.isdigit():
        raise ValueError(f"expected {EXPECTED_DIGITS:,} fractional digits")
    return digits


def markdown_table(headers: list[str], rows: list[list[str]]) -> str:
    lines = ["| " + " | ".join(headers) + " |"]
    lines.append("|" + "|".join("---" for _ in headers) + "|")
    lines.extend("| " + " | ".join(row) + " |" for row in rows)
    return "\n".join(lines)


def decimal_prefix(units: int, places: int) -> str:
    return f"0.{units:0{places}d}"


def scientific(value: mp.mpf, digits: int = 11) -> str:
    return mp.nstr(value, digits, min_fixed=0, max_fixed=0)


def candidate_a(digits: bytes) -> tuple[list[list[str]], list[str], mp.mpf]:
    """Check the dyadic signed cut law with certified 40-digit brackets."""
    scale = 10**EXTREME_DIGITS
    zero_word = b"0" * EXTREME_DIGITS
    nine_word = b"9" * EXTREME_DIGITS
    rows: list[list[str]] = []
    discrepancies: list[str] = []
    normalized_extremes: list[mp.mpf] = []

    for j in range(12, 20):
        start = 1 << j
        stop = 1 << (j + 1)
        full_stop = min(stop, len(digits) - EXTREME_DIGITS + 1)
        if full_stop <= start:
            raise ValueError(f"not enough digits for block j={j}")

        min_n = max_n = start
        min_word = max_word = digits[start : start + EXTREME_DIGITS]
        for n in range(start + 1, full_stop):
            word = digits[n : n + EXTREME_DIGITS]
            if word < min_word:
                min_n, min_word = n, word
            if word > max_word:
                max_n, max_word = n, word

        # The final 19 positions of j=19 have fewer than 40 retained digits.
        # Their available prefixes suffice to prove they cannot be extrema.
        unresolved_min = unresolved_max = False
        for n in range(full_stop, stop):
            prefix = digits[n:]
            unresolved_min |= prefix <= min_word[: len(prefix)]
            unresolved_max |= prefix >= max_word[: len(prefix)]

        min_units = int(min_word)
        max_units = int(max_word)
        # If the following tail is nonzero, these are the first 40 digits of
        # 1-x at the maximizing suffix (digitwise nines-complement).
        min_one_minus_units = scale - 1 - max_units
        min_ambiguous = min_word == zero_word or unresolved_min
        max_ambiguous = max_word == nine_word or unresolved_max

        threshold = mp.mpf(j) / (1 << j)
        eps_min = mp.mpf(4) / 15 * (mp.mpf(5) / 8) ** min_n
        eps_max = mp.mpf(4) / 15 * (mp.mpf(5) / 8) ** max_n
        min_lower = mp.mpf(min_units) / scale
        min_upper = mp.mpf(min_units + 1) / scale
        one_minus_lower = mp.mpf(min_one_minus_units) / scale
        one_minus_upper = mp.mpf(scale - max_units) / scale
        min_pass = (
            not min_ambiguous
            and min_lower > eps_min
            and min_upper < threshold - 2 * eps_min
        )
        max_pass = (
            not max_ambiguous
            and one_minus_lower > eps_max
            and one_minus_upper < threshold - 2 * eps_max
        )
        passed = min_pass and max_pass

        norm_min = min_lower * (1 << j) / j
        norm_one_minus = one_minus_lower * (1 << j) / j
        normalized_extremes.extend((norm_min, norm_one_minus))
        rows.append(
            [
                str(j),
                f"[{start:,}, {stop:,})",
                f"{decimal_prefix(min_units, EXTREME_DIGITS)} @ {min_n:,}",
                f"{decimal_prefix(min_one_minus_units, EXTREME_DIGITS)} @ {max_n:,}",
                f"{float(norm_min):.7f}",
                f"{float(norm_one_minus):.7f}",
                "PASS" if passed else "AMBIGUOUS" if min_ambiguous or max_ambiguous else "FAIL",
            ]
        )
        if not passed:
            discrepancies.append(f"A j={j}: expected PASS")

    max_normalized = max(normalized_extremes)
    if abs(max_normalized - mp.mpf("0.2804")) > mp.mpf("0.0001"):
        discrepancies.append(
            "A: maximum normalized extreme "
            f"{mp.nstr(max_normalized, 10)} is not about 0.2804"
        )
    return rows, discrepancies, max_normalized


def ceil_div(numerator: int, denominator: int) -> int:
    return -(-numerator // denominator)


def candidate_b(digits: bytes) -> tuple[list[list[str]], list[str]]:
    """Check shell-safe colour/cylinder saturation using bytearray bitsets."""
    rows: list[list[str]] = []
    discrepancies: list[str] = []
    tail_scale = 10**SAFETY_DIGITS
    zero_tail = b"0" * SAFETY_DIGITS
    nine_tail = b"9" * SAFETY_DIGITS
    rho = mp.mpf(10) / 16**7

    for ell in range(7, 11):
        shell_start = ceil_div(5**ell - 5, 56)
        shell_stop = ceil_div(5 ** (ell + 1) - 5, 56)
        shell_size = shell_stop - shell_start
        power = 5**ell
        assert power <= 56 * shell_start + 5 < 5 ** (ell + 1)
        assert power <= 56 * (shell_stop - 1) + 5 < 5 ** (ell + 1)

        max_k = 0
        while 64 * ell * ell * 10 ** (max_k + 1) <= power:
            max_k += 1

        states: dict[int, tuple[bytearray, list[int], list[int]]] = {}
        for k in range(1, max_k + 1):
            pair_count = 4 * 10**k
            states[k] = (bytearray(pair_count), [0] * pair_count, [-1] * pair_count)
            # Per the requested 64-digit safety convention, every retained
            # safe suffix clears 2*rho^m throughout this shell.
            assert mp.power(10, -(k + SAFETY_DIGITS)) > 2 * rho**shell_start

        for m in range(shell_start, shell_stop):
            eta = int(power <= 14 * m + 1)
            colour = (pow(2, m, 5) * (4 + 2 * eta)) % 5
            assert 1 <= colour <= 4
            for k, (seen, best, best_m) in states.items():
                word = int(digits[m : m + k])
                tail = digits[m + k : m + k + SAFETY_DIGITS]
                if len(tail) != SAFETY_DIGITS:
                    raise ValueError(f"not enough digits at m={m}, k={k}")
                if tail == zero_tail or tail == nine_tail:
                    continue
                tail_units = int(tail)
                # A digit-only lower bound for distance from either cylinder
                # endpoint; subtract one unit for the unknown infinite tail.
                margin_units = min(tail_units, tail_scale - 1 - tail_units)
                index = (colour - 1) * 10**k + word
                seen[index] = 1
                if margin_units > best[index]:
                    best[index] = margin_units
                    best_m[index] = m

        for k, (seen, best, best_m) in states.items():
            words = 10**k
            missing = seen.count(0)
            worst_index = min(range(len(best)), key=best.__getitem__)
            worst_units = best[worst_index]
            worst_colour = worst_index // words + 1
            worst_word = worst_index % words
            worst_margin = mp.mpf(worst_units) / 10 ** (k + SAFETY_DIGITS)
            rows.append(
                [
                    str(ell),
                    str(k),
                    f"[{shell_start:,}, {shell_stop:,}) ({shell_size:,})",
                    f"{4 * words:,}",
                    str(missing),
                    f"q={worst_colour}, w={worst_word:0{k}d}, m={best_m[worst_index]:,}",
                    scientific(worst_margin),
                ]
            )
            if missing:
                discrepancies.append(f"B ell={ell}, k={k}: expected 0 missing, got {missing}")

    return rows, discrepancies


def orbit_value(digits: bytes, n: int, places: int) -> mp.mpf:
    suffix = digits[n : n + places]
    if len(suffix) != places:
        raise ValueError(f"not enough digits for x_{n} at {places} places")
    return mp.mpf(int(suffix)) / 10**places


def candidate_c(digits: bytes) -> tuple[list[list[str]], list[str]]:
    """Check the one-step theta-seven fixed-branch recurrence."""
    mp.mp.dps = MP_DPS
    c = mp.frac(16 * mp.pi)
    a = 1 - c
    beta = mp.frac(144 * mp.pi)
    delta = mp.mpf("1e-30")
    identity_error = 10 * a + beta - (a + 7)

    carry_low = (7 - beta) / 10
    carry_high = (8 - beta) / 10
    # For carry 7, v>a+delta maps to x in (delta, carry_high-a),
    # while v<a-delta maps to x in [c+carry_low, 1-delta).
    right_bounds = (delta, carry_high - a)
    left_bounds = (c + carry_low, 1 - delta)
    assert abs(right_bounds[1] - c / 10) < mp.mpf("1e-58")
    assert abs(left_bounds[0] - (mp.mpf(9) / 10 + c / 10)) < mp.mpf("1e-58")

    rows: list[list[str]] = []
    discrepancies: list[str] = []
    constants = "; ".join(
        (
            f"c={mp.nstr(c, 25)}",
            f"a={mp.nstr(a, 25)}",
            f"beta={mp.nstr(beta, 25)}",
        )
    )
    rows.append(["constants (60 dps)", constants, "-"])

    expected = {18: (6_983, 19_335), 19: (13_716, 38_772)}
    boundaries = (*right_bounds, *left_bounds)
    boundary_units = {
        length: tuple(int(mp.floor(boundary * 10**length)) for boundary in boundaries)
        for length in range(1, EXTREME_DIGITS + 1)
    }
    for j in (18, 19):
        right_count = left_count = ambiguous = 0
        for n in range(1 << j, 1 << (j + 1)):
            length = min(EXTREME_DIGITS, len(digits) - n)
            if length <= 0:
                raise ValueError(f"no suffix digits at n={n}")
            units = int(digits[n : n + length])
            comparisons = tuple(
                (units > threshold) - (units < threshold)
                for threshold in boundary_units[length]
            )
            if 0 in comparisons:
                ambiguous += 1
                continue
            if comparisons[0] > 0 and comparisons[1] < 0:
                right_count += 1
            if comparisons[2] > 0 and comparisons[3] < 0:
                left_count += 1

        observed = (right_count, left_count)
        passed = observed == expected[j] and ambiguous == 0
        rows.append(
            [
                f"block j={j} [{1 << j:,}, {1 << (j + 1):,})",
                f"right={right_count:,}; left={left_count:,}; ambiguous={ambiguous}",
                "PASS" if passed else "FAIL",
            ]
        )
        if not passed:
            discrepancies.append(
                f"C j={j}: expected right/left={expected[j]}, got {observed}, ambiguous={ambiguous}"
            )

    identity_pass = abs(identity_error) < mp.mpf("1e-58")
    rows.append(
        [
            "10a + beta - (a + 7)",
            scientific(identity_error, 6),
            "PASS" if identity_pass else "FAIL",
        ]
    )
    if not identity_pass:
        discrepancies.append(f"C identity residual: {mp.nstr(identity_error, 12)}")

    sample_ns = (262_144, 400_000, 524_288, 800_000)
    recurrence_errors: list[mp.mpf] = []
    recurrence_cells: list[str] = []
    for n in sample_ns:
        x_n = orbit_value(digits, n, MP_DPS)
        x_next = orbit_value(digits, n + 1, MP_DPS)
        v_n = mp.frac(x_n - c)
        v_next = mp.frac(x_next - c)
        error = v_next - mp.frac(10 * v_n + beta)
        recurrence_errors.append(error)
        recurrence_cells.append(f"n={n:,}: {scientific(error, 6)}")
    recurrence_pass = max(map(abs, recurrence_errors)) < mp.mpf("1e-58")
    rows.append(
        [
            "v_(n+1) - {10v_n + beta}",
            "; ".join(recurrence_cells),
            "PASS" if recurrence_pass else "FAIL",
        ]
    )
    if not recurrence_pass:
        discrepancies.append("C recurrence residual exceeded 1e-58")

    return rows, discrepancies


def main() -> None:
    mp.mp.dps = MP_DPS
    digits = load_fractional_digits()
    a_rows, a_discrepancies, _ = candidate_a(digits)
    b_rows, b_discrepancies = candidate_b(digits)
    c_rows, c_discrepancies = candidate_c(digits)
    discrepancies = a_discrepancies + b_discrepancies + c_discrepancies

    sections = [
        "### A. Dyadic signed cut law\n\n"
        + markdown_table(
            ["j", "block", "min x @ n (40 digits)", "min (1-x) @ n (40 digits)", "norm x", "norm (1-x)", "result"],
            a_rows,
        ),
        "### B. Five-adic shell-safe cylinder saturation\n\n"
        + markdown_table(
            ["l", "k", "shell [start, stop) (size)", "(q,w) pairs", "missing", "worst pair witness", "worst best margin lower bound"],
            b_rows,
        ),
        "### C. Theta-seven fixed-branch recurrence (H=1)\n\n"
        + markdown_table(["check", "value", "result"], c_rows),
        "### Discrepancies\n\n" + ("; ".join(discrepancies) if discrepancies else "none"),
    ]
    report = "\n\n".join(sections)
    OUTPUT_PATH.write_text(report + "\n", encoding="utf-8")
    print(report)


if __name__ == "__main__":
    main()
