#!/usr/bin/env python3
"""Independent replay of the frozen three-grid full-phase experiment.

This file deliberately imports no branch checker.  It reconstructs the six
endpoint pairs, the small exact BBP sums, a separately rounded MPFR prefix of
pi, the 3-adic endpoint units, every phase centre, the complete residual
grids, and the frozen aggregate record.  All finite conclusions remain
``experiment``; the two asymptotic statements and canonical V1 are not
asserted.
"""

from __future__ import annotations

import hashlib
import math
import sys
from fractions import Fraction
from pathlib import Path

import gmpy2


ROOT = Path(__file__).resolve().parents[2]
PINS = {
    "problems/local/pi-digits.txt":
        "2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825",
    "work/ultrapi-resume/bbp_three_primary_epoch_20260813.md":
        "5b34ceb3aa2857b9227cce5ac7ae84cafbbac47d2c12adf889c37f11280d6fd7",
    "work/ultrapi-resume/bbp_odd_cofactor_short_orbit_experiment_20260813.md":
        "c648520d7c118ed63326afffce407a05ff2b05ca69efae36caeb20d1a06851c3",
    "work/ultrapi-resume/bbp_three_grid_full_phase_experiment_20260813.md":
        "f58f45259f19feb4f2e72f505199ed4476dfdec02bbdb82fbf6892bd6ec80b80",
    "work/ultrapi-resume/bbp_three_grid_full_phase_experiment_20260813_check.py":
        "502ecbb618c778c319bbbadb5e338281dded77138a569b98d3c0062f896e3458",
}

EXACT_E = (4, 6, 8)
SHADOW_E = (10, 12, 14)
ALL_E = EXACT_E + SHADOW_E
WIDTH = 50
RECORD_SHA256 = "2ef85d90315e487fb006ce6b39ca17731d8b20d6f0e129de0faf9422f9501f3d"

EXPECTED_ROWS = {
    (4, "pre-drop"): (49, 59, 11, 4, 9, 38,
        "795f6833c03628fe5364d6a4b8c436f21093a000768acd7f192593adb65d3a4f", (5, 5, 1)),
    (4, "first-drop"): (50, 60, 11, 3, 3, 23,
        "e801a211bb35884574a56fb6c6a45e05171e50fa4ecc791c6aaa53ce7471f056", (2, 3, 6)),
    (6, "pre-drop"): (454, 546, 93, 6, 81, 524,
        "0b8ff5fc08e2296b83be7af3ee3d356e45c66296e20054e64700c7b9359cf1b5", (24, 35, 34)),
    (6, "first-drop"): (455, 547, 93, 5, 27, 185,
        "7b3f10be60c9101b86264d0b7b928117dffd82615370bcbaecad22fc18eb24f4", (37, 33, 23)),
    (8, "pre-drop"): (4099, 4935, 837, 8, 729, 4898,
        "73cb3a7687ac43e28aaf79d343e1c82abb733f0c3c1c17acb558b9663c852100", (262, 293, 282)),
    (8, "first-drop"): (4100, 4936, 837, 7, 243, 914,
        "839c4655f26521f858d9ef57fd6299ac6e8ebadbb707299534444d478108a34d", (272, 272, 293)),
    (10, "pre-drop"): (36904, 44436, 7533, 10, 6561, 57386,
        "8d67b02749042f3478fd223e35de1cdfa829685429ce003bba288a217ec42a68", (2545, 2461, 2527)),
    (10, "first-drop"): (36905, 44438, 7534, 9, 2187, 18410,
        "149b6aff5b2a2e0bfc1acd2c08b22845f9c9e2392ca81f99cdb39fc823ba0943", (2477, 2566, 2491)),
    (12, "pre-drop"): (332149, 399947, 67799, 12, 59049, 175484,
        "9a85632c5bead273ff28f869cc50e11a36112e66bfe91ebd64823f77f6aff544", (22830, 22469, 22500)),
    (12, "first-drop"): (332150, 399948, 67799, 11, 19683, 175874,
        "273c09470cc99348b48270fc677aebd3c28a487b3447a4ed057db468137c655d", (22672, 22496, 22631)),
    (14, "pre-drop"): (2989354, 3599540, 610187, 14, 531441, 3364130,
        "89be41027b03ac08c5b54b7929e064b35f542ea190c0fcb8760f5b519e7a5fbf", (203860, 203175, 203152)),
    (14, "first-drop"): (2989355, 3599542, 610188, 13, 177147, 353021,
        "ef7150391927db873370439dccd9767cee9036048e8f51a27592cc1f69b14c0e", (203122, 203525, 203541)),
}

FRACTION_SHA256 = {
    (4, "pre-drop"): "5d587fa24114f1bb0babc1652053b227043167e948b4a685281df899ce28772b",
    (4, "first-drop"): "21ce353eea81858edc07c3cf7a280c5a39c1cc9edf60791f5c2c9cbe569a9aa7",
    (6, "pre-drop"): "b99709e38f3846bdc08de616cb2efc049f70fe4b9f9ab998ea4c82016ddf54fc",
    (6, "first-drop"): "4f833d093ed2b202042833908708c29734996f8978186982937fee3cccf65566",
    (8, "pre-drop"): "b9673780cbf68442704c8e3038b1edf2d42fa2dbfc369ab1c0e6f76e7be036ca",
    (8, "first-drop"): "04ebea7334a2307d3a1599db01fe1b36a13e17498313b7a4ce835eb50b9b7081",
}

# Frozen primary intervals.  The independent 448-bit recomputation of each
# decimal-centre Fourier magnitude must lie inside these outward intervals.
FOURIER_INTERVALS = {
    (4, "pre-drop", 1): ("6.246183516252936587e-2", "6.246183516252936588e-2"),
    (4, "pre-drop", 2): ("3.144541462089753489e-1", "3.144541462089753490e-1"),
    (4, "first-drop", 1): ("1.587970854961311666e-1", "1.587970854961311667e-1"),
    (4, "first-drop", 2): ("2.843151473068742656e-1", "2.843151473068742657e-1"),
    (6, "pre-drop", 1): ("4.573809420483817092e-2", "4.573809420483817093e-2"),
    (6, "pre-drop", 2): ("6.478613027406348734e-2", "6.478613027406348735e-2"),
    (6, "first-drop", 1): ("3.816107023454736587e-2", "3.816107023454736588e-2"),
    (6, "first-drop", 2): ("8.285184098993259941e-2", "8.285184098993259942e-2"),
    (8, "pre-drop", 1): ("2.713838313110788290e-2", "2.713838313110788291e-2"),
    (8, "pre-drop", 2): ("4.919569368392041313e-2", "4.919569368392041314e-2"),
    (8, "first-drop", 1): ("2.541966359715514603e-2", "2.541966359715514604e-2"),
    (8, "first-drop", 2): ("4.743544957612972536e-2", "4.743544957612972537e-2"),
    (10, "pre-drop", 1): ("9.721896079649570105e-3", "9.721896694753052303e-3"),
    (10, "pre-drop", 2): ("9.630868174766871042e-3", "9.630869404973835438e-3"),
    (10, "first-drop", 1): ("9.677988731089702469e-3", "9.677989346159851597e-3"),
    (10, "first-drop", 2): ("9.490597811005525052e-3", "9.490599041145823307e-3"),
    (12, "pre-drop", 1): ("3.738370299901889495e-3", "3.738370307495531020e-3"),
    (12, "pre-drop", 2): ("2.150900359986231833e-3", "2.150900375173514883e-3"),
    (12, "first-drop", 1): ("3.714558216389401252e-3", "3.714558223982997054e-3"),
    (12, "first-drop", 2): ("2.127232237671982159e-3", "2.127232252859173762e-3"),
    (14, "pre-drop", 1): ("8.812544463201868657e-4", "8.812544464139352130e-4"),
    (14, "pre-drop", 2): ("1.751827311403345359e-3", "1.751827311590842054e-3"),
    (14, "first-drop", 1): ("8.785408552902152745e-4", "8.785408553839635590e-4"),
    (14, "first-drop", 2): ("1.750255850680495026e-3", "1.750255850867991596e-3"),
}


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def v(integer: int, prime: int) -> int:
    if integer == 0:
        raise ValueError("zero valuation")
    answer = 0
    integer = abs(integer)
    while integer % prime == 0:
        integer //= prime
        answer += 1
    return answer


def coeff(k: int) -> Fraction:
    return Fraction(
        120 * k * k + 151 * k + 47,
        (2 * k + 1) * (4 * k + 3) * (8 * k + 1) * (8 * k + 5),
    )


def pole_coeff(k: int) -> Fraction:
    return (
        Fraction(4, 8 * k + 1)
        - Fraction(1, 2 * (2 * k + 1))
        - Fraction(1, 8 * k + 5)
        - Fraction(1, 2 * (4 * k + 3))
    )


def endpoint_rows(e: int) -> tuple[tuple[int, str, int], ...]:
    a = (3**e - 1) // 8
    return ((5 * a - 1, "pre-drop", e), (5 * a, "first-drop", e - 1))


def exact_upper(depth: int) -> int:
    # Establish the decimal logarithm by exact integer inequalities, not a
    # floating logarithm.  The initial estimate is corrected if necessary.
    guess = int(depth * math.log10(16))
    value = 1 << (4 * depth)
    while pow(10, guess + 1) <= value:
        guess += 1
    while pow(10, guess) > value:
        guess -= 1
    assert pow(10, guess) <= value < pow(10, guess + 1)
    return guess


def exact_small_sums() -> dict[tuple[int, str], Fraction]:
    targets = {
        depth: (e, stage)
        for e in EXACT_E
        for depth, stage, _ in endpoint_rows(e)
    }
    partial = Fraction()
    power = 1
    answer: dict[tuple[int, str], Fraction] = {}
    for k in range(max(targets) + 1):
        if k:
            power <<= 4
        a = coeff(k)
        assert a == pole_coeff(k) and 0 < a
        # The exact identity D-k^2*N =
        # 392k^4+873k^3+665k^2+194k+15 proves a(k)<1/k^2
        # for k>=1, which in turn proves the stated positive tail bound.
        if k:
            assert a < Fraction(1, k * k)
        partial += a / power
        if k in targets:
            key = targets[k]
            digest = hashlib.sha256(
                f"{partial.numerator}/{partial.denominator}".encode()
            ).hexdigest()
            assert digest == FRACTION_SHA256[key]
            answer[key] = partial
    return answer


def endpoint_units_mod_three() -> dict[tuple[int, str], int]:
    """Independent coefficient-polynomial 3-adic prefix computation."""
    top = max(ALL_E)
    modulus = 3**top
    targets = {
        depth: (e, stage, reduced)
        for e in ALL_E
        for depth, stage, reduced in endpoint_rows(e)
    }
    inv16 = pow(16, -1, modulus)
    inv16k = 1
    scaled = 0
    answer: dict[tuple[int, str], int] = {}
    for k in range(max(targets) + 1):
        numerator = 120 * k * k + 151 * k + 47
        denominator = (
            (2 * k + 1) * (4 * k + 3) * (8 * k + 1) * (8 * k + 5)
        )
        vn = v(numerator, 3)
        vd = v(denominator, 3)
        shift = top + vn - vd
        assert shift >= 0
        unit_num = numerator // (3**vn)
        unit_den = denominator // (3**vd)
        term = (
            unit_num
            * 3**shift
            * pow(unit_den, -1, modulus)
            * inv16k
        ) % modulus
        scaled = (scaled + term) % modulus
        if k in targets:
            e, stage, reduced = targets[k]
            divisor = 3 ** (top - reduced)
            assert scaled % divisor == 0
            beta = (scaled // divisor) % (3**reduced)
            assert beta % 3 == 2
            assert beta == EXPECTED_ROWS[e, stage][5]
            answer[e, stage] = beta
        inv16k = inv16k * inv16 % modulus
    return answer


def certified_pi_digits(places: int) -> str:
    # More guard precision than the primary run, with independent directed
    # endpoints.  Equality of the floors certifies the entire prefix.
    bits = math.ceil((places + 96) * math.log2(10))
    scale = gmpy2.mpz(10) ** places
    down = gmpy2.context(gmpy2.get_context(), precision=bits, round=gmpy2.RoundDown)
    up = gmpy2.context(gmpy2.get_context(), precision=bits, round=gmpy2.RoundUp)
    with down:
        lo = gmpy2.floor(gmpy2.const_pi() * scale)
    with up:
        hi = gmpy2.floor(gmpy2.const_pi() * scale)
    assert lo == hi
    text = str(lo)
    assert text[0] == "3" and len(text) == places + 1
    return text[1:]


def sixteen_prefix(digits: str) -> int:
    total = len(digits)
    q = int("3" + digits)
    divisor = 10 ** (total - WIDTH)
    lo = 16 * q // divisor
    hi = 16 * (q + 1) // divisor
    assert lo == hi
    return lo % (10**WIDTH)


def exact_residues(depth: int, value: Fraction) -> list[int]:
    modulus = value.denominator
    p = value.numerator
    upper = exact_upper(depth)
    result = []
    residue = ((pow(10, depth, modulus) - 16) * p) % modulus
    for _ in range(depth, upper + 1):
        result.append(residue)
        residue = (10 * residue + 144 * p) % modulus
    assert result[-1] == ((pow(10, upper, modulus) - 16) * p) % modulus
    return result


def decimal_residues(depth: int, digits: str, sixteen: int) -> list[int]:
    modulus = 10**WIDTH
    return [
        (int(digits[n:n + WIDTH]) - sixteen) % modulus
        for n in range(depth, exact_upper(depth) + 1)
    ]


def high_precision_fourier(residues: list[int], modulus: int, h: int) -> gmpy2.mpfr:
    context = gmpy2.context(
        gmpy2.get_context(), precision=448, round=gmpy2.RoundToNearest
    )
    with context:
        factor = 2 * h * gmpy2.const_pi()
        real = gmpy2.mpfr(0)
        imag = gmpy2.mpfr(0)
        for residue in residues:
            x = gmpy2.mpfr(gmpy2.mpq(residue, modulus))
            sine, cosine = gmpy2.sin_cos(factor * x)
            real += cosine
            imag += sine
        real /= len(residues)
        imag /= len(residues)
        return gmpy2.sqrt(real * real + imag * imag)


def analyze(
    e: int,
    stage: str,
    reduced: int,
    beta: int,
    residues: list[int],
    modulus: int,
    error: Fraction,
    record_hasher: "hashlib._Hash",
) -> dict[str, object]:
    depth = {s: m for m, s, _ in endpoint_rows(e)}[stage]
    upper = exact_upper(depth)
    count = upper - depth + 1
    expected = EXPECTED_ROWS[e, stage]
    assert (depth, upper, count, reduced, 3 ** (reduced - 2), beta) == expected[:6]
    assert len(residues) == count and len(set(residues)) == count

    # The exact dyadic denominator formula rules out true collisions because
    # every exponent in the row is smaller than its residual 2-height.
    assert upper < 4 * depth - v(depth + 1, 2)

    width = (modulus.bit_length() + 7) // 8
    stream = hashlib.sha256()
    for residue in residues:
        stream.update(residue.to_bytes(width, "big"))
    residue_digest = stream.hexdigest()
    assert residue_digest == expected[6]

    ordered = sorted(residues)
    gaps = [b - a for a, b in zip(ordered, ordered[1:])]
    gaps.append(modulus + ordered[0] - ordered[-1])
    gap_num = max(gaps)
    target_num, target_n = min(
        (min(r, modulus - r), depth + offset)
        for offset, r in enumerate(residues)
    )

    period = 3 ** (reduced - 2)
    primary_modulus = 3 * period
    lifted = (pow(10, depth, 3 * primary_modulus) - 16) % (3 * primary_modulus)
    assert lifted % 3 == 0
    quotient = lifted // 3
    visits = [0] * period
    ternary = [0, 0, 0]
    min_boundary = 3 * modulus
    for residue in residues:
        delta = beta * quotient % primary_modulus
        assert delta % 3 == 2
        j = (delta - 2) // 3
        visits[j] += 1
        phase_bin = 3 * residue // modulus
        grid_bin = 3 * j // period
        ternary[(phase_bin - grid_bin) % 3] += 1
        coordinate = 3 * residue
        min_boundary = min(
            min_boundary,
            *(abs(coordinate - boundary * modulus) for boundary in range(4)),
        )
        quotient = (10 * quotient + 48) % primary_modulus
    assert min(visits) > 0 and max(visits) - min(visits) <= 1
    assert tuple(ternary) == expected[7]
    if error:
        assert min_boundary * error.denominator > 3 * modulus * error.numerator

    c0, c1, c2 = ternary
    rho_sq = Fraction(
        c0*c0 + c1*c1 + c2*c2 - c0*c1 - c1*c2 - c2*c0,
        count*count,
    )

    for h in (1, 2):
        magnitude = high_precision_fourier(residues, modulus, h)
        lo_s, hi_s = FOURIER_INTERVALS[e, stage, h]
        context = gmpy2.context(gmpy2.get_context(), precision=448)
        with context:
            lo = gmpy2.mpfr(lo_s)
            hi = gmpy2.mpfr(hi_s)
        assert lo < magnitude < hi

    record = "|".join(str(item) for item in (
        e, stage, depth, upper, count, reduced, period, beta, modulus,
        error.numerator, error.denominator, target_num, target_n, gap_num,
        min_boundary, *ternary, rho_sq.numerator, rho_sq.denominator,
        residue_digest,
    ))
    record_hasher.update((record + "\n").encode())
    return {
        "key": (e, stage),
        "count": count,
        "gap": Fraction(gap_num, modulus),
        "target": Fraction(target_num, modulus),
        "error": error,
        "rho_sq": rho_sq,
    }


def main() -> None:
    if hasattr(sys, "set_int_max_str_digits"):
        sys.set_int_max_str_digits(0)

    for relative, expected in PINS.items():
        assert sha(ROOT / relative) == expected, relative

    source = (ROOT / "problems/local/pi-digits.txt").read_text()
    assert "V1 (CANONICAL" in source and "Status: OPEN" in source
    report_text = (ROOT / "work/ultrapi-resume/bbp_three_grid_full_phase_experiment_20260813.md").read_text()
    assert "asserts_v1=false" in report_text
    assert "`conjecture` (endpoint gap law)" in report_text

    exact = exact_small_sums()
    betas = endpoint_units_mod_three()
    for e in EXACT_E:
        for _, stage, reduced in endpoint_rows(e):
            value = exact[e, stage]
            assert v(value.denominator, 3) == reduced
            cofactor = value.denominator // 3**reduced
            direct_beta = value.numerator * pow(cofactor, -1, 3**reduced) % 3**reduced
            assert direct_beta == betas[e, stage]

    maximum_upper = max(
        exact_upper(depth)
        for e in SHADOW_E
        for depth, _, _ in endpoint_rows(e)
    )
    digits = certified_pi_digits(maximum_upper + WIDTH + 10)
    sixteen = sixteen_prefix(digits)

    hasher = hashlib.sha256()
    rows = []
    for e in ALL_E:
        for depth, stage, reduced in endpoint_rows(e):
            if e in EXACT_E:
                value = exact[e, stage]
                residues = exact_residues(depth, value)
                modulus = value.denominator
                error = Fraction()
            else:
                residues = decimal_residues(depth, digits, sixteen)
                modulus = 10**WIDTH
                error = Fraction(1, modulus) + Fraction(1, 15 * (depth + 1)**2)
            rows.append(analyze(
                e, stage, reduced, betas[e, stage], residues, modulus, error, hasher
            ))

    assert hasher.hexdigest() == RECORD_SHA256

    # Recheck the two finite summary ranges using outward error transfers.
    for row in rows:
        gap_lo = max(Fraction(), row["gap"] - 2 * row["error"])
        gap_hi = min(Fraction(1), row["gap"] + 2 * row["error"])
        count = row["count"]
        ratio_lo = float(gap_lo) * count / math.log(count)
        ratio_hi = float(gap_hi) * count / math.log(count)
        assert 0.899 < ratio_lo <= ratio_hi < 1.084
        if row["key"][0] >= 6:
            scaled = math.sqrt(float(row["rho_sq"] * count))
            assert 0.526 < scaled < 1.331

    target = {row["key"]: row["target"] for row in rows}
    assert target[8, "pre-drop"] < target[6, "pre-drop"]
    assert target[10, "pre-drop"] > target[8, "pre-drop"]
    assert target[12, "pre-drop"] < target[10, "pre-drop"]
    assert target[14, "pre-drop"] < target[12, "pre-drop"]

    print("claim_status=experiment")
    print(f"source_pins={len(PINS)}")
    print(f"exact_fraction_rows={2 * len(EXACT_E)}")
    print(f"directed_shadow_rows={2 * len(SHADOW_E)}")
    print(f"complete_grid_rows={len(rows)}")
    print(f"fourier_recomputations={2 * len(rows)}")
    print(f"exact_record_sha256={hasher.hexdigest()}")
    print("gap_conjecture_asserted=false")
    print("fourier_decay_asserted=false")
    print("fixed_sixteen_return_asserted=false")
    print("canonical_v1_asserted=false")
    print("status=PASS")


if __name__ == "__main__":
    main()
