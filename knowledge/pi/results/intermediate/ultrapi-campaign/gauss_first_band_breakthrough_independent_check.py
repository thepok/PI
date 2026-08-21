#!/usr/bin/env python3
"""Independent finite audit for the Gauss first-band two-ray report.

Every bounded scan printed here is an experiment.  The checker validates exact
finite identities and artifact hygiene; it proves no asymptotic estimate and no
statement about the decimal digits of pi.
"""

from __future__ import annotations

from fractions import Fraction
from hashlib import sha256
from math import comb, gcd, isqrt, log
from pathlib import Path
import re
import subprocess
import sys
from urllib.parse import unquote


ROOT = Path(__file__).resolve().parents[2]
REPORT = Path(__file__).with_name(
    "gauss_first_band_breakthrough_independent_audit_20260813.md"
)
PRIMARY_REPORT = Path(__file__).with_name(
    "gauss_first_band_breakthrough_attack_20260813.md"
)
PRIMARY_CHECKER = Path(__file__).with_name(
    "gauss_first_band_breakthrough_attack_20260813_check.py"
)
TARGET = ROOT / "problems/local/pi-digits.txt"

EXPECTED_TARGET_SHA = (
    "2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825"
)
EXPECTED_PRIMARY_REPORT_SHA = (
    "cba7b6115efc11de85b61634e1109430b9a215eda335cd0bea1cd2345a517e23"
)
EXPECTED_PRIMARY_CHECKER_SHA = (
    "ec046cf117145b245cb20ea6822f4a757b6eed52c54e9ac3e278f51333a73ff7"
)
SOURCE_PINS = {
    "https://cs.uwaterloo.ca/journals/JIS/VOL9/Noe/noe35.pdf":
        "971d271f35eb4400ac223f7e3536cdc7ac28e14393caa03c1204bc16d30a094c",
    "https://arxiv.org/pdf/2411.03681v2":
        "f4c604453c2b81a48dd3ee56aabab0ef3a6a78b0d14a21a2b323bd4818d6db42",
    "https://arxiv.org/pdf/math/0512239v2":
        "5e9c4f6345a7171b112d16b6eb12b7388334c9123e8d39058d22080e4f031b9d",
    "https://arxiv.org/pdf/1008.3887v13":
        "a4540dc374dc9ef0fcad856c9a69c247d345fec94127ac8a6f09353f18995eb1",
}

TWO_RAY_LIMIT = 1_600
FINITE_FIELD_LIMIT = 251
CRT_LIMIT = 460
COUNTERMODEL_DEPTHS = (1_000, 10_000, 100_000, 1_000_000)


def digest(path: Path) -> str:
    return sha256(path.read_bytes()).hexdigest()


def prime_table(limit: int) -> bytearray:
    table = bytearray(b"\x01") * (limit + 1)
    table[0:2] = b"\x00\x00"
    for divisor in range(2, isqrt(limit) + 1):
        if table[divisor]:
            start = divisor * divisor
            table[start : limit + 1 : divisor] = b"\x00" * (
                (limit - start) // divisor + 1
            )
    return table


def coefficient_formula(n: int) -> int:
    return sum(
        comb(n, 2 * k) * comb(2 * k, k) * 2 ** (n - k)
        for k in range(n // 2 + 1)
    )


def coefficients(limit: int) -> list[int]:
    values = [1, 2]
    for n in range(1, limit):
        numerator = 2 * (2 * n + 1) * values[n] + 4 * n * values[n - 1]
        assert numerator % (n + 1) == 0
        values.append(numerator // (n + 1))
    return values[: limit + 1]


def artifact_audit() -> tuple[int, int]:
    assert digest(TARGET) == EXPECTED_TARGET_SHA
    assert digest(PRIMARY_REPORT) == EXPECTED_PRIMARY_REPORT_SHA
    assert digest(PRIMARY_CHECKER) == EXPECTED_PRIMARY_CHECKER_SHA

    paths = (PRIMARY_REPORT, PRIMARY_CHECKER, REPORT, Path(__file__))
    checked_bytes = 0
    checked_links = 0
    for path in paths:
        payload = path.read_bytes()
        text = payload.decode("utf-8")
        assert payload.endswith(b"\n"), f"missing final newline: {path}"
        bad = [
            (offset, value)
            for offset, value in enumerate(payload)
            if (value < 32 and value not in (9, 10)) or value == 127
        ]
        assert not bad, f"unexpected C0/DEL bytes in {path}: {bad[:8]}"
        for line_number, line in enumerate(text.splitlines(), 1):
            assert line == line.rstrip(" \t"), (
                f"trailing whitespace at {path}:{line_number}"
            )
        checked_bytes += len(payload)

        if path.suffix != ".md":
            continue
        for match in re.finditer(r"\]\(([^)]+)\)", text):
            href = match.group(1).strip()
            if re.match(r"^[a-zA-Z][a-zA-Z0-9+.-]*:", href):
                continue
            local_part = unquote(href.split("#", 1)[0])
            if not local_part:
                continue
            # A TeX fragment such as ``[X^m](X^2+...)`` also matches the
            # lightweight Markdown regex.  Only the artifact file extensions
            # used by these two reports are local-link candidates.
            if not local_part.endswith((".md", ".py", ".txt")):
                continue
            linked = (path.parent / local_part).resolve()
            assert linked.exists(), f"broken local link {href!r} in {path}"
            checked_links += 1

    primary_text = PRIMARY_REPORT.read_text(encoding="utf-8")
    audit_text = REPORT.read_text(encoding="utf-8")
    for url, pin in SOURCE_PINS.items():
        assert url in primary_text
        assert pin in primary_text
        assert url in audit_text
        assert pin in audit_text

    for text in (primary_text.lower(), audit_text.lower()):
        assert "canonical v1 remains a `conjecture`" in text
        false_positive_claims = (
            "canonical v1 is proved",
            "canonical v1 is a `verified resolution`",
            "this proves every finite decimal",
            "we have proved every finite decimal",
        )
        assert not any(phrase in text for phrase in false_positive_claims)

    return checked_bytes, checked_links


def multiply_by_quadratic(poly: list[int], modulus: int) -> list[int]:
    result = [0] * (len(poly) + 2)
    for index, value in enumerate(poly):
        result[index] = (result[index] + value) % modulus
        result[index + 1] = (result[index + 1] - 2 * value) % modulus
        result[index + 2] = (result[index + 2] - value) % modulus
    return result


def replay_finite_field_identities(
    is_prime: bytearray, values: list[int]
) -> tuple[int, int, int]:
    for n in range(81):
        assert values[n] == coefficient_formula(n)

    polynomial_coefficients = 0
    lucas_pairs = 0
    reflection_pairs = 0
    for p in range(3, FINITE_FIELD_LIMIT + 1, 2):
        if not is_prime[p]:
            continue
        q = (p - 1) // 2
        polynomial = [1]
        for _ in range(q):
            polynomial = multiply_by_quadratic(polynomial, p)
        inverse_two = pow(2, -1, p)
        normalized = [
            values[s] % p * pow(inverse_two, s, p) % p for s in range(p)
        ]
        assert polynomial == normalized
        assert sum(value != 0 for value in polynomial) >= q + 1
        polynomial_coefficients += p

        for t in range(p):
            assert values[p + t] % p == 2 * values[t] % p
            lucas_pairs += 1

        zeros = []
        for s in range(q + 1):
            scalar = pow(-4, q - s, p)
            assert values[p - 1 - s] % p == scalar * values[s] % p
            assert (values[p - 1 - s] % p == 0) == (values[s] % p == 0)
            reflection_pairs += 1
        for s in range(p):
            if values[s] % p == 0:
                zeros.append(s)
        assert all(right - left > 1 for left, right in zip(zeros, zeros[1:]))

    return polynomial_coefficients, lucas_pairs, reflection_pairs


def first_band(n: int, is_prime: bytearray, values: list[int]) -> set[int]:
    return {
        p
        for p in range(n // 2 + 1, n)
        if 2 * p > n and is_prime[p] and values[n] % p == 0
    }


def ray_maps(
    n: int, is_prime: bytearray, values: list[int]
) -> tuple[dict[int, int], dict[int, int]]:
    direct: dict[int, int] = {}
    reflected: dict[int, int] = {}
    for r in range(1, (n - 1) // 3 + 1):
        p = n - r
        if is_prime[p] and values[r] % p == 0:
            assert p not in direct
            direct[p] = r

        numerator = n + 1 + r
        if numerator % 2 == 0:
            p = numerator // 2
            if is_prime[p] and p % 2 == 1 and values[r] % p == 0:
                assert p not in reflected
                reflected[p] = r
    return direct, reflected


def endpoint_class(r: int, n: int, delta: Fraction) -> str:
    if r * delta.denominator < delta.numerator * n:
        return "low"
    high_numerator = delta.denominator - 3 * delta.numerator
    if r * 3 * delta.denominator > high_numerator * n:
        return "high"
    return "core"


def check_endpoint_interval(
    n: int, p: int, r: int, delta: Fraction, endpoint: str
) -> None:
    is_direct = p == n - r
    is_reflected = 2 * p == n + 1 + r
    assert is_direct or is_reflected
    if endpoint == "low" and is_direct:
        assert p > (1 - delta) * n and p < n
    elif endpoint == "low":
        assert p > Fraction(n, 2)
        assert p < Fraction(1 + delta, 2) * n + 1
    elif endpoint == "high" and is_direct:
        assert p >= Fraction(2 * n + 1, 3)
        assert p < (Fraction(2, 3) + delta) * n
    elif endpoint == "high":
        assert p > (Fraction(2, 3) - delta / 2) * n
        assert p <= Fraction(2 * n + 1, 3)
    else:
        raise AssertionError("endpoint interval called for core index")


def replay_two_rays_and_endpoints(
    is_prime: bytearray, values: list[int]
) -> tuple[int, int, list[tuple[int, int, int]], int]:
    selected_pairs = 0
    merger_rows: list[tuple[int, int, int]] = []
    endpoint_partitions = 0
    deltas = (Fraction(1, 20), Fraction(1, 12), Fraction(1, 8))

    for n in range(4, TWO_RAY_LIMIT + 1):
        actual = first_band(n, is_prime, values)
        direct, reflected = ray_maps(n, is_prime, values)
        assert actual == set(direct) | set(reflected)
        selected_pairs += len(actual)

        for p in set(direct) & set(reflected):
            r_direct = direct[p]
            r_reflected = reflected[p]
            assert r_direct == r_reflected
            r = r_direct
            assert n == 3 * r + 1
            assert p == 2 * r + 1
            assert n - p == r == (p - 1) // 2
            merger_rows.append((n, r, p))

        for p in actual:
            t = n - p
            r = min(t, p - 1 - t)
            assert 3 * r <= n - 1
            assert values[r] % p == 0
            assert p == n - r or 2 * p == n + 1 + r

        count = len(actual)
        weight = sum(log(p) for p in actual)
        if count:
            assert count * log(n / 2) <= weight + 1e-12
            assert weight <= count * log(n) + 1e-12

        for delta in deltas:
            core: set[int] = set()
            endpoints: set[int] = set()
            for p in actual:
                t = n - p
                r = min(t, p - 1 - t)
                location = endpoint_class(r, n, delta)
                if location == "core":
                    core.add(p)
                else:
                    endpoints.add(p)
                    check_endpoint_interval(n, p, r, delta, location)
            assert core.isdisjoint(endpoints)
            assert actual == core | endpoints
            endpoint_partitions += 1

    expected_mergers = {
        (46, 15, 31),
        (334, 111, 223),
        (574, 191, 383),
        (718, 239, 479),
    }
    assert expected_mergers <= set(merger_rows)
    return TWO_RAY_LIMIT - 3, selected_pairs, merger_rows, endpoint_partitions


def replay_crt(is_prime: bytearray, values: list[int]) -> int:
    instances = 0
    for n in range(4, CRT_LIMIT + 1):
        band = [p for p in range(3, n, 2) if 2 * p > n and is_prime[p]]
        primorial = 1
        for p in band:
            primorial *= p
        package = sum((primorial // p) * values[n - p] for p in band)
        selected_product = 1
        for p in band:
            selected = values[n - p] % p == 0
            assert (package % p == 0) == selected
            if selected:
                selected_product *= p
        assert gcd(primorial, package) == selected_product
        instances += 1
    return instances


def replay_countermodel(
    is_prime: bytearray,
) -> tuple[int, list[tuple[int, int, float]]]:
    assert Fraction(4, 5) - Fraction(3, 4) == Fraction(1, 20)
    owner: dict[int, tuple[int, int, int]] = {}
    rows: list[tuple[int, int, float]] = []

    previous_upper = 0
    for n in COUNTERMODEL_DEPTHS:
        lower = 3 * n // 4
        upper = 4 * n // 5
        assert previous_upper < lower
        previous_upper = upper
        weight = 0.0
        hits = 0
        for p in range(lower + 1, upper):
            if not is_prime[p]:
                continue
            assert p not in owner
            z = n - p
            reflected = p - 1 - z
            q = (p - 1) // 2
            assert 0 < z < q < reflected < p - 1
            assert reflected - z > n / 4 - 1
            assert reflected - z > 1
            assert p == n - z
            owner[p] = (n, z, reflected)
            hits += 1
            weight += log(p)
        rows.append((n, hits, weight / n))

    for _, z, reflected in owner.values():
        assert reflected - z > 1
    return len(owner), rows


def run_primary_checker() -> None:
    result = subprocess.run(
        [sys.executable, str(PRIMARY_CHECKER)],
        cwd=ROOT,
        check=True,
        capture_output=True,
        text=True,
    )
    assert "PASS: exact Lucas/reflection/two-ray" in result.stdout
    assert "BOUNDARY:" in result.stdout


def main() -> None:
    checked_bytes, checked_links = artifact_audit()
    max_prime = max(COUNTERMODEL_DEPTHS[-1], TWO_RAY_LIMIT, 2 * FINITE_FIELD_LIMIT)
    is_prime = prime_table(max_prime)
    values = coefficients(max(TWO_RAY_LIMIT, 2 * FINITE_FIELD_LIMIT))

    polynomial_coefficients, lucas_pairs, reflection_pairs = (
        replay_finite_field_identities(is_prime, values)
    )
    depths, selected, mergers, endpoint_partitions = replay_two_rays_and_endpoints(
        is_prime, values
    )
    crt_instances = replay_crt(is_prime, values)
    model_primes, model_rows = replay_countermodel(is_prime)
    run_primary_checker()

    hashes = {
        path.name: digest(path)
        for path in (PRIMARY_REPORT, PRIMARY_CHECKER, REPORT, Path(__file__))
    }
    print(
        "PASS: finite-field coefficient identity/reflection on "
        f"{polynomial_coefficients} coefficients, {lucas_pairs} Lucas pairs, "
        f"and {reflection_pairs} reflected pairs"
    )
    print(
        "PASS: exact two-ray union on "
        f"{depths} depths with {selected} selected pairs; "
        f"selected merger rows={mergers}"
    )
    print(
        "PASS: exact endpoint partitions on "
        f"{endpoint_partitions} (depth, delta) pairs and CRT gcd on "
        f"{crt_instances} depths"
    )
    print(
        "PASS: target/source pins, primary replay, links, UTF-8, C0=0, "
        f"and whitespace across {checked_bytes} bytes and {checked_links} local links"
    )
    print(
        "EXPERIMENT: abstract one-minimal-zero model used "
        f"{model_primes} primes; rows (N, hits, weighted_ratio)={model_rows}"
    )
    print(f"HASHES: {hashes}")
    print(
        "BOUNDARY: no little-o first-band estimate, exceptional-gcd bound, "
        "decimal-cylinder hit, candidate resolution, or verified resolution is proved"
    )


if __name__ == "__main__":
    main()
