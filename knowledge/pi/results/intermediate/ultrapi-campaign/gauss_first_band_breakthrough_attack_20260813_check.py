#!/usr/bin/env python3
"""Exact finite replay for gauss_first_band_breakthrough_attack_20260813.md.

All bounded output is an experiment.  The script does not claim an
asymptotic estimate or any result about the decimal expansion of pi.
"""

from __future__ import annotations

from math import gcd, isqrt, log
from pathlib import Path


LIMIT = 3_000
CRT_LIMIT = 420


def scan_artifact_hygiene() -> int:
    checker_path = Path(__file__)
    report_path = checker_path.with_name(
        checker_path.name.removesuffix("_check.py") + ".md"
    )
    checked_bytes = 0
    for path in (report_path, checker_path):
        payload = path.read_bytes()
        bad = [
            (offset, value)
            for offset, value in enumerate(payload)
            if (value < 32 and value not in (9, 10)) or value == 127
        ]
        assert not bad, f"unexpected C0/DEL bytes in {path}: {bad[:8]}"
        checked_bytes += len(payload)
    return checked_bytes


def prime_table(limit: int) -> list[bool]:
    table = bytearray(b"\x01") * (limit + 1)
    table[0:2] = b"\x00\x00"
    for d in range(2, isqrt(limit) + 1):
        if table[d]:
            table[d * d : limit + 1 : d] = b"\x00" * (
                (limit - d * d) // d + 1
            )
    return [bool(x) for x in table]


def central_coefficients(limit: int) -> list[int]:
    # A_m = [X^m](X^2 + 2X + 2)^m.
    values = [1, 2]
    for m in range(1, limit):
        numerator = 2 * (2 * m + 1) * values[m] + 4 * m * values[m - 1]
        assert numerator % (m + 1) == 0
        values.append(numerator // (m + 1))
    return values[: limit + 1]


def first_band_from_primes(
    n: int, primes: list[int], a: list[int]
) -> set[int]:
    return {p for p in primes if 2 * p > n and p < n and a[n] % p == 0}


def first_band_from_two_rays(
    n: int, is_prime: list[bool], a: list[int]
) -> set[int]:
    selected: set[int] = set()
    for r in range(1, (n - 1) // 3 + 1):
        p_direct = n - r
        if is_prime[p_direct] and a[r] % p_direct == 0:
            selected.add(p_direct)

        numerator = n + 1 + r
        if numerator % 2 == 0:
            p_reflected = numerator // 2
            if is_prime[p_reflected] and a[r] % p_reflected == 0:
                selected.add(p_reflected)
    return selected


def replay_first_band() -> tuple[int, int, tuple[int, list[int]]]:
    is_prime = prime_table(LIMIT)
    primes = [p for p in range(3, LIMIT + 1, 2) if is_prime[p]]
    a = central_coefficients(LIMIT)
    tested_pairs = 0
    selected_pairs = 0
    maximizer = (0, [])

    for n in range(4, LIMIT + 1):
        direct = first_band_from_primes(n, primes, a)
        rays = first_band_from_two_rays(n, is_prime, a)
        assert direct == rays
        if len(direct) > len(maximizer[1]):
            maximizer = (n, sorted(direct))

        for p in primes:
            if not (2 * p > n and p < n):
                continue
            tested_pairs += 1
            t = n - p
            # One-digit Lucas and first-block reflection, checked against
            # independently generated exact integers.
            assert (a[n] % p == 0) == (a[t] % p == 0)
            r = min(t, p - 1 - t)
            assert 0 <= r <= (p - 1) // 2
            assert (a[t] % p == 0) == (a[r] % p == 0)
            if a[n] % p == 0:
                selected_pairs += 1
                assert 3 * r <= n - 1
                assert p == n - r or 2 * p == n + 1 + r

    return tested_pairs, selected_pairs, maximizer


def replay_crt_identity() -> int:
    is_prime = prime_table(CRT_LIMIT)
    primes = [p for p in range(3, CRT_LIMIT + 1, 2) if is_prime[p]]
    a = central_coefficients(CRT_LIMIT)
    instances = 0

    for n in range(4, CRT_LIMIT + 1):
        band = [p for p in primes if 2 * p > n and p < n]
        primorial = 1
        for p in band:
            primorial *= p
        package = sum((primorial // p) * a[n - p] for p in band)
        selected_product = 1
        for p in band:
            if a[n - p] % p == 0:
                selected_product *= p
            assert (package % p == 0) == (a[n - p] % p == 0)
        assert gcd(primorial, package) == selected_product
        instances += 1

    return instances


def replay_endpoint_product() -> int:
    is_prime = prime_table(LIMIT)
    a = central_coefficients(LIMIT)
    instances = 0

    for n in range(20, LIMIT + 1, 11):
        cutoff = min(isqrt(n), (n - 1) // 3)
        endpoint_product = 1
        for r in range(1, cutoff + 1):
            candidates: set[int] = set()
            p_direct = n - r
            if is_prime[p_direct] and a[r] % p_direct == 0:
                candidates.add(p_direct)
            numerator = n + 1 + r
            if numerator % 2 == 0:
                p_reflected = numerator // 2
                if is_prime[p_reflected] and a[r] % p_reflected == 0:
                    candidates.add(p_reflected)
            local_product = 1
            for p in candidates:
                local_product *= p
            assert a[r] % local_product == 0
            endpoint_product *= local_product
        bound = 1
        for r in range(1, cutoff + 1):
            bound *= a[r]
        assert bound % endpoint_product == 0
        instances += 1

    return instances


def replay_abstract_obstruction() -> tuple[int, list[tuple[int, int, float]]]:
    # The construction in the report uses N_j = 10^j.  This finite replay
    # checks three rows; the PNT supplies the rigorous asymptotic weight.
    depths = [1_000, 10_000, 100_000]
    is_prime = prime_table(max(depths))
    owner: dict[int, tuple[int, int]] = {}
    rows: list[tuple[int, int, float]] = []

    for n in depths:
        hits = []
        weight = 0.0
        for p in range(3 * n // 4 + 1, 4 * n // 5 + 1):
            if not is_prime[p]:
                continue
            assert p not in owner  # the prime intervals are disjoint
            r = n - p
            reflected = p - 1 - r
            assert 1 < r < reflected < p - 1
            assert reflected - r > 1
            assert 2 * r <= p - 1
            owner[p] = (r, reflected)
            hits.append(p)
            weight += log(p)
        rows.append((n, len(hits), weight / n))

    return len(owner), rows


def main() -> None:
    checked_bytes = scan_artifact_hygiene()
    tested, selected, maximizer = replay_first_band()
    crt_instances = replay_crt_identity()
    endpoint_instances = replay_endpoint_product()
    abstract_primes, abstract_rows = replay_abstract_obstruction()
    print(
        "PASS: exact Lucas/reflection/two-ray first-band encoding on "
        f"{tested} prime-depth pairs through n={LIMIT}, with {selected} selected pairs"
    )
    print(
        "PASS: CRT gcd package on "
        f"{crt_instances} depths and small-r product bound on {endpoint_instances} depths"
    )
    print(
        "PASS: artifact hygiene C0=0 (excluding LF/TAB) across "
        f"{checked_bytes} bytes"
    )
    print(
        "EXPERIMENT: largest first-band collision multiplicity through "
        f"n={LIMIT} is {len(maximizer[1])} at n={maximizer[0]}, primes={maximizer[1]}"
    )
    print(
        "EXPERIMENT: abstract symmetric one-minimal-zero construction used "
        f"{abstract_primes} distinct primes; rows (N, hits, weighted_ratio)={abstract_rows}"
    )
    print(
        "BOUNDARY: finite replays prove no little-o estimate, no exceptional-gcd "
        "bound, and no decimal-cylinder hit"
    )


if __name__ == "__main__":
    main()
