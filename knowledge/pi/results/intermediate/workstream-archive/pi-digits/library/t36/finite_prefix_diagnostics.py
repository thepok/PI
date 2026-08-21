#!/usr/bin/env python3
"""Exact integer diagnostics for the T36 cross-base prefix relations."""

from hashlib import sha256
from math import gcd
from pathlib import Path

CANONICAL_SHA256 = "2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825"


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def carry(n: int, m: int, a: int, d: int) -> int:
    return 10**m * a - 16**n * d


def compatible(n: int, m: int, a: int, d: int) -> bool:
    kappa = carry(n, m, a, d)
    return -10**m < kappa < 16**n


def overlap_numerator(n: int, m: int, a: int, d: int) -> int:
    return min(10**m * (a + 1), 16**n * (d + 1)) - max(
        10**m * a, 16**n * d
    )


def decimal_digits(d: int, m: int) -> tuple[int, ...]:
    return tuple(int(ch) for ch in f"{d:0{m}d}")


def avoids(digits: tuple[int, ...], word: tuple[int, ...]) -> bool:
    k = len(word)
    return k == 0 or all(digits[i : i + k] != word for i in range(len(digits) - k + 1))


def compatible_states(n: int, m: int, word: tuple[int, ...]):
    scale16 = 16**n
    scale10 = 10**m
    for a in range(scale16):
        first_d = scale10 * a // scale16
        last_d = (scale10 * (a + 1) - 1) // scale16
        for d in range(first_d, last_d + 1):
            if avoids(decimal_digits(d, m), word):
                yield a, d, carry(n, m, a, d)


def synchronous_children(n: int, m: int, a: int, d: int, word: tuple[int, ...]):
    for h in range(16):
        for e in range(10):
            child_a = 16 * a + h
            child_d = 10 * d + e
            if compatible(n + 1, m + 1, child_a, child_d) and avoids(
                decimal_digits(child_d, m + 1), word
            ):
                old = carry(n, m, a, d)
                new = carry(n + 1, m + 1, child_a, child_d)
                require(
                    new == 160 * old + 10 ** (m + 1) * h - 16 ** (n + 1) * e,
                    "synchronous carry transition failed",
                )
                yield h, e, new


def check_identities() -> None:
    for n, m in ((1, 1), (1, 2), (2, 1), (2, 2)):
        for a in range(16**n):
            for d in range(10**m):
                kappa = carry(n, m, a, d)
                overlap = overlap_numerator(n, m, a, d)
                require(
                    compatible(n, m, a, d) == (overlap > 0),
                    "compatibility test failed",
                )
                require(
                    overlap == min(kappa + 10**m, 16**n) - max(kappa, 0),
                    "signed overlap numerator identity failed",
                )


def main() -> None:
    source_bytes = Path("pi-digits.txt").read_bytes()
    source_hash = sha256(source_bytes).hexdigest()
    require(source_hash == CANONICAL_SHA256, "canonical source hash mismatch")
    print(f"canonical_sha256={source_hash}")

    check_identities()
    print("identity_checks=PASS levels=(1,1),(1,2),(2,1),(2,2)")

    word = (2,)
    for n, m in ((1, 1), (1, 2), (2, 1), (2, 2), (3, 3)):
        states = list(compatible_states(n, m, word))
        carries = {state[2] for state in states}
        print(
            f"tau_word=2 level=({n},{m}) states={len(states)} "
            f"distinct_carries={len(carries)} min_carry={min(carries)} max_carry={max(carries)}"
        )

    children = list(synchronous_children(1, 1, 0, 0, word))
    rendered = " ".join(f"(h={h:X},e={e},carry={new})" for h, e, new in children)
    print(f"children parent=(n=1,m=1,A=0,D=0), w=2: {rendered}")

    for n in range(1, 7):
        a = 16**n - 1
        d = 10**n - 1
        kappa = carry(n, n, a, d)
        divisor = gcd(10**n, 16**n)
        reduced = kappa // divisor
        require(compatible(n, n, a, d), "top state is not compatible")
        require(avoids(decimal_digits(d, n), word), "top state does not avoid word")
        require(divisor == 2**n, "gcd identity failed")
        require(reduced == 8**n - 5**n, "reduced carry identity failed")
        print(
            f"top_state n={n} A={a} D={d} carry={kappa} "
            f"gcd={divisor} reduced_carry={reduced}"
        )

    print("classification=diagnostic_only; no inference about pi, V1, or V3")


if __name__ == "__main__":
    main()
