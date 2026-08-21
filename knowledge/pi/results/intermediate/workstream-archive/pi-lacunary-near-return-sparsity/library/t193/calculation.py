#!/usr/bin/env python3
"""Exact finite model calculation; it is not evidence about pi."""
from math import comb

N = 10**16
m = N.bit_length()  # Do not use this as the screen depth.
depth = len(str(N)) - 1
assert depth == 16
screen = depth // 4
assert screen == 4

# The rational-diagonal model has binom(2n,n) mod 2 = 1 only at n = 0.
# Hence its N overlapping length-four blocks have multiplicities 1 and N - 1.
assert comb(0, 0) % 2 == 1
for n in range(1, 1000):
    assert comb(2 * n, n) % 2 == 0
energy = 1 + (N - 1) ** 2
benchmark = N**2 // 10**screen
print(f"N={N}")
print(f"m=floor((1/4)log_10(N))={screen}")
print(f"rational_diagonal_energy={energy}")
print(f"decimal_uniform_benchmark={benchmark}")
print(f"energy_exceeds_benchmark={energy > benchmark}")
