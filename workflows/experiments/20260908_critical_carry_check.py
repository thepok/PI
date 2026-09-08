#!/usr/bin/env python3
"""Finite exact BBP critical-horizon checks; no infinite digit claim.

Independent direct sums and the forced recurrence are compared. No pi
digits, floating-point pi, or external runtime files are inputs.
"""

from fractions import Fraction as F


def coefficient(j):
    return F(4, 8*j+1) - F(2, 8*j+4) - F(1, 8*j+5) - F(1, 8*j+6)


def main():
    last_start, horizon_cap = 150, 100
    cutoff = last_start + horizon_cap
    rho = F(5, 8)
    r = [coefficient(j) for j in range(cutoff + 2)]
    forcing = [rho**j * r[j] for j in range(cutoff + 1)]
    partial, direct = F(0), []
    for j in range(cutoff + 1):
        partial += r[j] / 16**j
        direct.append(partial)
    heads = [F(47, 15)]
    for j in range(1, cutoff + 1):
        heads.append(10 * heads[-1] + forcing[j])
    assert r[0] == heads[0]
    assert all(heads[j] == 10**j * direct[j] for j in range(cutoff + 1))
    assert all(0 < r[j+1] < r[j] for j in range(cutoff + 1))
    assert all(0 < forcing[j] < 1 for j in range(1, cutoff + 1))
    observed = {}
    for n in range(1, last_start + 1):
        accumulated = F(0)
        for length in range(1, horizon_cap + 1):
            previous = accumulated
            accumulated = 10 * accumulated + forcing[n + length]
            if accumulated >= 1:
                break
        else:
            raise AssertionError("finite horizon cap exhausted")
        assert previous < 1 <= accumulated < 11
        m = n + length
        assert accumulated == 10**m * (direct[m] - direct[n])
        scale = 10**length * rho**n * r[n+1]
        assert scale / 16 <= accumulated <= scale / 15
        whole_n, whole_m = heads[n] // 1, heads[m] // 1
        state_n = heads[n] - whole_n
        block = whole_m - 10**length * whole_n
        old_block = (10**length * state_n) // 1
        increment = block - old_block
        assert block == (10**length * state_n + accumulated) // 1
        assert increment == ((10**length * state_n) % 1 + accumulated) // 1
        assert 1 <= increment <= 11
        depths = []
        for h in range(2, length + 1):
            carry = old_block % 10**h + increment >= 10**h
            crossing = ((10**(m-h) * direct[m]) // 1
                        > (10**(m-h) * direct[n]) // 1)
            assert carry == crossing
            assert carry == (block % 10**h < increment)
            if carry:
                assert whole_m % 10**h < increment
                depths.append(h)
        observed[n] = max(depths, default=0)
    assert max(observed.values()) == 2
    assert [n for n, h in observed.items() if h == 2] == [23, 76, 134]
    print("PASS: exact sums/recurrence, minimal horizons, block and crossing identities;")
    print("finite n<=150 only: maximum depth 2 at n=23,76,134; not an infinite proof.")


if __name__ == "__main__":
    main()
