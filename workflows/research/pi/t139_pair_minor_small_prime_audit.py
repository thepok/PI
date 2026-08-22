#!/usr/bin/env python3
"""Exact P14 small-prime audit built on the registered T138 replay."""

from collections import Counter
from contextlib import redirect_stdout
from importlib.util import module_from_spec, spec_from_file_location
from io import StringIO
from itertools import combinations
from pathlib import Path


SOURCE = Path(__file__).with_name("t138_plucker_content_census.py")
spec = spec_from_file_location("t138", SOURCE)
assert spec is not None and spec.loader is not None
t138 = module_from_spec(spec)
with redirect_stdout(StringIO()):
    spec.loader.exec_module(t138)


def pair_xi(m: int, x) -> int:
    qm, zm, _, _ = t138.phase(m, -1, x)
    q0, z0, _, _ = t138.phase(m, 0, x)
    assert q0 == 10 * qm + 3
    return qm * z0 - q0 * zm


def cross_k(checkpoints: tuple[int, int, int, int]) -> int:
    xis = [pair_xi(m, t138.canonical_x(m)) for m in checkpoints]
    return xis[0] * xis[3] - xis[1] * xis[2]


quarter_mod6 = Counter()
for n, _, offsets in t138.eligible:
    checkpoints = tuple(n + r for r in offsets)
    quarter_mod6[cross_k(checkpoints) % 6] += 1

assert quarter_mod6 == Counter({0: 6, 1: 1, 2: 10, 3: 3, 4: 10, 5: 2})
assert cross_k((17, 18, 19, 21)) % 6 == 5

print("quarter_K_mod_6", dict(sorted(quarter_mod6.items())))
for run in (tuple(range(168, 173)), tuple(range(335, 340))):
    residues = []
    for subset in combinations(run, 4):
        value = cross_k(subset)
        assert value != 0
        residues.append((subset, value % 6))
    print("all_BAD_run", f"{run[0]}..{run[-1]}", "K_mod_6", residues)
