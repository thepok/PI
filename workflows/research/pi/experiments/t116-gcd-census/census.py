#!/usr/bin/env python3
"""T116 exact gcd census (canonical synchronized sampled BBP recurrence).

Exact source equations (Lean: T74/T77/T98/T106):

  poleOne(k)   =  4 / ((8*k+1) * 16^k)
  poleTwo(k)   = -1 / (2*(2*k+1) * 16^k)
  poleThree(k) = -1 / ((8*k+5) * 16^k)
  poleFour(k)  = -1 / (2*(4*k+3) * 16^k)
  term(k)      = poleOne(k)+poleTwo(k)+poleThree(k)+poleFour(k)
               = (120k^2+151k+47) / ((2k+1)(4k+3)(8k+1)(8k+5) * 16^k)
  bbpPartial(M) = sum_{k=0}^{M} term(k)

  Q_N = reduced( 10^N * bbpPartial(7*N) )            (= sampledBBPValue orbit seed)
  F_N = reduced( sampledBBPForcingRat N )
      = reduced( 10^(N+1) * (bbpPartial(7(N+1)) - bbpPartial(7*N)) )
  U_N = 10*Q.num*F.den + F.num*Q.den
  V_N = Q.den*F.den
  g_N = gcd(|U_N|, V_N)

All arithmetic is exact (fractions.Fraction / Python ints).  No floating
point anywhere.  Discovery range N=0..255; frozen holdout N=256..511.

Preregistered laws (one exact witness rejects):
  G1: every prime of g_N lies in {2, 5}
  G2: g_N divides 10
  G3: g_N^2 <= V_N
  G4: g_N <= 10^6

Output: census.json (deterministic serialization).
"""

import hashlib
import json
import sys
import time

sys.set_int_max_str_digits(200000)
from fractions import Fraction

DISCOVERY_MAX = 255
HOLDOUT_MIN = 256
HOLDOUT_MAX = 511
N_MAX = HOLDOUT_MAX
G4_BOUND = 10 ** 6
BASE_PRIMES = (2, 5)


def term(k):
    """bbpCombinedTerm(k): the four-pole BBP rational coefficient."""
    return Fraction(120 * k * k + 151 * k + 47,
                    (2 * k + 1) * (4 * k + 3) * (8 * k + 1) * (8 * k + 5)
                    * 16 ** k)


def build_partials(m_max):
    """partials[M] = bbpPartial(M) for M = 0..m_max (exact)."""
    partials = []
    s = Fraction(0)
    for k in range(m_max + 1):
        s += term(k)
        partials.append(s)
    return partials


def factorize(n):
    """Trial-divide n > 0; return sorted list of prime factors with multiplicity."""
    fs = []
    d = 2
    while d * d <= n:
        while n % d == 0:
            fs.append(d)
            n //= d
        d += 1 if d == 2 else 2
    if n > 1:
        fs.append(n)
    return fs


def valuation(n, p):
    c = 0
    while n % p == 0:
        n //= p
        c += 1
    return c


def classify_prime(p, div_d, div_e):
    if p in BASE_PRIMES and not (div_d and div_e):
        return "base10"
    if div_d and div_e:
        return "common_denominator"
    if div_d:
        return "q_den_only"
    return "f_den_only"


def main():
    t0 = time.time()
    import math

    partials = build_partials(7 * (N_MAX + 1))

    records = []
    for N in range(N_MAX + 1):
        Q = Fraction(10) ** N * partials[7 * N]
        # Independent-of-difference route to F: seven new terms (T106).
        F_diff = Fraction(10) ** (N + 1) * (partials[7 * (N + 1)] - partials[7 * N])
        F_seven = Fraction(10) ** (N + 1) * sum(
            term(7 * N + j + 1) for j in range(7))
        assert F_diff == F_seven, f"N={N}: forcing routes disagree"
        F = F_diff
        A, D = Q.numerator, Q.denominator
        C, E = F.numerator, F.denominator
        U = 10 * A * E + C * D
        V = D * E
        g = math.gcd(abs(U), V)
        assert g > 0 and V % g == 0 and abs(U) % g == 0

        pfactors = factorize(g)
        primes_g = []
        class_counts = {}
        seen = {}
        for p in pfactors:
            seen[p] = seen.get(p, 0) + 1
        for p in sorted(seen):
            div_d = (D % p == 0)
            div_e = (E % p == 0)
            cls = classify_prime(p, div_d, div_e)
            primes_g.append({
                "p": str(p),
                "exp": seen[p],
                "class": cls,
                "divides_q_den": div_d,
                "divides_f_den": div_e,
                "in_base10": p in BASE_PRIMES,
            })
            class_counts[cls] = class_counts.get(cls, 0) + 1
        ratio = Fraction(g, V)
        records.append({
            "n": N,
            "q_num": str(A), "q_den": str(D),
            "f_num": str(C), "f_den": str(E),
            "u": str(U), "v": str(V), "g": str(g),
            "v2_g": valuation(g, 2),
            "v5_g": valuation(g, 5),
            "bitlen_u": U.bit_length(),
            "bitlen_v": V.bit_length(),
            "bitlen_g": g.bit_length(),
            "primes_g": primes_g,
            "prime_source_class_counts": class_counts,
            "ratio_g_over_v_num": str(ratio.numerator),
            "ratio_g_over_v_den": str(ratio.denominator),
        })

    def eval_laws(lo, hi):
        out = {}
        for lid in ("G1", "G2", "G3", "G4"):
            wit = None
            for r in records:
                if not (lo <= r["n"] <= hi):
                    continue
                g = int(r["g"])
                v = int(r["v"])
                bad = None
                if lid == "G1":
                    off = [int(e["p"]) for e in r["primes_g"]
                           if e["p"] not in ("2", "5")]
                    if off:
                        bad = {"n": r["n"], "g": r["g"],
                               "offending_primes": [str(x) for x in off]}
                elif lid == "G2":
                    if 10 % g != 0:
                        bad = {"n": r["n"], "g": r["g"]}
                elif lid == "G3":
                    if g * g > v:
                        bad = {"n": r["n"], "g": r["g"], "v": r["v"]}
                else:  # G4
                    if g > G4_BOUND:
                        bad = {"n": r["n"], "g": r["g"]}
                if bad is not None:
                    wit = bad
                    break
            out[lid] = {
                "statement": LAWS[lid],
                "verdict": "rejected" if wit is not None else "accepted_experiment",
                "first_witness": wit,
            }
        return out

    LAWS = {
        "G1": "every prime dividing g_N lies in {2,5}",
        "G2": "g_N divides 10",
        "G3": "g_N^2 <= V_N",
        "G4": "g_N <= 10^6",
    }

    verdicts_full = eval_laws(0, N_MAX)
    verdicts_disc = eval_laws(0, DISCOVERY_MAX)
    verdicts_hold = eval_laws(HOLDOUT_MIN, HOLDOUT_MAX)

    rec_json = json.dumps(records, sort_keys=True, separators=(",", ":"))
    records_sha = hashlib.sha256(rec_json.encode("utf-8")).hexdigest()

    doc = {
        "schema": "t116-gcd-census-v1",
        "meta": {
            "description": "Exact gcd census of the canonical synchronized "
                           "sampled BBP recurrence (T116)",
            "definitions": {
                "term(k)": "(120k^2+151k+47)/((2k+1)(4k+3)(8k+1)(8k+5)*16^k)",
                "bbpPartial(M)": "sum_{k=0}^{M} term(k)",
                "Q_N": "reduced(10^N * bbpPartial(7N))",
                "F_N": "reduced(10^(N+1) * (bbpPartial(7(N+1))-bbpPartial(7N)))"
                       " == reduced(10^(N+1) * sum_{j=1}^{7} term(7N+j))",
                "U_N": "10*q_num*f_den + f_num*q_den",
                "V_N": "q_den*f_den",
                "g_N": "gcd(|U_N|, V_N)",
            },
            "arithmetic": "exact rationals/integers only; no floats",
            "discovery_range": [0, DISCOVERY_MAX],
            "holdout_range": [HOLDOUT_MIN, HOLDOUT_MAX],
            "num_records": len(records),
            "records_sha256": records_sha,
            "status_boundary": "finite-range survival is experiment only; "
                               "no asymptotic, occupancy, density, or V1 claim",
        },
        "laws_all_N_0_511": verdicts_full,
        "laws_discovery_N_0_255": verdicts_disc,
        "laws_holdout_N_256_511": verdicts_hold,
        "records": records,
    }

    path = "census.json"
    with open(path, "w", encoding="utf-8") as fh:
        json.dump(doc, fh, sort_keys=True, separators=(",", ":"),
                  ensure_ascii=True)
        fh.write("\n")

    elapsed = time.time() - t0
    print(f"DISCOVERY_RANGE=0..{DISCOVERY_MAX}")
    print(f"HOLDOUT_RANGE={HOLDOUT_MIN}..{HOLDOUT_MAX}")
    print(f"wrote {path}: {len(records)} records, records_sha256={records_sha}, "
          f"{elapsed:.1f}s")
    for scope, vv in (("all", verdicts_full), ("discovery", verdicts_disc),
                      ("holdout", verdicts_hold)):
        for lid, res in vv.items():
            w = res["first_witness"]
            print(f"{scope:9s} {lid}: {res['verdict']}"
                  + (f" (witness N={w['n']})" if w else ""))
    return 0


if __name__ == "__main__":
    sys.exit(main())

