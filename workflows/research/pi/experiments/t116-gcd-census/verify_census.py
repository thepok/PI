#!/usr/bin/env python3
"""T116 independent verifier.

Independently recomputes, from the source equations only:
  * bbpPartial via its own four-pole pole functions,
  * F_N via the seven-term identity AND the partial-difference route,
  * Q_N, U_N, V_N, g_N,
then checks every field of census.json, re-derives every recorded law
verdict from the stored data and from the recomputed data, and verifies
the canonical records hash.  Any mismatch (mutation) => exit nonzero.
No floats anywhere.
"""

import hashlib
import json
import math
import sys
from fractions import Fraction

sys.set_int_max_str_digits(200000)

EXPECTED_SCHEMA = "t116-gcd-census-v1"
N_MAX_EXPECTED = 511
DISCOVERY_MAX = 255
HOLDOUT_MIN = 256
G4_BOUND = 10 ** 6


def fail(msg):
    print(f"VERIFY FAIL: {msg}", file=sys.stderr)
    sys.exit(1)


# ---- independent recomputation of the source equations ---------------------

def pole_one(k):
    return Fraction(4, (8 * k + 1)) / Fraction(16) ** k


def pole_two(k):
    return -Fraction(1, 2) / Fraction(2 * k + 1) / Fraction(16) ** k


def pole_three(k):
    return -Fraction(1, 8 * k + 5) / Fraction(16) ** k


def pole_four(k):
    return -Fraction(1, 2) / Fraction(4 * k + 3) / Fraction(16) ** k


def term(k):
    return pole_one(k) + pole_two(k) + pole_three(k) + pole_four(k)


PARTIALS = None


def build_partials():
    global PARTIALS
    if PARTIALS is None:
        PARTIALS = []
        s = Fraction(0)
        for k in range(7 * (N_MAX_EXPECTED + 1) + 1):
            s += term(k)
            PARTIALS.append(s)


def partial(m):
    build_partials()
    return PARTIALS[m]


def factorize(n):
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


def is_prime(n):
    """Independent primality check for each factor emitted by factorize."""
    if n < 2:
        return False
    if n % 2 == 0:
        return n == 2
    d = 3
    while d * d <= n:
        if n % d == 0:
            return False
        d += 2
    return True


def valuation(n, p):
    c = 0
    while n % p == 0:
        n //= p
        c += 1
    return c


def classify_prime(p, div_d, div_e):
    if p in (2, 5) and not (div_d and div_e):
        return "base10"
    if div_d and div_e:
        return "common_denominator"
    if div_d:
        return "q_den_only"
    return "f_den_only"


# ----------------------------------------------------------------------------

def main():
    try:
        with open("census.json", encoding="utf-8") as fh:
            doc = json.load(fh)
    except Exception as exc:
        fail(f"cannot load census.json: {exc}")

    if doc.get("schema") != EXPECTED_SCHEMA:
        fail(f"bad schema {doc.get('schema')!r}")
    meta = doc.get("meta") or {}
    if meta.get("discovery_range") != [0, DISCOVERY_MAX] or \
       meta.get("holdout_range") != [HOLDOUT_MIN, N_MAX_EXPECTED]:
        fail("meta ranges wrong")

    records = doc.get("records")
    if not isinstance(records, list):
        fail("records missing")
    if meta.get("num_records") != len(records):
        fail("num_records mismatch")
    if len(records) != N_MAX_EXPECTED + 1:
        fail(f"expected {N_MAX_EXPECTED + 1} records")
    if meta.get("num_records") != N_MAX_EXPECTED + 1:
        fail("meta num_records wrong")
    if meta.get("arithmetic") != "exact rationals/integers only; no floats":
        fail("meta arithmetic boundary wrong")
    if meta.get("status_boundary") != (
        "finite-range survival is experiment only; no asymptotic, occupancy, "
        "density, or V1 claim"
    ):
        fail("meta status boundary wrong")
    indices = [r.get("n") if isinstance(r, dict) else None for r in records]
    if indices != list(range(N_MAX_EXPECTED + 1)):
        fail("records must be the exact ordered unique range N=0..511")

    # canonical records hash
    rec_json = json.dumps(records, sort_keys=True, separators=(",", ":"),
                          ensure_ascii=True)
    got_sha = hashlib.sha256(rec_json.encode("utf-8")).hexdigest()
    if meta.get("records_sha256") != got_sha:
        fail(f"records_sha256 mismatch: stored {meta.get('records_sha256')} "
             f"recomputed {got_sha}")

    # per-record independent replay
    for r in records:
        n = r.get("n")
        if not isinstance(n, int) or not (0 <= n <= N_MAX_EXPECTED):
            fail(f"record index bad: {n!r}")
        Q = Fraction(10) ** n * partial(7 * n)
        F_diff = Fraction(10) ** (n + 1) * (partial(7 * (n + 1))
                                            - partial(7 * n))
        F_seven = Fraction(10) ** (n + 1) * sum(
            term(7 * n + j + 1) for j in range(7))
        if F_diff != F_seven:
            fail(f"N={n}: forcing routes disagree")
        A, D = Q.numerator, Q.denominator
        C, E = F_diff.numerator, F_diff.denominator
        U = 10 * A * E + C * D
        V = D * E
        g = math.gcd(abs(U), V)

        checks = {
            "q_num": str(A), "q_den": str(D),
            "f_num": str(C), "f_den": str(E),
            "u": str(U), "v": str(V), "g": str(g),
            "v2_g": valuation(g, 2),
            "v5_g": valuation(g, 5),
            "bitlen_u": U.bit_length(),
            "bitlen_v": V.bit_length(),
            "bitlen_g": g.bit_length(),
            "ratio_g_over_v_num": str(Fraction(g, V).numerator),
            "ratio_g_over_v_den": str(Fraction(g, V).denominator),
        }
        for key, want in checks.items():
            if key not in r:
                fail(f"N={n}: missing field {key}")
            if str(r[key]) != str(want):
                fail(f"N={n}: field {key} stored={r[key]} recomputed={want}")

        pf = factorize(g)
        factor_product = math.prod(pf)
        if factor_product != g or any(not is_prime(p) for p in pf):
            fail(f"N={n}: factorization is not a prime product for g")
        exp_counts = {}
        for p in pf:
            exp_counts[p] = exp_counts.get(p, 0) + 1
        pg = r.get("primes_g")
        if not isinstance(pg, list) or \
                sorted(int(e["p"]) for e in pg) != sorted(exp_counts):
            fail(f"N={n}: primes_g mismatch with gcd factorization")
        cls_counts = {}
        for e in pg:
            p = int(e["p"])
            dd = (D % p == 0)
            de = (E % p == 0)
            if not dd or (not de and p not in (2, 5)):
                fail(f"N={n}: p={p} violates T116 prime-support invariant")
            if bool(e["divides_q_den"]) != dd or \
               bool(e["divides_f_den"]) != de or \
               bool(e["in_base10"]) != (p in (2, 5)) or \
               int(e["exp"]) != exp_counts[p]:
                fail(f"N={n}: prime entry wrong for p={p}")
            want_cls = classify_prime(p, dd, de)
            if e["class"] != want_cls:
                fail(f"N={n}: class wrong for p={p}")
            cls_counts[want_cls] = cls_counts.get(want_cls, 0) + 1
        if r.get("prime_source_class_counts") != cls_counts:
            fail(f"N={n}: prime_source_class_counts mismatch")

    # ---- verdicts: recompute from stored data, then cross-check ----------
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
                    off = [e["p"] for e in r["primes_g"]
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
                else:
                    if g > G4_BOUND:
                        bad = {"n": r["n"], "g": r["g"]}
                if bad is not None:
                    wit = bad
                    break
            out[lid] = {
                "statement": LAWS[lid],
                "verdict": "rejected" if wit else "accepted_experiment",
                "first_witness": wit,
            }
        return out

    LAWS = {
        "G1": "every prime dividing g_N lies in {2,5}",
        "G2": "g_N divides 10",
        "G3": "g_N^2 <= V_N",
        "G4": "g_N <= 10^6",
    }

    for key, (lo, hi) in (
            ("laws_all_N_0_511", (0, N_MAX_EXPECTED)),
            ("laws_discovery_N_0_255", (0, DISCOVERY_MAX)),
            ("laws_holdout_N_256_511", (HOLDOUT_MIN, N_MAX_EXPECTED))):
        want = eval_laws(lo, hi)
        if doc.get(key) != want:
            fail(f"{key} mismatch:\nstored ={json.dumps(doc.get(key))}\n"
                 f"expect={json.dumps(want)}")

    # sanity: verdicts must also agree with independently recomputed values
    for scope_key, (lo, hi) in (
            ("laws_all_N_0_511", (0, N_MAX_EXPECTED)),
            ("laws_discovery_N_0_255", (0, DISCOVERY_MAX)),
            ("laws_holdout_N_256_511", (HOLDOUT_MIN, N_MAX_EXPECTED))):
        for lid, res in doc[scope_key].items():
            w = res["first_witness"]
            if res["verdict"] == "rejected":
                if w is None:
                    fail(f"{scope_key}/{lid}: rejected without witness")
                nw = w["n"]
                if not (lo <= nw <= hi):
                    fail(f"{scope_key}/{lid}: witness out of range")
                g_r = int(records[nw]["g"])
                v_r = int(records[nw]["v"])
                # confirm the witness really violates the law on stored data
                ok_violation = (
                    (lid == "G1" and any(e["p"] not in ("2", "5")
                                         for e in records[nw]["primes_g"]))
                    or (lid == "G2" and 10 % g_r != 0)
                    or (lid == "G3" and g_r * g_r > v_r)
                    or (lid == "G4" and g_r > G4_BOUND)
                )
                if not ok_violation:
                    fail(f"{scope_key}/{lid}: witness does not violate law")
                # confirm it is the FIRST witness
                for r2 in records[:nw]:
                    if not (lo <= r2["n"] <= hi):
                        continue
                    g2, v2 = int(r2["g"]), int(r2["v"])
                    viol = ((lid == "G1" and any(e["p"] not in ("2", "5")
                                                 for e in r2["primes_g"]))
                            or (lid == "G2" and 10 % g2 != 0)
                            or (lid == "G3" and g2 * g2 > v2)
                            or (lid == "G4" and g2 > G4_BOUND))
                    if viol:
                        fail(f"{scope_key}/{lid}: earlier witness at "
                             f"N={r2['n']}")
            else:
                if w is not None:
                    fail(f"{scope_key}/{lid}: accepted but has witness")

    print("VERIFY OK: all fields, hashes, and every verdict reproduced "
          f"independently ({len(records)} records, N=0..{N_MAX_EXPECTED}).")
    print(f"DISCOVERY_RANGE=0..{DISCOVERY_MAX}")
    print(f"HOLDOUT_RANGE={HOLDOUT_MIN}..{N_MAX_EXPECTED}")
    print("EXACT_REPLAY=PASS")
    return 0


if __name__ == "__main__":
    sys.exit(main())
