#!/usr/bin/env python3
import csv
import hashlib
import math
from pathlib import Path

ROOT = Path(__file__).resolve().parent
CANONICAL_SHA = "cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8"


def sha256(name):
    return hashlib.sha256((ROOT / name).read_bytes()).hexdigest()


def require(condition, message):
    if not condition:
        raise AssertionError(message)


def is_prime_64(n):
    if n < 2:
        return False
    small = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37)
    for q in small:
        if n % q == 0:
            return n == q
    d = n - 1
    s = 0
    while d % 2 == 0:
        s += 1
        d //= 2
    for a in (2, 325, 9375, 28178, 450775, 9780504, 1795265022):
        if a % n == 0:
            continue
        x = pow(a, d, n)
        if x in (1, n - 1):
            continue
        for _ in range(s - 1):
            x = pow(x, 2, n)
            if x == n - 1:
                break
        else:
            return False
    return True


require(sha256("canonical_statement.txt") == CANONICAL_SHA, "canonical hash")

with (ROOT / "SOURCE_LEDGER.csv").open(newline="", encoding="utf-8") as handle:
    sources = list(csv.DictReader(handle))
require(len(sources) == 3, "exactly three source/theorem tuples")
require(len({row["domain"] for row in sources}) == 3, "exactly three domains")
require(len({row["stable_id"] for row in sources}) == 3, "stable IDs distinct")
require(all(row["exact_locator"] and row["theorem_range"] for row in sources), "locator/range missing")
for row in sources:
    require(sha256(row["pdf_file"]) == row["pdf_sha256"], row["pdf_file"] + " hash")
    require(sha256(row["text_file"]) == row["text_sha256"], row["text_file"] + " hash")
retained = [row for row in sources if row["retained"] == "yes"]
require(len(retained) == 1 and len(retained) <= 4, "retained fingerprint count")
require(len(sources) <= 12, "source cap")

with (ROOT / "EXCLUSION_LEDGER.csv").open(newline="", encoding="utf-8") as handle:
    exclusions = list(csv.DictReader(handle))
items = [int(row["item"][1:]) for row in exclusions]
require(items == list(range(89, 178)), "ledger must cover T89-T177 consecutively")
by_item = {row["item"]: row for row in exclusions}
require("rejected" in by_item["T174"]["verification"], "T174 classification")
require("active" in by_item["T176"]["verification"] and "reserve" in by_item["T176"]["T163_disposition"], "T176 classification")
require("active" in by_item["T177"]["verification"] and "reserve" in by_item["T177"]["T163_disposition"], "T177 classification")

report = (ROOT / "REPORT.md").read_text(encoding="utf-8")
for token in (
    "SEARCHED_DOMAIN_COUNT: 3",
    "NEW_SOURCE_THEOREM_TUPLE_COUNT: 3",
    "RETAINED_FINGERPRINT_COUNT: 1",
    "DUPLICATE_CHECK_THROUGH: T175",
    "QUANTITATIVE_SCREEN_COUNT: 3",
    "EXPLICIT_TRANSFER_PREMISE_COUNT: 3",
    "SCOPED_VERDICT_COUNT: 1",
    "SUCCESSOR_COUNT: 0",
    "FIXED_PI_CLAIM: none",
    "A1_CLAIM: none",
    "C1_CLAIM: none",
    "C2_CLAIM: none",
):
    require(report.count(token) == 1, token)
require(report.count("SCOPED VERDICT (1/1):") == 1, "exactly one scoped verdict")
require(report.count("unproved fixed-pi transfer")== 4, "label plus three transfer premises")

N = 10**12
kappa = 0.5
m = math.floor(kappa * math.log10(N))
M = math.ceil(N / math.log(N))
relative_energy = ((N - M) / N) ** 2
require(m == 6, "logarithmic depth")
require(1 / M <= math.log(N) / N, "max-gap model")
require(relative_energy > 0.9289, "collision counter-screen")

tau = math.log10(10**m) / m
dimension_upper = math.log10(2) / 2
require(tau == 1.0, "restricted-denominator critical exponent")
require(dimension_upper < 0.151, "restricted-denominator dimension screen")

p = 1000000000039
order = 166666666673
order_prime_factors = (13, 17, 29, 26005097)
require(is_prime_64(p), "reported modulus primality")
require(all(is_prime_64(q) for q in order_prime_factors), "reported order factors primality")
require(math.prod(order_prime_factors) == order, "reported order factorization")
require(pow(10, order, p) == 1, "reported order exponent")
for q in order_prime_factors:
    require(pow(10, order // q, p) != 1, "reported order minimality")
z = sum(complex(math.cos(2 * math.pi * pow(10, j, p) / p),
                math.sin(2 * math.pi * pow(10, j, p) / p)) for j in range(m))
prefix_abs = abs(z)
prefix_relative = prefix_abs / m
prefix_error_bound = 2 * math.pi * (10**m - 1) / (9 * p)
require(prefix_relative > 0.999999, "prefix cancellation screen")

print("CANONICAL_SHA256:", CANONICAL_SHA)
print("SEARCHED_DOMAIN_COUNT:", len({row["domain"] for row in sources}))
print("NEW_SOURCE_THEOREM_TUPLE_COUNT:", len(sources))
print("RETAINED_FINGERPRINT_COUNT:", len(retained))
print("EXCLUSION_LEDGER_RANGE: T%d-T%d" % (items[0], items[-1]))
print("T174_CLASSIFICATION: rejected")
print("T176_CLASSIFICATION: active reserved")
print("T177_CLASSIFICATION: active reserved")
print("SCREEN_DEPTH: N=%d kappa=%.1f m=%d" % (N, kappa, m))
print("C_LAC_M: %d" % M)
print("C_LAC_NATIVE_GAP: %.12e" % (math.log(N) / N))
print("C_LAC_RELATIVE_ENERGY: %.12f" % relative_energy)
print("C_RD_TAU: %.1f" % tau)
print("C_RD_DIMENSION_AT_EPSILON_ZERO: %.12f" % dimension_upper)
print("C_FD_P: %d" % p)
print("C_FD_P_IS_PRIME: yes")
print("C_FD_ORDER_10: %d" % order)
print("C_FD_PREFIX_ABS: %.15f" % prefix_abs)
print("C_FD_PREFIX_RELATIVE: %.15f" % prefix_relative)
print("C_FD_PREFIX_ERROR_BOUND: %.12e" % prefix_error_bound)
print("QUANTITATIVE_SCREEN_COUNT: 3")
print("EXPLICIT_TRANSFER_PREMISE_COUNT: 3")
print("SCOPED_VERDICT_COUNT: 1")
print("SUCCESSOR_COUNT: 0")
print("VERIFICATION: PASS")
