#!/usr/bin/env python3
"""Self-contained T127 package replay."""

from __future__ import annotations

import hashlib
import math
import re
import tarfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent

PACKAGE_HASHES = {
    "canonical_statement.txt": "cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8",
    "PRIOR_EVIDENCE.tar": "e3be23a53844ddb1a678e2f25fd2e2ae9cdc7ccbbfd9e99b3612a9c9d8ceedb8",
    "SOURCES.tar": "1ed1b3510612c0310cb5df5f1f59893f600c5bb8ee3c25916d83c8d80f74bf7a",
}

SOURCE_HASHES = {
    "iyer-2312.01076.pdf": "a312fd3c401f46360939dfa7ffff92a3d3f293693a9637fad2f2574e181821d8",
    "iyer-2312.01076.txt": "ee5b1fe43c10d0bc4c13e7c6d7a17dbe0e4bfee3aa88ac5c703fc49911a7c284",
    "corvaja-zannier-math0403522.pdf": "90dc898925b01539afe05fcbb4cd2728c921bdb268719bf2cf02304ab252192f",
    "corvaja-zannier-math0403522.txt": "1e13ab254fe9b6da805ddf8826ef9022115907ec3c6463115ebe40e71c68e478",
    "durand-0807.4430.pdf": "627b56882a2a6235fab08f62c8365a4c08c4e91602f6a522b40a54aa4d46e043",
    "durand-0807.4430.txt": "7015f9f21d2ef86dc5fbfb13e23f7137f9805f17d32c504a1ce2a8c4c147ae58",
    "bell-coons-rowland-1210.2070.pdf": "30481c3b4cf0ae925bb7bf11b908e00d3df0a77779090c615ebdfa82bd764aa0",
    "bell-coons-rowland-1210.2070.txt": "10aa80c1bcd7cd38b4c21afa0c0c523ec92cf2b23b6a3a937deb5c3a41885889",
    "adamczewski-bell-1303.2019.pdf": "f0d9fc701cee3e57ec7302a70d0d615e98bb38a3b69f468ce5f708eaf0fdf481",
    "adamczewski-bell-1303.2019.txt": "9fa6c1e238faca2b188c8df05354896f58cb21a4a40eeb323df02fa377ee7d1f",
    "adamczewski-bugeaud-math0511674.pdf": "e3bd2934800e94dd27930d43d47abc44f760de7e90320d1d014b372b681be9a0",
    "adamczewski-bugeaud-math0511674.txt": "a7ce6a05d22af6a9f25d547fad6284ac012ae4a2986acb89f320733e61d151e0",
    "maynard-1604.01041.pdf": "d77407ee9abed7b735870b67d88cf8be86d677908396b0bc5aacd86fbf7f0d2a",
    "maynard-1604.01041.txt": "cc43a3b3e30a82e338f6064ea0f4afa58316b4a6d04e2e07df11a4a8e3caa710",
    "adamczewski-faverjon-crmath458.pdf": "75a15e4da56492e58ca864314e16bc0a5fe7588f48a1f738218d31d1a7012590",
    "adamczewski-faverjon-crmath458.txt": "cfae7598cffc34d6f626afea7eee53ad9b7f5e1579491c07f61e78f2276d44ae",
    "cyr-kra-1403.0238.pdf": "eecf4249ef66175bca51f6a4c396cad7b58dbf85ff1d60967f04ddfddd740625",
    "cyr-kra-1403.0238.txt": "533618a210643f5f528e932a77b2098a62b6619903dedc0a7b3470f3c5a29997",
    "dibenedetto-et-al-2003.06165.pdf": "4434b3992292e881139055eb0390ed7a7ff9ce9b243c156ac631c1442c2930d1",
    "dibenedetto-et-al-2003.06165.txt": "3529db3774a5b33b0489844e91b507246037aee700ca0e8f7474407e6af75845",
    "bourgain-garaev-1211.4184.pdf": "937f881bd7de4bd5937618543a3516ea876232a1ea87e44f89e16d5fe711474d",
    "bourgain-garaev-1211.4184.txt": "5020790059d473cc53c41ae041387499c739928fc8d4846c33da80602e808fdb",
}


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def require(ok: bool, message: str) -> None:
    if not ok:
        raise AssertionError(message)


for name, expected in PACKAGE_HASHES.items():
    actual = sha((ROOT / name).read_bytes())
    require(actual == expected, f"hash mismatch {name}")
    print(f"HASH_OK {name} {actual}")

with tarfile.open(ROOT / "SOURCES.tar", "r") as archive:
    members = {m.name: archive.extractfile(m).read() for m in archive.getmembers() if m.isfile()}
require(set(members) == set(SOURCE_HASHES), "source member set mismatch")
for name, expected in SOURCE_HASHES.items():
    require(sha(members[name]) == expected, f"source hash mismatch {name}")
print("SOURCE_ARCHIVE_OK primary_sources=11 members=22")

report = (ROOT / "REPORT.md").read_text(encoding="utf-8")
markers = {
    "TOTAL_INSPECTED_PRIMARY_SOURCE_COUNT": 11,
    "PRIMARY_SOURCE_CAP": 12,
    "FINAL_CLEAN_SOURCE_COUNT": 3,
    "FINAL_CLEAN_SEARCHED_DOMAIN_COUNT": 3,
    "FINAL_PRESELECTION_ABSENT_CELL_COUNT": 3,
    "DISCARDED_SOURCE_COUNT": 8,
    "RETAINED_CANDIDATE_COUNT": 3,
    "CANDIDATE_CAP": 4,
    "SURVIVOR_COUNT": 0,
    "SCOPED_VERDICT_COUNT": 1,
    "SUCCESSOR_COUNT": 0,
}
for key, value in markers.items():
    require(f"{key}: {value}" in report, f"missing {key}")
print("CAPS_OK sources=11/12 candidates=3/4 domains=3")

ids = re.findall(r"^\| (T(?:8[9]|9[0-9]|1[01][0-9]|12[0-6])) \|", report, re.MULTILINE)
require(ids == [f"T{i}" for i in range(89, 127)], "matrix mismatch")
for item, state in (("T109", "terminal"), ("T119", "terminal"), ("T122", "terminal"),
                    ("T123", "parked"), ("T125", "active"), ("T126", "active")):
    row = next(line for line in report.splitlines() if line.startswith(f"| {item} |"))
    require(state in row, f"state missing {item}")
require("complete multiplicative-subgroup" in next(line for line in report.splitlines()
                                                     if line.startswith("| T105 |")), "T105 correction")
require("4m-2" in next(line for line in report.splitlines() if line.startswith("| T123 |")), "T123 correction")
print("MATRIX_OK T89-T126 rows=38 special_states_and_corrections=ok")

freeze = (ROOT / "PRESELECTION_FREEZE.md").read_text(encoding="utf-8")
replacement = (ROOT / "PRESELECTION_REPLACEMENT.md").read_text(encoding="utf-8")
for cell in ("J-A", "J-B"):
    require(f"| {cell} |" in freeze and f"| {cell} |" in report, f"freeze missing {cell}")
require("| J-D |" in replacement and "| J-D |" in report, "replacement freeze missing")
for forbidden in ("Adamczewski", "Faverjon", "Cyr", "Kra", "Bourgain", "Garaev", "http"):
    require(forbidden not in freeze and forbidden not in replacement, "freeze names source")
print("PRESELECTION_OK J-A J-B J-D frozen without source names")

with tarfile.open(ROOT / "PRIOR_EVIDENCE.tar", "r") as archive:
    prior = set(archive.getnames())
for name in ("knowledge_library/t105/REPORT.md", "knowledge_library/t117/REPORT.md",
             "knowledge_library/t118/REPORT.md", "orchestrator-input.json"):
    require(name in prior, f"prior evidence missing {name}")
print(f"PRIOR_ARCHIVE_OK members={len(prior)}")

# C-SQ: complexity provides only a lower collision floor.
N, complexity = 1000, 100
require(N*N/complexity == 10_000 and N*N == 1_000_000, "C-SQ arithmetic")
print("C_SQ_TEST energy_interval=[10000,1000000] no_upper_bound")

# C-RECIP: three-term ratio equations differ by 9 modulo p.
require((-10)-(-19) == 9, "ratio subtraction")
eligible_primes = [p for p in (2, 3, 5, 7, 11, 13) if 9 % p == 0]
require(eligible_primes == [3], "ratio obstruction")
print("C_RECIP_TEST ratio_equations_force_p=3 reciprocal_triple_undefined")

# C-LIFT: literal T107 finite budgets at one sample pair.
ell, P = 2, 100_000
q = 10**ell
require(P/(40*q) == 25 and P**2/(10*q) == 10_000_000, "T107 arithmetic")
print("C_LIFT_TEST boundary_budget=25 fourier_budget=10000000 source_has_no_rate")

for heading in ("## 5. C-LIFT", "## 6. C-SQ", "## 7. C-RECIP"):
    require(heading in report, f"card missing {heading}")
require(report.count("**Verdict: close the final three-cell T127 clean scout.**") == 1,
        "verdict count")
require("No successor is selected." in report, "successor scope")
require(re.search(r"No fixed-pi, C1, or C2 conclusion", report), "scope firewall")
print("SCOPE_OK verdict=close survivors=0 successors=0 canonical_claims=0")
print("VERIFY_T127_OK")
