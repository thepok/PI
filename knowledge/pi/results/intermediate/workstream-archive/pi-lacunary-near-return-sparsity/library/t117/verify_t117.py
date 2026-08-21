#!/usr/bin/env python3
"""Self-contained integrity and finite-arithmetic checks for T117."""

from __future__ import annotations

import hashlib
import json
import math
import re
from collections import Counter
from pathlib import Path


ROOT = Path(__file__).resolve().parent

HASHES = {
    "canonical_statement.txt": "cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8",
    "mauduit-sarkozy-1997.pdf": "d95bbd2b7cbecfb0cee08f82a41f7879579277f865b8f0d0dc53c5e79e2a39fa",
    "mauduit-sarkozy-1997.txt": "e3aa1279155d19d144057cf518b4597d61aff4d4070f86b9806fa1ff35a05fd4",
    "weil-1948-pnas.pdf": "c19b498bacb4878f2067e679f92306f3f2a3fa54f53937f12c5d6650a5f5abef",
    "weil-1948-pnas.txt": "c3d84b507fc00d3bf5beb17e760102984d72fd77c0dfa0bae4fe1991a8abc6a6",
    "prior-t109-REPORT.md": "6b4f27464b76c67ea6fe41990f9ed6d3242c8c763b880fb4862fbac16f3ffcdf",
    "prior-t109-SKEPTIC.json": "987966c0c2074ab1b058bd16024806165f3e63357c51c5d46524faafc25fc558",
    "prior-t114-REPORT.md": "db21ac7d0a7845264c727132293db149a06a832d6f67700fd9ceb0f69a142cca",
    "prior-t116-REPORT.md": "573011bda281022483a113829138112494b73d667323c30aa2a0ef03bba32cd1",
}

PRIOR_PINS = {
    89: "ad90a5a5084f7ef19f4fce052ae99330f0cab9103f2942ee164d713de2a8b5b9",
    90: "730c5cdaf154bd375084a243fc82ebf6ab4ce2c1e234baf43515d4aaea34cfc0",
    91: "a684f15960a176f37ee2e8e853313e05e0e2f8de9674be2fcd744f59fe62573e",
    92: "155f1a4652f125bcf48e668315b05199a6077a943bf19f714e1e1ad02d9e19c1",
    93: "2ff685b20920f5a2d71db2b8a300ce8c2762152c3d4b2c59236b160ed812f8ae",
    94: "f399dfac1990b3cc4a6c9e69127a1ceff22356c6b656ec2e3a1b9045be6efa10",
    95: "08baad91851c1d25ceaa82f86cbe8b728ca2c063f31f01f83c5fa96aea45d8cb",
    96: "de8940fd7927a20d88626cec7ae8b411cd2788c1fdecb762496a72c8f18019aa",
    97: "fb3c58a436d173902ccf3577dc02d1702403f681d6cc08a39481e1c73cd31a8e",
    98: "b6b8d30499543fadf5be200b85afe3929dcba5b7a7d96061476965060c589f57",
    99: "9778fd0fdc3151b0e3f8888afdb1d1049347e926d266f2981e7daa3bc44af2b4",
    100: "7328d1730a68b820441f4e6c1eb9c4bbb99abb34193dbcc1270f6990a8c905fb",
    101: "ddd24794d6e6795a4aa466819782aa63a6578d70746ce4d592bb18ef644c243e",
    102: "49a63d0003102728766a41e026400f3bc69e9baeb42e66338510bcbecc1d6304",
    103: "ed690a31fbc19d08c817bcb2558ec259788e37d4f8243261ece1b9eafbbb5df0",
    104: "2dee0c91ce8480785a851df4aad06e0ab65f92e647fa7f67605b868129fc16d5",
    105: "ff63d5a956765beda402cc36e953a6f678ad1bf900254e6e2e8a20326842ed9f",
    106: "824971b102f33b41f6c2f79ad616cc03b1ce83d59aec5edafa836f2cafa89f61",
    107: "45cb809d65c38b866ad7c46c913d617c61f8e97e777ccdec8ed9645e4982ae28",
    108: "97f6333ee777b45b842530876ac5e6d29309cfe0987a1ce669690c86c8e5caee",
    109: "6b4f27464b76c67ea6fe41990f9ed6d3242c8c763b880fb4862fbac16f3ffcdf",
    110: "4eaa088ecb7ea8936d5c35d1eefb66027b376a020c8e76f4a2b91c012a3cb668",
    111: "89eae292ac15699fd7175b879189d6eb5560fd692029f8a9dbdc1093583156d8",
    112: "72884fc7d8d594cfd2f380cafde121c541c1aa316badf054ac143bb102abcefa",
    113: "30ff535624185d37981311d2f1e2a072d300221bec3f049351e5cae1026ed445",
    114: "db21ac7d0a7845264c727132293db149a06a832d6f67700fd9ceb0f69a142cca",
    115: "29cd0707df354aef8f50e4dfa4b9a780b863d93aef26cebdc4cbb8488ee27a36",
    116: "573011bda281022483a113829138112494b73d667323c30aa2a0ef03bba32cd1",
}


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def marker_value(report: str, name: str) -> int:
    match = re.search(rf"^{re.escape(name)}: ([0-9]+)$", report, re.MULTILINE)
    require(match is not None, f"missing marker {name}")
    return int(match.group(1))


def located_line(text: str, anchor: str, low: int, high: int) -> None:
    matches = [
        index
        for index, line in enumerate(text.splitlines(), start=1)
        if anchor in line
    ]
    require(
        any(low <= index <= high for index in matches),
        f"anchor {anchor!r} not in {low}..{high}: {matches}",
    )


def legendre(a: int, p: int) -> int:
    a %= p
    if a == 0:
        return 0
    value = pow(a, (p - 1) // 2, p)
    return -1 if value == p - 1 else value


def bit(a: int, p: int) -> int:
    return 1 if legendre(a, p) == 1 else 0


def cyclic_counts(p: int, m: int) -> Counter[tuple[int, ...]]:
    return Counter(tuple(bit(x + j, p) for j in range(m)) for x in range(p))


def linear_counts(p: int, m: int) -> Counter[tuple[int, ...]]:
    return Counter(
        tuple(bit(x + j, p) for j in range(m)) for x in range(p - m + 1)
    )


def error_bound(p: int, m: int) -> float:
    return m + 0.5 * m * math.sqrt(p)


def check_integrity() -> None:
    for name, expected in HASHES.items():
        actual = sha256(ROOT / name)
        require(actual == expected, f"hash mismatch {name}: {actual} != {expected}")

    report = (ROOT / "REPORT.md").read_text(encoding="utf-8")
    source_count = marker_value(report, "PRIMARY_SOURCE_COUNT")
    source_cap = marker_value(report, "PRIMARY_SOURCE_CAP")
    family_count = marker_value(report, "RETAINED_FAMILY_COUNT")
    family_cap = marker_value(report, "RETAINED_FAMILY_CAP")
    require(source_count == 2 and source_count <= source_cap == 6, "source cap/count")
    require(family_count == 1 and family_count <= family_cap == 2, "family cap/count")
    require(marker_value(report, "TERMINAL_VERDICT_COUNT") == 1, "verdict marker")
    require(marker_value(report, "SUCCESSOR_COUNT") == 0, "successor marker")
    require(report.count("TERMINAL VERDICT (1/1):") == 1, "verdict count")
    require(report.count("**HOLD AS MODEL.**") == 1, "hold verdict count")
    require("PI-TRACE (conjecture, not asserted)" in report, "PI-TRACE label")
    require(
        "This report proves no statement about pi, canonical A1, C1, C2" in report,
        "scope firewall",
    )
    require("It is therefore only an A13/A14 related model" in report, "sibling scope")

    rows = {}
    for line in report.splitlines():
        match = re.match(r"^\| T(\d+) \|", line)
        if match:
            rows[int(match.group(1))] = line
    require(set(rows) == set(range(89, 117)), f"prior rows: {sorted(rows)}")
    for item, pin in PRIOR_PINS.items():
        require(pin in rows[item], f"T{item} pin missing")
    require(
        "rejected report SHA" in rows[109]
        and "sufficient tests as necessary" in rows[109],
        "T109 status",
    )
    require(
        "accepted report SHA" in rows[114]
        and "determinant specializations and exponent comparisons proof sketch"
        in rows[114]
        and "pointwise character sums" in rows[114],
        "T114 status",
    )
    require(
        "accepted report SHA" in rows[116]
        and "selector and collision deductions proof sketch" in rows[116]
        and "pointwise subset-product cancellation" in rows[116],
        "T116 status",
    )

    source = (ROOT / "mauduit-sarkozy-1997.txt").read_text(encoding="utf-8")
    located_line(source, "Proposition 1.", 240, 260)
    located_line(source, "Theorem 1.", 370, 390)
    located_line(source, "Theorem 2.", 395, 410)
    located_line(source, "Corollary 1.", 410, 425)
    located_line(source, "Lemma 3.", 450, 465)
    located_line(source, "f (n) = (n + h1 )(n + h2 )", 520, 560)
    weil = (ROOT / "weil-1948-pnas.txt").read_text(encoding="utf-8")
    located_line(weil, "ON SOME EXPONENTIAL SUMS", 25, 35)
    located_line(weil, "all the a, have the absolute value", 110, 125)
    require(
        (ROOT / "mauduit-sarkozy-1997.pdf").read_bytes().startswith(b"%PDF-"),
        "S1 not PDF",
    )
    require(
        (ROOT / "weil-1948-pnas.pdf").read_bytes().startswith(b"%PDF-"),
        "S2 not PDF",
    )

    pins = (ROOT / "SOURCE_PINS.md").read_text(encoding="utf-8")
    require(
        pins.count("## S1:") == 1 and pins.count("## S2:") == 1,
        "source ledger count",
    )
    for name, expected in HASHES.items():
        require(expected in pins, f"pin ledger missing {name}")

    search = (ROOT / "SEARCH_LOG.md").read_text(encoding="utf-8")
    require(PRIOR_PINS[114] in search, "search log missing accepted T114 pin")
    require(PRIOR_PINS[116] in search, "search log missing accepted T116 pin")
    require("T116 unavailable" not in search, "stale T116 availability claim")

    t109_review = json.loads(
        (ROOT / "prior-t109-SKEPTIC.json").read_text(encoding="utf-8")
    )
    require(t109_review.get("verdict") == "escalate", "T109 skeptic verdict")
    require(
        "failure of sufficient upper-bound certificates"
        in t109_review.get("notes", ""),
        "T109 rejection reason",
    )
    require(
        (ROOT / "prior-t109-REPORT.md").read_text(encoding="utf-8").startswith(
            "# T109:"
        ),
        "T109 report",
    )
    t114 = (ROOT / "prior-t114-REPORT.md").read_text(encoding="utf-8")
    require(
        t114.startswith("# T114:")
        and "DELIVERY_READINESS: READY" in t114
        and "TERMINAL VERDICT (1/1): **CLOSE.**" in t114,
        "T114 accepted report status",
    )
    t116 = (ROOT / "prior-t116-REPORT.md").read_text(encoding="utf-8")
    require(
        t116.startswith("# T116:")
        and "TERMINAL_VERDICT: hold as model" in t116
        and "SUCCESSOR_COUNT: 1" in t116,
        "T116 accepted report status",
    )


def check_combinatorics() -> None:
    for m in range(1, 20):
        lhs = sum(math.comb(m, d) * d for d in range(1, m + 1))
        require(lhs == m * 2 ** (m - 1), f"subset identity m={m}")


def check_patterns() -> None:
    primes = (3, 5, 7, 11, 13, 17, 29, 43, 67, 101, 127, 199)
    checked = 0
    for p in primes:
        for m in range(1, min(p, 8) + 1):
            cyc = cyclic_counts(p, m)
            lin = linear_counts(p, m)
            require(sum(cyc.values()) == p, f"cyclic mass p={p},m={m}")
            require(
                sum(lin.values()) == p - m + 1,
                f"linear mass p={p},m={m}",
            )
            require(
                len({(-j) % p for j in range(m)}) == m,
                f"exception set p={p},m={m}",
            )

            expected = p / (2**m)
            bound = error_bound(p, m)
            for word_id in range(2**m):
                word = tuple((word_id >> (m - 1 - j)) & 1 for j in range(m))
                require(
                    abs(cyc[word] - expected) <= bound + 1e-12,
                    f"pattern bound p={p},m={m},w={word}",
                )
                require(
                    lin[word] <= cyc[word],
                    f"endpoint inclusion p={p},m={m},w={word}",
                )

            c_cyc = sum(value * value for value in cyc.values())
            c_lin = sum(value * value for value in lin.values())
            cyclic_rhs = p * (expected + bound)
            linear_rhs = (p - m + 1) * (expected + bound)
            require(
                c_cyc <= cyclic_rhs + 1e-12,
                f"cyclic collision p={p},m={m}",
            )
            require(
                c_lin <= linear_rhs + 1e-12,
                f"linear collision p={p},m={m}",
            )
            checked += 1
    print(f"FINITE_PATTERN_CASES={checked}")


def show_scale() -> None:
    for kappa in (0.25, 0.40, 0.49):
        values = []
        for p in (1009, 10007, 100003, 1000003):
            m = max(1, math.floor(kappa * math.log2(p)))
            ratio = (2**m) * error_bound(p, m) / p
            values.append(f"p={p},m={m},R={ratio:.8f}")
        print(f"KAPPA={kappa:.2f}: " + "; ".join(values))


def main() -> None:
    check_integrity()
    check_combinatorics()
    check_patterns()
    show_scale()
    print("SOURCE_COUNT=2<=6")
    print("FAMILY_COUNT=1<=2")
    print("T89_T116_ROWS=28")
    print("T117_REPLAY_OK")


if __name__ == "__main__":
    main()
