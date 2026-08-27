#!/usr/bin/env python3
"""Self-contained finite replay for the T133 proof-sketch report.

Finite checks are experiments. Universal claims rest on the displayed proofs.
"""

from __future__ import annotations

from collections import Counter
from fractions import Fraction
import hashlib
import io
import math
from pathlib import Path
import re
import subprocess
import tarfile
import tempfile


ROOT = Path(__file__).resolve().parent

EXPECTED = {
    "canonical_statement.txt": "cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8",
    "singh-venkataramana-1208.6460v2.pdf": "edc121df43a7921658c4e5ab4d728ad3021de746f9712ba5f92db933d0b0c1b3",
    "adamczewski-bell-smertnig-2003.03429v2.pdf": "c70932ece1c4cdcf5a62b39f91103c98841b3b958f3f622d58550322b9469353",
    "badziahin-zorin-1707.06677v1.pdf": "f8de296ba104cca97f4f6c3d45647e21c3db3d2207274facaf2c16b445483d15",
}

PRIOR_HASHES = {
    "T91-REPORT.md": "a684f15960a176f37ee2e8e853313e05e0e2f8de9674be2fcd744f59fe62573e",
    "T94-REPORT.md": "f399dfac1990b3cc4a6c9e69127a1ceff22356c6b656ec2e3a1b9045be6efa10",
    "T97-REPORT.md": "fb3c58a436d173902ccf3577dc02d1702403f681d6cc08a39481e1c73cd31a8e",
    "T101-REPORT.md": "ddd24794d6e6795a4aa466819782aa63a6578d70746ce4d592bb18ef644c243e",
    "T112-REPORT.md": "72884fc7d8d594cfd2f380cafde121c541c1aa316badf054ac143bb102abcefa",
    "T115-REPORT.md": "29cd0707df354aef8f50e4dfa4b9a780b863d93aef26cebdc4cbb8488ee27a36",
    "T118-REPORT.md": "2ed7a176bedb2f3a1627dffd4002f6b6141f078fe5c73798041b4fba90c7410e",
    "T124-REPORT.md": "461df40595e9d59852b7d86f8df8800b0e5fafaf6803843cb2ea1e29d737dd86",
    "T126-REPORT.md": "afa4bf0c5ef48042c68f4b938c94ecb0890c5722bc97d72e08bb9ef616e39ed8",
    "T7-FiniteCylinderEnergy.lean": "cac7b8da11c9369510e2e6e76b8bc74820b50ffe0285310475c7cf8ee1cfe91c",
    "T107-AveragedTriangularFejer.lean": "45cb809d65c38b866ad7c46c913d617c61f8e97e777ccdec8ed9645e4982ae28",
    "T133-binding-prompt.txt": "969089188470d713ae3f7d9c9a31a4fcaa07c4506894d9c280319122b45bfefc",
    "T133-orchestrator-snapshot.json": "64dd3a8dbfe1e665f0c409d1979e795a12b6ceb69a4afd99d505d34e485cc78d",
}

STATES = ("A", "X", "F")
TRANSITION = {
    "A": (("A", 0), ("X", 1), ("X", 0), ("X", -1), ("X", -2)),
    "X": (("A", 0), ("X", 1), ("X", 0), ("X", -1), ("F", 0)),
    "F": (("X", 2), ("X", 1), ("X", 0), ("X", -1), ("F", 0)),
}
TERMINAL = {"A": 0, "X": 0, "F": 2}
CARRY_CLASSES = {
    "A": {(0, 0, 0)},
    "X": {(0, 0, 1), (0, 1, 2), (1, 1, 3), (1, 2, 4)},
    "F": {(1, 2, 5)},
}


def sha_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sha_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1 << 20), b""):
            digest.update(block)
    return digest.hexdigest()


def digit_sum(n: int, base: int) -> int:
    total = 0
    while n:
        n, digit = divmod(n, base)
        total += digit
    return total


def valuation(n: int, p: int) -> int:
    result = 0
    while n and n % p == 0:
        n //= p
        result += 1
    return result


def factorial_valuation(n: int, p: int) -> int:
    result = 0
    power = p
    while power <= n:
        result += n // power
        power *= p
    return result


def u_product(n: int) -> int:
    result = 1
    for k in range(1, n + 1):
        result *= (6 * k - 5) * (6 * k - 1)
    return result


def u_factorial(n: int) -> int:
    return math.factorial(6 * n) * math.factorial(n) // (
        12**n * math.factorial(3 * n) * math.factorial(2 * n)
    )


def floor_u_valuation(n: int, p: int) -> int:
    if p in (2, 3):
        return 0
    total = 0
    power = p
    while power <= 6 * n:
        total += 6 * n // power - 3 * n // power - 2 * n // power + n // power
        power *= p
    return total


def centered_direct(n: int) -> int:
    return 2 * floor_u_valuation(n, 5) - n


def centered_digits(n: int) -> int:
    numerator = digit_sum(2 * n, 5) + digit_sum(3 * n, 5)
    numerator -= digit_sum(6 * n, 5) + digit_sum(n, 5)
    assert numerator % 2 == 0
    return numerator // 2


def transducer(n: int, digits: int) -> int:
    assert 0 <= n < 5**digits
    state = "A"
    total = 0
    for _ in range(digits):
        n, digit = divmod(n, 5)
        state, weight = TRANSITION[state][digit]
        total += weight
    return total + TERMINAL[state]


def carry_class(triple: tuple[int, int, int]) -> str:
    matches = [state for state, triples in CARRY_CLASSES.items() if triple in triples]
    assert len(matches) == 1, triple
    return matches[0]


def verify_transition_table() -> None:
    count = 0
    for state in STATES:
        expected_for_class = None
        for triple in CARRY_CLASSES[state]:
            row = []
            for digit in range(5):
                c2, c3, c6 = triple
                nxt = ((2 * digit + c2) // 5, (3 * digit + c3) // 5, (6 * digit + c6) // 5)
                nxt_state = carry_class(nxt)
                weight = -digit + 2 * (nxt[2] - nxt[1] - nxt[0])
                row.append((nxt_state, weight))
                count += 1
            if expected_for_class is None:
                expected_for_class = tuple(row)
            assert tuple(row) == expected_for_class
        assert expected_for_class == TRANSITION[state]
    assert count == 30  # 6 carry triples times 5 digits
    print("TRANSITIONS OK all 15 quotient transitions from all 30 carry transitions")


def extremal_dp(k: int) -> dict[str, tuple[int, int]]:
    values = {state: (TERMINAL[state], TERMINAL[state]) for state in STATES}
    for _ in range(k):
        new = {}
        for state in STATES:
            lows = []
            highs = []
            for nxt, weight in TRANSITION[state]:
                low, high = values[nxt]
                lows.append(weight + low)
                highs.append(weight + high)
            new[state] = (min(lows), max(highs))
        values = new
    return values


def alpha(n: int) -> int:
    return 2 * n + 2 * factorial_valuation(n, 2)


def beta(n: int) -> int:
    return 2 * n + 2 * factorial_valuation(n, 3)


def coefficient(n: int) -> Fraction:
    return Fraction(u_product(n), 36**n * math.factorial(n) ** 2)


def order(n: int) -> int:
    exponent = beta(n)
    return 1 if exponent <= 2 else 3 ** (exponent - 2)


def occupancy_formula(n: int, prefix: int) -> int:
    a = alpha(n)
    if prefix <= a:
        return prefix
    length = prefix - a
    d = order(n)
    quotient, remainder = divmod(length, d)
    return a + remainder * (quotient + 1) ** 2 + (d - remainder) * quotient**2


def occupancy_direct(n: int, prefix: int) -> int:
    value = coefficient(n)
    modulus = value.denominator
    labels = [(value.numerator * pow(10, j, modulus)) % modulus for j in range(prefix)]
    counts = Counter(labels)
    return sum(count * count for count in counts.values())


def threshold(m: int) -> int:
    n = 0
    while floor_u_valuation(n, 5) < m:
        n += 1
    return n


def check_hashes_and_sources() -> None:
    for name, expected in EXPECTED.items():
        actual = sha_file(ROOT / name)
        assert actual == expected, (name, actual, expected)
        print(f"HASH OK {name} {actual}")
    for name in EXPECTED:
        if name.endswith(".pdf"):
            assert (ROOT / name).read_bytes()[:4] == b"%PDF"

    anchors = {
        "singh-venkataramana-1208.6460v2.pdf": ("Set θ", "D = (θ + β1 − 1)"),
        "adamczewski-bell-smertnig-2003.03429v2.pdf": ("Definition 3.3", "Theorem 3.5"),
        "badziahin-zorin-1707.06677v1.pdf": ("t2n = tn", "fT M (z 2 )"),
    }
    with tempfile.TemporaryDirectory() as temp:
        for name, needles in anchors.items():
            output = Path(temp) / (name + ".txt")
            subprocess.run(
                ["pdftotext", "-layout", str(ROOT / name), str(output)],
                check=True,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
            )
            text = output.read_text(encoding="utf-8")
            for needle in needles:
                assert needle in text, (name, needle)
    print("SOURCE ANCHORS OK exact bounded PDF-text anchors")


def check_prior_archive() -> None:
    seen = {}
    with tarfile.open(ROOT / "prior_evidence.tar.gz", "r:gz") as archive:
        for member in archive.getmembers():
            if not member.isfile():
                continue
            extracted = archive.extractfile(member)
            assert extracted is not None
            seen[Path(member.name).name] = sha_bytes(extracted.read())
    assert seen == PRIOR_HASHES, (seen.keys(), PRIOR_HASHES.keys())
    print(f"PRIOR ARCHIVE OK {len(seen)} byte-pinned members")


def check_report_contract() -> None:
    report = (ROOT / "REPORT.md").read_text(encoding="utf-8")
    pins = (ROOT / "SOURCE_PINS.md").read_text(encoding="utf-8")
    search = (ROOT / "SEARCH_LOG.md").read_text(encoding="utf-8")

    def marker(name: str) -> int:
        matches = re.findall(rf"^{re.escape(name)}: ([0-9]+)$", report, re.MULTILINE)
        assert len(matches) == 1, (name, matches)
        return int(matches[0])

    assert report.count("SCOPED_VERDICT: CLOSE") == 1
    assert report.count("SCOPED_VERDICT:") == 1
    assert report.count("## 12. Scoped verdict") == 1
    assert report.rstrip().endswith("SCOPED_VERDICT: CLOSE")
    assert marker("TERMINAL_VERDICT_COUNT") == 1
    assert marker("SUCCESSOR_COUNT") <= 1
    assert marker("SEARCHED_DOMAIN_COUNT") == 3
    assert marker("PRIMARY_SOURCE_COUNT") <= 12
    assert marker("CANDIDATE_CARD_COUNT") <= 4
    assert marker("RETAINED_CANDIDATE_COUNT") <= 4
    assert marker("PRE_KILL_SURVIVOR_COUNT") == 1
    assert marker("POST_KILL_SURVIVOR_COUNT") == 0
    assert len(re.findall(r"^\| S[1-9][0-9]* \|", pins, re.MULTILINE)) == marker("PRIMARY_SOURCE_COUNT")
    assert len(re.findall(r"^\| C-[A-Z0-9]+ \|", report, re.MULTILINE)) == marker("CANDIDATE_CARD_COUNT")
    for domain in ("hypergeometric arithmetic", "automatic or regular sequences", "Mahler functional equations"):
        assert domain in report
    assert "Restricted-denominator approximation and structured\nexponential sums were not searched." in report
    assert "CANDIDATE_CARD_COUNT: 3" in search
    assert "RETAINED_CANDIDATE_COUNT: 1" in search
    assert "unproved additional arithmetic-continuation" in report
    assert "no fixed-pi, C1, or C2" in report
    for item in ("T91", "T94", "T97", "T101", "T112", "T115", "T118", "T124", "T126", "T131", "T132"):
        assert f"| {item}" in report or f"| active {item}" in report
    print("REPORT CONTRACT OK numeric caps, cards, comparisons, premise, one verdict, zero successors")


def check_valuation_identity_and_transducer() -> None:
    primes = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31)
    for n in range(0, 101):
        assert u_product(n) == u_factorial(n)
        u = u_product(n)
        for p in primes:
            assert valuation(u, p) == floor_u_valuation(n, p)
        assert centered_direct(n) == centered_digits(n)
        digits = 0
        bound = 1
        while bound <= n:
            digits += 1
            bound *= 5
        assert transducer(n, digits) == centered_direct(n)
    print("VALUATIONS OK product/factorial/floor/digit/transducer n=0..100")


def check_extrema() -> None:
    expected_rows = {
        0: {"A": (0, 0), "X": (0, 0), "F": (2, 2)},
        1: {"A": (-2, 1), "X": (-1, 2), "F": (-1, 2)},
    }
    for k, expected in expected_rows.items():
        assert extremal_dp(k) == expected
    for k in range(2, 11):
        expected = {"A": (-(k + 1), k + 1), "X": (-k, k + 1), "F": (-k, k + 2)}
        assert extremal_dp(k) == expected
    for r in range(1, 9):
        values = [transducer(n, r) for n in range(5**r)]
        expected_max = 1 if r == 1 else r + 1
        assert min(values) == -(r + 1)
        assert max(values) == expected_max
        min_witness = int("3" * (r - 1) + "4", 5)
        assert transducer(min_witness, r) == -(r + 1)
        if r == 1:
            assert transducer(1, 1) == 1
        else:
            max_witness = int("4" + "1" * (r - 1), 5)
            assert transducer(max_witness, r) == r + 1
        print(f"EXTREMA EXPERIMENT r={r} min={min(values)} max={max(values)}")
    print("EXTREMAL DP OK exact symbolic rows k=0..10 and brute blocks r=1..8")


def check_reduction_threshold_order_occupancy() -> None:
    for n in range(1, 41):
        value = coefficient(n)
        expected_alpha = 4 * n - 2 * digit_sum(n, 2)
        expected_beta = 3 * n - digit_sum(n, 3)
        assert alpha(n) == expected_alpha
        assert beta(n) == expected_beta
        assert value.denominator == 2**expected_alpha * 3**expected_beta
        assert math.gcd(value.numerator, 6) == 1
        expected_v5_numerator = (centered_direct(n) + digit_sum(n, 5)) // 2
        assert valuation(value.numerator, 5) == expected_v5_numerator
        for j in range(expected_alpha + 3):
            assert (value * 10**j).denominator == 2 ** max(expected_alpha - j, 0) * 3**expected_beta
    for m in range(1, 101):
        tau = threshold(m)
        radius = math.ceil(math.log(4 * m + 4, 5))
        assert 2 * m - radius - 1 <= tau <= 2 * m + radius + 1
    for n in range(1, 5):
        d = order(n)
        modulus = 3 ** beta(n)
        assert pow(10, d, modulus) == 1
        if d > 1:
            assert pow(10, d // 3, modulus) != 1
        for prefix in (alpha(n), alpha(n) + d, alpha(n) + 2 * d + min(7, d)):
            assert occupancy_direct(n, prefix) == occupancy_formula(n, prefix)
    print("REDUCTION/THRESHOLD/ORDER/OCCUPANCY OK bounded exact replay")


def check_kill_substitution() -> None:
    for agenda_a in (1, 2, 5, 10, 25):
        for n in range(max(agenda_a, 2), max(agenda_a, 2) + 25):
            d = order(n)
            length = agenda_a * n
            prefix = alpha(n) + length
            q = coefficient(n).denominator
            assert length <= n * n <= 9 ** (n - 1) <= d
            assert occupancy_formula(n, prefix) == prefix
            assert agenda_a * n * prefix <= prefix * prefix
            assert 2 * n * math.log(6) <= math.log(q) + 1e-12
            assert math.log(q) <= n * (4 * math.log(2) + 3 * math.log(3)) + 1e-12
            assert (agenda_a + 2) * n <= prefix <= (agenda_a + 4) * n
    print("N ASYMP LOG Q KILL TEST OK bounded substitutions")


def main() -> None:
    print("All finite calculations below are EXPERIMENT checks, not universal proofs.")
    check_hashes_and_sources()
    check_prior_archive()
    check_report_contract()
    verify_transition_table()
    check_valuation_identity_and_transducer()
    check_extrema()
    check_reduction_threshold_order_occupancy()
    check_kill_substitution()
    print("T133 REPLAY PASS")


if __name__ == "__main__":
    main()
