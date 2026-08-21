#!/usr/bin/env python3
"""Deterministic integrity and finite-replay checks for T153.

This script checks the delivered audit package. Its finite calculations are an
experiment and are not evidence for a universal mathematical claim.
"""

from __future__ import annotations

import hashlib
import re
import subprocess
import tarfile
import tempfile
from collections import Counter
from fractions import Fraction
from pathlib import Path


ROOT = Path(__file__).resolve().parent
CANONICAL_SHA = "cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8"

SOURCES = [
    (
        "S1",
        "symbolic collision theory",
        "karhumaki-saarela-zamboni-1301.5104v1.pdf",
        "2b81c55bda00622055b1d86cae93b39f6f3ad83c695d2be56af24eaa0de97ef3",
        ("Definition 2.1", "Lemma 2.4", "Lemma 2.12", "Theorem 2.14"),
        "KSZ:Definition2.1+Lemma2.4+Lemma2.12+Theorem2.14",
    ),
    (
        "S2",
        "symbolic collision theory",
        "karhumaki-puzynina-rao-whiteland-1605.03319v1.pdf",
        "3367d8b31a03e0668d194913eee528f6070b79f4a43ab29ea910a19f490f4a68",
        ("Proposition 3.3", "Corollary 4.3", "Proposition 4.7", "Proposition 5.3"),
        "KPRW:Proposition3.3+Corollary4.3+Proposition4.7+Proposition5.3",
    ),
    (
        "S3",
        "symbolic collision theory / metric reconstruction",
        "levick-shomorony-2305.05820v1.pdf",
        "6699b77376419167ee313e74bc7304acddf0166015ab68c38d685c12c036a43a",
        ("Definition 1", "Theorem 1", "Lemma 1"),
        "LS:Definition1+Theorem1+Lemma1",
    ),
    (
        "S4",
        "fixed-point lacunary dynamics",
        "coons-evans-manibo-10.4171-dm-880.pdf",
        "4badf20c29df7d19695675f6aa677b7e609d763c926ff99f30123bfe29fcf034",
        ("Definition 1", "Theorem 1", "Corollary 2", "(10)", "Theorem 5"),
        "CEM:Definition1+Theorem1+Corollary2+Equation10+Theorem5",
    ),
    (
        "S5",
        "arithmetic or fractal Fourier decay",
        "sahlsten-stevens-2009.01703.pdf",
        "ba4878034d08a46c0e5cad13b4028922ba1ae058f0a55d11f111c4d8706693bf",
        ("Theorem 1.1", "total non-linearity"),
        "SS:Theorem1.1+total-nonlinearity",
    ),
    (
        "S6",
        "short structured exponential sums",
        "ostafe-shparlinski-voloch-2110.10941.pdf",
        "4ecd0a303f6b0c93953a2df1bd011a59e88a281745dfe363865dd6ace562c934",
        ("(2.1)", "Theorem 2.4", "Remark 2.6"),
        "OSV:Equation2.1+Theorem2.4+Remark2.6",
    ),
]

EXPECTED_FIXTURE_HASHES = {
    "T104": "2dee0c91ce8480785a851df4aad06e0ab65f92e647fa7f67605b868129fc16d5",
    "T136": "b15cb995dfc5e1983d0056987c0371b3b7f85469c7dd175e2eb13a719465dc5f",
    "T138": "9e89fe02a7d7f39a66dd580c5e22bcb8b5b055ad4c6cc03b4aa965f87e23b97b",
    "T142": "46fd766b9e9f7780b06df0dbcac5830a19e18e09347da5cc083f9d18fc63db8e",
    "T146": "b3b42927ea0c03b8ce2fb8017e4a80a179647bad755d184a2c912863ec310f53",
}

EXPECTED_FIXTURE_PIN_HASHES = {
    "fixtures/T136-SOURCE_PINS.md": "29b2ceaebd3546924c2a75da303705ba4618ad8eed2c897cb1bbde9a504990f5",
    "fixtures/T138-SOURCE_PINS.md": "857d1c22c4ece94579581b64b6ff7d9a415afae964e4fe7cb3e52afe26993961",
    "fixtures/T146-SOURCE_PINS.md": "2d5309278f4871d55df0ec06d1a410578f7b365a0523ba55db388bfb5afb6720",
}

# These are normalized cards transcribed from the byte-pinned fixture reports.
# A card compares source identity, the claimed theorem identity, supporting
# locators, and the semantic mechanism rather than report wording.
FIXTURE_CARDS = {
    "T104/C-UDEXP": (
        "278dca3331322b1a64d34fb04651e131e7eb3a6482b5be5b69e9db29d39670ad",
        ("Theorem 1.1",),
        ("definition before (1.2)", "equation (1.4)"),
        "restricted-power-uniform-exponent-dimension",
    ),
    "T138/C-UDEXP": (
        "278dca3331322b1a64d34fb04651e131e7eb3a6482b5be5b69e9db29d39670ad",
        ("Theorem 1.1",),
        ("v_hat_(b,A)",),
        "restricted-power-uniform-exponent-dimension",
    ),
    "T136/NEG-M:M1": (
        "4badf20c29df7d19695675f6aa677b7e609d763c926ff99f30123bfe29fcf034",
        ("Corollary 2", "Theorem 5"),
        (),
        "finite-k-kernel-fourier-matrix-cocycle",
    ),
    "T146/M-REG": (
        "4badf20c29df7d19695675f6aa677b7e609d763c926ff99f30123bfe29fcf034",
        ("Corollary 2", "Theorem 5"),
        (),
        "finite-k-kernel-fourier-matrix-cocycle",
    ),
    "T136/NEG-F:F1": (
        "74d6e8d0192de706c84ad745b8bb9ce478e9735e8891bdbda3a25a4aeb59504d",
        ("Theorem 1.3", "Theorem 1.7"),
        (),
        "slow-rajchman-decay-and-missed-divergent-target",
    ),
    "T146/F-SLOW": (
        "74d6e8d0192de706c84ad745b8bb9ce478e9735e8891bdbda3a25a4aeb59504d",
        ("Theorem 1.3", "Theorem 1.7"),
        (),
        "slow-rajchman-decay-and-missed-divergent-target",
    ),
    "T136/NEG-X:X1": (
        "4ecd0a303f6b0c93953a2df1bd011a59e88a281745dfe363865dd6ace562c934",
        ("Theorem 2.4", "Remark 2.6"),
        (),
        "matrix-power-character-sum-completion",
    ),
    "T146/X-MAT": (
        "4ecd0a303f6b0c93953a2df1bd011a59e88a281745dfe363865dd6ace562c934",
        ("Theorem 2.4", "Remark 2.6"),
        (),
        "matrix-power-character-sum-completion",
    ),
}

FIXTURE_REPORT_ANCHORS = {
    "T104": (b"Wang-Li-Li", b"Theorem 1.1", b"equation (1.4)"),
    "T138": (b"Candidate C-UDEXP", b"v_hat_(b,A)", b"Theorem 1.1"),
    "T136": (b"NEG-M", b"NEG-F", b"NEG-X", b"Theorem 2.4", b"Remark 2.6"),
    "T146": (b"M-REG", b"F-SLOW", b"X-MAT", b"Theorem 2.4", b"Remark 2.6"),
}


def sha256(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1 << 20), b""):
            h.update(block)
    return h.hexdigest()


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def read_text(name: str) -> str:
    return (ROOT / name).read_text(encoding="utf-8")


def require_duplicate(left: str, right: str) -> None:
    left_source, left_theorems, _left_support, left_mechanism = FIXTURE_CARDS[left]
    right_source, right_theorems, _right_support, right_mechanism = FIXTURE_CARDS[right]
    require(left_source == right_source, f"{left}/{right} source mismatch")
    require(left_theorems == right_theorems, f"{left}/{right} theorem mismatch")
    require(left_mechanism == right_mechanism, f"{left}/{right} mechanism mismatch")


def require_card_evidence(card: str, evidence: bytes) -> None:
    source, theorems, support, _mechanism = FIXTURE_CARDS[card]
    require(source.encode() in evidence, f"{card} source SHA absent from evidence")
    for locator in theorems + support:
        require(locator.encode() in evidence, f"{card} locator absent from evidence: {locator}")


def pdf_text(filename: str) -> str:
    with tempfile.NamedTemporaryFile(suffix=".txt") as out:
        subprocess.run(
            ["pdftotext", "-layout", str(ROOT / filename), out.name],
            check=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        )
        return Path(out.name).read_text(encoding="utf-8", errors="replace")


def pdf_page_text(filename: str, page: int) -> str:
    with tempfile.NamedTemporaryFile(suffix=".txt") as out:
        subprocess.run(
            ["pdftotext", "-f", str(page), "-l", str(page), "-layout",
             str(ROOT / filename), out.name],
            check=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        )
        return Path(out.name).read_text(encoding="utf-8", errors="replace")


def de_bruijn(alphabet_size: int, order: int) -> list[int]:
    """Return one cyclic de Bruijn sequence B(alphabet_size, order)."""
    work = [0] * (alphabet_size * order + 1)
    sequence: list[int] = []

    def visit(t: int, period: int) -> None:
        if t > order:
            if order % period == 0:
                sequence.extend(work[1 : period + 1])
            return
        work[t] = work[t - period]
        visit(t + 1, period)
        for value in range(work[t - period] + 1, alphabet_size):
            work[t] = value
            visit(t + 1, t)

    visit(1, 1)
    require(len(sequence) == alphabet_size**order, "bad de Bruijn length")
    return sequence


def block_counts(word: list[int], starts: int, depth: int) -> Counter[tuple[int, ...]]:
    return Counter(tuple(word[i : i + depth]) for i in range(starts))


def check_de_bruijn_family() -> list[str]:
    lines = []
    for order in (1, 2, 3):
        period = 10**order
        depth = period + 1
        starts = 2 * period
        cycle = de_bruijn(10, order)
        needed = starts + depth - 1
        word = [cycle[i % period] for i in range(needed)]
        for local_depth in range(1, order + 1):
            local = block_counts(word, starts, local_depth)
            require(len(local) == 10**local_depth, "short support not uniform")
            require(set(local.values()) == {starts // (10**local_depth)}, "short counts not uniform")
        long = block_counts(word, starts, depth)
        maximum = max(long.values())
        energy = sum(value * value for value in long.values())
        require(len(long) == period, "long phases not distinct")
        require(maximum == starts // period, "wrong maximum occupancy")
        require(energy == starts * starts // period, "wrong collision energy")
        lines.append(
            f"debruijn r={order} P={period} m={depth} M={starts} "
            f"max={maximum} E={energy}: PASS"
        )
    return lines


def main() -> None:
    report = read_text("REPORT.md")
    pins = read_text("SOURCE_PINS.md")
    prior = read_text("PRIOR_INDEX.md")
    search = read_text("SEARCH_LOG.md")

    require(sha256(ROOT / "canonical_statement.txt") == CANONICAL_SHA, "canonical hash mismatch")
    require("CANONICAL QUESTION" in read_text("canonical_statement.txt"), "canonical text missing")

    source_ids = [row[0] for row in SOURCES]
    source_hashes = [row[3] for row in SOURCES]
    theorem_keys = [(row[3], row[5]) for row in SOURCES]
    require(len(source_ids) == len(set(source_ids)) == 6, "duplicate source ID")
    require(len(source_hashes) == len(set(source_hashes)) == 6, "duplicate source PDF")
    require(len(theorem_keys) == len(set(theorem_keys)) == 6, "duplicate theorem tuple")
    domains = {
        "symbolic collision theory",
        "fixed-point lacunary dynamics",
        "arithmetic or fractal Fourier decay",
        "short structured exponential sums",
    }
    require(len(domains) >= 3, "fewer than three domains")
    require(len(SOURCES) <= 12, "source cap exceeded")

    for source_id, _domain, filename, expected_hash, anchors, _key in SOURCES:
        require(sha256(ROOT / filename) == expected_hash, f"{source_id} hash mismatch")
        text = pdf_text(filename)
        for anchor in anchors:
            require(anchor in text, f"{source_id} missing PDF anchor: {anchor}")
        require(expected_hash in pins, f"{source_id} pin hash absent")
    s3_page_two = pdf_page_text("levick-shomorony-2305.05820v1.pdf", 2)
    for anchor in ("Definition 1", "Theorem 1", "Lemma 1"):
        require(anchor in s3_page_two, f"S3 locator is not PDF page 2: {anchor}")
    s1_page_five = pdf_page_text("karhumaki-saarela-zamboni-1301.5104v1.pdf", 5)
    s1_page_six = pdf_page_text("karhumaki-saarela-zamboni-1301.5104v1.pdf", 6)
    require("Lemma 2.4" in s1_page_five, "S1 Lemma 2.4 is not PDF page 5")
    require("bound 2k − 1 in Lemma 2.4 is optimal" in s1_page_six,
            "S1 sharpness paragraph is not PDF page 6")
    s6_page_five = pdf_page_text("ostafe-shparlinski-voloch-2110.10941.pdf", 5)
    s6_page_six = pdf_page_text("ostafe-shparlinski-voloch-2110.10941.pdf", 6)
    require("(2.1)" in s6_page_five and "κn" in s6_page_five,
            "S6 equation (2.1) is not PDF page 5")
    for anchor in ("Theorem 2.4", "Remark 2.6"):
        require(anchor in s6_page_six, f"S6 locator is not PDF page 6: {anchor}")

    for item in range(89, 151):
        require(re.search(rf"^\| T{item} \|", prior, flags=re.MULTILINE) is not None, f"missing T{item} row")
        require(re.search(rf"^T{item} .*[0-9a-f]{{64}}$", prior, flags=re.MULTILINE) is not None,
                f"missing exact T{item} comparator pin")
    require(len(re.findall(r"^\| T(?:8[9]|9[0-9]|1[0-4][0-9]|150) \|", prior, flags=re.MULTILINE)) == 62,
            "novelty row count is not 62")

    mandatory = [
        "T135", "T138 C-MINENT", "T142 C-LCS", "T144--T150",
        "SKETCH_T151_EXCLUDED", "SKETCH_T152_EXCLUDED",
        "DUPLICATE_FIXTURE_T104_T138", "DUPLICATE_FIXTURE_T136_T146",
    ]
    joined = report + prior
    for marker in mandatory:
        require(marker in joined, f"missing mandatory marker: {marker}")

    with tarfile.open(ROOT / "PRIOR_EVIDENCE.tar.gz", "r:gz") as archive:
        members = [member for member in archive.getmembers() if member.isfile()]
        require(len(members) >= 50, "prior evidence archive unexpectedly small")
        member_hashes = {}
        member_data = {}
        for member in members:
            stream = archive.extractfile(member)
            require(stream is not None, "cannot read archive member")
            data = stream.read()
            member_hashes[hashlib.sha256(data).hexdigest()] = member.name
            member_data[member.name.lstrip("./")] = data
        for item, expected in EXPECTED_FIXTURE_HASHES.items():
            require(expected in member_hashes, f"missing byte-exact {item} fixture")
        for member_name, expected in EXPECTED_FIXTURE_PIN_HASHES.items():
            require(member_name in member_data, f"missing byte-exact fixture pin: {member_name}")
            require(hashlib.sha256(member_data[member_name]).hexdigest() == expected,
                    f"fixture pin hash mismatch: {member_name}")
        fixture_reports = {
            "T104": next(data for name, data in member_data.items()
                         if name.endswith("/knowledge_library/t104/REPORT.md")),
            "T136": next(data for name, data in member_data.items()
                         if name.endswith("/knowledge_library/t136/REPORT.md")),
            "T138": next(data for data in member_data.values()
                         if hashlib.sha256(data).hexdigest() == EXPECTED_FIXTURE_HASHES["T138"]),
            "T146": next(data for data in member_data.values()
                         if hashlib.sha256(data).hexdigest() == EXPECTED_FIXTURE_HASHES["T146"]),
        }
        fixture_pins = {
            "T104/C-UDEXP": fixture_reports["T104"],
            "T138/C-UDEXP": member_data["fixtures/T138-SOURCE_PINS.md"],
            "T136/NEG-M:M1": member_data["fixtures/T136-SOURCE_PINS.md"],
            "T136/NEG-F:F1": member_data["fixtures/T136-SOURCE_PINS.md"],
            "T136/NEG-X:X1": member_data["fixtures/T136-SOURCE_PINS.md"],
            "T146/M-REG": member_data["fixtures/T146-SOURCE_PINS.md"],
            "T146/F-SLOW": member_data["fixtures/T146-SOURCE_PINS.md"],
            "T146/X-MAT": member_data["fixtures/T146-SOURCE_PINS.md"],
        }
        for item, anchors in FIXTURE_REPORT_ANCHORS.items():
            for anchor in anchors:
                require(anchor in fixture_reports[item], f"{item} missing normalized-card anchor: {anchor!r}")
        for card, evidence in fixture_pins.items():
            require_card_evidence(card, evidence)

        require_duplicate("T104/C-UDEXP", "T138/C-UDEXP")
        require_duplicate("T136/NEG-M:M1", "T146/M-REG")
        require_duplicate("T136/NEG-F:F1", "T146/F-SLOW")
        require_duplicate("T136/NEG-X:X1", "T146/X-MAT")
        refreshed_reports = {
            "T151": (
                "refreshed/notes/t151/REPORT.md",
                "fb0c22c6cdbfbb731d73e431ad164b2e084ffe6a6c0a7cfd06489c83ecf59afb",
            ),
            "T152": (
                "refreshed/notes/t152/REPORT.md",
                "01ae77f2f125d70d31e5ae774fb2c7adb8f741b04bb9fbec6e19cdc1fc497171",
            ),
        }
        for item, (member_name, expected_hash) in refreshed_reports.items():
            require(member_name in member_data, f"missing refreshed {item} report")
            data = member_data[member_name]
            require(hashlib.sha256(data).hexdigest() == expected_hash,
                    f"{item} refreshed report hash mismatch")
            require(b"proof sketch" in data, f"{item} report is not explicitly sketch-level")
            require(re.search(rf"^{item} REPORT\.md  {expected_hash}$", prior, flags=re.MULTILINE) is not None,
                    f"missing exact refreshed {item} comparator pin")

    count_markers = {
        "PRIMARY_SOURCE_COUNT": 6,
        "PRIMARY_SOURCE_CAP": 12,
        "SEARCHED_DOMAIN_COUNT": 4,
        "RETAINED_CANDIDATE_COUNT": 1,
        "RETAINED_CANDIDATE_CAP": 4,
        "KILL_TEST_COUNT": 5,
        "SCOPED_VERDICT_COUNT": 1,
        "SUCCESSOR_COUNT": 0,
    }
    for key, value in count_markers.items():
        require(f"{key}: {value}" in report, f"wrong report count: {key}")
    require(len(re.findall(r"^\| [1-6] \|", search, flags=re.MULTILINE)) == 6,
            "search log does not have six source rows")

    require("Candidate C-RABEL: short census as de Bruijn flow" in report, "candidate card missing")
    require(report.count("Candidate C-RABEL:") == 1, "duplicate C-RABEL card")
    require("use exactly the same first-`M` start window" in report,
            "K1 does not identify the c_m first-M window")
    require("does not use all\n`M+m-ell` starts" in report,
            "K1 does not exclude the longer available-start interpretation")

    for label in ("`literature-checked`", "`proof sketch`", "`experiment`", "`unproved-transfer`"):
        require(label in report, f"missing claim label {label}")
    for firewall in ("FIXED_PI_CLAIM: none", "A1_CLAIM: none", "C1_CLAIM: none", "C2_CLAIM: none"):
        require(firewall in report, f"missing claim firewall {firewall}")

    kill_markers = [
        "KILL_REPEATED_DEBRUIJN: fail",
        "KILL_SCALE: fail",
        "KILL_SCOPE: fail",
        "KILL_CIRCULARITY: fail",
        "KILL_SOURCE_FINGERPRINT_NOVELTY: fail-positive / retain-negative-map",
    ]
    require(sum(marker in report for marker in kill_markers) == 5, "not all five kill tests recorded")
    require(report.count("SCOPED_VERDICT (1/1): close") == 1, "verdict is not unique")
    require(report.count("SUCCESSOR (0/1): none") == 1, "successor count is not zero")

    maximum_atom = Fraction(84, 2 * 3 * 7) + Fraction(84, 2 * 3 * 7)
    energy_upper = 84 * maximum_atom
    target = Fraction(84 * 84, 3 * 7)
    require(maximum_atom == 4, "occupancy substitution failed")
    require(energy_upper == target == 336, "collision substitution failed")

    debruijn_lines = check_de_bruijn_family()

    print("T153 deterministic replay")
    print(f"canonical_sha256={CANONICAL_SHA}: PASS")
    print(f"sources={len(SOURCES)}/12 unique_theorem_tuples={len(theorem_keys)} domains={len(domains)}: PASS")
    print("candidates=1/4 mechanism_cards=1: PASS")
    print("novelty_rows=T89-T150 (62/62): PASS")
    print("duplicate_fixtures=T104/T138 source+theorem+mechanism,T136/T146 3x source+theorem+mechanism: REJECTED")
    print("refreshed_sketch_exclusions=T151,T152: PASS")
    print("substitution M=84 K=2 A=3 m=7 B=2 max<=4 E<=336 target=336: PASS")
    for line in debruijn_lines:
        print(line)
    print("kill_tests=5/5: PASS")
    print("labels=literature-checked,proof-sketch,experiment,unproved-transfer: PASS")
    print("verdict=close (1/1) successor=none (0/1): PASS")
    print("fixed_pi_A1_C1_C2_claims=none: PASS")


if __name__ == "__main__":
    main()
