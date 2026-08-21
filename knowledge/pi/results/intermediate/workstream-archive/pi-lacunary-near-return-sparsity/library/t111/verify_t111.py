#!/usr/bin/env python3
"""Self-contained integrity and finite transcription checks for T111.

The finite checks are experiments. They do not prove the universal arguments
in REPORT.md or any statement about the decimal orbit of pi.
"""

from __future__ import annotations

import hashlib
from pathlib import Path


ROOT = Path(__file__).resolve().parent
CANONICAL_SHA = "cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8"
PDF_HASHES = {
    "fishman-merrill-simmons-2018.pdf":
        "a1aa39f1783491077c55513c737895253bb7a7323fa7eb823afac672e48924d4",
    "masakova-pelantova-0809.0603v2.pdf":
        "20087497414478431cbd704789a918b702c72687b3f8eb5e3417e1e5d98c3d43",
    "moshchevitin-0709.3419v2.pdf":
        "d6b435d06149f5b5030be9a0e31175a8b8676d64e612acee282be74fd9f874a5",
}
TEXT_HASHES = {
    "fishman-merrill-simmons-2018.txt":
        "34621967d63c119b5b1f0d25fda15804cdfbb2dafaae17e0008ec9b9eaa9eff8",
    "masakova-pelantova-0809.0603v2.txt":
        "92ea4484ae306da6859b5dee975c3497ab348e7d476a2922a7651f088472fcbc",
    "moshchevitin-0709.3419v2.txt":
        "117fc4dee8a4d5bbeef0d1d36af90599146d228f0af6529068bdd437b2ae5278",
}


def sha256(name: str) -> str:
    return hashlib.sha256((ROOT / name).read_bytes()).hexdigest()


def assert_contains(name: str, markers: list[str]) -> None:
    text = (ROOT / name).read_text(encoding="utf-8")
    for marker in markers:
        assert marker in text, f"missing marker in {name}: {marker!r}"


def blocks(word: list[int], length: int, starts: int) -> list[tuple[int, ...]]:
    return [tuple(word[i:i + length]) for i in range(starts)]


def fms_extension(old: list[int], order: int, alphabet_size: int) -> list[int]:
    """One deterministic extension from the corrected Corollary 4.3 graph.

    This is not asserted to be the lexicographically least extension used to
    define the report's point. It checks the corrected nested mechanism on
    small orders.
    """
    assert len(old) == alphabet_size ** order + order - 1
    fixed = old + [old[order - 1]]
    used_edges = {
        tuple(fixed[i:i + order + 1])
        for i in range(alphabet_size ** order)
    }
    vertices = blocks(old, order, alphabet_size ** order)
    outgoing: dict[tuple[int, ...], list[int]] = {}
    for vertex in vertices:
        allowed = []
        for digit in range(alphabet_size):
            edge = vertex + (digit,)
            if edge not in used_edges:
                allowed.append(digit)
        outgoing[vertex] = list(reversed(allowed))

    labels_reversed: list[int] = []

    def visit(vertex: tuple[int, ...]) -> None:
        while outgoing[vertex]:
            digit = outgoing[vertex].pop()
            nxt = vertex[1:] + (digit,) if order > 1 else (digit,)
            visit(nxt)
            labels_reversed.append(digit)

    visit(tuple(fixed[:order]))
    labels = list(reversed(labels_reversed))
    result = fixed + labels
    assert len(result) == alphabet_size ** (order + 1) + order
    return result


def decimal_code(block: tuple[int, ...]) -> int:
    value = 0
    for digit in block:
        value = 10 * value + digit
    return value


def check_debruijn_experiment() -> list[str]:
    alphabet_size = 4
    symbols = [0, 1, 2, 3]
    odd_digits = [1, 3, 5, 7]
    word = symbols[:]
    lines = []
    for order in range(1, 5):
        expected_starts = alphabet_size ** order
        factors = blocks(word, order, expected_starts)
        assert len(factors) == expected_starts
        assert len(set(factors)) == expected_starts
        codes = [decimal_code(tuple(odd_digits[d] for d in factor)) for factor in factors]
        assert all(code % 2 == 1 for code in codes)
        modulus = 10 ** order
        for i, left in enumerate(codes):
            for j, right in enumerate(codes):
                cyclic = min((left - right) % modulus, (right - left) % modulus)
                if cyclic <= 1:
                    assert i == j
        lines.append(
            f"order={order} starts={expected_starts} unique={len(set(factors))} "
            "cyclic_neighbors=diagonal-only"
        )
        if order < 4:
            word = fms_extension(word, order, alphabet_size)
    return lines


def check_report_contract() -> None:
    report = (ROOT / "REPORT.md").read_text(encoding="utf-8")
    pins = (ROOT / "SOURCE_PINS.md").read_text(encoding="utf-8")
    required = [
        "PRIMARY_SOURCE_COUNT: 3",
        "RETAINED_CANDIDATE_COUNT: 2",
        "SEARCHED_LANE_COUNT: 3",
        "TERMINAL_VERDICT_COUNT: 1",
        "SUCCESSOR_COUNT: 1",
        "P_x(K,c,m0)",
        "Q_x(m,N) <= (2*ceil(K*m)+1)*N",
        "TERMINAL_VERDICT: develop",
        "T109/T110",
        "first failed clause",
    ]
    for marker in required:
        assert marker in report, f"missing report contract marker: {marker!r}"
    assert report.count("TERMINAL_VERDICT:") == 1
    assert report.count("TERMINAL_VERDICT_COUNT:") == 1
    assert "TERMINAL_VERDICT: close" not in report
    assert "TERMINAL_VERDICT: hold as model" not in report
    assert report.count("### Named computable nested decimal") == 2
    assert pins.count("## S1:") == 1
    assert pins.count("## S2:") == 1
    assert pins.count("## S3:") == 1
    assert "Audit and retrieval date: 2026-08-10 UTC." in pins
    for expected in [*PDF_HASHES.values(), *TEXT_HASHES.values()]:
        assert expected in pins, f"source ledger omits hash: {expected}"

    source_locators = [
        "Corollary 4.3",
        "Remark 3.3",
        "Theorem 4.1",
        "Equation (5)",
        "Theorem 2",
        "Section 6B",
    ]
    for locator in source_locators:
        assert locator in pins, f"source ledger omits locator: {locator}"

    prior_hashes = [
        "aa0979b629131c6e30c2d8a8dc8c70499ff03d98cd35b2f49841f7669585116c",
        "a684f15960a176f37ee2e8e853313e05e0e2f8de9674be2fcd744f59fe62573e",
        "f399dfac1990b3cc4a6c9e69127a1ceff22356c6b656ec2e3a1b9045be6efa10",
        "fb3c58a436d173902ccf3577dc02d1702403f681d6cc08a39481e1c73cd31a8e",
        "ddd24794d6e6795a4aa466819782aa63a6578d70746ce4d592bb18ef644c243e",
        "8fa767cf17deb3ff7b17f94d2d57679122c7cc46e1d9d7a2286846e12ae51787",
        "97f6333ee777b45b842530876ac5e6d29309cfe0987a1ce669690c86c8e5caee",
        "ed690a31fbc19d08c817bcb2558ec259788e37d4f8243261ece1b9eafbbb5df0",
        "2dee0c91ce8480785a851df4aad06e0ab65f92e647fa7f67605b868129fc16d5",
        "ff63d5a956765beda402cc36e953a6f678ad1bf900254e6e2e8a20326842ed9f",
    ]
    for prior_hash in prior_hashes:
        assert prior_hash in report, f"report omits prior pin: {prior_hash}"

    rejection_markers = [
        "finite-only de Bruijn cycles or bounded searches",
        "almost-everywhere points",
        "subexponential-complexity words",
        "scalar irrationality or irrationality exponent",
        "previously audited automatic or fixed-morphic words",
        "previously audited paperfolding mechanism",
        "previously audited Toeplitz mechanism",
        "previously audited Stoneham mechanism",
        "**First failed clause:** exponential prefix-factor complexity.",
        "**First failed clause:** a named computable nested infinite decimal.",
        "the first failed comparison clause is",
    ]
    for marker in rejection_markers:
        assert marker in report, f"report omits rejection marker: {marker}"

    assert "source theorem `literature-checked`" in report
    assert "derivation `proof sketch`" in report
    assert "finite_checks_label=experiment" not in report
    prohibited_assertions = [
        "P_pi(K,c,m0) holds",
        "RD-pi holds",
        "the canonical statement is true",
    ]
    for assertion in prohibited_assertions:
        assert assertion not in report, f"prohibited positive assertion: {assertion}"


def main() -> None:
    assert sha256("canonical_statement.txt") == CANONICAL_SHA
    for name, expected in PDF_HASHES.items():
        assert sha256(name) == expected, f"hash mismatch: {name}"
    for name, expected in TEXT_HASHES.items():
        assert sha256(name) == expected, f"hash mismatch: {name}"

    assert_contains("fishman-merrill-simmons-2018.txt", [
        "Corollary 4.3.",
        "totally de Bruijn",
        "Remark 3.3.",
    ])
    assert_contains("masakova-pelantova-0809.0603v2.txt", [
        "Theorem 4.1",
        "Sturmian words",
        "R(n)",
    ])
    assert_contains("moshchevitin-0709.3419v2.txt", [
        "Theorem 2.",
        "Subexponentional sequen es",
        "Hausdor",
    ])
    check_report_contract()
    output = [
        "canonical_sha256=ok",
        "primary_pdf_hashes=3/3",
        "source_pdf_and_text_hashes=6/6",
        "source_anchor_sets=3/3",
        "report_contract=ok",
        *check_debruijn_experiment(),
        "finite_checks_label=experiment",
    ]
    expected_raw = (ROOT / "raw_output.txt").read_text(encoding="utf-8").splitlines()
    assert output == expected_raw, "replay output differs from raw_output.txt"
    print("\n".join(output))


if __name__ == "__main__":
    main()
