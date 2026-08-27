#!/usr/bin/env python3
import hashlib
from pathlib import Path


ROOT = Path(__file__).resolve().parent

EXPECTED = {
    "canonical_statement.txt": "cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8",
    "lyons-peres-2020-corrected.pdf": "3ba07bc0fb0397dc256610b328c869983d7ab4f709c78952d86646e25a15d043",
    "lyons-peres-2020-corrected.txt": "3f734a0413e5250be19bb227bcae28aec26350eb878101d03ba1496954aaad7a",
    "feng-lau-2002.pdf": "1ead52b41ef41987ae07067b06fb83d0f5196c40a4e88d7c3c9524ab8c3e7bec",
    "feng-lau-2002.txt": "5fe33cd079e2e54b488a7d37e193975d1f769ad5a72d850670461e87b782563e",
    "kaenmaki-sahlsten-shmerkin-2015.pdf": "6e17b161355633d4293ad2428550cbc7b919f8ee3fbfa4adb36970d5daa5783f",
    "kaenmaki-sahlsten-shmerkin-2015.txt": "b37f8b34299c37e0acb4d7010522becf8e83c64520f9e1f07a27523d3a97f64d",
    "almeida-costa-2016.pdf": "f774b8a9df74809038e95b4925867e99673f2fb055e4568e507a67bb0f2c1ce4",
    "almeida-costa-2016.txt": "57b1e48172ea02ab285dfafd9427373e28036720311e86a82cf0f4054deafc24",
}

LOCATORS = {
    "canonical_statement.txt": {
        2: "pairs are ordered and the diagonal is included",
        8: "A1 (CANONICAL)",
        23: "A16:",
    },
    "lyons-peres-2020-corrected.txt": {
        27403: "15.5 Derived Trees",
        27413: "Given a unit flow",
        27415: "for x",
        27417: "D (T)",
        27475: "Theorem 15.20.",
        27493: "Proof.",
    },
    "feng-lau-2002.txt": {
        28: "subshift",
        29: "primitive",
        85: "Theorem 1.1.",
        97: "matrices is used",
        108: "([IJ])",
        109: "Heurteaux",
        369: "Corollary 2.6.",
        380: "full",
    },
    "kaenmaki-sahlsten-shmerkin-2015.txt": {
        692: "Definition 3.1",
        710: "Definition 3.2",
        723: "Definition 3.4",
        736: "non-empty and compact",
        754: "Definition 3.7",
        767: "Write FD",
        797: "Theorem 3.10.",
        802: "quasi-Palm",
    },
    "almeida-costa-2016.txt": {
        359: "Subshifts",
        369: "Let A be a finite set.",
        371: "shift mapping",
        375: "L(X )",
        379: "is an isomorphism",
        380: "factorial, prolongable languages",
    },
}


def digest(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(block)
    return h.hexdigest()


def main() -> None:
    for name, expected in EXPECTED.items():
        actual = digest(ROOT / name)
        if actual != expected:
            raise SystemExit(f"hash mismatch for {name}: {actual} != {expected}")

    for name, checks in LOCATORS.items():
        # Locator line numbers count newline-delimited lines; form-feed page
        # markers emitted by pdftotext are content, not extra lines.
        lines = (ROOT / name).read_text(encoding="utf-8").split("\n")
        for line_number, needle in checks.items():
            actual = lines[line_number - 1]
            if needle not in actual:
                raise SystemExit(
                    f"locator mismatch for {name}:{line_number}: {needle!r} not in {actual!r}"
                )

    report = (ROOT / "REPORT.md").read_text(encoding="utf-8")
    required = (
        "start-depth anchoring",
        "predicate stability",
        "mass tightness",
        "branch quantifiers",
        "T37 artificial stream only",
        "quasiBernoulli_tangentBranch_pullback",
        "Nothing here establishes either premise for pi, C2, or canonical A1.",
    )
    for phrase in required:
        if phrase not in report:
            raise SystemExit(f"REPORT.md is missing required audit phrase: {phrase!r}")

    print(f"verified {len(EXPECTED)} retained hashes")
    print(f"verified {sum(map(len, LOCATORS.values()))} exact text locators")
    print("verified audit scope and matrix labels")


if __name__ == "__main__":
    main()
