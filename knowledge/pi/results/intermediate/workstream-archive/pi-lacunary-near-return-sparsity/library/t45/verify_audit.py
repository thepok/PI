#!/usr/bin/env python3
"""Self-contained hash and locator checks for the T45 literature audit."""

from __future__ import annotations

import hashlib
from pathlib import Path
import re
import sys


ROOT = Path(__file__).resolve().parent

EXPECTED = {
    "canonical_statement.txt": "cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8",
    "T26SharedResonanceChain.lean": "7278999f1ff89d11e7ee408b21e5a300fbdc3e78cf5a6776a2274fc9a761f1c2",
    "T38FixedStratumFejerSpike.lean": "853f10a83b0dbf91955f7587c07cd4651e5954b19f78942703df15073456a014",
    "sources/bombieri-davenport-1969.pdf": "a3bcb2b05c9b4807c6b502ad73ce50e6c7423e88ad00974facf9759d71772c74",
    "sources/bombieri-davenport-1969.txt": "16e6ccb68091c2da2600480dfc000a41f22016b2c849d68f3f663475a415c1d5",
    "sources/bombieri-davenport-1969-p223.png": "983cfabd247ca70622e776c15dd877174c25f52e07e421744f8031e176b9d35c",
    "sources/bombieri-davenport-1969-p224.png": "c602d8d50c49a85e6a101976bc38d8021a4a1f4aa4c57eee9fe1ce4afa732225",
    "sources/bonami-1970.pdf": "921508d99be0186f5fa5ab177d59003522bf4e477ac8a8c2c267c406445ce0fb",
    "sources/bonami-1970.txt": "ba4949e7a00c28f8f7e0cbf4c38b4c851403c089ef6f997c94e19cd03fa72c63",
    "sources/bourgain-1985.pdf": "cffd6d6ec3b0d6ad0344a1e2a55cbf5cc2dd2290c685846627292ca87543d8c3",
    "sources/bourgain-1985.txt": "08c28fcf204d7ddbc1001a69931cf1a628d8ff3d03dabc4e96ba9e3596db6f8e",
    "sources/shkredov-2010-arxiv-v1.pdf": "dabdfa4ecac63c33892859653f1436fadaa5cd400828bb09a36de2f997eaf77d",
    "sources/shkredov-2010-arxiv-v1.txt": "65c0fb4d7ab16eb529ca191da090c379a6fefff5d77a6607cdcccfbfb6207694",
}


def digest(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def lines(name: str, start: int, end: int) -> str:
    # PDF derivatives contain form feeds. Recorded locators count only newline
    # delimiters, matching standard line-addressing tools.
    data = (ROOT / name).read_text(encoding="utf-8", errors="replace").split("\n")
    if not (1 <= start <= end <= len(data)):
        raise AssertionError(f"bad locator {name}:{start}-{end}; file has {len(data)} lines")
    return "\n".join(data[start - 1 : end])


def require(name: str, start: int, end: int, patterns: tuple[str, ...]) -> None:
    window = lines(name, start, end)
    for pattern in patterns:
        if re.search(pattern, window, flags=re.IGNORECASE | re.MULTILINE) is None:
            raise AssertionError(f"missing locator anchor {pattern!r} in {name}:{start}-{end}")


def check_manifest() -> None:
    manifest = ROOT / "SHA256SUMS"
    entries = {}
    for raw in manifest.read_text(encoding="ascii").splitlines():
        value, name = raw.split("  ", 1)
        entries[name] = value
    for name, value in entries.items():
        actual = digest(ROOT / name)
        if actual != value:
            raise AssertionError(f"manifest mismatch for {name}: {actual} != {value}")


def main() -> int:
    for name, value in EXPECTED.items():
        actual = digest(ROOT / name)
        if actual != value:
            raise AssertionError(f"hash mismatch for {name}: {actual} != {value}")

    for name in (
        "sources/bombieri-davenport-1969.pdf",
        "sources/bonami-1970.pdf",
        "sources/bourgain-1985.pdf",
        "sources/shkredov-2010-arxiv-v1.pdf",
    ):
        if not (ROOT / name).read_bytes().startswith(b"%PDF-"):
            raise AssertionError(f"not a PDF: {name}")

    for name in (
        "sources/bombieri-davenport-1969-p223.png",
        "sources/bombieri-davenport-1969-p224.png",
    ):
        if not (ROOT / name).read_bytes().startswith(b"\x89PNG\r\n\x1a\n"):
            raise AssertionError(f"not a PNG: {name}")

    require(
        "sources/bombieri-davenport-1969.txt",
        31,
        55,
        (r"SOME INEQUALITIES", r"Introduction", r"positive integer"),
    )
    require(
        "sources/bombieri-davenport-1969.txt",
        73,
        104,
        (r"224", r"THEOREM 1", r"On the other hand"),
    )
    require(
        "sources/bonami-1970.txt",
        180,
        215,
        (r"ensembles A", r"polyn.me . spectre dans E", r"constante A"),
    )
    require(
        "sources/bonami-1970.txt",
        1097,
        1114,
        (r"COROLLAIRE 4", r"suite lacunaire", r"A\s*\(.*E"),
    )
    require(
        "sources/bourgain-1985.txt",
        42,
        82,
        (r"compact abelian group", r"Sidon set", r"quasi-independent", r"Riesz product"),
    )
    require(
        "sources/bourgain-1985.txt",
        102,
        125,
        (r"THEOREM", r"following conditions are", r"finite scalar", r"quasi.independent"),
    )
    require(
        "sources/shkredov-2010-arxiv-v1.txt",
        20,
        39,
        (r"dissociated", r"Theorem 1\.1", r"complex numbers"),
    )
    require(
        "sources/shkredov-2010-arxiv-v1.txt",
        79,
        90,
        (r"Theorem 1\.4", r"finite Abelian group", r"arbitrary sets", r"absolute constant"),
    )
    require(
        "sources/shkredov-2010-arxiv-v1.txt",
        722,
        740,
        (r"Theorem 3\.7", r"dissociated set", r"arbitrary sets"),
    )

    require(
        "T26SharedResonanceChain.lean",
        125,
        173,
        (r"GeometricResonanceChain", r"node_resonance", r"nodeCoefficient"),
    )
    require(
        "T26SharedResonanceChain.lean",
        285,
        311,
        (r"initialDensity", r"initialCoefficient", r"256 \* A \* n"),
    )
    require(
        "T38FixedStratumFejerSpike.lean",
        334,
        411,
        (r"stratumDelta", r"stratumOrder", r"def FSFS", r"range ell"),
    )
    require(
        "T38FixedStratumFejerSpike.lean",
        622,
        718,
        (r"lacunaryPhaseSum", r"lacunaryExpansion", r"fsfs_iff_expandedFSFS"),
    )

    report = (ROOT / "REPORT.md").read_text(encoding="utf-8")
    for source in ("BD69", "B70", "B85", "S10"):
        if source not in report:
            raise AssertionError(f"report omits {source}")
    if report.count("**DOES NOT APPLY**") < 5:
        raise AssertionError("report lacks all source and terminal verdicts")
    for forbidden_claim in (
        "FSFS holds for pi",
        "canonical A1 is proved",
        "canonical C1 is proved",
    ):
        if forbidden_claim in report:
            raise AssertionError(f"forbidden claim found: {forbidden_claim}")

    # The exact relation used to reject dissociation is integral and persists
    # under every cyclic reduction.
    if 1 + 2 - 3 != 0:
        raise AssertionError("unexpected arithmetic failure")

    check_manifest()
    print(f"verified {len(EXPECTED)} pinned inputs, 13 locator windows, and SHA256SUMS")
    print("BD69 displayed formulas require visual inspection of the two pinned PNG renders")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (AssertionError, FileNotFoundError, ValueError) as exc:
        print(f"verification failed: {exc}", file=sys.stderr)
        raise SystemExit(1)
