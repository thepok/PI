#!/usr/bin/env python3
"""Prepare and audit an isolated native-toolchain build of pinned PiExponent.

This does not add an upstream result to PI's formal library.  The source audit
is a guard around the native build, literal statement checks, and axiom report;
it is not itself a Lean parser or a replacement for kernel checking.
"""

from __future__ import annotations

import argparse
import copy
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys


UPSTREAM_REV = "1581d4cbdd69a0faf34b2089614fe2a814316a6a"
TOOLCHAIN = "leanprover/lean4:v4.34.1\n"
ROOT_MODULE = "OAI.NumberTheory.PiExponent.Main"
PROOF_PREFIX = "OAI.NumberTheory.PiExponent."
EXPECTED_MODULES = 869
ALLOWED_AXIOMS = frozenset({"propext", "Classical.choice", "Quot.sound"})
THEOREMS = (
    "OAI.PiExponent.main",
    "OAI.PiExponent.pi_eventual_lower_bound",
    "OAI.PiExponent.pi_irrationalityExponent_eq_two",
    "OAI.PiExponent.flint_hills_summable",
)
PACKAGE_PINS = {
    "mathlib": ("https://github.com/leanprover-community/mathlib4.git",
                "d13f23b723b8a846827a245b89c10fc7d3f11612"),
    "plausible": ("https://github.com/leanprover-community/plausible",
                  "118aa17ee84656b8bd727fef7c458ee8c833385c"),
    "LeanSearchClient": ("https://github.com/leanprover-community/LeanSearchClient",
                         "ddf04cf3949fa556442341e87d47f9f6e6074707"),
    "importGraph": ("https://github.com/leanprover-community/import-graph",
                    "e928b72544873815af278d38681b31c0293588e3"),
    "proofwidgets": ("https://github.com/leanprover-community/ProofWidgets4",
                     "106ff4fafc74ef4ac99d81dbf3ab399118f497a5"),
    "aesop": ("https://github.com/leanprover-community/aesop",
              "355695d523e41d0554926416cba2a2b3544fbbc9"),
    "Qq": ("https://github.com/leanprover-community/quote4",
           "6a489d9af5d0c47e5b259e2e8bcdfc1811b5a259"),
    "batteries": ("https://github.com/leanprover-community/batteries",
                  "f2effa3d803fda822b1f97b806c47cf2adfbcbc2"),
    "Cli": ("https://github.com/leanprover/lean4-cli",
            "e92c9f15fdfacc8536f31cfb3b7ad26c3c8cd204"),
}
LAKEFILE = '''import Lake

open Lake DSL

package OAI where
  version := v!"0.1.0"
  fixedToolchain := true
  leanOptions := #[⟨`autoImplicit, false⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "d13f23b723b8a846827a245b89c10fc7d3f11612"

lean_lib OAI
'''


class AuditError(RuntimeError):
    pass


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AuditError(message)


def command(args: list[str], cwd: Path) -> bytes:
    result = subprocess.run(args, cwd=cwd, stdout=subprocess.PIPE,
                            stderr=subprocess.PIPE, check=False)
    require(result.returncode == 0,
            f"Command failed ({result.returncode}): {args!r}\n"
            + result.stderr.decode("utf-8", errors="replace"))
    return result.stdout


def git_blob(data: bytes) -> str:
    return hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def masked_lean(source: str) -> str:
    """Mask nested comments and ordinary strings, preserving line positions."""
    output = list(source)
    index = 0
    depth = 0
    in_string = False
    while index < len(source):
        if depth:
            if source.startswith("/-", index):
                output[index:index + 2] = "  "
                depth += 1
                index += 2
            elif source.startswith("-/", index):
                output[index:index + 2] = "  "
                depth -= 1
                index += 2
            else:
                if source[index] != "\n":
                    output[index] = " "
                index += 1
        elif in_string:
            if source[index] == "\\":
                output[index] = " "
                index += 1
                if index < len(source):
                    if source[index] != "\n":
                        output[index] = " "
                    index += 1
            elif source[index] == '"':
                output[index] = " "
                in_string = False
                index += 1
            else:
                if source[index] != "\n":
                    output[index] = " "
                index += 1
        elif source.startswith("--", index):
            end = source.find("\n", index)
            if end < 0:
                end = len(source)
            output[index:end] = " " * (end - index)
            index = end
        elif source.startswith("/-", index):
            output[index:index + 2] = "  "
            depth = 1
            index += 2
        elif source[index] == '"':
            output[index] = " "
            in_string = True
            index += 1
        else:
            index += 1
    require(depth == 0 and not in_string, "Unterminated Lean comment or string")
    return "".join(output)


def source_imports(source: str, label: str) -> list[str]:
    code = masked_lean(source)
    forbidden = re.search(r"\b(?:sorry|admit|native_decide|axiom|unsafe|opaque)\b"
                          r"|Lean\.ofReduce(?:Bool|Nat)\b"
                          r"|debug\.skipKernelTC", code)
    require(forbidden is None, f"Forbidden source token in {label}: {forbidden}")
    imports: list[str] = []
    for match in re.finditer(r"(?m)^[ \t]*(?:public[ \t]+)?import[ \t]+([^\n]+)", code):
        for module in match.group(1).split():
            require(re.fullmatch(r"[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*",
                                 module) is not None,
                    f"Unsupported import syntax in {label}: {module}")
            imports.append(module)
    return imports


def external_allowed(module: str) -> bool:
    return (module == "Mathlib" or module.startswith("Mathlib.")
            or module == "Lean.Elab.Tactic.Omega")


def pinned_file(upstream: Path, relative: str) -> bytes:
    path = upstream / relative
    require(path.is_file() and not path.is_symlink(), f"Missing regular source file: {path}")
    data = path.read_bytes()
    expected = command(["git", "rev-parse", f"{UPSTREAM_REV}:{relative}"], upstream).decode().strip()
    require(git_blob(data) == expected, f"Working file differs from pinned Git blob: {relative}")
    return data


def validate_upstream_head(upstream: Path) -> None:
    head = command(["git", "rev-parse", "HEAD"], upstream).decode().strip()
    require(head == UPSTREAM_REV, f"Expected upstream {UPSTREAM_REV}, found {head}")


def closure(upstream: Path) -> tuple[dict[str, bytes], list[str]]:
    pending = [ROOT_MODULE]
    contents: dict[str, bytes] = {}
    external: set[str] = set()
    while pending:
        module = pending.pop()
        relative = module.replace(".", "/") + ".lean"
        if relative in contents:
            continue
        require(module.startswith(PROOF_PREFIX), f"Unexpected proof module: {module}")
        data = pinned_file(upstream, "lean/" + relative)
        contents[relative] = data
        for imported in source_imports(data.decode("utf-8"), relative):
            if imported.startswith(PROOF_PREFIX):
                pending.append(imported)
            else:
                require(external_allowed(imported), f"Unexpected external import in {relative}: {imported}")
                external.add(imported)
    require(len(contents) == EXPECTED_MODULES,
            f"Pinned import closure changed: expected {EXPECTED_MODULES}, found {len(contents)}")
    subtree = upstream / "lean/OAI/NumberTheory/PiExponent"
    available = {str(path.relative_to(upstream / "lean")) for path in subtree.rglob("*.lean")}
    require(set(contents) == available, "Pinned proof subtree differs from the import closure")
    return contents, sorted(external)


def trimmed_manifest(raw: bytes) -> bytes:
    original = json.loads(raw)
    packages = original["packages"]
    by_name = {package["name"]: package for package in packages}
    require(len(by_name) == len(packages), "Duplicate package names in upstream manifest")
    selected = []
    for name, (url, revision) in PACKAGE_PINS.items():
        require(name in by_name, f"Missing pinned package: {name}")
        package = copy.deepcopy(by_name[name])
        require(package.get("type") == "git" and package.get("url") == url
                and package.get("rev") == revision and package.get("subDir") is None,
                f"Upstream package pin changed: {name}")
        selected.append(package)
    manifest = {"version": original["version"], "packagesDir": ".lake/packages",
                "packages": selected, "name": "OAI", "lakeDir": ".lake",
                "fixedToolchain": True}
    return (json.dumps(manifest, indent=2) + "\n").encode()


def write_json(path: Path, value: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def prepare(upstream: Path, build: Path, report_path: Path) -> None:
    upstream, build = upstream.resolve(), build.resolve()
    require(build != upstream and upstream not in build.parents and build not in upstream.parents,
            "Source and isolated build directories must not overlap")
    require(not build.exists() or not any(build.iterdir()), "Build directory must be absent or empty")
    validate_upstream_head(upstream)
    files, external = closure(upstream)
    source_config = {}
    for relative in ("lean/lean-toolchain", "lean/lake-manifest.json", "lean/lakefile.lean"):
        source_config[relative] = pinned_file(upstream, relative)
    require(source_config["lean/lean-toolchain"] == TOOLCHAIN.encode(), "Unexpected native toolchain")
    config = {
        "lean-toolchain": source_config["lean/lean-toolchain"],
        "lakefile.lean": LAKEFILE.encode(),
        "lake-manifest.json": trimmed_manifest(source_config["lean/lake-manifest.json"]),
        "PiExponentGate.lean": Path(__file__).with_name("PiExponentGate.lean").read_bytes(),
    }
    source_imports(config["PiExponentGate.lean"].decode(), "PiExponentGate.lean")
    for relative, data in {**files, **config}.items():
        target = build / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(data)
    report = {
        "phase": "prepared; native verification has not yet passed",
        "upstream_repository": "openai/math", "upstream_revision": UPSTREAM_REV,
        "root_module": ROOT_MODULE, "module_count": len(files),
        "external_imports": external, "toolchain": TOOLCHAIN.strip(),
        "proof_files": {name: {"git_blob": git_blob(data), "sha256": digest(data)}
                        for name, data in sorted(files.items())},
        "build_config_sha256": {name: digest(data) for name, data in sorted(config.items())},
        "upstream_config_git_blobs": {name: git_blob(data) for name, data in sorted(source_config.items())},
        "package_pins": {name: {"url": url, "revision": rev}
                         for name, (url, rev) in PACKAGE_PINS.items()},
        "allowed_axioms": sorted(ALLOWED_AXIOMS),
        "scope": "External native verification only; no PI port or V1 conclusion",
    }
    write_json(report_path, report)
    print(f"Prepared {len(files)} pinned proof modules and {len(PACKAGE_PINS)} dependency pins.")


def parse_axioms(output: str) -> dict[str, list[str]]:
    """Accept one complete Lean axiom report for each expected declaration."""
    pattern = re.compile(r"(?m)^'([^'\n]+)' (?:depends on axioms:\s*\[([^\]]*)\]"
                         r"|does not depend on any axioms)[ \t]*$")
    result: dict[str, list[str]] = {}
    spans = []
    for match in pattern.finditer(output):
        name = match.group(1)
        require(name in THEOREMS, f"Unexpected axiom report: {name}")
        require(name not in result, f"Duplicate axiom report: {name}")
        raw = match.group(2)
        axioms = [] if raw is None or not raw.strip() else [item.strip() for item in raw.split(",")]
        require(all(re.fullmatch(r"[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*", item)
                    for item in axioms), f"Malformed axiom list for {name}")
        require(len(axioms) == len(set(axioms)), f"Duplicate axiom name for {name}")
        require(set(axioms) <= ALLOWED_AXIOMS,
                f"Disallowed axioms for {name}: {sorted(set(axioms) - ALLOWED_AXIOMS)}")
        result[name] = sorted(axioms)
        spans.append(match.span())
    remainder = output
    for start, end in reversed(spans):
        remainder = remainder[:start] + " " * (end - start) + remainder[end:]
    require("depends on axioms" not in remainder and "depend on any axioms" not in remainder,
            "Malformed or unparsed axiom report")
    require(set(result) == set(THEOREMS),
            f"Missing axiom reports: {sorted(set(THEOREMS) - set(result))}")
    return result


def check_unchanged(upstream: Path, build: Path, report: dict, packages: bool) -> None:
    validate_upstream_head(upstream)
    require(report.get("upstream_revision") == UPSTREAM_REV and report.get("module_count") == EXPECTED_MODULES,
            "Report does not describe the expected pinned source")
    for relative, hashes in report["proof_files"].items():
        data = pinned_file(upstream, "lean/" + relative)
        require(git_blob(data) == hashes["git_blob"], f"Source report changed: {relative}")
        target = build / relative
        require(target.is_file() and not target.is_symlink() and digest(target.read_bytes()) == hashes["sha256"],
                f"Build proof source changed: {relative}")
    actual = {str(path.relative_to(build)) for path in (build / "OAI").rglob("*.lean")}
    require(actual == set(report["proof_files"]), "Unexpected or missing build proof sources")
    for relative, expected in report["upstream_config_git_blobs"].items():
        require(git_blob(pinned_file(upstream, relative)) == expected, f"Upstream configuration changed: {relative}")
    for relative, expected in report["build_config_sha256"].items():
        path = build / relative
        require(path.is_file() and not path.is_symlink() and digest(path.read_bytes()) == expected,
                f"Isolated build configuration changed: {relative}")
    if packages:
        manifest = json.loads((build / "lake-manifest.json").read_text())
        actual_pins = {entry["name"]: (entry["url"], entry["rev"]) for entry in manifest["packages"]}
        require(actual_pins == PACKAGE_PINS and len(manifest["packages"]) == len(PACKAGE_PINS),
                "Resolved dependency manifest changed")
        for name, (url, revision) in PACKAGE_PINS.items():
            directory = build / ".lake/packages" / name
            head = command(["git", "rev-parse", "HEAD"], directory).decode().strip()
            origin = command(["git", "remote", "get-url", "origin"], directory).decode().strip()
            require(head == revision and origin.removesuffix(".git") == url.removesuffix(".git"),
                    f"Resolved dependency pin changed: {name}")
            command(["git", "diff", "--exit-code", "HEAD", "--"], directory)


def finish(upstream: Path, build: Path, report_path: Path) -> None:
    upstream, build = upstream.resolve(), build.resolve()
    report = json.loads(report_path.read_text())
    check_unchanged(upstream, build, report, packages=True)
    version = command(["lake", "env", "lean", "--version"], build).decode().strip()
    require(re.search(r"\bversion 4\.34\.1\b", version) is not None, f"Unexpected Lean version: {version}")
    process = subprocess.run(["lake", "env", "lean", "PiExponentGate.lean"], cwd=build,
                             stdout=subprocess.PIPE, stderr=subprocess.STDOUT, check=False)
    output = process.stdout.decode("utf-8", errors="strict")
    log_path = report_path.with_name("axioms.log")
    log_path.write_text(output, encoding="utf-8")
    print(output, end="" if output.endswith("\n") else "\n")
    require(process.returncode == 0, f"Literal statement/axiom gate failed: exit {process.returncode}")
    axioms = parse_axioms(output)
    check_unchanged(upstream, build, report, packages=True)
    report.update({
        "phase": "native statement and axiom checks passed",
        "lean_version": version,
        "lake_version": command(["lake", "--version"], build).decode().strip(),
        "axioms": axioms,
        "axiom_log_sha256": digest(process.stdout),
        "kernel_recheck": "Separate required lean-action step; consult the workflow result",
    })
    write_json(report_path, report)
    print("PASS: literal statements, four axiom reports, source identity, and dependency pins.")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("phase", choices=("prepare", "finish"))
    parser.add_argument("--upstream", required=True, type=Path)
    parser.add_argument("--build", required=True, type=Path)
    parser.add_argument("--report", required=True, type=Path)
    args = parser.parse_args()
    try:
        if args.phase == "prepare":
            prepare(args.upstream, args.build, args.report)
        else:
            finish(args.upstream, args.build, args.report)
        return 0
    except (AuditError, KeyError, ValueError, OSError) as error:
        print(f"FAIL: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
