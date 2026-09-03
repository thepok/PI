#!/usr/bin/env python3
"""Check the generated pi knowledge index and all of its local references."""

from __future__ import annotations

import subprocess
import sys
from pathlib import Path
from typing import Any

import build_knowledge as build


ROOT = build.ROOT
INDEX_PATH = build.INDEX_PATH
ALLOWED_LABELS = {
    "experiment",
    "conjecture",
    "proof sketch",
    "machine-checked",
    "literature-checked",
    "candidate resolution",
    "verified resolution",
}


class Checks:
    def __init__(self) -> None:
        self.errors: list[str] = []

    def require(self, condition: bool, message: str) -> None:
        if not condition:
            self.errors.append(message)

    def path(self, raw: Any, context: str) -> Path | None:
        if not isinstance(raw, str) or not raw.strip():
            self.errors.append(f"{context} has no path")
            return None
        relative = Path(raw.split("#", 1)[0])
        if relative.is_absolute():
            self.errors.append(f"{context} uses an absolute path: {raw}")
            return None
        resolved = (ROOT / relative).resolve()
        try:
            resolved.relative_to(ROOT.resolve())
        except ValueError:
            self.errors.append(f"{context} escapes the repository: {raw}")
            return None
        if not resolved.is_file():
            self.errors.append(f"{context} path does not exist: {raw}")
            return None
        return resolved


def records_by_id(
    checks: Checks, records: list[dict[str, Any]], context: str
) -> dict[str, dict[str, Any]]:
    result: dict[str, dict[str, Any]] = {}
    for record in records:
        entry_id = record.get("id")
        if not isinstance(entry_id, str) or not entry_id:
            checks.errors.append(f"{context} contains an invalid id")
        elif entry_id in result:
            checks.errors.append(f"{context} repeats id {entry_id}")
        else:
            result[entry_id] = record
    return result


def check_round_trip(
    checks: Checks,
    index: dict[str, Any],
    records: dict[str, list[dict[str, Any]]],
) -> None:
    all_index_ids: set[str] = set()
    for category in build.CATEGORIES:
        indexed = index.get(category)
        if not isinstance(indexed, list) or not all(
            isinstance(record, dict) for record in indexed
        ):
            checks.errors.append(f"INDEX.yaml {category} must be a list of mappings")
            continue
        indexed_by_id = records_by_id(checks, indexed, f"INDEX.yaml {category}")
        record_map = records_by_id(checks, records[category], f"entries {category}")
        overlap = all_index_ids & indexed_by_id.keys()
        if overlap:
            checks.errors.append(
                "INDEX.yaml repeats ids across categories: " + ", ".join(sorted(overlap))
            )
        all_index_ids.update(indexed_by_id)
        if indexed_by_id != record_map:
            missing = sorted(indexed_by_id.keys() - record_map.keys())
            extra = sorted(record_map.keys() - indexed_by_id.keys())
            changed = sorted(
                entry_id
                for entry_id in indexed_by_id.keys() & record_map.keys()
                if indexed_by_id[entry_id] != record_map[entry_id]
            )
            checks.errors.append(
                f"{category} entries differ from INDEX.yaml: "
                f"missing={missing}, extra={extra}, changed={changed}"
            )


def check_labels_and_routes(checks: Checks, index: dict[str, Any]) -> None:
    for category in ("results", "open_problems"):
        for record in index.get(category, []):
            label = record.get("label")
            checks.require(
                label in ALLOWED_LABELS,
                f"{record.get('id', '<unknown>')} has out-of-vocabulary label {label!r}",
            )
            if label == "machine-checked":
                lean_names = record.get("lean")
                checks.require(
                    isinstance(lean_names, list)
                    and bool(lean_names)
                    and all(isinstance(name, str) and name for name in lean_names),
                    f"machine-checked entry {record.get('id')} has no Lean name",
                )
    for record in index.get("closed_routes", []):
        separator = record.get("separator")
        checks.require(
            isinstance(separator, str) and bool(separator.strip()),
            f"closed route {record.get('id')} needs a separator or literal 'none recorded'",
        )


def check_lean_names(checks: Checks, index: dict[str, Any]) -> None:
    audit_path = ROOT / "audit/AxiomAudit.lean"
    audit = audit_path.read_text(encoding="utf-8")
    theory_paths = [ROOT / "TheoryLib.lean", *(ROOT / "TheoryLib").rglob("*.lean")]
    theory = "\n".join(
        path.read_text(encoding="utf-8") for path in theory_paths if path.is_file()
    )
    for record in index.get("results", []):
        lean_names = record.get("lean", [])
        if not isinstance(lean_names, list):
            checks.errors.append(f"{record.get('id')} lean field must be a list")
            continue
        for name in lean_names:
            checks.require(
                isinstance(name, str) and (name in audit or name in theory),
                f"Lean name not found in audit/AxiomAudit.lean or TheoryLib: {name!r}",
            )


def check_paths_and_reachability(
    checks: Checks,
    index: dict[str, Any],
    records: dict[str, list[dict[str, Any]]],
) -> None:
    reachable = {INDEX_PATH.relative_to(ROOT).as_posix()}
    document_ids: set[str] = set()
    for number, document in enumerate(index.get("documents", []), start=1):
        context = f"document {number}"
        if not isinstance(document, dict):
            checks.errors.append(f"{context} must be a mapping")
            continue
        document_id = document.get("id")
        checks.require(
            isinstance(document_id, str)
            and bool(document_id)
            and document_id not in document_ids,
            f"{context} has an invalid or duplicate id {document_id!r}",
        )
        if isinstance(document_id, str):
            document_ids.add(document_id)
        path = checks.path(document.get("path"), context)
        if path is not None:
            reachable.add(path.relative_to(ROOT).as_posix())

    archive_paths: set[str] = set()
    for number, archive in enumerate(index.get("archive", []), start=1):
        context = f"archive record {number}"
        if not isinstance(archive, dict):
            checks.errors.append(f"{context} must be a mapping")
            continue
        path = checks.path(archive.get("path"), context)
        if path is not None:
            relative = path.relative_to(ROOT).as_posix()
            checks.require(relative not in archive_paths, f"duplicate archive path: {relative}")
            archive_paths.add(relative)
            reachable.add(relative)
        checks.path(archive.get("moved_from"), f"{context} moved_from")

    for category in build.CATEGORIES:
        for record in index.get(category, []):
            entry_id = record.get("id", "<unknown>")
            source = checks.path(record.get("source"), f"entry {entry_id} source")
            if source is not None:
                source_relative = source.relative_to(ROOT).as_posix()
                if source_relative.startswith("knowledge/"):
                    reachable.add(source_relative)
            if category == "results":
                checks.path(record.get("file"), f"entry {entry_id} file")
            entry_path = build.ENTRIES_DIR / build.entry_filename(str(entry_id))
            if entry_path.is_file():
                reachable.add(entry_path.relative_to(ROOT).as_posix())

    actual = {
        path.relative_to(ROOT).as_posix()
        for path in (ROOT / "knowledge").rglob("*")
        if path.is_file()
        and "archive" not in path.relative_to(ROOT / "knowledge").parts
    }
    unreachable = sorted(actual - reachable)
    if unreachable:
        checks.errors.append(
            "knowledge files unreachable from INDEX.yaml documents/archive/entry sources: "
            + ", ".join(unreachable)
        )


def check_source_quotes(checks: Checks) -> None:
    for path in sorted(build.ENTRIES_DIR.glob("*.md")):
        try:
            record, body = build.parse_record(path)
        except ValueError as error:
            checks.errors.append(str(error))
            continue
        body_lines = body.rstrip("\n").splitlines()
        checks.require(
            len(body_lines) <= 20,
            f"{path.relative_to(ROOT)} has {len(body_lines)} prose lines; maximum is 20",
        )
        quoted: list[str] = []
        for line in body_lines:
            if line == ">":
                quoted.append("")
            elif line.startswith("> "):
                quoted.append(line[2:])
            else:
                checks.errors.append(
                    f"{path.relative_to(ROOT)} prose is not a Markdown source quotation"
                )
                quoted = []
                break
        if not quoted:
            continue
        source = checks.path(record.get("source"), f"entry {record.get('id')} quote source")
        if source is None:
            continue
        try:
            source_text = source.read_text(encoding="utf-8")
        except UnicodeDecodeError:
            checks.errors.append(f"entry {record.get('id')} quote source is not UTF-8 text")
            continue
        checks.require(
            "\n".join(quoted) in source_text,
            f"entry {record.get('id')} quotation is not verbatim in {source.relative_to(ROOT)}",
        )


def check_generated_views(checks: Checks) -> None:
    result = subprocess.run(
        [sys.executable, str(ROOT / build.GENERATED_BY), "--check"],
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        check=False,
    )
    if result.returncode != 0:
        checks.errors.append("generated knowledge views are stale:\n" + result.stdout.rstrip())


def main() -> int:
    checks = Checks()
    try:
        index = build.load_yaml(INDEX_PATH)
        records = build.load_records()
    except (OSError, ValueError) as error:
        print(f"ERROR: {error}", file=sys.stderr)
        return 1

    metadata = index.get("_meta", {})
    checks.require(
        isinstance(metadata, dict) and metadata.get("generated_by") == build.GENERATED_BY,
        f"INDEX.yaml _meta.generated_by must be {build.GENERATED_BY!r}",
    )
    check_round_trip(checks, index, records)
    check_labels_and_routes(checks, index)
    check_lean_names(checks, index)
    check_paths_and_reachability(checks, index, records)
    check_source_quotes(checks)
    check_generated_views(checks)

    if checks.errors:
        for error in checks.errors:
            print(f"ERROR: {error}", file=sys.stderr)
        return 1
    total = sum(len(records[category]) for category in build.CATEGORIES)
    print(
        f"PASS: knowledge index is consistent ({total} entries; labels, paths, "
        "Lean names, source quotes, reachability, and generated views checked)."
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
