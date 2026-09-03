#!/usr/bin/env python3
"""Build the compact pi knowledge views from per-entry records."""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path
from typing import Any, NoReturn
from urllib.parse import quote

import yaml


ROOT = Path(__file__).resolve().parents[2]
INDEX_PATH = ROOT / "knowledge/pi/INDEX.yaml"
ENTRIES_DIR = ROOT / "knowledge/pi/entries"
FRONTIER_PATH = ROOT / "FRONTIER.md"
LEDGER_PATH = ROOT / "knowledge/pi/workstreams/ATTEMPT_LEDGER.md"
OPEN_PROBLEMS_PATH = ROOT / "knowledge/pi/workstreams/OPEN_PROBLEMS.md"
HISTORY_MARKER = "<!-- generated above; hand-written history below -->"
GENERATED_BY = "workflows/verification/build_knowledge.py"
CATEGORIES = ("results", "open_problems", "closed_routes")

RESULT_FIELDS = {
    "id",
    "title",
    "label",
    "lean",
    "file",
    "statement",
    "does_not_show",
    "source",
}
OPEN_PROBLEM_REQUIRED_FIELDS = {
    "id",
    "statement",
    "would_resolve",
    "label",
    "source",
}
OPEN_PROBLEM_OPTIONAL_FIELDS = {"strength_order"}
CLOSED_ROUTE_FIELDS = {
    "id",
    "title",
    "dies_at",
    "separator",
    "strongest_retained",
    "reopening_condition",
    "source",
}


class IndentedSafeDumper(yaml.SafeDumper):
    """Keep sequence indentation aligned with the hand-maintained index style."""

    def increase_indent(self, flow: bool = False, indentless: bool = False) -> int:
        return super().increase_indent(flow, False)


def fail(message: str) -> NoReturn:
    raise ValueError(message)


def load_yaml(path: Path) -> dict[str, Any]:
    data = yaml.safe_load(path.read_text(encoding="utf-8"))
    if not isinstance(data, dict):
        fail(f"{path.relative_to(ROOT)} must contain a YAML mapping")
    return data


def dump_yaml(data: Any) -> str:
    return yaml.dump(
        data,
        Dumper=IndentedSafeDumper,
        allow_unicode=True,
        default_flow_style=False,
        sort_keys=False,
        width=4096,
    )


def parse_record(path: Path) -> tuple[dict[str, Any], str]:
    text = path.read_text(encoding="utf-8")
    if not text.startswith("---\n"):
        fail(f"{path.relative_to(ROOT)} has no YAML front matter")
    closing = text.find("\n---\n", 4)
    if closing < 0:
        fail(f"{path.relative_to(ROOT)} has unterminated YAML front matter")
    front_matter = yaml.safe_load(text[4:closing])
    if not isinstance(front_matter, dict):
        fail(f"{path.relative_to(ROOT)} front matter must be a mapping")
    body = text[closing + 5 :]
    if not body.strip():
        fail(f"{path.relative_to(ROOT)} must contain a source quotation")
    if len(body.rstrip("\n").splitlines()) > 20:
        fail(f"{path.relative_to(ROOT)} has more than 20 prose lines")
    return front_matter, body


def entry_filename(entry_id: str) -> str:
    """Encode the one index ID containing POSIX's path separator."""
    return entry_id.replace("%", "%25").replace("/", "%2F") + ".md"


def entry_href(entry_id: str) -> str:
    return "../entries/" + quote(entry_filename(entry_id), safe="")


def classify(record: dict[str, Any], path: Path) -> str:
    fields = set(record)
    if "dies_at" in fields:
        expected = CLOSED_ROUTE_FIELDS
        category = "closed_routes"
    elif "would_resolve" in fields:
        expected = OPEN_PROBLEM_REQUIRED_FIELDS | (fields & OPEN_PROBLEM_OPTIONAL_FIELDS)
        if not OPEN_PROBLEM_REQUIRED_FIELDS <= fields:
            missing = sorted(OPEN_PROBLEM_REQUIRED_FIELDS - fields)
            fail(f"{path.relative_to(ROOT)} is missing fields: {missing}")
        if fields - (OPEN_PROBLEM_REQUIRED_FIELDS | OPEN_PROBLEM_OPTIONAL_FIELDS):
            extra = sorted(fields - (OPEN_PROBLEM_REQUIRED_FIELDS | OPEN_PROBLEM_OPTIONAL_FIELDS))
            fail(f"{path.relative_to(ROOT)} has unexpected fields: {extra}")
        category = "open_problems"
    else:
        expected = RESULT_FIELDS
        category = "results"
    if fields != expected:
        fail(
            f"{path.relative_to(ROOT)} fields differ from the {category} schema: "
            f"missing={sorted(expected - fields)}, extra={sorted(fields - expected)}"
        )
    return category


def load_records() -> dict[str, list[dict[str, Any]]]:
    records: dict[str, list[dict[str, Any]]] = {category: [] for category in CATEGORIES}
    seen: dict[str, Path] = {}
    if not ENTRIES_DIR.is_dir():
        fail(f"missing entry directory: {ENTRIES_DIR.relative_to(ROOT)}")
    for path in sorted(ENTRIES_DIR.glob("*.md"), key=lambda item: item.name.casefold()):
        record, _ = parse_record(path)
        entry_id = record.get("id")
        if not isinstance(entry_id, str) or not entry_id:
            fail(f"{path.relative_to(ROOT)} has an invalid id")
        expected_name = entry_filename(entry_id)
        if path.name != expected_name:
            fail(f"{path.relative_to(ROOT)} must be named {expected_name}")
        if entry_id in seen:
            fail(
                f"duplicate entry id {entry_id!r}: "
                f"{seen[entry_id].relative_to(ROOT)} and {path.relative_to(ROOT)}"
            )
        seen[entry_id] = path
        records[classify(record, path)].append(record)
    if not seen:
        fail(f"no records found under {ENTRIES_DIR.relative_to(ROOT)}")
    return records


def natural_key(value: str) -> tuple[tuple[int, Any], ...]:
    parts = re.split(r"(\d+)", value.casefold())
    return tuple((1, int(part)) if part.isdigit() else (0, part) for part in parts)


def order_like_index(
    records: list[dict[str, Any]], current: dict[str, Any], category: str
) -> list[dict[str, Any]]:
    by_id = {record["id"]: record for record in records}
    ordered: list[dict[str, Any]] = []
    for old_record in current.get(category, []):
        old_id = old_record.get("id") if isinstance(old_record, dict) else None
        if old_id in by_id:
            ordered.append(by_id.pop(old_id))
    ordered.extend(by_id[key] for key in sorted(by_id, key=natural_key))
    return ordered


def build_index(
    current: dict[str, Any], records: dict[str, list[dict[str, Any]]]
) -> dict[str, Any]:
    ordered = {
        category: order_like_index(records[category], current, category)
        for category in CATEGORIES
    }
    built: dict[str, Any] = {}
    for key, value in current.items():
        built[key] = ordered[key] if key in ordered else value
    for category in CATEGORIES:
        if category not in built:
            built[category] = ordered[category]
    metadata = dict(built.get("_meta", {}))
    metadata["generated_by"] = GENERATED_BY
    built["_meta"] = metadata
    return built


def table_cell(value: Any) -> str:
    if isinstance(value, list):
        value = ", ".join(str(item) for item in value)
    return str(value).replace("\n", "<br>").replace("|", "\\|")


def render_frontier(current: str, index: dict[str, Any]) -> str:
    heading = "## Machine-checked status (generated from INDEX.yaml)"
    rows = [
        "| ID | Label | Lean name | What it does not show |",
        "|---|---|---|---|",
    ]
    for record in index["results"]:
        if record["label"] != "machine-checked":
            continue
        lean_names = "<br>".join(f"`{name}`" for name in record["lean"])
        rows.append(
            "| {id} | {label} | {lean} | {does_not_show} |".format(
                id=table_cell(record["id"]),
                label=table_cell(record["label"]),
                lean=lean_names,
                does_not_show=table_cell(record["does_not_show"]),
            )
        )
    replacement = heading + "\n\n" + "\n".join(rows) + "\n\n"
    pattern = re.compile(
        rf"^{re.escape(heading)}\n.*?(?=^## )", re.MULTILINE | re.DOTALL
    )
    if not pattern.search(current):
        fail(f"could not find the generated status section in {FRONTIER_PATH.name}")
    return pattern.sub(replacement, current, count=1)


def split_history(current: str, path: Path) -> str:
    marker = HISTORY_MARKER + "\n"
    if HISTORY_MARKER not in current:
        return current
    if current.count(HISTORY_MARKER) != 1 or marker not in current:
        fail(f"malformed history marker in {path.relative_to(ROOT)}")
    return current.split(marker, 1)[1]


def render_ledger(current: str, index: dict[str, Any]) -> str:
    rows = [
        "| ID | Route family | First fatal line | Separator | Strongest retained | Reopen only with |",
        "|---|---|---|---|---|---|",
    ]
    for record in index["closed_routes"]:
        entry_id = table_cell(record["id"])
        rows.append(
            f"| [`{entry_id}`]({entry_href(record['id'])}) | "
            f"{table_cell(record['title'])} | {table_cell(record['dies_at'])} | "
            f"{table_cell(record['separator'])} | "
            f"{table_cell(record['strongest_retained'])} | "
            f"{table_cell(record['reopening_condition'])} |"
        )
    generated = (
        "# Attempt ledger index\n\n"
        f"Generated by `{GENERATED_BY}` from `knowledge/pi/entries/`.\n\n"
        + "\n".join(rows)
        + "\n\n"
        + HISTORY_MARKER
        + "\n"
    )
    return generated + split_history(current, LEDGER_PATH)


def render_open_problems(current: str, index: dict[str, Any]) -> str:
    rows = [
        "| ID | Statement | Strength order | Would resolve | Label |",
        "|---|---|---|---|---|",
    ]
    for record in index["open_problems"]:
        entry_id = table_cell(record["id"])
        rows.append(
            f"| [`{entry_id}`]({entry_href(record['id'])}) | "
            f"{table_cell(record['statement'])} | "
            f"{table_cell(record.get('strength_order', []))} | "
            f"{table_cell(record['would_resolve'])} | {table_cell(record['label'])} |"
        )
    generated = (
        "# Open-problem index\n\n"
        f"Generated by `{GENERATED_BY}` from `knowledge/pi/entries/`.\n\n"
        + "\n".join(rows)
        + "\n\n"
        + HISTORY_MARKER
        + "\n"
    )
    return generated + split_history(current, OPEN_PROBLEMS_PATH)


def github_slug(line: str) -> str:
    heading = re.sub(r"^#+\s*", "", line.strip()).casefold()
    heading = re.sub(r"[^\w\s-]", "", heading, flags=re.UNICODE)
    return re.sub(r"\s", "-", heading)


def source_excerpt(record: dict[str, Any]) -> str:
    source, _, anchor = record["source"].partition("#")
    source_path = ROOT / source
    if not source_path.is_file():
        fail(f"entry {record['id']} source does not exist: {source}")
    lines = source_path.read_text(encoding="utf-8").splitlines()
    headings = [
        (index, line)
        for index, line in enumerate(lines)
        if line.lstrip().startswith("#")
    ]
    start: int | None = None
    if anchor:
        for index, line in headings:
            if github_slug(line.lstrip()) == anchor.casefold():
                start = index
                break
    if start is None and headings:
        start = headings[0][0]
    if start is None:
        start = next((index for index, line in enumerate(lines) if line.strip()), None)
    if start is None:
        fail(f"entry {record['id']} source is empty: {source}")

    excerpt: list[str] = []
    for line in lines[start:]:
        if line.strip() == "-/":
            break
        if excerpt and line.lstrip().startswith("#"):
            break
        excerpt.append(line)
        if len(excerpt) == 8:
            break
    while excerpt and not excerpt[-1].strip():
        excerpt.pop()
    if not excerpt:
        fail(f"could not quote source prose for entry {record['id']}")
    return "\n".join(">" if not line else f"> {line}" for line in excerpt) + "\n"


def bootstrap_entries(index: dict[str, Any]) -> None:
    ENTRIES_DIR.mkdir(parents=True, exist_ok=True)
    count = 0
    created = 0
    for category in CATEGORIES:
        for record in index.get(category, []):
            if not isinstance(record, dict) or not isinstance(record.get("id"), str):
                fail(f"invalid {category} record in {INDEX_PATH.relative_to(ROOT)}")
            path = ENTRIES_DIR / entry_filename(record["id"])
            front_matter = dump_yaml(record)
            expected = f"---\n{front_matter}---\n{source_excerpt(record)}"
            if path.exists():
                if path.read_text(encoding="utf-8") != expected:
                    fail(f"--bootstrap refuses to overwrite {path.relative_to(ROOT)}")
            else:
                path.write_text(expected, encoding="utf-8")
                created += 1
            count += 1
    print(f"bootstrapped {count} entry records ({created} created)")


def write_or_check(path: Path, expected: str, check: bool) -> bool:
    current = path.read_text(encoding="utf-8") if path.exists() else ""
    if current == expected:
        return False
    if check:
        print(f"OUT OF DATE: {path.relative_to(ROOT)}", file=sys.stderr)
        return True
    path.write_text(expected, encoding="utf-8")
    print(f"updated {path.relative_to(ROOT)}")
    return False


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument(
        "--bootstrap",
        action="store_true",
        help="create entry records once from the current index before building",
    )
    mode.add_argument(
        "--check", action="store_true", help="report stale generated files without writing"
    )
    args = parser.parse_args()

    current_index = load_yaml(INDEX_PATH)
    if args.bootstrap:
        bootstrap_entries(current_index)

    records = load_records()
    built_index = build_index(current_index, records)
    expected_index = dump_yaml(built_index)
    expected_frontier = render_frontier(
        FRONTIER_PATH.read_text(encoding="utf-8"), built_index
    )
    expected_ledger = render_ledger(
        LEDGER_PATH.read_text(encoding="utf-8"), built_index
    )
    expected_open_problems = render_open_problems(
        OPEN_PROBLEMS_PATH.read_text(encoding="utf-8"), built_index
    )

    stale = False
    stale |= write_or_check(INDEX_PATH, expected_index, args.check)
    stale |= write_or_check(FRONTIER_PATH, expected_frontier, args.check)
    stale |= write_or_check(LEDGER_PATH, expected_ledger, args.check)
    stale |= write_or_check(OPEN_PROBLEMS_PATH, expected_open_problems, args.check)
    if args.check and stale:
        return 1
    counts = ", ".join(f"{key}={len(built_index[key])}" for key in CATEGORIES)
    print(f"knowledge views current ({counts})")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except ValueError as error:
        print(f"ERROR: {error}", file=sys.stderr)
        raise SystemExit(1)
