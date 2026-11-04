"""Upstream bugs (`upstream/bugs/*.json`) and the lift's backlog of tests
(`python/tests/lift_backlog.json`): records people and agents edit by hand,
one entry each, checked here.

Maintainer tooling (`sverify_dev`): not in the wheel, and not part of sverify's
API.

Each upstream bug follows `upstream/bug.schema.json`: the project and
version, a status, a summary, a minimal repro, how sverify handles it, how it
was found, and when it was last checked against which releases. The lift's
backlog lists the tests that wait on SQL the lift does not read yet (#240),
each with the reason it waits.

The documents are the record; there is no generated overview. The command

    uv run python -m sverify_dev.bugs

checks both (`tests/test_bugs.py` runs the same check).
"""

from __future__ import annotations

import json
import re
import sys
from pathlib import Path
from typing import Any

import jsonschema

from sverify_dev import facts

REPO = Path(__file__).resolve().parents[3]
ROOT = REPO / "upstream"
SCHEMA = ROOT / "bug.schema.json"
BACKLOG = REPO / "python" / "tests" / "lift_backlog.json"

#: The id prefix of each project.
PREFIXES = {
    "sqlglot": "SG",
    "datafusion": "DF",
    "duckdb": "DD",
    "deltalake": "DL",
    "polars": "PL",
    "spark": "SP",
    "ibis": "IB",
    "substrait": "ST",
}

Bug = dict[str, Any]


def load(root: Path = ROOT) -> dict[Path, Bug]:
    """Every upstream bug, by path."""
    return {p: json.loads(p.read_text()) for p in sorted((root / "bugs").glob("*.json"))}


def validate(docs: dict[Path, Bug], root: Path = ROOT) -> list[str]:
    """What is wrong with the documents: the schema, the file names, ids that
    repeat or don't match the project, and links to files or engine facts
    that do not exist."""
    validator = jsonschema.Draft202012Validator(json.loads((root / SCHEMA.name).read_text()))
    repo = root.parent
    fact_ids = {str(f.get("id")) for f in facts.load(repo / "characterization").values()}
    problems: list[str] = []
    seen: set[str] = set()
    for path, b in docs.items():
        where = path.relative_to(repo).as_posix()
        errors = sorted(validator.iter_errors(b), key=lambda e: list(e.path))
        problems += [f"{where}: {'/'.join(map(str, e.path))}: {e.message}" for e in errors]
        if errors:
            continue
        if b["id"] in seen:
            problems.append(f"{where}: id {b['id']} repeats")
        seen.add(b["id"])
        if path.name != f"{b['id']}.json":
            problems.append(f"{where}: the file is not named after its id {b['id']}")
        prefix = PREFIXES[b["project"]]
        if not b["id"].startswith(f"{prefix}-"):
            problems.append(f"{where}: a {b['project']} bug's id starts with {prefix}-")
        for file in b.get("files", []):
            if not (repo / file).exists():
                problems.append(f"{where}: no file {file}")
        for fact in b.get("facts", []):
            if fact not in fact_ids:
                problems.append(f"{where}: no fact {fact}")
    return problems


BACKLOG_SCHEMA = {
    "type": "object",
    "additionalProperties": False,
    "required": ["tests"],
    "properties": {
        "description": {"type": "string"},
        "tests": {
            "type": "array",
            "items": {
                "type": "object",
                "additionalProperties": False,
                "required": ["test", "reason"],
                "properties": {
                    "test": {"description": "A pytest node id from python/.", "type": "string"},
                    "reason": {
                        "description": "What the test waits on.",
                        "type": "string",
                        "minLength": 1,
                    },
                },
            },
        },
    },
}


def validate_backlog(path: Path = BACKLOG) -> list[str]:
    """What is wrong with the lift's backlog: its shape, ids that repeat, and
    ids whose file or test function does not exist. (A parametrization is
    only known after collection; a stale one fails the run as not listed.)"""
    doc = json.loads(path.read_text())
    where = path.name
    errors = list(jsonschema.Draft202012Validator(BACKLOG_SCHEMA).iter_errors(doc))
    if errors:
        return [f"{where}: {'/'.join(map(str, e.path))}: {e.message}" for e in errors]
    base = path.parent.parent  # node ids are relative to python/
    problems: list[str] = []
    seen: set[str] = set()
    for entry in doc["tests"]:
        node = entry["test"]
        if node in seen:
            problems.append(f"{where}: {node} repeats")
        seen.add(node)
        file, _, rest = node.partition("::")
        names = rest.split("[", 1)[0].split("::")
        source = base / file
        if not rest or not source.is_file():
            problems.append(f"{where}: {node}: no test file {file}")
            continue
        text = source.read_text()
        for kind, name in zip(["class"] * (len(names) - 1) + ["def"], names, strict=True):
            if not re.search(rf"^\s*(?:async\s+)?{kind}\s+{re.escape(name)}\b", text, re.M):
                problems.append(f"{where}: {node}: {file} has no {kind} {name}")
    return problems


def main() -> None:
    docs = load()
    problems = validate(docs) + validate_backlog()
    if problems:
        sys.exit("\n".join(problems))
    print(f"{len(docs)} upstream bugs and the lift's backlog, well-formed")


if __name__ == "__main__":
    main()
