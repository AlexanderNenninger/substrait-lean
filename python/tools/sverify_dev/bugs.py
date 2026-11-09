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

The documents are the record. `upstream/REPORT.md` is generated from them:
the entries ready to report first, then the count of each class by project.
The command

    uv run python -m sverify_dev.bugs

checks both (`tests/test_bugs.py` runs the same check), and with `--write`
also renders `upstream/REPORT.md`. The `Generated files` workflow writes it on
`main`; feature branches leave it alone.
"""

from __future__ import annotations

import json
import re
import sys
from pathlib import Path
from typing import Any, NamedTuple

import jsonschema

from sverify_dev import facts

REPO = Path(__file__).resolve().parents[3]
ROOT = REPO / "upstream"
SCHEMA = ROOT / "bug.schema.json"
BACKLOG = REPO / "python" / "tests" / "lift_backlog.json"
REPORT = ROOT / "REPORT.md"


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
        prefix = PROJECTS[b["project"]].prefix
        if not b["id"].startswith(f"{prefix}-"):
            problems.append(f"{where}: a {b['project']} bug's id starts with {prefix}-")
        if b.get("kind") == "spec-gap" and b["project"] != "substrait":
            problems.append(f"{where}: only Substrait's entries are spec gaps")
        for file in b.get("files", []):
            if not (repo / file).exists():
                problems.append(f"{where}: no file {file}")
        for fact in b.get("facts", []):
            if fact not in fact_ids:
                problems.append(f"{where}: no fact {fact}")
        if classify(b) == "report" and "title" not in b:
            problems.append(f"{where}: a bug to report has a title (REPORT.md lists it)")
    return problems


#: The classes of the report, in its order, with what each means.
CLASSES = {
    "report": "reproduces on the latest release or main, and no upstream issue reports it",
    "filed": "reported upstream, still open",
    "fixed": "fixed on the project's main, released or due in a release",
    "duplicate": "an open upstream issue covers it: a comment there with the case",
    "not-a-bug": "documented or intended, or matters only to sverify's model (an engine fact)",
    "spec-gap": "Substrait leaves it unspecified: for the spec discussion",
    "unverified": "not yet checked against the latest release",
}

_STATUS_CLASS = {
    "confirmed": "report",
    "filed": "filed",
    "fixed upstream": "fixed",
    "duplicate": "duplicate",
    "not a bug": "not-a-bug",
    "unverified": "unverified",
}


class Project(NamedTuple):
    prefix: str
    """The prefix of its entries' ids."""
    name: str
    """Its name as the report shows it."""


#: The projects, in the report's order.
PROJECTS = {
    "duckdb": Project("DD", "DuckDB"),
    "polars": Project("PL", "Polars"),
    "spark": Project("SP", "Spark"),
    "sqlglot": Project("SG", "SQLGlot"),
    "ibis": Project("IB", "Ibis"),
    "deltalake": Project("DL", "delta-rs"),
    "datafusion": Project("DF", "DataFusion"),
    "substrait": Project("ST", "Substrait"),
}


def classify(b: Bug) -> str:
    """The entry's class in the report: a spec gap by its kind, every other
    entry by its status."""
    if b.get("kind") == "spec-gap":
        return "spec-gap"
    return _STATUS_CLASS[b["status"]]


def _order(b: Bug) -> tuple[int, int]:
    return list(PROJECTS).index(b["project"]), int(b["id"].split("-")[1])


def _versions(b: Bug) -> str:
    last = b["checked"][-1]
    against = ", ".join(f"{k} {v}" for k, v in last["against"].items())
    return f"{against} ({last['checked_at']})"


def _issue(url: str) -> str:
    """A link to an upstream issue, named `owner/repo#n`."""
    m = re.fullmatch(r"https://github\.com/([^/]+/[^/]+)/(?:issues|pull)/(\d+)", url)
    return f"[{m[1]}#{m[2]}]({url})" if m else url


def render(docs: dict[Path, Bug]) -> str:
    """`upstream/REPORT.md`: the bugs to report, the open issues to comment
    on, and the count of each class by project."""
    bugs = sorted(docs.values(), key=_order)
    by_class: dict[str, list[Bug]] = {c: [b for b in bugs if classify(b) == c] for c in CLASSES}
    link = "[{0}](bugs/{0}.json)".format
    out = [
        "# Upstream report",
        "",
        "<!-- Generated from `bugs/*.json` by `python -m sverify_dev.bugs --write`. -->",
        "",
        f"Sverify's upstream ledger holds {len(bugs)} entries ([README](README.md)). "
        f"{len(by_class['report'])} are bugs to report: each reproduces on the version "
        "named, and no upstream issue reports it. Each entry has the repro, what was "
        "searched and how sverify handles it. The `upstream-report` skill drafts the issue.",
        "",
        "## To report",
        "",
        "| Entry | Project | What goes wrong | Reproduces on |",
        "|---|---|---|---|",
    ]
    out += [
        f"| {link(b['id'])} | {PROJECTS[b['project']].name} | {b['title']} | {_versions(b)} |"
        for b in by_class["report"]
    ]
    out += [
        "",
        "## To comment on",
        "",
        "An open upstream issue covers these; the case is worth a comment there.",
        "",
        "| Entry | Project | Issue |",
        "|---|---|---|",
    ]
    out += [
        f"| {link(b['id'])} | {PROJECTS[b['project']].name} | {_issue(b['upstream'][0])} |"
        for b in by_class["duplicate"]
    ]
    shown = [c for c in CLASSES if by_class[c]]
    out += [
        "",
        "## By class and project",
        "",
        "| Project | " + " | ".join(shown) + " | total |",
        "|---|" + "---:|" * (len(shown) + 1),
    ]
    for project, (_, name) in PROJECTS.items():
        row = [sum(b["project"] == project for b in by_class[c]) for c in shown]
        out.append(f"| {name} | " + " | ".join(map(str, row)) + f" | {sum(row)} |")
    totals = [len(by_class[c]) for c in shown]
    out.append("| total | " + " | ".join(map(str, totals)) + f" | {sum(totals)} |")
    out += ["", "The classes:", ""]
    out += [f"- `{c}`: {CLASSES[c]}." for c in shown]
    for c in ("filed", "fixed", "not-a-bug", "spec-gap"):
        if by_class[c]:
            out += ["", f"{c}: " + ", ".join(link(b["id"]) for b in by_class[c]) + "."]
    return "\n".join(out) + "\n"


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


def main(argv: list[str]) -> None:
    docs = load()
    problems = validate(docs) + validate_backlog()
    if problems:
        sys.exit("\n".join(problems))
    print(f"{len(docs)} upstream bugs and the lift's backlog, well-formed")
    if "--write" in argv:
        REPORT.write_text(render(docs))


if __name__ == "__main__":
    main(sys.argv[1:])
