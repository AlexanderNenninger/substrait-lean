"""Engine facts (`characterization/<engine>/facts/*.json`): what each engine
does, one finding per document, with the checks that support it.

Maintainer tooling (`sverify_dev`): not in the wheel, and not part of sverify's
API.

Each document follows `characterization/fact.schema.json`: the engine and its
exact version, what the engine does, what the reference semantics does, a
status, and its provenance (when it was checked, how, by what, and the
evidence: links at a tag or commit, ledgers, probes, SQL repros).

A fact's `options` names the items of the characterization checklist
(`characterization/areas.json`) it settles. The documents are the record;
there is no generated overview. The command

    uv run python -m sverify_dev.facts

checks them (`tests/test_facts.py` runs the same check), and

    uv run python -m sverify_dev.facts --coverage polars

lists, per area and item of the checklist, the engine's facts that settle it.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path
from typing import Any

import jsonschema

REPO = Path(__file__).resolve().parents[3]
ROOT = REPO / "characterization"
SCHEMA = ROOT / "fact.schema.json"
AREAS = ROOT / "areas.json"

Fact = dict[str, Any]


def engines(root: Path = ROOT) -> list[str]:
    """The engines with a `facts/` folder."""
    return sorted(p.parent.name for p in root.glob("*/facts") if p.is_dir())


def load(root: Path = ROOT) -> dict[Path, Fact]:
    """Every fact document, by path."""
    return {p: json.loads(p.read_text()) for p in sorted(root.glob("*/facts/*.json"))}


def checklist(root: Path = ROOT) -> dict[str, list[str]]:
    """The checklist's item ids, by area, in order."""
    areas = json.loads((root / AREAS.name).read_text())["areas"]
    return {a["id"]: [i["id"] for i in a["items"]] for a in areas}


def validate(docs: dict[Path, Fact], root: Path = ROOT) -> list[str]:
    """What is wrong with the documents: the schema, the file names, ids that
    repeat, checklist items that do not exist, and references to files,
    probes or facts that do not exist."""
    validator = jsonschema.Draft202012Validator(json.loads((root / SCHEMA.name).read_text()))
    repo = root.parent
    problems: list[str] = []
    items = [i for area in checklist(root).values() for i in area]
    problems += [
        f"{AREAS.name}: item {i} repeats" for i in sorted(set(items)) if items.count(i) > 1
    ]
    ids = {str(f.get("id")) for f in docs.values()}
    seen: set[str] = set()
    for path, f in docs.items():
        where = path.relative_to(repo).as_posix()
        errors = sorted(validator.iter_errors(f), key=lambda e: list(e.path))
        problems += [f"{where}: {'/'.join(map(str, e.path))}: {e.message}" for e in errors]
        if errors:
            continue
        if f["id"] in seen:
            problems.append(f"{where}: id {f['id']} repeats")
        seen.add(f["id"])
        if path.name != f"{f['id']}.json":
            problems.append(f"{where}: the file is not named after its id {f['id']}")
        for item in f.get("options", []):
            if item not in items:
                problems.append(f"{where}: {item!r} is not an item of {AREAS.name}")
        engine = path.parent.parent.name
        if f["engine"] != engine or not f["id"].startswith(f"{engine}-"):
            problems.append(f"{where}: engine and id must start with the folder's {engine!r}")
        linked = [*f.get("supersedes", [])]
        if "superseded_by" in f:
            linked.append(f["superseded_by"])
        for other in linked:
            if other not in ids:
                problems.append(f"{where}: no fact {other}")
        for check in f["provenance"]:
            for e in check.get("evidence", []):
                if "file" not in e:
                    continue
                target = repo / e["file"]
                if not target.is_file():
                    problems.append(f"{where}: no file {e['file']}")
                elif "probe" in e:
                    constructs = {p["construct"] for p in json.loads(target.read_text())["probes"]}
                    if e["probe"] not in constructs:
                        problems.append(f"{where}: {e['file']} has no probe {e['probe']!r}")
        # Prose that names another fact (`duckdb-R2`) names one that exists,
        # or a group of them (`duckdb-R15` for `duckdb-R15-…`).
        prefixes = "|".join(engines(root))
        text = json.dumps([f.get("description"), f.get("reference"), f["provenance"]])
        for name in re.findall(rf"\b(?:{prefixes})-[A-Z][A-Za-z0-9-]*[A-Za-z0-9]", text):
            if not any(i == name or i.startswith(f"{name}-") for i in ids):
                problems.append(f"{where}: names {name}, which is not a fact")
    return problems


Coverage = dict[str, dict[str, list[str]]]


def coverage(docs: dict[Path, Fact], engine: str, root: Path = ROOT) -> Coverage:
    """Per area and item of the checklist, the ids of `engine`'s current facts
    (not superseded) that settle it; an empty list is a missing item."""
    found = {area: {i: [] for i in items} for area, items in checklist(root).items()}
    where = {i: area for area, items in found.items() for i in items}
    for f in docs.values():
        if f.get("engine") != engine or "superseded_by" in f:
            continue
        for item in f.get("options", []):
            if item in where:
                found[where[item]][item].append(f["id"])
    return found


def report(found: Coverage) -> str:
    """`coverage`'s result as text: one line per item, then the counts."""
    lines = []
    for area, items in found.items():
        covered = sum(1 for ids in items.values() if ids)
        lines.append(f"{area} ({covered}/{len(items)})")
        lines += [f"  {i}: {', '.join(ids) or 'missing'}" for i, ids in items.items()]
    total = sum(len(items) for items in found.values())
    covered = sum(1 for items in found.values() for ids in items.values() if ids)
    gaps = [a for a, items in found.items() if not all(items.values())]
    lines.append(f"{covered}/{total} items covered; gaps in: {', '.join(gaps) or 'none'}")
    return "\n".join(lines)


def main(argv: list[str] | None = None) -> None:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("--coverage", metavar="ENGINE", help="list the checklist's coverage")
    args = parser.parse_args(argv)
    docs = load()
    problems = validate(docs)
    if problems:
        sys.exit("\n".join(problems))
    if args.coverage:
        if args.coverage not in engines():
            sys.exit(f"no engine {args.coverage!r}; the engines are {', '.join(engines())}")
        print(report(coverage(docs, args.coverage)))
        return
    print(f"{len(docs)} facts, well-formed")


if __name__ == "__main__":
    main()
