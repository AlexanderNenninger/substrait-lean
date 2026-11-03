"""Engine facts (`characterization/<engine>/facts/*.json`): what each engine
does, one finding per document, with the checks that support it.

Maintainer tooling (`sverify_dev`): not in the wheel, and not part of sverify's
API.

Each document follows `characterization/fact.schema.json`: the engine and its
exact version, what the engine does, what the reference semantics does, a
status, and its provenance (when it was checked, how, by what, and the
evidence: links at a tag or commit, ledgers, probes, SQL repros).

The documents are the record; there is no generated overview. The command

    uv run python -m sverify_dev.facts

checks them (`tests/test_facts.py` runs the same check).
"""

from __future__ import annotations

import json
import re
import sys
from pathlib import Path
from typing import Any

import jsonschema

REPO = Path(__file__).resolve().parents[3]
ROOT = REPO / "characterization"
SCHEMA = ROOT / "fact.schema.json"

Fact = dict[str, Any]


def engines(root: Path = ROOT) -> list[str]:
    """The engines with a `facts/` folder."""
    return sorted(p.parent.name for p in root.glob("*/facts") if p.is_dir())


def load(root: Path = ROOT) -> dict[Path, Fact]:
    """Every fact document, by path."""
    return {p: json.loads(p.read_text()) for p in sorted(root.glob("*/facts/*.json"))}


def validate(docs: dict[Path, Fact], root: Path = ROOT) -> list[str]:
    """What is wrong with the documents: the schema, the file names, ids that
    repeat, and references to files, probes or facts that do not exist."""
    validator = jsonschema.Draft202012Validator(json.loads((root / SCHEMA.name).read_text()))
    repo = root.parent
    problems: list[str] = []
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


def main() -> None:
    docs = load()
    problems = validate(docs)
    if problems:
        sys.exit("\n".join(problems))
    print(f"{len(docs)} facts, well-formed")


if __name__ == "__main__":
    main()
