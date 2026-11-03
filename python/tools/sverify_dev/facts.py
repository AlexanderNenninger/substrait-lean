"""Engine facts (`characterization/<engine>/facts/*.json`): what each engine
does, one finding per document, with the checks that support it.

Maintainer tooling (`sverify_dev`): not in the wheel, and not part of sverify's
API.

Each document follows `characterization/fact.schema.json`: the engine and its
exact version, what the engine does, what the reference semantics does, a
status, and its provenance (when it was checked, how, by what, and the
evidence: links at a tag or commit, ledgers, probes, SQL repros).

`characterization/<engine>/FACTS.md`, the readable overview, is generated
from the documents by

    uv run python -m sverify_dev.facts --write

Feature branches leave it alone: the `Generated files` workflow regenerates it
on `main` after every merge. Without `--write`, the command checks the
documents (`tests/test_facts.py` runs the same check).
"""

from __future__ import annotations

import json
import os
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


def _natural(s: str) -> list[Any]:
    return [int(x) if x.isdigit() else x for x in re.split(r"(\d+)", s)]


def order(facts: list[Fact]) -> list[Fact]:
    """Semantics before frontend facts, then by id (R2 before R10)."""
    return sorted(facts, key=lambda f: (f.get("layer") == "frontend", _natural(f["id"])))


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


def _prose(p: str | list[str]) -> str:
    return p if isinstance(p, str) else "\n\n".join(p)


def _cell(s: str) -> str:
    return s.replace("|", "\\|").replace("\n", " ")


def _evidence(e: dict[str, str], here: Path, repo: Path) -> str:
    parts = []
    if "url" in e:
        label = e["url"].split("/test/sql/", 1)[-1] if "/test/sql/" in e["url"] else e["url"]
        parts.append(f"[{label}]({e['url']})")
    if "file" in e:
        rel = os.path.relpath(repo / e["file"], here)
        name = Path(e["file"]).name
        parts.append(f"`{e['probe']}` in [{name}]({rel})" if "probe" in e else f"[{name}]({rel})")
    if "test" in e:
        parts.append(f"`{e['test']}`")
    if "sql" in e:
        parts.append(f"`{e['sql']}`" + (f" gives `{e['observed']}`" if "observed" in e else ""))
    if "note" in e:
        parts.append(f"({e['note']})")
    return " ".join(parts)


def _last_checked(f: Fact) -> str:
    dates = [c["checked_at"] for c in f["provenance"] if c["checked_at"] != "unknown"]
    return max(dates, default="unknown")


def _issues(f: Fact) -> str:
    return ", ".join(f"#{n}" for n in [*f.get("issues", []), *f.get("prs", [])])


def render(engine: str, facts: list[Fact], root: Path = ROOT) -> str:
    """`characterization/<engine>/FACTS.md`."""
    here = root / engine
    repo = root.parent
    facts = order(facts)
    versions = ", ".join(sorted({f["engine_version"] for f in facts}))
    lines = [
        f"# {engine}: facts",
        "",
        f"Generated from [facts/](facts/) by `uv run python -m sverify_dev.facts --write`; "
        f"do not edit by hand. One JSON document per finding, in the format of "
        f"[fact.schema.json](../fact.schema.json). Version checked: {versions}.",
        "",
        "| Id | Finding | Area | Status | Verdict | ≈ entries | Last checked |",
        "|---|---|---|---|---|---:|---|",
    ]
    for f in facts:
        verdict, entries = f.get("verdict", ""), str(f.get("ledger_entries", ""))
        cells = [f"[{f['id']}](#{f['id'].lower()})", _cell(f["title"]), f["area"], f["status"],
                 _cell(verdict), entries, _last_checked(f)]  # fmt: skip
        lines.append("| " + " | ".join(cells) + " |")
    settings: dict[str, list[str]] = {}
    for f in facts:
        for name, value in f.get("settings", {}).items():
            if not isinstance(value, list):  # a list: checked under each value
                settings.setdefault(name, []).append(f["id"])
    if settings:
        lines += ["", "Settings the facts depend on, at one value:", ""]
        lines += [f"- `{name}`: {', '.join(ids)}" for name, ids in sorted(settings.items())]
    for f in facts:
        meta = [f"{engine} {f['engine_version']}", f["area"], f["status"]]
        if f.get("layer") == "frontend":
            meta.append("frontend")
        if f.get("constructs"):
            meta.append(", ".join(f"`{c}`" for c in f["constructs"]))
        if f.get("settings"):
            meta.append(", ".join(f"`{k} = {json.dumps(v)}`" for k, v in f["settings"].items()))
        if _issues(f):
            meta.append(_issues(f))
        lines += ["", f'## <a id="{f["id"].lower()}"></a>{f["id"]}. {f["title"]}', "",
                  " · ".join(meta), "", _prose(f["description"])]  # fmt: skip
        if "reference" in f:
            lines += ["", "Reference:", "", _prose(f["reference"])]
        lines += ["", "Checked:", ""]
        for c in f["provenance"]:
            item = f"- {c['checked_at']}, {c['method']}, by {c['checked_by']}"
            evidence = [_evidence(e, here, repo) for e in c.get("evidence", [])]
            if evidence:
                item += ": " + "; ".join(evidence)
            item += "."
            if "notes" in c:
                item += " " + _prose(c["notes"]).replace("\n\n", " ")
            lines.append(item)
        for key, label in (("supersedes", "Supersedes"), ("superseded_by", "Superseded by")):
            if key in f:
                ids = f[key] if isinstance(f[key], list) else [f[key]]
                lines += ["", f"{label} " + ", ".join(f"[{i}](#{i.lower()})" for i in ids) + "."]
    return "\n".join(lines) + "\n"


def write(root: Path = ROOT) -> None:
    """Rewrite each engine's FACTS.md from its documents."""
    docs = load(root)
    for engine in engines(root):
        facts = [f for p, f in docs.items() if p.parent.parent.name == engine]
        (root / engine / "FACTS.md").write_text(render(engine, facts, root))


def main() -> None:
    docs = load()
    problems = validate(docs)
    if problems:
        sys.exit("\n".join(problems))
    if "--write" in sys.argv:
        write()
    print(f"{len(docs)} facts, well-formed")


if __name__ == "__main__":
    main()
