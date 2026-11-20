"""The decision ledger (`decisions/*.json`): every project decision, one
document each, with who made it, its scope, its status and what it replaces.

Maintainer tooling (`sverify_dev`): not in the wheel, and not part of sverify's
API.

Decisions come from three records: the D-numbered decisions of the reference
(`docs/decisions.md`), the theory advisor's numbered rulings (notes outside the
repository; an entry names its file) and the maintainer's rulings. Each
document follows `decisions/decision.schema.json`. The command

    uv run python -m sverify_dev.decisions

checks them (`tests/test_decision_ledger.py` runs the same check): each file
against the schema, its name against its id, every link to an entry that
exists, `supersedes` and `superseded_by` (and `amends` and `amended_by`)
agreeing both ways, a status that fits its links, and an entry for every
section of `docs/decisions.md`. With `--write` it also renders
`docs/ledger.md`, the view of what is in force. The `Generated files`
workflow writes it on `main`; feature branches leave it alone.

`decisions/private/` holds the maintainer's rulings that do not bear on
sverify's design or that carry sensitive details (process, tooling, plans). It
is in `.gitignore`: the checker reads it where it exists and passes without it,
as in CI, and the page shows public entries only. A held-back entry may link to
a public one; a public entry never names a held-back one.
"""

from __future__ import annotations

import json
import re
import sys
from collections import Counter, defaultdict
from pathlib import Path
from typing import Any

import jsonschema

REPO = Path(__file__).resolve().parents[3]
ROOT = REPO / "decisions"
PRIVATE = "private"
SCHEMA = ROOT / "decision.schema.json"
PAGE = REPO / "docs" / "ledger.md"
DECISIONS = REPO / "docs" / "decisions.md"
ISSUES = "https://github.com/AlexanderNenninger/substrait-lean/issues/"

Decision = dict[str, Any]

SCOPE_TITLES = {
    "reference-semantics": "Reference semantics",
    "api": "API",
    "engines": "Engines",
    "architecture": "Architecture",
    "process": "CI and process",
    "release": "Release",
}
STATUSES = ("in-force", "unclear", "superseded", "withdrawn", "reserved")
DECIDERS = {"user": "maintainer", "fable": "theory advisor", "coordinator": "coordinator"}
#: Each link field and its reverse.
LINKS = {
    "supersedes": "superseded_by",
    "superseded_by": "supersedes",
    "amends": "amended_by",
    "amended_by": "amends",
}


def load(root: Path = ROOT) -> dict[Path, Decision]:
    """The public entries, and the held-back ones where `root/private` exists."""
    paths = [p for p in sorted(root.glob("*.json")) if p.name != SCHEMA.name]
    return {p: json.loads(p.read_text()) for p in paths + sorted(root.glob(f"{PRIVATE}/*.json"))}


def is_private(path: Path) -> bool:
    return path.parent.name == PRIVATE


def public(docs: dict[Path, Decision]) -> dict[Path, Decision]:
    return {p: d for p, d in docs.items() if not is_private(p)}


def decision_headings(text: str | None = None) -> dict[str, str]:
    """The D-numbers `docs/decisions.md` has a section for, with its anchor."""
    text = DECISIONS.read_text() if text is None else text
    return {
        m[1]: re.sub(r"[^\w\- ]", "", f"{m[1]}. {m[2]}".lower()).replace(" ", "-")
        for m in re.finditer(r"^### (D\d+)\. (.+)$", text, re.M)
    }


def validate(docs: dict[Path, Decision], headings: dict[str, str] | None = None) -> list[str]:
    validator = jsonschema.Draft202012Validator(json.loads(SCHEMA.read_text()))
    problems = [
        f"{path.name}: {'/'.join(map(str, e.absolute_path)) or 'document'}: {e.message}"
        for path, doc in docs.items()
        for e in validator.iter_errors(doc)
    ]
    if problems:
        return problems
    by_id: dict[str, Decision] = {}
    held = {doc["id"] for path, doc in docs.items() if is_private(path)}
    for path, doc in docs.items():
        ident = doc["id"]
        if path.name != f"{ident}.json":
            problems.append(f"{path.name}: its id is {ident}, so the file is {ident}.json")
        if ident in by_id:
            problems.append(f"{ident}: listed twice")
        by_id[ident] = doc
    for ident, doc in by_id.items():
        for field, back in LINKS.items():
            for target in doc.get(field, []):
                if target not in by_id:
                    problems.append(f"{ident}: {field} {target}, which has no entry")
                elif target in held and ident not in held:
                    problems.append(f"{ident}: {field} {target}, which is held back")
                elif ident in held and target not in held:
                    continue
                elif ident not in by_id[target].get(back, []):
                    problems.append(f"{ident}: {field} {target}, but {target} lacks {back} {ident}")
        status, note = doc["status"], doc.get("note")
        if status == "unclear" and not note:
            problems.append(f"{ident}: unclear, and no note says why")
        if status == "superseded" and not doc.get("superseded_by"):
            problems.append(f"{ident}: superseded, and no entry supersedes it")
        if doc.get("superseded_by") and status not in ("superseded", "withdrawn", "unclear"):
            problems.append(
                f"{ident}: superseded by {', '.join(doc['superseded_by'])}, but {status}"
            )
        if status == "withdrawn" and not doc.get("superseded_by") and not note:
            problems.append(f"{ident}: withdrawn, and neither a link nor a note says by what")
    headings = decision_headings() if headings is None else headings
    for d in sorted(set(headings) - set(by_id), key=lambda d: int(d[1:])):
        problems.append(f"{d}: docs/decisions.md has it, the ledger does not")
    for ident, doc in by_id.items():
        if ident.startswith("D") and ident not in headings and not doc.get("note"):
            problems.append(f"{ident}: not in docs/decisions.md, and no note says where it is")
    return problems


def _key(ident: str) -> tuple[int, int, str]:
    m = re.match(r"^[DF](\d+)", ident)
    return ({"D": 0, "U": 1, "F": 2}[ident[0]], int(m[1]) if m else 10**6, ident)


def _anchor(ident: str) -> str:
    return ident.lower().replace(".", "")


def render(docs: dict[Path, Decision], headings: dict[str, str] | None = None) -> str:
    headings = decision_headings() if headings is None else headings
    entries = sorted(docs.values(), key=lambda d: _key(d["id"]))

    def ref(ident: str) -> str:
        if ident in headings:
            return f"[{ident}](decisions.md#{headings[ident]})"
        return f"[{ident}](#{_anchor(ident)})"

    def refs(idents: list[str]) -> str:
        return ", ".join(map(ref, idents))

    out = [
        "# Decision ledger",
        "",
        "Every decision made on sverify, for contributors: the reference's D-numbered",
        "decisions ([decisions.md](decisions.md)), the theory advisor's numbered rulings",
        "and the maintainer's rulings, one entry each, with who decided, its scope, its",
        "status and what it replaces.",
        "",
        "Each entry is a file in [`decisions/`](../decisions/), checked against",
        "[`decision.schema.json`](../decisions/decision.schema.json) by",
        "`python -m sverify_dev.decisions`, which also writes this page. A ruling's",
        "text stays in the coordinator's notes folder, and its entry names the file.",
        "An entry whose standing the record does not settle is `unclear`, with the",
        "reason. The maintainer's rulings on process and tooling, and any with",
        "sensitive details, stay out of the repository.",
        "",
        "## Counts",
        "",
        "| Record | " + " | ".join(STATUSES) + " | total |",
        "|---|" + "---:|" * (len(STATUSES) + 1),
    ]
    counts: dict[str, Counter[str]] = defaultdict(Counter)
    record = {"D": "decisions.md", "F": "theory advisor's rulings", "U": "maintainer's rulings"}
    for e in entries:
        counts[record[e["id"][0]]][e["status"]] += 1
    for name in record.values():
        c = counts[name]
        out.append(f"| {name} | " + " | ".join(str(c[s]) for s in STATUSES) + f" | {c.total()} |")
    out += [
        "",
        "## What's in force",
        "",
        "Each scope's entries in force, newest first. An amended entry is in force as",
        "amended.",
        "",
    ]
    for scope, title in SCOPE_TITLES.items():
        live = [e for e in entries if e["scope"] == scope and e["status"] == "in-force"]
        live.sort(key=lambda e: (e["date"], _key(e["id"])), reverse=True)
        out += [f"### {title}", ""]
        for e in live:
            tail = f" Amended by {refs(e['amended_by'])}." if e.get("amended_by") else ""
            out.append(f"- {ref(e['id'])} ({e['date']}): {e['summary']}{tail}")
        out.append("")
    out += ["## Unclear and reserved", ""]
    for e in entries:
        if e["status"] in ("unclear", "reserved"):
            out.append(
                f"- {ref(e['id'])}, {e['status']}: {e['summary']} {e.get('note', '')}".rstrip()
            )
    out += [
        "",
        "## All entries",
        "",
        "| Id | Date | By | Scope | Status | Decision | Issues | Links | Source |",
        "|---|---|---|---|---|---|---|---|---|",
    ]
    names = {"supersedes": "replaces", "superseded_by": "replaced by"}
    for e in entries:
        links = "; ".join(
            f"{names.get(f, f.replace('_', ' '))} {refs(e[f])}" for f in LINKS if e.get(f)
        )
        nums = sorted(set(e.get("issues", [])) | set(e.get("prs", [])))
        issues = ", ".join(f"[#{n}]({ISSUES}{n})" for n in nums)
        text = " ".join(filter(None, [e["summary"], e.get("note")])).replace("|", "\\|")
        cells = [
            f'<a id="{_anchor(e["id"])}"></a>{e["id"]}',
            e["date"],
            DECIDERS[e["decided_by"]],
            e["scope"],
            e["status"],
            text,
            issues,
            links,
            e.get("source", "").replace("|", "/"),
        ]
        out.append("| " + " | ".join(cells) + " |")
    return "\n".join(out) + "\n"


def main(argv: list[str]) -> None:
    docs = load()
    problems = validate(docs)
    if problems:
        sys.exit("\n".join(problems))
    print(f"{len(docs)} decisions, well-formed")
    if "--write" in argv:
        PAGE.write_text(render(public(docs)))


if __name__ == "__main__":
    main(sys.argv[1:])
