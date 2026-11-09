"""Write the docs site's generated pages before `great-docs build` (`poe docs`).

Great Docs renders the directories `python/examples/`, `python/semantics/`,
`python/design/` and `python/ledgers/` as sections of the site (`sections:` in
`great-docs.yml`), and Quarto's search indexes them, entry by entry. They are
written here, at build time, and ignored by git (CLAUDE.md, "Generated
files"):

- `examples/`: `docs/examples.md`;
- `semantics/` and `design/`: the reference and design pages of `docs/`
  (`DOC_SECTIONS`), with GitHub's heading anchors. Links between pages the
  site has stay on the site; links to other files of the repository point at
  GitHub.
- `ledgers/`: the upstream ledger (`upstream/bugs/*.json`, bugs and spec
  gaps), each engine's characterization (`characterization/<engine>/facts/`),
  the checklist's coverage per engine (`characterization/areas.json`) and the
  realizability table (`docs/realizability.md`). Each entry is a heading with
  its id as the anchor, so search finds it by id, engine, function, option
  and text; the index page lists every entry with a filter.

Usage, from `python/`:

    python scripts/docs_pages.py            # writes examples/, semantics/, design/, ledgers/
    python scripts/docs_pages.py --out DIR  # writes them under DIR
"""

from __future__ import annotations

import argparse
import html
import json
import re
import shutil
from collections.abc import Iterable, Mapping
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[2]
REPO = "https://github.com/AlexanderNenninger/substrait-lean"
BLOB = f"{REPO}/blob/main"
ISSUE = f"{REPO}/issues"

# The evidence levels of a fact, weakest first (characterization/fact.schema.json).
EVIDENCE = ["docs", "source", "engine_test", "probe", "fuzz", "proof"]
PROJECTS = {
    "duckdb": "DuckDB",
    "polars": "Polars",
    "datafusion": "DataFusion",
    "spark": "Spark",
    "sqlglot": "SQLGlot",
    "ibis": "Ibis",
    "deltalake": "delta-rs",
    "delta-rs": "delta-rs",
    "substrait": "Substrait",
}
# The facts pages: one per engine with a profile, one for the others.
FACT_PAGES = [("duckdb", "duckdb-facts"), ("polars", "polars-facts")]
OTHER_FACTS = "other-facts"


# -- text ---------------------------------------------------------------------


def _paragraphs(value: str | list[str] | None) -> list[str]:
    if value is None:
        return []
    return [value] if isinstance(value, str) else list(value)


def md(text: str | list[str]) -> str:
    """Text from a JSON document as Markdown: `$` and `@` outside code spans
    are escaped, so Pandoc reads no math and no citations. A list is a list
    of paragraphs."""
    if not isinstance(text, str):
        return "\n\n".join(md(p) for p in text)
    parts = re.split(r"(```.*?```|`[^`]*`)", text, flags=re.S)
    for i in range(0, len(parts), 2):
        parts[i] = parts[i].replace("$", r"\$").replace("@", r"\@")
    return "".join(parts)


def item(text: str) -> str:
    """A paragraph as a list item: its later lines indented under the bullet,
    so a fenced code block in it stays inside the item."""
    return "- " + md(text).replace("\n", "\n  ")


def cell(text: str | list[str]) -> str:
    """Text for a pipe table's cell."""
    return " ".join(md(text).replace("|", r"\|").split())


def page_id(engine: str) -> str:
    return dict(FACT_PAGES).get(engine, OTHER_FACTS)


def fact_link(fact_id: str, engines: Mapping[str, str]) -> str:
    """A link to a fact's anchor, or the bare id where no fact has it."""
    engine = engines.get(fact_id)
    if engine is None:
        return f"`{fact_id}`"
    return f"[{fact_id}]({page_id(engine)}.md#{fact_id})"


def bug_link(bug_id: str, bugs: Mapping[str, dict]) -> str:
    bug = bugs.get(bug_id)
    if bug is None:
        return f"`{bug_id}`"
    page = "spec-gaps" if bug.get("kind") == "spec-gap" else "upstream-bugs"
    return f"[{bug_id}]({page}.md#{bug_id})"


def issue_links(issues: Iterable[int]) -> str:
    return ", ".join(f"[#{n}]({ISSUE}/{n})" for n in issues)


def file_link(path: str) -> str:
    return f"[`{path}`]({BLOB}/{path})"


def url_link(url: str) -> str:
    return f"<{url}>"


# -- links of copied pages ------------------------------------------------------

_LINK = re.compile(r"(\]\()([^)\s]+)(\))")


def rewrite_links(text: str, source: Path, local: Mapping[str, str]) -> str:
    """Point the relative links of `source` (a file of the repository) at
    GitHub, except those to files the site has (`local`: repository path to
    the page's name in the same section)."""

    def fix(m: re.Match[str]) -> str:
        target = m.group(2)
        if re.match(r"^[a-z]+:|^#|^<", target):
            return m.group(0)
        path, _, anchor = target.partition("#")
        resolved = (source.parent / path).resolve()
        try:
            rel = resolved.relative_to(ROOT).as_posix()
        except ValueError:
            return m.group(0)
        if rel in local:
            new = local[rel]
        elif resolved.is_dir():
            new = f"{REPO}/tree/main/{rel}"
        else:
            new = f"{BLOB}/{rel}"
        return f"{m.group(1)}{new}{'#' + anchor if anchor else ''}{m.group(3)}"

    return _LINK.sub(fix, text)


#: The ledger pages' style. Tables fit the page and wrap: long code spans and
#: lists of facts would otherwise widen a table past the screen (Great Docs
#: gives a table in its scroll wrapper `width: max-content`, which this
#: overrides). Each entry (a level-2 section once Quarto shifts the
#: headings) starts below a rule; its metadata line (`.ledger-meta`) is
#: italic and smaller; inline code is 0.875em of the text around it.
PAGE_STYLE = """```{=html}
<style>
main table, main .gd-table-scroll > table {
  table-layout: fixed; width: 100% !important; min-width: 0; font-size: 0.85rem;
}
main table th, main table td {
  overflow-wrap: anywhere; white-space: normal; vertical-align: top;
}
main table code { white-space: normal; }
main :not(pre) > code { font-size: 0.875em !important; line-height: inherit; }
main section.level2 {
  border-top: 1px solid var(--bs-border-color, #dee2e6);
  margin-top: 2.25rem; padding-top: 0.75rem;
}
main .ledger-meta {
  font-style: italic; font-size: 0.9em; color: var(--bs-secondary-color, #6c757d);
}
main .ledger-meta p { margin-bottom: 0.75rem; }
</style>
```

"""


def front(title: str, description: str, gfm_ids: bool = False) -> str:
    """The page's front matter and style. `gfm_ids` makes Pandoc give
    headings GitHub's anchors (`#d13-choosing-the-route`), so a page copied
    from `docs/` keeps the anchors its links use."""
    reader = "from: markdown+gfm_auto_identifiers\n" if gfm_ids else ""
    return f'---\ntitle: "{title}"\ndescription: "{description}"\n{reader}---\n\n' + PAGE_STYLE


def strip_title(text: str) -> str:
    """A Markdown document without its first `# ` heading (the front matter
    carries the title)."""
    return re.sub(r"\A# [^\n]*\n+", "", text, count=1)


# -- the upstream ledger ------------------------------------------------------


def load_bugs(root: Path) -> dict[str, dict]:
    docs = [_load(p) for p in sorted((root / "upstream/bugs").glob("*.json"))]
    return {d["id"]: d for d in sorted(docs, key=_id_key)}


def _load(path: Path) -> dict:
    """A JSON document, with its path (`_path`) for its relative links."""
    return {**json.loads(path.read_text()), "_path": path.resolve()}


def _id_key(doc: dict) -> tuple:
    prefix, _, n = doc["id"].partition("-")
    return (prefix, int(n) if n.isdigit() else 0, n)


def bugs_by_project(bugs: list[dict], facts: Mapping[str, str]) -> str:
    """Entries under a heading per project: Quarto's search indexes the
    sections one level below the page's top headings."""
    out = []
    for project in sorted({b["project"] for b in bugs}, key=lambda p: PROJECTS.get(p, p)):
        out += [f"## {PROJECTS.get(project, project)}", ""]
        out += [bug_entry(b, facts) for b in bugs if b["project"] == project]
    return "\n".join(out)


def bug_entry(bug: dict, facts: Mapping[str, str]) -> str:
    project = PROJECTS.get(bug["project"], bug["project"])
    title = md(_paragraphs(bug["summary"])[0].split(". ")[0].rstrip("."))
    if len(title) > 110:
        title = title[:107].rsplit(" ", 1)[0] + " …"
    out = [f"### {bug['id']}: {title} {{#{bug['id']}}}", ""]
    meta = [
        f"Project: {project} {bug['version']}",
        f"status: {bug['status']}",
    ]
    if bug.get("kind"):
        meta.append(f"kind: {bug['kind']}")
    if bug.get("fixed_in"):
        meta.append(f"fixed in {bug['fixed_in']}")
    out += ["::: {.ledger-meta}", "; ".join(meta) + ".", ":::", ""]
    out += [md(p) + "\n" for p in _paragraphs(bug["summary"])]
    if repro := _paragraphs(bug.get("repro")):
        out += ["Reproduction:", ""] + [item(p) for p in repro] + [""]
    if handling := _paragraphs(bug.get("handling")):
        out += ["How sverify handles it:", ""] + [item(p) for p in handling] + [""]
    out += [f"Status: {md(bug['status_note'])}", ""]
    refs = []
    if bug.get("facts"):
        refs.append("facts " + ", ".join(fact_link(f, facts) for f in bug["facts"]))
    if bug.get("issues"):
        refs.append("issues " + issue_links(bug["issues"]))
    if bug.get("upstream"):
        refs.append("upstream " + ", ".join(url_link(u) for u in bug["upstream"]))
    if bug.get("prs"):
        refs.append("pull requests " + ", ".join(_pr(p) for p in bug["prs"]))
    if bug.get("files"):
        refs.append("files " + ", ".join(file_link(f) for f in bug["files"]))
    if refs:
        out += ["See: " + "; ".join(refs) + ".", ""]
    out += [f"Found by {md(bug['found_by'])}.", ""]
    for c in bug["checked"]:
        against = ", ".join(f"{k} {v}" for k, v in c["against"].items())
        note = f": {md(c['note'])}" if c.get("note") else ""
        out.append(f"- Checked {c['checked_at']} against {against}{note}")
    return rewrite_links("\n".join(out) + "\n", bug["_path"], {})


def _pr(p: Any) -> str:
    if isinstance(p, int):
        return f"[#{p}]({REPO}/pull/{p})"
    return url_link(str(p)) if str(p).startswith("http") else md(str(p))


# -- the characterization -------------------------------------------------------


def load_facts(root: Path) -> dict[str, dict]:
    from sverify_dev import facts

    docs = [_load(p) for p in sorted(facts.load(root / "characterization"))]
    return {d["id"]: d for d in sorted(docs, key=lambda d: (d["engine"], d["area"], d["id"]))}


def fact_entry(fact: dict, bugs: Mapping[str, dict], engines: Mapping[str, str]) -> str:
    out = [f"### {fact['id']}: {md(fact['title'])} {{#{fact['id']}}}", ""]
    meta = [
        f"Engine: {fact['engine']} {fact['engine_version']}",
        f"area: {fact['area']}",
        f"status: {fact['status']}",
        f"evidence: {fact['evidence']}",
    ]
    out += ["::: {.ledger-meta}", "; ".join(meta) + ".", ":::", ""]
    out += [f"Verdict: {md(fact['verdict'])}", ""]
    out += [md(p) + "\n" for p in _paragraphs(fact["description"])]
    if fact.get("reference"):
        out += [f"The reference: {md(fact['reference'])}", ""]
    if fact.get("options"):
        out += ["Options: " + ", ".join(f"`{o}`" for o in fact["options"]) + ".", ""]
    if fact.get("rows"):
        rows = [
            " ".join(f"`{r[k]}`" for k in ("group", "option") if k in r)
            + f" ({', '.join(r['types'])}"
            + (f"; evidence {r['evidence']}" if r.get("evidence") else "")
            + ")"
            for r in fact["rows"]
        ]
        out += ["Rows of the choice tables: " + "; ".join(rows) + ".", ""]
    if fact.get("constructs"):
        out += ["Constructs: " + ", ".join(f"`{c}`" for c in fact["constructs"]) + ".", ""]
    if fact.get("settings"):
        out += [f"Settings: `{json.dumps(fact['settings'], sort_keys=True)}`.", ""]
    refs = []
    if cited := [b for b in bugs.values() if fact["id"] in b.get("facts", [])]:
        refs.append("upstream ledger " + ", ".join(bug_link(b["id"], bugs) for b in cited))
    if fact.get("ledger_entries"):
        refs.append(f"about {fact['ledger_entries']} entries of the replay ledger")
    if fact.get("issues"):
        refs.append("issues " + issue_links(fact["issues"]))
    if fact.get("prs"):
        refs.append("pull requests " + ", ".join(_pr(p) for p in fact["prs"]))
    for key, word in (("supersedes", "supersedes"), ("superseded_by", "superseded by")):
        if fact.get(key):
            ids = fact[key] if isinstance(fact[key], list) else [fact[key]]
            refs.append(word + " " + ", ".join(fact_link(f, engines) for f in ids))
    if refs:
        out += ["See: " + "; ".join(refs) + ".", ""]
    out += ["Provenance:", ""]
    for p in fact["provenance"]:
        line = f"- {p['checked_at']}, {p['method']}, by {md(str(p['checked_by']))}"
        if p.get("notes"):
            line += f": {md(p['notes'])}"
        out.append(line)
        for e in p.get("evidence") or []:
            out.append(f"    - {_evidence(e)}")
    return rewrite_links("\n".join(out) + "\n", fact["_path"], {})


def _evidence(e: dict) -> str:
    parts = []
    if e.get("sql"):
        parts.append(f"`{e['sql']}`" if "`" not in e["sql"] else md(e["sql"]))
    if "observed" in e:
        observed = e["observed"] if isinstance(e["observed"], str) else json.dumps(e["observed"])
        parts.append(f"gives `{observed}`" if "`" not in observed else md(observed))
    if e.get("probe"):
        parts.append(f"probe `{e['probe']}`")
    if e.get("file"):
        parts.append(f"in {file_link(e['file'])}")
    if e.get("test"):
        parts.append(f"test `{e['test']}`")
    if e.get("url"):
        parts.append(url_link(e["url"]))
    if e.get("note"):
        parts.append(md(e["note"]))
    return " ".join(parts) if parts else md(json.dumps(e))


def facts_page(
    title: str,
    facts: list[dict],
    bugs: Mapping[str, dict],
    engines: Mapping[str, str],
    areas: list[dict],
) -> str:
    order = [a["id"] for a in areas]
    out = [
        front(title, f"{len(facts)} facts: what the engine does, with provenance"),
        "Each fact records what the engine does at a pinned version, what the reference "
        "semantics does, and the checks behind it, from "
        f"[`characterization/`]({REPO}/tree/main/characterization) "
        f"([the format]({BLOB}/characterization/fact.schema.json)). "
        "Evidence runs from `docs` to `source`, `engine_test`, `probe`, `fuzz` and `proof`.",
        "",
    ]
    several = len({f["engine"] for f in facts}) > 1
    for engine in sorted({f["engine"] for f in facts}):
        mine = [f for f in facts if f["engine"] == engine]
        for area in sorted({f["area"] for f in mine}, key=lambda a: _index(order, a)):
            head = f"{PROJECTS.get(engine, engine)}: {area}" if several else area
            out += [f"## {head}", ""]
            out += [fact_entry(f, bugs, engines) for f in mine if f["area"] == area]
    return "\n".join(out)


def _index(order: list[str], item: str) -> int:
    return order.index(item) if item in order else len(order)


def coverage_page(areas: list[dict], facts: list[dict]) -> str:
    engines = sorted({f["engine"] for f in facts}, key=lambda e: (e not in dict(FACT_PAGES), e))
    by_engine: dict[str, dict[str, list[dict]]] = {e: {} for e in engines}
    for f in facts:
        if f.get("superseded_by"):
            continue
        for item in f.get("options", []):
            by_engine[f["engine"]].setdefault(item, []).append(f)
    out = [
        front("Coverage", "The characterization checklist, item by item, per engine"),
        "The checklist of [`characterization/areas.json`]"
        f"({BLOB}/characterization/areas.json): for each item, the facts that settle it on "
        "each engine and the strongest evidence among them, or `missing`. "
        "`python -m sverify_dev.facts --coverage <engine>` prints the same.",
        "",
        "| Engine | Items settled | Facts |",
        "|---|---|---|",
    ]
    items = [i for a in areas for i in a["items"]]
    for e in engines:
        settled = sum(1 for i in items if by_engine[e].get(i["id"]))
        n = sum(1 for f in facts if f["engine"] == e)
        out.append(f"| {PROJECTS.get(e, e)} | {settled} of {len(items)} | {n} |")
    out.append("")
    engine_ids = {f["id"]: f["engine"] for f in facts}
    for a in areas:
        out += [f"## {a['id']} {{#area-{a['id']}}}", ""]
        out += ["| Item | Question | " + " | ".join(PROJECTS.get(e, e) for e in engines) + " |"]
        out += ["|---|---|" + "---|" * len(engines)]
        for i in a["items"]:
            row = [f"`{i['id']}`", cell(i.get("question", ""))]
            for e in engines:
                fs = by_engine[e].get(i["id"], [])
                if not fs:
                    row.append("missing")
                    continue
                best = max((f["evidence"] for f in fs), key=lambda v: _index(EVIDENCE, v))
                links = ", ".join(fact_link(f["id"], engine_ids) for f in fs)
                row.append(f"{best}: {links}")
            out.append("| " + " | ".join(row) + " |")
        out.append("")
    return "\n".join(out)


# -- the index with its filter ----------------------------------------------------

_FILTER = """
```{=html}
<input id="ledger-filter" type="search" placeholder="Filter by id, engine, option, status or text"
  style="width:100%;padding:0.4rem;margin:0.5rem 0 1rem 0" aria-label="Filter the ledgers">
<script>
document.addEventListener("DOMContentLoaded", () => {
  const input = document.getElementById("ledger-filter");
  const rows = Array.from(document.querySelectorAll("#ledger-entries tbody tr"));
  const count = document.getElementById("ledger-count");
  const apply = () => {
    const words = input.value.toLowerCase().split(/\\s+/).filter(Boolean);
    let shown = 0;
    for (const row of rows) {
      const text = row.textContent.toLowerCase();
      const hit = words.every((w) => text.includes(w));
      row.style.display = hit ? "" : "none";
      shown += hit;
    }
    count.textContent = `${shown} of ${rows.length} entries`;
  };
  const q = new URLSearchParams(location.search).get("q");
  if (q) input.value = q;
  input.addEventListener("input", apply);
  apply();
});
</script>
```
"""


def index_page(bugs: Mapping[str, dict], facts: Mapping[str, dict]) -> str:
    gaps = [b for b in bugs.values() if b.get("kind") == "spec-gap"]
    real = [b for b in bugs.values() if b.get("kind") != "spec-gap"]
    counts = {e: sum(1 for f in facts.values() if f["engine"] == e) for e, _ in FACT_PAGES}
    other = len(facts) - sum(counts.values())
    out = [
        front("Ledgers", "What sverify knows about each engine, and what it found upstream"),
        "Sverify keeps two ledgers, both JSON documents in the repository with their "
        "provenance. The site renders them at build time, so the site's search finds an "
        "entry by its id, engine, function, option or text, and the table below filters them.",
        "",
        f"- [Upstream bugs](upstream-bugs.md): {len(real)} bugs found in SQLGlot, the engines, "
        "Ibis, delta-rs and Substrait's tooling, each with a reproduction and how sverify "
        f"handles it ([`upstream/`]({REPO}/tree/main/upstream)).",
        f"- [Spec gaps](spec-gaps.md): {len(gaps)} behaviours Substrait's extension YAMLs "
        "leave unspecified though Substrait could express them.",
        f"- [DuckDB facts](duckdb-facts.md) ({counts['duckdb']}) and "
        f"[Polars facts](polars-facts.md) ({counts['polars']}): each engine's "
        "characterization, a diff against the reference semantics, one fact per finding; "
        f"[other engines](other-facts.md) ({other}).",
        "- [Coverage](coverage.md): the characterization checklist per engine, with the "
        "strongest evidence for each item.",
        "- [Realizability](realizability.md): how a plan verified under the reference runs "
        "on DuckDB and Polars, option by option.",
        "",
        "## All entries",
        "",
        _FILTER,
        '<p id="ledger-count"></p>',
        "",
        entries_table(bugs, facts),
        "",
    ]
    return "\n".join(out)


#: The index table's longest summary, in characters.
SUMMARY_MAX = 160

_STYLE = """<style>
#ledger-entries th:nth-child(1) { width: 16%; }
#ledger-entries th:nth-child(2), #ledger-entries th:nth-child(3),
#ledger-entries th:nth-child(4) { width: 11%; }
#ledger-entries th:nth-child(5) { width: 14%; }
#ledger-entries th:nth-child(6) { width: 37%; }
</style>"""


def plain(text: str | list[str], n: int = SUMMARY_MAX) -> str:
    """One line of plain text: the first sentence of `text`, without Markdown
    (links keep their text, code spans their content), at most `n`
    characters."""
    text = " ".join(_paragraphs(text) if not isinstance(text, str) else [text])
    text = re.sub(r"\[([^\]]*)\]\([^)]*\)", r"\1", text)
    text = re.sub(r"<(https?://[^>]*)>", r"\1", text)
    text = " ".join(text.replace("`", "").split())
    first = re.split(r"(?<=\.)\s", text, maxsplit=1)[0]
    if len(first) <= n:
        return first
    return first[: n - 2].rsplit(" ", 1)[0] + " …"


def _row(href: str, ident: str, cells: list[str]) -> str:
    tds = "".join(f"<td>{html.escape(c)}</td>" for c in cells)
    return f'<tr><td><a href="{href}"><code>{html.escape(ident)}</code></a></td>{tds}</tr>'


def entries_table(bugs: Mapping[str, dict], facts: Mapping[str, dict]) -> str:
    """Every ledger entry, one row each, as HTML: the cells are plain text,
    so no entry's Markdown can break the table."""
    rows = []
    for b in bugs.values():
        page = "spec-gaps" if b.get("kind") == "spec-gap" else "upstream-bugs"
        kind = "spec gap" if b.get("kind") == "spec-gap" else "bug"
        project = PROJECTS.get(b["project"], b["project"])
        rows.append(
            _row(
                f"{page}.html#{b['id']}",
                b["id"],
                [kind, project, b["status"], "", plain(b["summary"])],
            )
        )
    for f in facts.values():
        opts = f.get("options", []) + sorted(
            {r["group"] for r in f.get("rows", []) if "group" in r}
        )
        project = f"{PROJECTS.get(f['engine'], f['engine'])} {f['engine_version']}"
        rows.append(
            _row(
                f"{page_id(f['engine'])}.html#{f['id']}",
                f["id"],
                [
                    f"fact ({f['area']})",
                    project,
                    f"{f['status']}, {f['evidence']}",
                    " ".join(opts),
                    plain(f"{plain(f['title'], 999)}: {plain(f['verdict'], 999)}"),
                ],
            )
        )
    head = "".join(
        f"<th>{h}</th>" for h in ("Id", "Kind", "Project", "Status", "Options", "Summary")
    )
    return "\n".join(
        [
            "```{=html}",
            _STYLE,
            '<table id="ledger-entries" class="table">',
            f"<thead><tr>{head}</tr></thead><tbody>",
            *rows,
            "</tbody></table>",
            "```",
        ]
    )


def _short(text: str, n: int = 200) -> str:
    text = " ".join(text.split())
    return text if len(text) <= n else text[: n - 1].rsplit(" ", 1)[0] + " …"


# -- the pages of docs/ ---------------------------------------------------------

#: The pages of `docs/` the site renders, by section (a directory of the site,
#: `sections:` in `great-docs.yml`), in order: the reference (what a plan
#: means, what 1.x keeps) and the design (how and why). The pages for
#: contributors (the decision log, the proof map, the coverage targets, the
#: layers) stay off the site; links to them go to GitHub. `docs/README.md` maps
#: every page to its kind.
DOC_SECTIONS: dict[str, list[tuple[str, str, str]]] = {
    "semantics": [
        ("docs/reference-semantics.md", "Reference semantics", "What a plan means, row by row"),
        ("docs/stability.md", "Stability in 1.x", "The formats, proofs, API and engines 1.x keeps"),
    ],
    "design": [
        ("docs/how-it-works.md", "How it works", "The checker, incremental views and the engines"),
        (
            "docs/engine-profiles.md",
            "Engine profiles",
            "Each engine's profile, shims and translation",
        ),
        ("docs/float-bounds.md", "Float error bounds", "Proved error bounds for doubles"),
        (
            "docs/optimizations.md",
            "Proved optimizations",
            "Guards, sharding, rewrites, pruning, IVM",
        ),
        ("docs/nested-values.md", "Nested values", "Lists, structs and lambdas in the model"),
        (
            "docs/trusted-base.md",
            "The trusted base",
            "What a result rests on that the kernel does not check",
        ),
        ("docs/prior-work.md", "Prior work", "The work sverify builds on, and related tools"),
    ],
}


def site_names() -> dict[str, tuple[str, str]]:
    """Each file of the repository the site renders: its section and page name."""
    names = {
        "docs/examples.md": ("examples", "examples"),
        "docs/realizability.md": ("ledgers", "realizability"),
    }
    for section, pages in DOC_SECTIONS.items():
        for path, _, _ in pages:
            names[path] = (section, Path(path).stem)
    return names


def relative(names: Mapping[str, tuple[str, str]], section: str) -> dict[str, str]:
    """The links from a page of `section` to the site's pages: `name.md` in the
    same section, `../other/name.md` in another; Quarto turns them into the
    pages' URLs."""
    return {
        path: f"{name}.md" if there == section else f"../{there}/{name}.md"
        for path, (there, name) in names.items()
    }


# -- writing ----------------------------------------------------------------------


def write(out: Path, root: Path = ROOT) -> None:
    bugs = load_bugs(root)
    facts = load_facts(root)
    areas = json.loads((root / "characterization/areas.json").read_text())["areas"]
    engines = {f["id"]: f["engine"] for f in facts.values()}

    ledgers = out / "ledgers"
    examples = out / "examples"
    for d in (ledgers, examples, *(out / s for s in DOC_SECTIONS)):
        shutil.rmtree(d, ignore_errors=True)
        d.mkdir(parents=True)
    local = site_names()

    (ledgers / "index.qmd").write_text(index_page(bugs, facts))
    real = [b for b in bugs.values() if b.get("kind") != "spec-gap"]
    gaps = [b for b in bugs.values() if b.get("kind") == "spec-gap"]
    (ledgers / "01-upstream-bugs.md").write_text(
        front("Upstream bugs", f"{len(real)} bugs found upstream, with how sverify handles each")
        + "Bugs and surprising behaviours sverify found in the projects it builds on, from "
        f"[`upstream/bugs/`]({REPO}/tree/main/upstream/bugs) "
        f"([the format]({BLOB}/upstream/bug.schema.json), "
        f"[the prefixes]({BLOB}/upstream/README.md)).\n\n" + bugs_by_project(real, engines)
    )
    (ledgers / "02-spec-gaps.md").write_text(
        front("Spec gaps", f"{len(gaps)} behaviours Substrait could express and leaves open")
        + "Behaviour Substrait's extension YAMLs leave unspecified, though Substrait could "
        "express it with an option, an option's value or a default, where engines differ "
        f"([core-semantics.md]({BLOB}/docs/core-semantics.md)).\n\n"
        + bugs_by_project(gaps, engines)
    )
    pages = [(e, p, f"{PROJECTS[e]} facts") for e, p in FACT_PAGES]
    for n, (engine, page, title) in enumerate(pages, start=3):
        mine = [f for f in facts.values() if f["engine"] == engine]
        (ledgers / f"0{n}-{page}.md").write_text(facts_page(title, mine, bugs, engines, areas))
    others = [f for f in facts.values() if f["engine"] not in dict(FACT_PAGES)]
    (ledgers / f"05-{OTHER_FACTS}.md").write_text(
        facts_page("Other engines' facts", others, bugs, engines, areas)
    )
    (ledgers / "06-coverage.md").write_text(coverage_page(areas, list(facts.values())))
    source = root / "docs/realizability.md"
    text = rewrite_links(strip_title(source.read_text()), source, relative(local, "ledgers"))
    (ledgers / "07-realizability.md").write_text(
        front("Realizability", "How a plan verified under the reference runs on each engine") + text
    )

    source = root / "docs/examples.md"
    text = rewrite_links(strip_title(source.read_text()), source, relative(local, "examples"))
    (examples / "examples.md").write_text(
        front("Examples", "Sverify's features in ten short examples, each a step up", True) + text
    )

    for section, pages in DOC_SECTIONS.items():
        here = relative(local, section)
        for n, (path, title, description) in enumerate(pages, start=1):
            source = root / path
            text = rewrite_links(strip_title(source.read_text()), source, here)
            name = Path(path).stem
            (out / section / f"{n:02d}-{name}.md").write_text(
                front(title, description, True) + text
            )


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--out", type=Path, default=ROOT / "python")
    args = parser.parse_args()
    write(args.out)
    print(f"wrote examples/, {'/, '.join(DOC_SECTIONS)}/ and ledgers/ under {args.out}")


if __name__ == "__main__":
    main()
