"""The realizability table: `obligations reference E` for each engine (#444,
step 3b).

Maintainer tooling (`sverify_dev`): not in the wheel, and not part of sverify's
API.

`substrait-check --realizability` computes, for each engine profile and each
group and option, how the translation from the reference discharges the
option (`SubstraitLean/Obligations.lean`). This module renders it as
`docs/realizability.md`:

    uv run python -m sverify_dev.realizability --write

`--check` exits 1 when the file is stale: run it
on a branch to see whether the change costs a shim, a precondition or a
refusal. The `Generated files` workflow rewrites the file on `main` after
every merge, so feature branches leave it alone. Two PRs that each kept it
current used to make it stale once both merged, and the batch failed.
"""

from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path
from typing import Any

from sverify import _engines

ROOT = Path(__file__).resolve().parents[3]
DOC = ROOT / "docs" / "realizability.md"


#: The summary's column for a case.
LABELS = {
    "refines_up_to": "observed",
    "approx": "observed (tolerance)",
    "uncharacterized": "not characterized",
}

#: The cases, in the order the summary counts them.
CASES = ("native", "shim", "refines_up_to", "approx", "precondition", "refused", "uncharacterized")


def table() -> dict[str, Any]:
    """`substrait-check --realizability`."""
    from sverify.engine import checker_path

    out = subprocess.run(
        [str(checker_path()), "--realizability"],
        capture_output=True,
        text=True,
        check=True,
        timeout=120,
    ).stdout
    return json.loads(out)


def _fact_link(engine: str, ident: str) -> str:
    """A fact id as a link to its document; a test id or another id as code."""
    path = _fact_path(engine, ident)
    if path is None:
        return f"`{ident}`"
    return f"[{ident}](../{path.relative_to(ROOT).as_posix()})"


#: Evidence levels, weakest first, as `characterization/fact.schema.json`'s
#: `evidence` (#601): `docs` < `source` < `engine_test` < `probe` < `fuzz` <
#: `proof`; `missing` where no fact covers the row.
LEVELS = ("missing", "docs", "source", "engine_test", "probe", "fuzz", "proof")

#: A fact's level from its checks' `provenance.method`, until each fact
#: states its own `evidence` (which `fact_level` prefers once it does).
METHOD_LEVELS = {
    "docs": "docs",
    "source-reading": "source",
    "probe": "probe",
    "manual-repro": "probe",
    "engine-test": "engine_test",
    "replay": "engine_test",
    "fuzz": "fuzz",
    "proof": "proof",
}

#: Theorems that relate the tables, not what the engine does: a row resting
#: only on one of these has no evidence of the engine's behaviour.
TABLE_THEOREMS = ("Choice.le_sound",)


def _fact_path(engine: str, ident: str) -> Path | None:
    for e in (engine, *sorted(_engines.NAMED)):
        path = ROOT / "characterization" / e / "facts" / f"{ident}.json"
        if path.exists():
            return path
    return None


def fact_level(engine: str, ident: str) -> str:
    """The strongest check of a fact: its `evidence` field where it has one,
    else the best `provenance.method` of its checks; `missing` for no fact."""
    path = _fact_path(engine, ident)
    if path is None:
        return "missing"
    doc = json.loads(path.read_text())
    if doc.get("evidence") in LEVELS:
        return doc["evidence"]
    found = [METHOD_LEVELS.get(p.get("method"), "missing") for p in doc.get("provenance") or []]
    return max(found, key=LEVELS.index, default="missing")


def row_level(engine: str, row: dict[str, Any]) -> str:
    """`proof` where a Lean lemma about the engine covers the row, else the
    strongest level among its facts, `missing` where it has none."""
    if row.get("evidence") == "proved" and row.get("theorem") not in TABLE_THEOREMS:
        return "proof"
    levels = [fact_level(engine, f) for f in row.get("facts") or []]
    return max(levels, key=LEVELS.index, default="missing")


def _q(q: dict[str, Any]) -> str:
    parts = []
    for k, v in q.items():
        parts.append(f"{k} {v['bound'] + ' bound' if isinstance(v, dict) else v}")
    return ", ".join(parts) or "exact"


def _behaviours(bs: list[str]) -> str:
    return ", ".join(f"`{b}`" for b in bs) if bs else "none"


def case_cell(row: dict[str, Any]) -> str:
    case = row["case"]
    if case == "shim":
        cell = f"shim `{row['shim']}` ({row.get('cost') or 'no cost'})"
    elif case == "refines_up_to":
        cell = f"observed: up to {_q(row.get('observation', row.get('q')) or {})}"
    elif case == "approx":
        cell = f"observed: within the {row['bound']}'s bound"
    elif case == "precondition":
        cell = f"precondition: {row['precondition']}"
    elif case == "uncharacterized":
        cell = "not characterized"
    else:
        cell = case
    if row.get("stated_missing"):
        cell += f"; stated {_behaviours(row['stated_missing'])}: not native"
    return cell


def evidence_cell(engine: str, row: dict[str, Any]) -> str:
    facts = ", ".join(_fact_link(engine, f) for f in row.get("facts") or [])
    if row.get("evidence") == "proved":
        return f"proved `{row['theorem']}`" + (f"; {facts}" if facts else "")
    if row.get("evidence") == "tested":
        return f"tested: {facts}"
    return ""


def counts(rows: list[dict[str, Any]]) -> dict[str, int]:
    return {c: sum(r["case"] == c for r in rows) for c in CASES}


def render(t: dict[str, Any]) -> str:
    out = [
        "# Realizability",
        "",
        "<!-- Generated by `python -m sverify_dev.realizability --write` from",
        "     `substrait-check --realizability`; tests/test_realizability.py checks it. -->",
        "",
        "For each engine and each option of the catalogue, how a plan verified under the",
        "reference runs there: `obligations reference E` of",
        "[core-semantics.md](core-semantics.md#obligations-option-by-option), computed",
        "from the reference's choices and tools and the engine's choices and observation",
        "rows (`SubstraitLean/Obligations.lean`). A row is per option, or per function",
        "group where a profile chooses by group.",
        "",
        "- native: the engine's behaviour is one the reference allows.",
        "- shim: the translation writes the shim first, at its cost: a written argument,",
        "  an expression per row or group, or a sort.",
        "- observed: the same as a result the reference allows up to an observation",
        "  (D18), such as rows as a multiset; a postcondition that observes more needs",
        "  the row's shim, or the plan is refused there.",
        "- observed (tolerance): within the plan's float bound (#85) of a result the",
        "  reference allows, a tolerance being an observation of doubles.",
        "- precondition: the engine differs only where the reference raises, so a plan",
        "  verified never to raise never reaches the difference; where the precondition",
        "  is checked on the data, its guard stays.",
        "- not characterized: outside the prototype slice; the engine's profile allows",
        "  every behaviour of the core there.",
        "",
        '"Stated … not native" lists the behaviours a plan may state for a Substrait',
        "option, other than the default, that the engine does not give as it is.",
        "",
        "Evidence is the Lean theorem a row rests on, or the facts and tests that record",
        "what the engine does. A row's level is `proof` where a Lean lemma about the",
        "engine covers it (its trusted model rests on the facts it cites), else the",
        "strongest check among its facts (`docs` < `source` < `engine_test` < `probe` <",
        "`fuzz`), and",
        "`missing` where no fact records the engine's behaviour; `Choice.le_sound` relates",
        "the tables only. The shim count per engine is D9's measure of few shims.",
        "",
        "## Summary",
        "",
        "| Engine | Version | Translation | Shims | "
        + " | ".join(LABELS.get(c, c) for c in CASES[0:1] + CASES[2:])
        + " | Refused functions |",
        "|---|---|---|---|" + "---|" * (len(CASES) - 1) + "---|",
    ]
    for name, e in t.items():
        n = counts(e["rows"])
        cells = [str(n[c]) for c in CASES[0:1] + CASES[2:]]
        out.append(
            f"| {_engines.title(name)} | {e['version']} | `{e['theorem']}` | "
            f"{len(e['shims'])} | " + " | ".join(cells) + f" | {len(e['refused_functions'])} |"
        )
    out += [
        "",
        "Rows per evidence level:",
        "",
        "| Engine | " + " | ".join(LEVELS[::-1]) + " |",
        "|---|" + "---|" * len(LEVELS),
    ]
    for name, e in t.items():
        levels = [row_level(name, r) for r in e["rows"]]
        out.append(
            f"| {_engines.title(name)} | "
            + " | ".join(str(levels.count(lv)) for lv in LEVELS[::-1])
            + " |"
        )
    out += ["", "## Shims", "", "| Engine | Shim | Cost | Options |", "|---|---|---|---|"]
    for name, e in t.items():
        for s in e["shims"]:
            opts = sorted(
                {
                    (f"{r['group']}: " if r["group"] else "") + f"`{r['option']}`"
                    for r in e["rows"]
                    if r["case"] == "shim" and r["shim"] == s["name"]
                }
            )
            out.append(
                f"| {_engines.title(name)} | `{s['name']}` | {s['cost']} | {', '.join(opts)} |"
            )
    for name, e in t.items():
        title = _engines.title(name)
        costs: dict[str, int] = {}
        for s in e["shims"]:
            costs[s["cost"]] = costs.get(s["cost"], 0) + 1
        by_cost = ", ".join(f"{v} {k}" for k, v in sorted(costs.items()))
        out += [
            "",
            f"## {title} {e['version']}",
            "",
            f"{len(e['shims'])} shims ({by_cost}). The translation as a whole rests on "
            f"`{e['theorem']}`.",
            "",
            "| Group | Option | Reference's tool | Reference | "
            f"{title} | Case | Level | Evidence |",
            "|---|---|---|---|---|---|---|---|",
        ]
        for r in e["rows"]:
            out.append(
                f"| {r['group'] or 'every'} | `{r['option']}` | {r['tool']} | "
                f"{_behaviours(r['reference'])} | {_behaviours(r['engine'])} | "
                f"{case_cell(r)} | {row_level(name, r)} | {evidence_cell(name, r)} |"
            )
        if e["refused_functions"]:
            out += ["", f"Refused on {title}, with no expression there:", ""]
            for f in e["refused_functions"]:
                facts = ", ".join(_fact_link(name, i) for i in f["facts"])
                out.append(f"- `{f['function']}` ({facts})")
    return "\n".join(out) + "\n"


def main(argv: list[str]) -> int:
    text = render(table())
    if "--write" in argv:
        DOC.write_text(text)
        return 0
    if "--check" in argv:
        if not DOC.exists() or DOC.read_text() != text:
            fix = "python -m sverify_dev.realizability --write"
            print(f"{DOC.relative_to(ROOT)} is stale: run {fix}")
            return 1
        return 0
    print(text, end="")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
