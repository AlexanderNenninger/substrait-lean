"""Engine facts (`characterization/<engine>/facts/*.json`): what each engine
does, one finding per document, with the checks that support it.

Maintainer tooling (`sverify_dev`): not in the wheel, and not part of sverify's
API.

Each document follows `characterization/fact.schema.json`: the engine and its
exact version, what the engine does, what the reference semantics does, a
status, and its provenance (when it was checked, how, by what, and the
evidence: links at a tag or commit, ledgers, probes, SQL repros).

A fact's `options` names the items of the characterization checklist
(`characterization/areas.json`) it settles, and its `rows` the rows of the
engine choice tables it settles: a function group of `core/Sverify/Core/Functions.lean`
(`groups`), one of the group's options and the types it was checked at. Its
`evidence` is the strongest kind of check in its provenance: `docs` <
`source` < `engine_test` < `probe` < `fuzz` < `proof`. The documents are the record; there
is no generated overview. The command

    uv run python -m sverify_dev.facts

checks them (`tests/test_facts.py` runs the same check), and

    uv run python -m sverify_dev.facts --coverage polars

lists, per row (group × option × type), the engine's facts that settle it
with their evidence, or `missing`, then per area and item of the checklist
as a rollup.
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
FUNCTIONS = REPO / "core" / "Sverify" / "Core" / "Functions.lean"

#: The kinds of evidence, weakest first.
EVIDENCE = ("docs", "source", "engine_test", "probe", "fuzz", "proof")
#: The evidence each provenance method gives. An engine's own test with an
#: expected result (DuckDB's sqllogictests, Polars's unit tests), read or
#: replayed (`sverify_dev.slt`), pins the intended behaviour on its input; a
#: hand-written repro runs the engine on chosen inputs, as a probe does.
METHOD_EVIDENCE = {
    "docs": "docs",
    "source-reading": "source",
    "engine-test": "engine_test",
    "replay": "engine_test",
    "probe": "probe",
    "manual-repro": "probe",
    "fuzz": "fuzz",
    "proof": "proof",
}

_INTS = ("i8", "i16", "i32", "i64")
_FLOATS = ("fp32", "fp64")
#: The types a group's functions take, by group or by the group's family
#: (`int.` for every `int.*` group). A group not listed takes `any`.
GROUP_TYPES: dict[str, tuple[str, ...]] = {
    "int.": _INTS,
    "dec.": ("decimal",),
    "fp.": _FLOATS,
    "cmp": _FLOATS,
    "str.": ("string",),
    "time.": ("date", "time", "timestamp", "timestamp_tz"),
    "list.": ("list",),
    "agg.isum": _INTS,
    "agg.fsum": _FLOATS,
    "agg.var": ("i64", "fp64", "decimal"),
    "agg.stat": ("i64", "fp64", "decimal"),
    "agg.order": (*_FLOATS, "list"),
    "agg.quant": ("i64", "fp64", "decimal"),
}
#: Options that only bear on some types: a row takes the group's types that
#: the option's list also has.
OPTION_TYPES: dict[str, tuple[str, ...]] = {
    **dict.fromkeys(
        ("nan_equality", "nan_order", "nan_kind", "nan_creation", "zero_sign", "float_overflow"),
        _FLOATS,
    ),
    "fp32": ("fp32",),
    "list_null_order": ("list",),
    "decimal_rescale": ("decimal",),
    "date_range": ("date", "timestamp", "timestamp_tz"),
    "time_interval_months": ("time",),
}
#: The group of a row at an option no function group takes (`null_order`),
#: and of `RELATION_OPTIONS`.
NO_GROUP = "-"
#: Options of relations as well as of function groups: `tie_order` is also
#: the order of a sort's ties.
RELATION_OPTIONS = ("tie_order",)

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


def groups(functions: Path = FUNCTIONS) -> dict[str, list[str]]:
    """Each function group's options: `Functions.groups` of `Functions.lean`
    (`substrait-check --options` prints the same), read from the source so no
    Lean build is needed."""
    text = functions.read_text()
    block = text[text.index("def groups") :]
    block = block[: block.index("\n\n")]
    found = {
        g: re.findall(r'"([a-z0-9_]+)"', opts)
        for g, opts in re.findall(r'\("([a-z0-9.]+)", \[([^\]]*)\]\)', block)
    }
    if not found:
        raise ValueError(f"no groups in {functions}")
    return found


def types_of(group: str, option: str) -> tuple[str, ...]:
    """The types of the row (`group`, `option`)."""
    family = next(
        (t for g, t in GROUP_TYPES.items() if g == group or (g[-1] == "." and group.startswith(g))),
        None,
    )
    narrow = OPTION_TYPES.get(option)
    if family is None:
        return narrow or ("any",)
    if narrow is None:
        return family
    return tuple(t for t in family if t in narrow) or family


Row = tuple[str, str, str]


def rows(root: Path = ROOT, functions: Path = FUNCTIONS) -> list[Row]:
    """The rows of the engine choice tables, (group, option, type): every
    group's options at its types, then the checklist's options no group
    takes and `RELATION_OPTIONS`, under `NO_GROUP`."""
    by_group = groups(functions)
    found = [(g, o, t) for g, opts in by_group.items() for o in opts for t in types_of(g, o)]
    grouped = {o for opts in by_group.values() for o in opts}
    areas = json.loads((root / AREAS.name).read_text())["areas"]
    for area in areas:
        for item in area["items"]:
            if item["kind"] == "option" and (
                item["id"] not in grouped or item["id"] in RELATION_OPTIONS
            ):
                found += [(NO_GROUP, item["id"], t) for t in types_of(NO_GROUP, item["id"])]
    return found


def evidence_of(fact: Fact) -> str:
    """The strongest evidence of `fact`'s provenance."""
    levels = [METHOD_EVIDENCE[c["method"]] for c in fact["provenance"]]
    return max(levels, key=EVIDENCE.index)


def validate(docs: dict[Path, Fact], root: Path = ROOT, functions: Path = FUNCTIONS) -> list[str]:
    """What is wrong with the documents: the schema, the file names, ids that
    repeat, checklist items and rows that do not exist, an `evidence` level
    other than the provenance's strongest, and references to files, probes or
    facts that do not exist."""
    validator = jsonschema.Draft202012Validator(json.loads((root / SCHEMA.name).read_text()))
    repo = root.parent
    problems: list[str] = []
    items = [i for area in checklist(root).values() for i in area]
    item_set = set(items)
    table_rows = set(rows(root, functions))
    table = {(g, o) for g, o, _ in table_rows}
    problems += [
        f"{AREAS.name}: item {i} repeats" for i in sorted(set(items)) if items.count(i) > 1
    ]
    ids = {str(f.get("id")) for f in docs.values()}
    # A fact named in prose (`duckdb-R2`) or a group of them (`duckdb-R15`
    # for `duckdb-R15-…`): every id and each of its dash-separated prefixes.
    named_ids = {i[:k] for i in ids for k in range(len(i) + 1) if k == len(i) or i[k] == "-"}
    fact_name = re.compile(rf"\b(?:{'|'.join(engines(root))})-[A-Z][A-Za-z0-9-]*[A-Za-z0-9]")
    # Each probe file's constructs, read once: many facts cite the same file.
    probes: dict[Path, set[str]] = {}
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
            if item not in item_set:
                problems.append(f"{where}: {item!r} is not an item of {AREAS.name}")
        if f["evidence"] != evidence_of(f):
            problems.append(
                f"{where}: evidence is {f['evidence']!r}; its provenance's strongest is "
                f"{evidence_of(f)!r}"
            )
        named = [
            (r.get("group", NO_GROUP), r["option"], t)
            for r in f.get("rows", [])
            for t in r["types"]
        ]
        problems += [
            f"{where}: rows name {g} × {o} × {t} twice"
            for g, o, t in sorted(set(named))
            if named.count((g, o, t)) > 1
        ]
        for row in f.get("rows", []):
            group = row.get("group", NO_GROUP)
            name = f"{group} × {row['option']}"
            if (group, row["option"]) not in table:
                problems.append(f"{where}: {name} is not a row of the choice tables")
                continue
            for t in row["types"]:
                if (group, row["option"], t) not in table_rows:
                    problems.append(
                        f"{where}: {name} has no type {t!r}; its types are "
                        f"{', '.join(types_of(group, row['option']))}"
                    )
            level = row.get("evidence", f["evidence"])
            if EVIDENCE.index(level) > EVIDENCE.index(f["evidence"]):
                problems.append(f"{where}: {name}'s evidence {level!r} is stronger than the fact's")
            if row["option"] in item_set and row["option"] not in f.get("options", []):
                problems.append(f"{where}: rows name {row['option']!r}, which options lack")
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
                    if target not in probes:
                        probes[target] = {
                            p["construct"] for p in json.loads(target.read_text())["probes"]
                        }
                    if e["probe"] not in probes[target]:
                        problems.append(f"{where}: {e['file']} has no probe {e['probe']!r}")
        # Prose that names another fact (`duckdb-R2`) names one that exists,
        # or a group of them (`duckdb-R15` for `duckdb-R15-…`).
        text = json.dumps([f.get("description"), f.get("reference"), f["provenance"]])
        for name in fact_name.findall(text):
            if name not in named_ids:
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


RowCoverage = dict[Row, list[tuple[str, str]]]


def row_coverage(
    docs: dict[Path, Fact], engine: str, root: Path = ROOT, functions: Path = FUNCTIONS
) -> RowCoverage:
    """Per row (group, option, type), `engine`'s current facts that settle it,
    as (id, evidence): the row entry's own `evidence`, else the fact's. An
    empty list is a missing row."""
    found: RowCoverage = {r: [] for r in rows(root, functions)}
    for f in docs.values():
        if f.get("engine") != engine or "superseded_by" in f:
            continue
        for row in f.get("rows", []):
            for t in row["types"]:
                key = (row.get("group", NO_GROUP), row["option"], t)
                if key in found:
                    found[key].append((f["id"], row.get("evidence", f.get("evidence", "?"))))
    return found


def strongest(facts_: list[tuple[str, str]]) -> str:
    """The strongest evidence among a row's facts, `missing` for none."""
    levels = [e for _, e in facts_ if e in EVIDENCE]
    return max(levels, key=EVIDENCE.index) if levels else "missing"


def row_report(found: RowCoverage, root: Path = ROOT) -> str:
    """`row_coverage`'s result as text: per group and option, each type's
    facts with their evidence, then counts per area and per evidence."""
    lines = []
    by_pair: dict[tuple[str, str], list[str]] = {}
    for (g, o, t), fs in found.items():
        settled = ", ".join(f"{i} ({e})" for i, e in fs) or "missing"
        by_pair.setdefault((g, o), []).append(f"{t}: {settled}")
    for (g, o), cells in by_pair.items():
        lines.append(f"{g} × {o}")
        lines += [f"  {c}" for c in cells]
    area_of = {i: a for a, items in checklist(root).items() for i in items}
    per_area: dict[str, list[int]] = {}
    for (_, o, _), fs in found.items():
        counts = per_area.setdefault(area_of.get(o, "(not on the checklist)"), [0, 0])
        counts[0] += bool(fs)
        counts[1] += 1
    lines.append("rows by area: " + ", ".join(f"{a} {c}/{n}" for a, (c, n) in per_area.items()))
    levels = [strongest(fs) for fs in found.values()]
    lines.append(
        "rows by strongest evidence: "
        + ", ".join(f"{e} {levels.count(e)}" for e in (*EVIDENCE, "missing"))
    )
    covered = sum(1 for fs in found.values() if fs)
    lines.append(f"{covered}/{len(found)} rows settled")
    return "\n".join(lines)


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
        print(row_report(row_coverage(docs, args.coverage)))
        print()
        print(report(coverage(docs, args.coverage)))
        return
    print(f"{len(docs)} facts, well-formed")


if __name__ == "__main__":
    main()
