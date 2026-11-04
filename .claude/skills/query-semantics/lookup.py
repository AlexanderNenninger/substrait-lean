"""What the repository says about a query, profile by profile. The static
first step of the `query-semantics` skill; `probe.py` runs the query.

It names the query's constructs, the Substrait functions they become, the
function groups and the options those meet (#444, `docs/core-semantics.md`),
and prints:

  profiles   with --table: `sv.verify` under each profile (reference,
             duckdb, polars for Ibis, substrait once #600 lands), the
             report, and the route and class to each engine
             (`sverify.routes.choose`)
  options    the (group, option) pairs the query meets
  choices    each profile's row for them (`substrait-check --options`):
             allowed behaviours, class, observation q, shim, facts
  facts      characterization/<engine>/facts/*.json for those options and
             functions, with evidence level and status
  ledger     upstream/bugs/*.json linked to those facts or naming the
             functions: engine bugs and spec gaps (kind "spec-gap")
  parser     SubstraitLean/Parse.lean: how the function is read, or refused
  producer   with --ibis: where the vendored Ibis producer translates each
             operation (sverify/ibis_substrait), or that it doesn't
  prose      catalogue/pitfalls.toml, features.toml, backend_semantics.py,
             the engine modules' docstrings and catalogue/status.json: older
             and broader; read them after the facts

Run from the repository root:
  uv run --project python python .claude/skills/query-semantics/lookup.py \\
      --sql 'SELECT a, CASE WHEN b <> 0 THEN a / b END AS q FROM r' \\
      --table r 'a:int64,b:int64'
"""

from __future__ import annotations

import argparse
import ast
import functools
import json
import re
import subprocess
import sys
import tomllib
from collections.abc import Iterable
from pathlib import Path
from typing import Any

import sqlglot
import sqlglot.expressions as e

ROOT = Path(__file__).resolve().parents[3]

#: Evidence levels, weakest first (#601). A fact without `evidence` takes its
#: provenance's strongest method.
EVIDENCE = ("docs", "source", "engine_test", "probe", "fuzz", "proof")
METHOD_EVIDENCE = {
    "docs": "docs", "source-reading": "source", "replay": "engine_test",
    "engine-test": "engine_test", "manual-repro": "probe", "probe": "probe",
    "fuzz": "fuzz", "proof": "proof",
}  # fmt: skip

#: The engines with a profile; the others are outside the profiles (#271).
PROFILE_ENGINES = ("duckdb", "polars")

# sqlglot node class -> Substrait function names.
SUBSTRAIT = {
    "Div": ["divide"], "IntDiv": ["divide"], "Mod": ["modulus"], "Add": ["add"],
    "Sub": ["subtract"], "Mul": ["multiply"], "Neg": ["negate"], "EQ": ["equal"],
    "NEQ": ["not_equal"], "LT": ["lt"], "GT": ["gt"], "LTE": ["lte"], "GTE": ["gte"],
    "And": ["and"], "Or": ["or"], "Not": ["not"], "Is": ["is_null", "is_not_null"],
    "Coalesce": ["coalesce"], "Nullif": ["nullif"], "Greatest": ["greatest"],
    "Least": ["least"], "Abs": ["abs"], "Pow": ["power"], "Round": ["round"],
    "Floor": ["floor"], "Ceil": ["ceil"], "Sqrt": ["sqrt"], "Exp": ["exp"], "Ln": ["ln"],
    "Upper": ["upper"], "Lower": ["lower"],
    "Length": ["char_length", "character_length"], "DPipe": ["concat"],
    "Concat": ["concat"], "StrPosition": ["strpos"],
    "Substring": ["substring"], "Like": ["like"], "ILike": ["ilike"], "Trim": ["trim", "btrim"],
    "TimestampTrunc": ["date_trunc"], "DateTrunc": ["date_trunc"], "Extract": ["extract"],
    "RowNumber": ["row_number"], "Lag": ["lag"], "Lead": ["lead"], "Sum": ["sum"],
    "Avg": ["avg"], "Min": ["min"], "Max": ["max"], "Count": ["count"],
    "Stddev": ["std_dev"], "StddevSamp": ["std_dev"], "Variance": ["variance"],
    "VarianceSamp": ["variance"], "Corr": ["corr"], "Median": ["median"],
    "RegexpLike": ["regexp_match_substring"], "IsNan": ["is_nan"],
    "Between": ["gte", "lte"], "Rank": ["rank"], "DenseRank": ["dense_rank"],
}  # fmt: skip

#: Options of relations, by the sqlglot node that meets them (group None).
RELATION_OPTIONS = {
    "Ordered": ["null_order", "tie_order"], "Window": ["tie_order"], "Limit": ["tie_order"],
}  # fmt: skip

# sqlglot node -> catalogue features (catalogue/features.toml).
FEATURES = {
    "Where": ["filter"], "Join": ["inner_join"], "Union": ["union_all", "union_distinct"],
    "Intersect": ["intersect_except"], "Except": ["intersect_except"],
    "Distinct": ["distinct"], "Order": ["order_by"], "Limit": ["limit"], "Offset": ["offset"],
    "With": ["cte"], "Group": ["group_by"], "Having": ["having"], "Count": ["count"],
    "Sum": ["sum"], "Avg": ["avg"], "Min": ["min_max"], "Max": ["min_max"],
    "RowNumber": ["row_number"], "Lag": ["lag_lead"], "Lead": ["lag_lead"],
    "Rank": ["rank"], "DenseRank": ["rank"],
    "Div": ["integer_division"], "IntDiv": ["integer_division"], "Case": ["case_when"],
    "Coalesce": ["coalesce_nullif"], "Nullif": ["coalesce_nullif"], "In": ["in_list"],
    "Between": ["between"], "Cast": ["cast_numeric"], "Like": ["like"],
    "RegexpLike": ["regex_match"], "Upper": ["string_basic"], "Lower": ["string_basic"],
    "Substring": ["string_basic"], "Length": ["string_basic"], "DPipe": ["string_basic"],
    "Round": ["math_funcs"], "Abs": ["math_funcs"], "Pow": ["math_funcs"],
    "Extract": ["date_part"], "TimestampTrunc": ["date_trunc"], "DateTrunc": ["date_trunc"],
    "Interval": ["interval_day_time"], "Exists": ["exists_subquery"],
    "Percentile": ["percentile"], "PercentileCont": ["percentile"],
    "ApproxDistinct": ["approx_distinct"], "Stddev": ["stddev_var"], "Corr": ["corr"],
}  # fmt: skip

# sqlglot node -> pitfall tags (catalogue/pitfalls.toml).
PITFALLS = {
    "Div": ["integer_division", "division_by_zero"], "IntDiv": ["integer_division"],
    "Mod": ["division_by_zero"], "Order": ["null_ordering", "tie_order"],
    "Limit": ["limit_without_order", "tie_order"], "Window": ["window_default_frame", "tie_order"],
    "Rank": ["rank_semantics"], "DenseRank": ["rank_semantics"], "Join": ["null_join_keys"],
    "Avg": ["null_aggregate", "empty_aggregate"], "Sum": ["float_sum_order", "empty_aggregate"],
    "Min": ["null_aggregate"], "Max": ["null_aggregate"], "Cast": ["implicit_coercion"],
    "Substring": ["substr_index"], "Like": ["like_escape", "string_collation"],
    "RegexpLike": ["regex_dialect"], "Interval": ["month_arithmetic", "timezone_dst"],
    "Round": ["round_half"], "Percentile": ["percentile_method"],
    "ApproxDistinct": ["approximate"], "Case": ["eager_evaluation"], "Add": ["int_overflow"],
    "Mul": ["int_overflow"], "IsNan": ["float_nan"],
}  # fmt: skip

# sqlglot node class -> words the engine modules' docstrings use for it.
KEYWORDS = {
    "Div": ["division", "divide", " / "], "IntDiv": ["division"], "Mod": ["%", "MOD", "remainder"],
    "Add": ["overflow"], "Mul": ["overflow"], "Sub": ["overflow"], "Order": ["NULL order", "sort"],
    "Ordered": ["NULLS"], "Limit": ["FETCH", "row order"], "Window": ["window", "row order"],
    "RowNumber": ["ROW_NUMBER", "row number"], "Lag": ["LAG"], "Lead": ["LEAD"],
    "Not": ["three-valued", "Kleene"], "And": ["Kleene"], "Or": ["Kleene"], "Is": ["IS TRUE"],
    "In": ["three-valued"], "Cast": ["cast", "CAST"],
    "Like": ["LIKE"], "ILike": ["LIKE"], "Substring": ["substring", "SUBSTR"],
    "Length": ["length", "code point"], "StrPosition": ["strpos"], "Trim": ["trim"],
    "RegexpLike": ["regular expression", "regex"], "Round": ["round"], "Pow": ["POWER", "pow"],
    "Sum": ["sum", "SUM"], "Avg": ["AVG", "average"], "Min": ["MIN"], "Max": ["MAX"],
    "Count": ["COUNT"], "Join": ["join"], "Interval": ["interval"],
    "TimestampTrunc": ["date_trunc", "trunc"], "DateTrunc": ["date_trunc", "trunc"],
    "IsNan": ["NaN"], "Case": ["CASE", "branch"],
}  # fmt: skip

#: Node types that say nothing about semantics.
BORING = {
    "Select", "From", "Table", "Column", "Identifier", "Literal", "Alias", "TableAlias",
    "Star", "Paren", "Tuple", "DataType", "Var", "Boolean", "Subquery",
}  # fmt: skip


def constructs(sql: str) -> set[str]:
    """The sqlglot node classes in the query, by name."""
    tree = sqlglot.parse_one(sql, read="duckdb")
    return {type(n).__name__ for n in tree.walk()}


def special(sql: str) -> list[str]:
    """Pitfalls the node types don't show."""
    tree = sqlglot.parse_one(sql, read="duckdb")
    tags = []
    for n in tree.find_all(e.In):
        if any(isinstance(x, e.Null) for x in n.expressions):
            tags.append("not_in_null")
    for n in tree.find_all(e.Count):
        if isinstance(n.this, e.Distinct):
            tags.append("count_distinct_null")
    if tree.find(e.Limit) and not tree.find(e.Order):
        tags.append("limit_without_order")
    return tags


def grep(path: Path, pattern: str, limit: int = 4) -> list[str]:
    rx = re.compile(pattern)
    lines = path.read_text().splitlines()
    return [
        f"{path.relative_to(ROOT)}:{i}: {ln.strip()[:110]}"
        for i, ln in enumerate(lines, 1)
        if rx.search(ln)
    ][:limit]


def schema_of(cols: str) -> dict[str, str]:
    """`'a:int64,b:string'` as a mapping."""
    return dict(c.split(":", 1) for c in cols.split(","))


# ------------------------------------------------------------ the checker


def checker() -> str | None:
    """The `substrait-check` sverify runs, or None."""
    try:
        from sverify.engine import checker_path

        return str(checker_path())
    except Exception:  # noqa: BLE001
        return None


@functools.cache
def table(flag: str) -> Any:
    """A table the checker prints (`--options`, `--functions`), or None."""
    path = checker()
    if path is None:
        return None
    try:
        out = subprocess.run([path, flag], capture_output=True, text=True, timeout=60, check=True)
        return json.loads(out.stdout)
    except (OSError, subprocess.SubprocessError, json.JSONDecodeError):
        return None


def options_for(fns: Iterable[str], nodes: set[str]) -> list[tuple[str | None, str]]:
    """The (group, option) pairs the functions and relations meet, from
    Lean's functions table (`--functions`, each row with its group and the
    group's options)."""
    out: list[tuple[str | None, str]] = []
    rows = table("--functions") or []
    for name in fns:
        for r in rows:
            if r.get("name") == name and r.get("group"):
                out += [(r["group"], o) for o in r.get("options", [])]
    for n in nodes:
        out += [(None, o) for o in RELATION_OPTIONS.get(n, [])]
    return list(dict.fromkeys(out))


def groups_of(fns: Iterable[str]) -> dict[str, set[str]]:
    rows = table("--functions") or []
    out: dict[str, set[str]] = {}
    for r in rows:
        if r.get("name") in fns and r.get("group"):
            out.setdefault(r["name"], set()).add(r["group"])
    return out


# --------------------------------------------------------------- profiles


def semantics_for(is_sql: bool) -> list[str]:
    """The profiles to verify under. Polars's checks Ibis only; SQL is
    DuckDB's."""
    base = ["reference", "duckdb"] if is_sql else ["reference", "polars", "duckdb"]
    return [*base, "substrait"]


def conditions(requires: list[list[str]], ensures: list[str]) -> tuple[dict, list]:
    """`--requires TABLE EXPR` and `--ensures EXPR`: Ibis deferred expressions
    over `_`, or sverify's conditions (`sv.max_rows(1000)`,
    `sv.equivalent(floats=sv.within(rel=1e-9))`)."""
    import ibis
    import sverify as sv

    ns = {"_": ibis._, "ibis": ibis, "sv": sv}
    req: dict[str, list] = {}
    for name, code in requires:
        req.setdefault(name, []).append(eval(code, ns))  # noqa: S307
    return req, [eval(code, ns) for code in ensures]  # noqa: S307


def verify_profiles(
    transform: Any,
    schemas: dict[str, Any] | None,
    requires: dict | None = None,
    ensures: list | None = None,
) -> dict[str, Any]:
    """`sv.verify` under each profile: semantics -> Report, or the error."""
    import sverify as sv

    out: dict[str, Any] = {}
    for sem in semantics_for(isinstance(transform, str)):
        try:
            out[sem] = sv.verify(
                transform,
                tables=schemas,
                requires=requires or None,
                ensures=ensures or (),
                semantics=sem,
            )
        except ValueError as err:
            msg = str(err)
            if sem == "substrait" and "semantics must be" in msg:
                msg = "no Profile.substrait in this sverify yet (#600)"
            out[sem] = msg
        except Exception as err:  # noqa: BLE001
            out[sem] = f"{type(err).__name__}: {err}"
    return out


def route_line(route: Any) -> str:
    """A route, its class, shims and warnings, in one or two lines."""
    head = "refused" if route.kind is None else route.kind
    cls = route.cls or "no class: no engine choices table yet, #587"
    if route.evidence:
        cls += f", {route.evidence}"
    out = f"{head} [{cls}]: {route.reason}"
    for s in route.shims:
        out += f"\n          shim: {s}"
    for w in route.warnings:
        out += f"\n          note: {w}"
    if not route.deterministic:
        out += "\n          note: the result is not determined up to row order (D10)"
    return out


def print_profiles(reports: dict[str, Any], engines: Iterable[str] = PROFILE_ENGINES) -> None:
    from sverify import routes

    print("\n== profiles (sv.verify(semantics=...); routes.choose to each engine)")
    for sem, rep in reports.items():
        if isinstance(rep, str):
            print(f"  {sem:10} not checked: {rep[:200]}")
            continue
        verdict = "verified" if rep.proved else "NOT verified"
        print(
            f"  {sem:10} {verdict}; observation {rep.observation}; "
            f"{'deterministic' if rep.deterministic else 'not determined up to row order'}"
        )
        skip = False
        for ln in str(rep).splitlines():
            # The output's bounds are long and say nothing about engines.
            if ln.startswith("known about the output"):
                skip = True
                continue
            if skip and ln.startswith(" "):
                continue
            skip = False
            if not ln.startswith("semantics:"):
                print(f"      {ln}")
        if rep.depends is not None:
            print(
                "      depends on: "
                + (
                    ", ".join(where(d.get("group"), d["option"]) for d in rep.depends)
                    or "no option"
                )
            )
        for eng in engines:
            try:
                r = routes.choose(rep, eng)
            except Exception as err:  # noqa: BLE001
                print(f"      -> {eng:8} {type(err).__name__}: {err}")
                continue
            print(f"      -> {eng:8} {route_line(r)}")
    print("  Report.run(con, engine, route='auto') takes that route and checks the")
    print("  preconditions on the data first (by default once #606 lands, #604).")


def where(group: str | None, option: str) -> str:
    return f"{group or '*'}.{option}"


# ------------------------------------------------------------------ facts


def prose(v: Any) -> str:
    """A fact's prose field (a string or a list of them), lower case."""
    return " ".join(v if isinstance(v, list) else [v or ""]).lower()


def evidence_of(fact: dict) -> str:
    if fact.get("evidence"):
        return fact["evidence"]
    levels = [METHOD_EVIDENCE.get(p.get("method", ""), "docs") for p in fact.get("provenance", [])]
    return max(levels, key=EVIDENCE.index) if levels else "docs"


@functools.cache
def all_facts() -> list[dict]:
    out = []
    for f in sorted(ROOT.glob("characterization/*/facts/*.json")):
        d = json.loads(f.read_text())
        d["_path"] = str(f.relative_to(ROOT))
        out.append(d)
    return out


def matching_facts(
    opts: list[tuple[str | None, str]], fns: set[str], groups: set[str], words: set[str]
) -> list[tuple[int, dict]]:
    """Facts that settle one of the options (by `rows` where a fact has them,
    else by `options`), or name one of the functions in `constructs`."""
    names = {o for _, o in opts}
    pairs = set(opts)
    out = []
    for d in all_facts():
        if d.get("superseded_by"):
            continue
        score = 0
        if d.get("rows"):
            for r in d["rows"]:
                g, o = r.get("group"), r.get("option")
                if (g, o) in pairs or (g in (None, "-") and (None, o) in pairs):
                    score += 3
                elif o in names and g in groups:
                    score += 2
        elif names & set(d.get("options", [])):
            score += 2
        cons = {c.lower() for c in d.get("constructs", [])}
        score += 2 * len(cons & fns)
        text = prose(d.get("title")) + " " + prose(d.get("description"))
        score += sum(w in text for w in words)
        if score >= 2:
            out.append((score, d))
    return sorted(out, key=lambda s: (s[1]["engine"], -s[0], -EVIDENCE.index(evidence_of(s[1]))))


def ledger_entries(fact_ids: set[str], fns: set[str], words: set[str]) -> list[dict]:
    out = []
    for f in sorted(ROOT.glob("upstream/bugs/*.json")):
        d = json.loads(f.read_text())
        text = " ".join(str(d.get(k, "")) for k in ("summary", "repro", "handling")).lower()
        hit = set(d.get("facts", [])) & fact_ids
        hit |= {n for n in fns if len(n) > 3 and re.search(rf"\b{re.escape(n)}\b", text)}
        hit |= {w for w in words if w in text}
        if hit:
            d["_why"] = ", ".join(sorted(hit))
            out.append(d)
    return out


# ------------------------------------------------------------------- main


def calls(path: Path, fn: str) -> list[dict]:
    """The constant arguments of every call `fn(...)` in a module."""
    out = []
    for node in ast.walk(ast.parse(path.read_text())):
        if isinstance(node, ast.Call) and getattr(node.func, "id", None) == fn:
            entry: dict = {
                "args": [a.value if isinstance(a, ast.Constant) else None for a in node.args]
            }
            for k in node.keywords:
                if isinstance(k.value, ast.Constant):
                    entry[k.arg] = k.value.value
            if entry["args"] and isinstance(entry["args"][0], str):
                out.append(entry)
    return out


def doc_chunks(path: Path) -> list[str]:
    """A module docstring's paragraphs and bullets."""
    doc = ast.get_docstring(ast.parse(path.read_text())) or ""
    chunks: list[str] = []
    for para in re.split(r"\n\s*\n", doc):
        parts = re.split(r"\n(?=[*-] )", para)
        chunks += [" ".join(p.split()) for p in parts if p.strip()]
    return chunks


def print_static(sql: str, fns: set[str], opts: list, words: set[str], prose: bool) -> None:
    nodes = constructs(sql)
    groups = groups_of(fns)
    all_groups = {g for gs in groups.values() for g in gs}

    print("\n== options the query meets (Lean's functions table; docs/core-semantics.md)")
    for f in sorted(fns):
        print(
            f"  {f}: groups "
            + (", ".join(sorted(groups.get(f, []))) or "none (not in Functions.lean)")
        )
    print("  " + (", ".join(where(g, o) for g, o in opts) or "none"))

    opt_json = table("--options") or {}
    choices = opt_json.get("choices") or {}
    print("\n== choices per profile (substrait-check --options)")
    for prof in ["reference", *PROFILE_ENGINES, "substrait"]:
        rows = choices.get(prof)
        if rows is None:
            pending = {"duckdb": "#587", "polars": "#587", "substrait": "#600"}.get(prof, "")
            print(f"  {prof}: no table in this checker yet {f'({pending})' if pending else ''}")
            continue
        by = {(r.get("group"), r["option"]): r for r in rows}
        print(f"  {prof}:")
        for g, o in opts:
            r = by.get((g, o))
            via = ""
            if r is None and (r := by.get((None, o))) is not None and g is not None:
                via = " (the row for every group)"
            if r is None:
                continue
            c = r["choice"]
            allowed = "any" if c.get("kind") == "any" else "/".join(c.get("behaviours") or [])
            extra = []
            if c.get("kind") == "asked":
                extra.append(f"default {'/'.join(c.get('default') or [])}")
            for k in ("class", "q", "shim", "rerun"):
                if r.get(k) not in (None, "", {}):
                    extra.append(f"{k} {json.dumps(r[k]) if isinstance(r[k], dict) else r[k]}")
            if r.get("facts"):
                extra.append(f"facts {', '.join(r['facts'])}")
            print(f"    {where(g, o):26} {allowed:24} {'; '.join(extra)}{via}")

    print("\n== facts (characterization/<engine>/facts; evidence docs < source <")
    print("   engine_test < probe < fuzz < proof)")
    hits = matching_facts(opts, {f.lower() for f in fns}, all_groups, words)
    shown: dict[str, int] = {}
    for _, d in hits:
        n = shown.get(d["engine"], 0)
        shown[d["engine"]] = n + 1
        if n >= 12:
            continue
        outside = "" if d["engine"] in PROFILE_ENGINES else " (outside the profiles)"
        print(
            f"  {d['id']:30} {d['engine_version']:10} {evidence_of(d):11} {d['status']:10} "
            f"{d.get('verdict') or d.get('title', '')}{outside}"[:200]
        )
    for eng, n in shown.items():
        if n > 12:
            print(f"  … {n - 12} more for {eng}")
    if not hits:
        print(
            "  none: the checklist may miss this (python -m sverify_dev.facts --coverage <engine>)"
        )

    print("\n== upstream ledger (upstream/bugs; ST-* with kind spec-gap)")
    ids = {d["id"] for _, d in hits}
    for d in ledger_entries(ids, {f.lower() for f in fns}, words):
        kind = d.get("kind", "bug")
        print(
            f"  {d['id']:6} {kind:9} {d['project']:10} {d['status']:10} "
            f"{' '.join(d.get('summary', '').split())[:120]}  [{d['_why']}]"
        )

    parse = ROOT / "SubstraitLean/Parse.lean"
    print("\n== SubstraitLean/Parse.lean (how the Substrait function is read)")
    for f in sorted(fns):
        lines = grep(parse, rf'"{f}"', 3)
        print(
            f"  {f}: "
            + (
                "\n      ".join(lines)
                if lines
                else "no arm by name (read from the table, or refused)"
            )
        )

    if not prose:
        print("\n(--prose adds the catalogue, pitfalls, backend_semantics.py and the")
        print(" engine modules' docstrings)")
        return

    pit = tomllib.loads((ROOT / "catalogue/pitfalls.toml").read_text())
    tags = sorted({t for n in nodes for t in PITFALLS.get(n, [])} | set(special(sql)))
    print("\n== pitfalls (catalogue/pitfalls.toml; prose, older than the facts)")
    for t in tags:
        if p := pit.get(t):
            print(f"  [{t}] {' '.join(p['description'].split())[:300]}")

    feats = tomllib.loads((ROOT / "catalogue/features.toml").read_text())
    feat_table = {k: v for sec in feats.values() for k, v in sec.items()}
    wanted = sorted({f for n in nodes for f in FEATURES.get(n, [])})
    print("\n== features (catalogue/features.toml: in the Lean model?)")
    for f in wanted:
        v = feat_table.get(f, {})
        print(
            f"  {f:20} lean={v.get('lean', '?'):8} {v.get('note', v.get('description', ''))[:90]}"
        )

    print("\n== catalogue/backend_semantics.py (prose per engine; `picks` is the reference's)")
    mine = nodes - BORING
    entries = calls(ROOT / "catalogue/backend_semantics.py", "E")
    scored = []
    for x in entries:
        try:
            theirs = (
                constructs(x["args"][3]) - BORING if len(x["args"]) > 3 and x["args"][3] else set()
            )
        except Exception:  # noqa: BLE001
            theirs = set()
        if len(mine & theirs) >= 1:
            scored.append((len(mine & theirs), x))
    for _, x in sorted(scored, key=lambda s: -s[0])[:4]:
        a = x["args"]
        print(f"  {a[0]} {a[1]}: {a[3]}\n      picks: {x.get('picks', '')}")

    print("\n== engine modules' docstrings")
    keys = sorted({k for n in nodes for k in KEYWORDS.get(n, [])})
    py = ROOT / "python/src/sverify"
    for path in [
        py / "sql/duckdb.py",
        py / "polars_engine.py",
        py / "_polars_shims.py",
        py / "sql/core/_base.py",
    ]:
        if not path.exists():
            continue
        found = [c for c in doc_chunks(path) if any(k in c for k in keys)]
        if found:
            print(f"  {path.relative_to(ROOT)}:")
            for c in found[:4]:
                print(f"    - {c[:300]}{'…' if len(c) > 300 else ''}")

    status = json.loads((ROOT / "catalogue/status.json").read_text())
    print("\n== catalogue queries with these features (catalogue/status.json, a snapshot)")
    shown_q = 0
    for qfile in sorted((ROOT / "catalogue/queries").glob("*.toml")):
        for q in tomllib.loads(qfile.read_text()).get("query", []):
            overlap = set(q.get("features", [])) & set(wanted) - {"filter", "project"}
            if len(overlap) >= max(1, min(2, len(wanted) - 1)) and shown_q < 6:
                s = status.get(q["id"], {})
                eng = json.dumps(s.get("engines", s.get("detail", "")))[:90]
                print(f"  {q['id']:28} {s.get('checker', '?'):9} {eng}")
                shown_q += 1


def ibis_table() -> Any:
    import ibis

    return ibis.table(
        {
            "x": "int64",
            "y": "int64",
            "v": "float64",
            "s": "string",
            "ts": "timestamp",
            "d": "date",
            "b": "boolean",
        },
        name="t",
    )


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawTextHelpFormatter)
    ap.add_argument("--sql", help="the query, in DuckDB's SQL")
    ap.add_argument("--ibis", help="Ibis code over the table t (or the --table tables)")
    ap.add_argument(
        "--table",
        nargs=2,
        action="append",
        default=[],
        metavar=("NAME", "COL:TYPE,..."),
        help="a table's schema: verify the query under each profile",
    )
    ap.add_argument(
        "--requires",
        nargs=2,
        action="append",
        default=[],
        metavar=("TABLE", "EXPR"),
        help="a precondition: an Ibis expression over _, or sv.max_rows(n)",
    )
    ap.add_argument(
        "--ensures",
        action="append",
        default=[],
        metavar="EXPR",
        help="a postcondition, e.g. sv.equivalent(floats=sv.within(rel=1e-9))",
    )
    ap.add_argument("--word", action="append", default=[], help="extra search words")
    ap.add_argument("--prose", action="store_true", help="also the older prose sources")
    args = ap.parse_args()
    if not args.sql and not args.ibis:
        ap.error("give --sql or --ibis")
    words = {w.lower() for w in args.word}

    import ibis

    schemas = {n: ibis.schema(schema_of(c)) for n, c in args.table}
    sql = args.sql
    expr = None
    if args.ibis:
        import ibis.expr.operations as ops

        tabs = {n: ibis.table(s, name=n) for n, s in schemas.items()} or {"t": ibis_table()}
        expr = eval(args.ibis, {"ibis": ibis, "_": ibis._, **tabs, "t": next(iter(tabs.values()))})  # noqa: S307
        sql = sql or ibis.to_sql(expr, dialect="duckdb")
        print("Ibis's DuckDB SQL:", " ".join(sql.split())[:300])
        producer = sorted((ROOT / "python/src/sverify/ibis_substrait").glob("*.py"))
        boring = {
            "Field",
            "Literal",
            "Project",
            "UnboundTable",
            "DatabaseTable",
            "SortKey",
            "Alias",
        }
        print("\n== python/src/sverify/ibis_substrait (the vendored Ibis producer)")
        for op in sorted({type(n).__name__ for n in expr.op().find(ops.Node)} - boring):
            lines = [ln for f in producer for ln in grep(f, rf"ops\.{op}\b", 2)][:2]
            print(
                f"  {op}: " + ("\n      ".join(lines) if lines else "no translation (Unsupported)")
            )

    nodes = constructs(sql)
    fns = {f for n in nodes for f in SUBSTRAIT.get(n, [])}
    print("constructs:", ", ".join(sorted(nodes - BORING)))

    plan_opts: list[tuple[str | None, str]] = []
    if schemas or expr is not None:
        req, ens = conditions(args.requires, args.ensures)
        reports = verify_profiles(expr if expr is not None else sql, schemas or None, req, ens)
        print_profiles(reports)
        from sverify import _plan_read, routes

        for rep in reports.values():
            if not isinstance(rep, str) and rep.plan:
                plan = json.loads(rep.plan)
                fns = {_plan_read.base_name(n) for n in _plan_read.function_names(plan).values()}
                deps = rep.depends if rep.depends is not None else routes.plan_options(plan)
                plan_opts = [(d.get("group"), d["option"]) for d in deps]
                break
    opts = (
        list(dict.fromkeys(plan_opts + options_for((), nodes)))
        if plan_opts
        else options_for(fns, nodes)
    )
    print_static(sql, fns, opts, words, args.prose)
    return 0


if __name__ == "__main__":
    sys.exit(main())
