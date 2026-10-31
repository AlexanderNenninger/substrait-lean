"""Collect what this repository already says about how a query's constructs
behave on sverify's frontends and backends, against the Lean model. The
static first step of the `query-semantics` skill; `probe.py` is the fallback.

It parses the SQL with sqlglot (Ibis code: give Ibis's SQL for it, or `--ibis`
to have it compiled), names the constructs, and prints, for each source:

  features   catalogue/features.toml: is the construct in the Lean model?
  pitfalls   catalogue/pitfalls.toml: what each engine does, with quirk ids
  nb15       notebooks/15_backend_semantics.py: the question per engine, Ibis
             backend, standard SQL and Snowflake, and the Lean model's pick
  nb14       notebooks/14_datafusion_semantics.py: DataFusion's quirks
  parser     SubstraitLean/Parse.lean: how the Substrait function is read
             (or refused), and the Lean operator it becomes
  backends   the docstrings of sverify/sql/{duckdb,snowflake,spark,core}.py and
             polars_engine.py: how each backend is made to give Lean's value
  catalogue  catalogue queries that use the same features, with status
  producer   with --ibis: where the vendored Ibis producer translates each
             Ibis operation (sverify/ibis_substrait), or that it doesn't

Run from the repository root or python/:
  uv run --project python python .claude/skills/query-semantics/lookup.py \\
      --sql 'SELECT x, x NOT IN (2, NULL) FROM n ORDER BY x DESC LIMIT 2'
"""

from __future__ import annotations

import argparse
import ast
import json
import re
import sys
import tomllib
from pathlib import Path

import sqlglot
import sqlglot.expressions as e

ROOT = Path(__file__).resolve().parents[3]

# sqlglot node class -> Substrait function names (as Parse.lean dispatches on them).
SUBSTRAIT = {
    "Div": ["divide"], "IntDiv": ["divide"], "Mod": ["modulus"], "Add": ["add"],
    "Sub": ["subtract"], "Mul": ["multiply"], "Neg": ["negate"], "EQ": ["equal"],
    "NEQ": ["not_equal"], "LT": ["lt"], "GT": ["gt"], "LTE": ["lte"], "GTE": ["gte"],
    "And": ["and"], "Or": ["or"], "Not": ["not"], "Is": ["is_null", "is_not_null"],
    "Coalesce": ["coalesce"], "Nullif": ["nullif"], "Greatest": ["greatest"],
    "Least": ["least"], "Abs": ["abs"], "Pow": ["power"], "Round": ["round"],
    "Floor": ["floor"], "Ceil": ["ceil"], "Upper": ["upper"], "Lower": ["lower"],
    "Length": ["character_length"], "DPipe": ["str_concat", "concat"],
    "Concat": ["str_concat", "concat"], "StrPosition": ["strpos"],
    "Substring": ["substring"], "Like": ["like"], "ILike": ["ilike"], "Trim": ["btrim"],
    "TimestampTrunc": ["date_trunc"], "DateTrunc": ["date_trunc"], "Extract": ["date_part"],
    "RowNumber": ["row_number"], "Lag": ["lag"], "Lead": ["lead"], "Sum": ["sum"],
    "Avg": ["avg"], "Min": ["min"], "Max": ["max"], "Count": ["count"],
    "RegexpLike": ["regexp_match"], "IsNan": ["is_nan", "isnan"],
    "Between": ["gte", "lte"], "Rank": ["rank"], "DenseRank": ["dense_rank"],
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

# sqlglot node class -> words the backend modules' docstrings use for it.
KEYWORDS = {
    "Div": ["division", "divide", " / "], "IntDiv": ["division"], "Mod": ["%", "MOD", "remainder"],
    "Add": ["overflow"], "Mul": ["overflow"], "Sub": ["overflow"], "Order": ["NULL order", "sort"],
    "Ordered": ["NULLS"], "Limit": ["FETCH", "row order"], "Window": ["window", "row order"],
    "RowNumber": ["ROW_NUMBER", "row number"], "Lag": ["LAG"], "Lead": ["LEAD"],
    "Not": ["three-valued", "Kleene"], "And": ["Kleene"], "Or": ["Kleene"], "Is": ["IS TRUE"],
    "In": ["three-valued"], "Null": ["NULL"], "Cast": ["cast", "CAST"],
    "Like": ["LIKE"], "ILike": ["LIKE"], "Substring": ["substring", "SUBSTR"],
    "Length": ["length", "code point"], "StrPosition": ["strpos"], "Trim": ["trim"],
    "Upper": ["upper", "case"], "Lower": ["lower", "case"],
    "RegexpLike": ["regular expression", "regex"],
    "DPipe": ["concat"], "Concat": ["concat"], "Round": ["round"], "Pow": ["POWER", "pow"],
    "Sum": ["sum", "SUM"], "Avg": ["AVG", "average"], "Min": ["MIN"], "Max": ["MAX"],
    "Count": ["COUNT"], "Join": ["join"], "Greatest": ["GREATEST"], "Least": ["LEAST"],
    "Interval": ["interval"], "Extract": ["date part", "date_part", "EXTRACT"],
    "TimestampTrunc": ["date_trunc", "trunc"], "DateTrunc": ["date_trunc", "trunc"],
    "Timestamp": ["timestamp"], "Union": ["union"], "IsNan": ["NaN"],
}  # fmt: skip

#: Node types that say nothing about semantics.
BORING = {
    "Select", "From", "Table", "Column", "Identifier", "Literal", "Alias", "TableAlias",
    "Star", "Paren", "Tuple", "DataType", "Var", "Boolean", "Subquery",
}  # fmt: skip


def constructs(sql: str) -> set[str]:
    """The sqlglot node classes in the query, by name."""
    tree = sqlglot.parse_one(sql, read="postgres")
    return {type(n).__name__ for n in tree.walk()}


def names(nodes: set[str]) -> set[str]:
    return nodes - BORING


def special(sql: str) -> list[str]:
    """Patterns the node types don't show."""
    tree = sqlglot.parse_one(sql, read="postgres")
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


# ------------------------------------------------------------------ sources


def calls(path: Path, fn: str) -> list[dict]:
    """The constant arguments of every call `fn(...)` in a notebook."""
    tree = ast.parse(path.read_text())
    out = []
    for node in ast.walk(tree):
        if isinstance(node, ast.Call) and getattr(node.func, "id", None) == fn:
            entry: dict = {"args": []}
            for a in node.args:
                entry["args"].append(a.value if isinstance(a, ast.Constant) else None)
            for k in node.keywords:
                if isinstance(k.value, ast.Constant):
                    entry[k.arg] = k.value.value
            if entry["args"] and isinstance(entry["args"][0], str):
                out.append(entry)
    return out


def sql_names(sql: str | None) -> set[str]:
    try:
        return names(constructs(sql)) if sql else set()
    except Exception:  # noqa: BLE001 - notebook SQL in other dialects
        return set()


def ranked(entries: list[dict], sql_of, mine: set[str], words: set[str]) -> list[tuple[int, dict]]:
    scored = []
    for x in entries:
        theirs = sql_names(sql_of(x))
        text = " ".join(str(v) for v in [*x["args"], *x.values()] if isinstance(v, str)).lower()
        score = 2 * len(mine & theirs) + sum(w in text for w in words)
        if score >= 2:
            scored.append((score, x))
    return sorted(scored, key=lambda s: -s[0])


def doc_chunks(path: Path) -> list[str]:
    """A module docstring's paragraphs and bullets."""
    doc = ast.get_docstring(ast.parse(path.read_text())) or ""
    chunks: list[str] = []
    for para in re.split(r"\n\s*\n", doc):
        parts = re.split(r"\n(?=\* )", para)
        chunks += [" ".join(p.split()) for p in parts if p.strip()]
    return chunks


def grep(path: Path, pattern: str, limit: int = 4) -> list[str]:
    rx = re.compile(pattern)
    lines = path.read_text().splitlines()
    return [f"{path.relative_to(ROOT)}:{i}: {ln.strip()[:110]}"
            for i, ln in enumerate(lines, 1) if rx.search(ln)][:limit]  # fmt: skip


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawTextHelpFormatter)
    ap.add_argument("--sql", help="the query (any common dialect; read as Postgres)")
    ap.add_argument(
        "--ibis", help="Ibis code over tables t (int64 x, string s, …): compiled to SQL"
    )
    ap.add_argument("--word", action="append", default=[], help="extra search words")
    args = ap.parse_args()
    sql = args.sql
    if args.ibis:
        import ibis

        t = ibis.table({"x": "int64", "y": "int64", "v": "float64", "s": "string",
                        "ts": "timestamp", "d": "date", "b": "boolean"}, name="t")  # fmt: skip
        import ibis.expr.operations as ops

        expr = eval(args.ibis, {"ibis": ibis, "t": t, "_": ibis._})  # noqa: S307
        sql = ibis.to_sql(expr, dialect="postgres")
        print("Ibis's Postgres SQL:", " ".join(sql.split()))
        boring = {"Field", "Literal", "Project", "UnboundTable", "SortKey", "Alias"}
        producer = ROOT / "python/src/sverify/ibis_substrait/__init__.py"
        print("\n== python/src/sverify/ibis_substrait (the vendored Ibis producer)")
        for op in sorted({type(n).__name__ for n in expr.op().find(ops.Node)} - boring):
            lines = grep(producer, rf"ops\.{op}\b", 3)
            print(
                f"  {op}: " + ("\n      ".join(lines) if lines else "no translation (Unsupported)")
            )
    if not sql:
        ap.error("give --sql or --ibis")

    nodes = constructs(sql)
    mine = names(nodes)
    words = {w.lower() for w in args.word}
    print("constructs:", ", ".join(sorted(mine)))

    feats = json.dumps(tomllib.loads((ROOT / "catalogue/features.toml").read_text()))
    feat_table = {k: v for sec in json.loads(feats).values() for k, v in sec.items()}
    wanted = sorted({f for n in nodes for f in FEATURES.get(n, [])})
    print("\n== features (catalogue/features.toml: in the Lean model?)")
    for f in wanted:
        v = feat_table.get(f, {})
        print(
            f"  {f:20} lean={v.get('lean', '?'):8} {v.get('note', v.get('description', ''))[:90]}"
        )

    pit = tomllib.loads((ROOT / "catalogue/pitfalls.toml").read_text())
    tags = sorted({t for n in nodes for t in PITFALLS.get(n, [])} | set(special(sql)))
    quirks: set[str] = set()
    print("\n== pitfalls (catalogue/pitfalls.toml)")
    for t in tags:
        p = pit.get(t)
        if p:
            quirks |= set(p.get("quirks", []))
            print(f"  [{t}] {p['description']}\n      engines: {p['engines']}")
            if p.get("quirks"):
                print(f"      DataFusion quirks: {', '.join(p['quirks'])}")

    nb15 = ROOT / "notebooks/15_backend_semantics.py"
    print("\n== notebooks/15_backend_semantics.py (per engine; the Lean model's pick)")
    for _, x in ranked(calls(nb15, "E"), lambda x: x["args"][3] if len(x["args"]) > 3 else None,
                       mine, words)[:6]:  # fmt: skip
        a = x["args"]
        print(f"  {a[0]} {a[1]}: {a[3]}")
        for k in ("std", "snowflake", "polars", "ibis", "engines", "sverify"):
            if x.get(k):
                print(f"      {k}: {x[k]}")
        print(f"      why: {x.get('why', '')}")
        print(f"      Lean picks: {x.get('picks', '')}")

    nb14 = ROOT / "notebooks/14_datafusion_semantics.py"
    entries = calls(nb14, "Q")
    hits = ranked(entries, lambda x: x["args"][2] if len(x["args"]) > 2 else None, mine, words)
    chosen = [x for _, x in hits[:5]] + [x for x in entries if x["args"][0] in quirks]
    print("\n== notebooks/14_datafusion_semantics.py (DataFusion's quirks)")
    seen = set()
    for x in chosen:
        a = x["args"]
        if a[0] in seen:
            continue
        seen.add(a[0])
        print(f"  {a[0]} {a[1]} [{a[3] if len(a) > 3 else ''}]: {a[2]}")
        print(f"      {a[4] if len(a) > 4 else ''}")

    parse = ROOT / "SubstraitLean/Parse.lean"
    fns = sorted({f for n in nodes for f in SUBSTRAIT.get(n, [])})
    print("\n== SubstraitLean/Parse.lean (how the Substrait function is read)")
    for f in fns:
        lines = grep(parse, rf'"{f}"', 3)
        print(f"  {f}: " + ("\n      ".join(lines) if lines else "not in the parser (refused)"))

    print("\n== backends: what each translation module says (module docstrings)")
    keys = sorted({k for n in nodes for k in KEYWORDS.get(n, [])})
    py = ROOT / "python/src/sverify"
    for path in [py / "sql/duckdb.py", py / "polars_engine.py", py / "sql/snowflake.py",
                 py / "sql/spark.py", py / "sql/core.py"]:  # fmt: skip
        hits = [c for c in doc_chunks(path) if any(k in c for k in keys)]
        if hits:
            print(f"  {path.relative_to(ROOT)}:")
            for c in hits[:5]:
                print(f"    - {c[:400]}{'…' if len(c) > 400 else ''}")

    status = json.loads((ROOT / "catalogue/status.json").read_text())
    print("\n== catalogue queries using these features (catalogue/status.json)")
    shown = 0
    for qfile in sorted((ROOT / "catalogue/queries").glob("*.toml")):
        for q in tomllib.loads(qfile.read_text()).get("query", []):
            overlap = set(q.get("features", [])) & set(wanted) - {"filter", "project"}
            if len(overlap) >= max(1, min(2, len(wanted) - 1)) and shown < 8:
                s = status.get(q["id"], {})
                s = s.get("as_double", s) if s.get("checker") != "verified" else s
                eng = json.dumps(s.get("engines", s.get("detail", "")))[:90]
                print(f"  {q['id']:28} {s.get('checker', '?'):9} {eng}")
                shown += 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
