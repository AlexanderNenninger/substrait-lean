"""How large the SQL sverify writes is, against the plan it was given (#821).

Maintainer tooling (`sverify_dev`): not in the wheel.

For every verified coverage case (`sverify_dev.coverage_cases`) and every
catalogue query, this writes Lean's written plan as the SQL of each dialect
(DuckDB, Snowflake and Spark; Polars runs the plan as expressions) and
measures it:

* `chars`: the SQL's length;
* `nodes`: SQLGlot's expression nodes in it;
* `depth`: how deeply its `CASE`s nest;

and the input:

* `in_nodes`: the nodes of the Substrait plan sverify was given: its
  expressions (field references, literals, calls, casts, `IF`s), its
  relations, and the columns its tables have (the SQL names each);

with their ratio, `ratio = nodes / in_nodes`. A shim that copies its argument
makes the ratio grow with the depth of nested calls (#821: three copies,
three levels deep, is 27). `tests/test_plan_size.py` bounds the ratio and the
depth (`BOUND`), so a new shim cannot blow up the SQL unnoticed.

    uv run python -m sverify_dev.plan_size              # the worst 25 per dialect
    uv run python -m sverify_dev.plan_size --all --json # every measurement
"""

from __future__ import annotations

import argparse
import json
import sys
from collections.abc import Iterator
from dataclasses import asdict, dataclass
from typing import Any

#: The bounds `tests/test_plan_size.py` checks: today's worst cases pass them.
#: Tighten them when a change makes the SQL smaller.
BOUND = {"ratio": 1000.0, "depth": 10, "chars": 560_000}

#: The keys of a Substrait expression node.
_EXPR_KEYS = frozenset(
    {"selection", "literal", "scalarFunction", "cast", "ifThen", "singularOrList",
     "windowFunction", "switchExpression", "nested", "subquery"}
)  # fmt: skip

#: The keys of a Substrait relation node.
_REL_KEYS = frozenset(
    {"read", "filter", "project", "aggregate", "join", "cross", "fetch", "sort", "set",
     "window", "extensionSingle", "extensionMulti", "extensionLeaf", "reference"}
)  # fmt: skip

#: The dialects of the SQL engines, with SQLGlot's name for each.
DIALECTS = {"duckdb": "duckdb", "snowflake": "snowflake", "spark": "spark"}


@dataclass(frozen=True)
class Size:
    source: str
    """`coverage` or `catalogue`."""
    label: str
    dialect: str
    in_nodes: int
    chars: int
    nodes: int
    depth: int

    @property
    def ratio(self) -> float:
        return self.nodes / max(self.in_nodes, 1)

    def row(self) -> dict[str, Any]:
        return {**asdict(self), "ratio": round(self.ratio, 1)}


def plan_nodes(plan: Any) -> int:
    """The nodes of a Substrait plan (protobuf JSON, parsed): expressions,
    relations and the columns of the tables it reads."""
    if isinstance(plan, dict):
        here = 1 if (_EXPR_KEYS | _REL_KEYS) & plan.keys() else 0
        if isinstance(schema := plan.get("baseSchema"), dict):
            here += len(schema.get("names", []))
        return here + sum(plan_nodes(v) for v in plan.values())
    if isinstance(plan, list):
        return sum(plan_nodes(v) for v in plan)
    return 0


def sql_size(sql: str, read: str) -> tuple[int, int]:
    """SQLGlot's expression nodes of `sql` and how deeply its `CASE`s nest."""
    import sqlglot
    from sqlglot import exp

    tree = sqlglot.parse_one(sql, read=read)
    nodes = 0
    depth = 0
    stack: list[tuple[Any, int]] = [(tree, 0)]
    while stack:
        node, d = stack.pop()
        nodes += 1
        if isinstance(node, exp.Case):
            d += 1
            depth = max(depth, d)
        stack.extend((c, d) for c in node.iter_expressions())
    return nodes, depth


def measure(source: str, label: str, plan_json: str) -> Iterator[Size]:
    """The written SQL's size in each dialect that writes the plan."""
    from sverify.engine import written_plan
    from sverify.sql import Unsupported
    from sverify.sql import to_sql as plan_sql
    from sverify.sql.duckdb import DUCKDB
    from sverify.sql.snowflake import SNOWFLAKE
    from sverify.sql.spark import SPARK

    in_nodes = plan_nodes(json.loads(plan_json))
    try:
        plan = json.loads(written_plan(plan_json))
    except ValueError:
        return  # `--write` refuses it (decimals, #27)
    for name, dialect in (("duckdb", DUCKDB), ("snowflake", SNOWFLAKE), ("spark", SPARK)):
        try:
            sql = plan_sql(plan, dialect)
        except Unsupported:
            try:
                sql = plan_sql(plan, dialect, deterministic=True)
            except Unsupported:
                continue
        nodes, depth = sql_size(sql, DIALECTS[name])
        yield Size(source, label, name, in_nodes, len(sql), nodes, depth)


def coverage_sizes() -> Iterator[Size]:
    from sverify.engine import run_checker
    from sverify.ibis_substrait import Unsupported, to_substrait_json
    from sverify_dev.coverage_cases import CASES

    for case in CASES:
        if case.expected != "verified":
            continue
        try:
            plan = to_substrait_json(case.build())
        except Unsupported:
            continue
        if run_checker((), plan)[0] != 0:
            continue
        yield from measure("coverage", case.label, plan)


def catalogue_sizes() -> Iterator[Size]:
    from sverify.engine import connect, plan_json, put_table, run_checker
    from sverify_dev import catalogue as cat

    schemas = cat.load_schemas()
    status = json.loads((cat.ROOT / "status.json").read_text())
    con = connect()
    loaded: set[str] = set()
    for q in cat.load_queries():
        if status.get(q.id, {}).get("checker") != "verified":
            continue
        if q.dataset not in loaded:
            for name, table in cat.synthetic(schemas, q.dataset, "native").items():
                put_table(con, name, table)
            loaded.add(q.dataset)
        try:
            plan = plan_json(con, cat.build(q, schemas, "native"))
        except Exception:  # noqa: BLE001 - the catalogue's own probe records these
            continue
        if run_checker((), plan)[0] != 0:
            continue
        yield from measure("catalogue", q.id, plan)


def sizes() -> list[Size]:
    return [*coverage_sizes(), *catalogue_sizes()]


def over(s: Size, bound: dict[str, float] = BOUND) -> list[str]:
    """What of `bound` a measurement exceeds."""
    out = []
    if s.ratio > bound["ratio"]:
        out.append(
            f"{s.nodes} nodes from {s.in_nodes} (ratio {s.ratio:.0f} > {bound['ratio']:.0f})"
        )
    if s.depth > bound["depth"]:
        out.append(f"CASE depth {s.depth} > {bound['depth']}")
    if s.chars > bound["chars"]:
        out.append(f"{s.chars} chars > {bound['chars']}")
    return out


def report(ss: list[Size], n: int | None) -> str:
    lines = []
    for dialect in DIALECTS:
        rows = sorted((s for s in ss if s.dialect == dialect), key=lambda s: -s.ratio)
        lines += [
            f"## {dialect}: {len(rows)} plans",
            "",
            "| source | query | in nodes | chars | nodes | ratio | CASE depth |",
            "|---|---|---:|---:|---:|---:|---:|",
        ]
        lines += [
            f"| {s.source} | {s.label} | {s.in_nodes} | {s.chars:,} | {s.nodes:,} "
            f"| {s.ratio:.1f} | {s.depth} |"
            for s in rows[:n]
        ]
        lines.append("")
    return "\n".join(lines)


def main(argv: list[str] | None = None) -> None:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--all", action="store_true", help="every measurement, not the worst 25")
    ap.add_argument("--json", action="store_true", help="JSON lines instead of tables")
    args = ap.parse_args(argv)
    ss = sizes()
    if args.json:
        rows = sorted(ss, key=lambda s: -s.ratio)
        for s in rows if args.all else rows[:25]:
            print(json.dumps(s.row()))
    else:
        print(report(ss, None if args.all else 25))
    bad = [(s, why) for s in ss if (why := over(s))]
    for s, why in bad:
        print(
            f"over the bound: {s.source} {s.label} ({s.dialect}): {'; '.join(why)}", file=sys.stderr
        )
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()
