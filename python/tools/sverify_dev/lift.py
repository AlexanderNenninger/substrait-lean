"""Oracles A and C for the SQLGlot lift (`sverify.sql_lift`, #239), and its
score on the benchmark queries of the catalogue (#229).

Maintainer tooling (`sverify_dev`): not in the wheel, and not part of sverify's
API.

* **Oracle A** (the lift): DuckDB runs the original SQL, and `Rel.eval`
  (`substrait-check`) evaluates the lifted plan with the tables inlined. No
  lowering is involved, so a difference points at the profile, SQLGlot's
  reading, or the Lean model.
* **Oracle C** (the round trip): the lifted plan, written back by Lean
  (`--write`) and printed as DuckDB SQL by `sverify.sql.duckdb`, runs on
  DuckDB, and gives what DuckDB gives on the original SQL.

`check` runs both on one query. `python -m sverify_dev.lift` scores the
benchmark suites (TPC-H, TPC-DS, SSB, ClickBench, JOB, H2O): each query's Ibis
expression is compiled to DuckDB SQL by Ibis (`ibis.to_sql`), the catalogue's
SQL taken as it is, and run on its synthetic data. The sqllogictest replay
scores the lift with `python -m sverify_dev.slt --frontend lift`.
"""

from __future__ import annotations

import argparse
import json
import subprocess
from collections import Counter
from collections.abc import Mapping, Sequence
from dataclasses import dataclass

import duckdb
import ibis
import pyarrow as pa
import sqlglot as sg

from sverify_dev import slt

#: The suites of #229's benchmark queries.
BENCHMARKS = ("tpch", "tpcds", "ssb", "clickbench", "job", "h2o")

#: The stages of `check`, in order; a query reaches `"agree"` past all.
STAGES = ("duckdb", "lift", "checker", "oracle A", "oracle C", "agree")


@dataclass
class Check:
    """How far a query got: the stage it stopped at (`STAGES`), and why."""

    stage: str
    detail: str = ""

    @property
    def ok(self) -> bool:
        return self.stage == "agree"


def duckdb_result(query: str, tables: Mapping[str, pa.Table]) -> pa.Table:
    """DuckDB running `query` over `tables`."""
    con = duckdb.connect()
    for name, t in tables.items():
        con.register(name, t)
    return con.sql(query).to_arrow_table()


def _ordered(query: str) -> bool:
    tree = sg.parse_one(query, read="duckdb")
    return isinstance(tree, sg.exp.Select) and tree.args.get("order") is not None


def _same(a: pa.Table, b: pa.Table, ordered: bool, fmt: slt.Formatter) -> bool:
    x, y = fmt.rows(a), fmt.rows(b)
    # Ties under ORDER BY may come in either order.
    return slt._same_bag(x, y, ordered) or (ordered and slt._same_bag(x, y, False))


def check(query: str, tables: Mapping[str, pa.Table], semantics: str = "duckdb") -> Check:
    """Oracles A and C on `query` over `tables` (Arrow tables by name)."""
    from sverify import duckdb_engine
    from sverify.engine import run_checker, written_plan
    from sverify.sql_lift import lift
    from sverify.testing import lean_values

    try:
        expected = duckdb_result(query, tables)
    except duckdb.Error as e:
        return Check("duckdb", str(e).splitlines()[0])
    schemas = {n: ibis.Schema.from_pyarrow(t.schema) for n, t in tables.items()}
    try:
        lifted = lift(query, schemas, semantics)
    except Exception as e:  # noqa: BLE001 - a refusal, or a bug: recorded
        kind = "" if type(e).__name__ == "Unsupported" else f"{type(e).__name__}: "
        return Check("lift", kind + str(e).splitlines()[0])
    plan = json.dumps(lifted.plan)
    code, out, err = run_checker((), plan)
    if code != 0:
        return Check("checker", ((err or out).strip().splitlines() or ["?"])[-1])
    fmt = slt.Formatter()
    ordered = _ordered(query)
    schema = lifted.schema.to_pyarrow()

    rows = {n: [tuple(r.values()) for r in t.to_pylist()] for n, t in tables.items()}
    try:
        inlined = slt._typed_inline(json.loads(plan), rows, None)
        lean = slt._as_table(lean_values(json.dumps(inlined)), schema)
    except subprocess.CalledProcessError as e:
        return Check("oracle A", f"Lean: {((e.stderr or '') + (e.output or '')).strip()[-200:]}")
    if not _same(expected, lean, ordered, fmt):
        return Check("oracle A", f"DuckDB {fmt.rows(expected)[:3]} vs Lean {fmt.rows(lean)[:3]}")

    try:
        got = duckdb_engine.run(written_plan(plan), tables)
    except Exception as e:  # noqa: BLE001 - the renderer or DuckDB refusing
        return Check("oracle C", f"{type(e).__name__}: {str(e).splitlines()[0][:200]}")
    if not _same(expected, got, ordered, fmt):
        return Check("oracle C", f"DuckDB {fmt.rows(expected)[:3]} vs plan {fmt.rows(got)[:3]}")
    return Check("agree")


def benchmark_sql(q: object, schemas: dict) -> str:
    """A catalogue query as DuckDB SQL: its SQL, or Ibis's DuckDB SQL for its
    expression."""
    from sverify_dev import catalogue

    built = catalogue.build(q, schemas, "native")  # pyrefly: ignore
    return built if isinstance(built, str) else ibis.to_sql(built, dialect="duckdb")


def score(suites: Sequence[str] = BENCHMARKS) -> dict[str, Check]:
    """`check` on each query of `suites`, over the catalogue's synthetic data."""
    from sverify_dev import catalogue

    schemas = catalogue.load_schemas()
    out: dict[str, Check] = {}
    for q in catalogue.load_queries():
        if q.suite not in suites:
            continue
        if q.not_expressible is not None:
            out[q.id] = Check("duckdb", "not expressible in the catalogue")
            continue
        try:
            sql = benchmark_sql(q, schemas)
        except Exception as e:  # noqa: BLE001 - Ibis cannot compile it
            out[q.id] = Check("duckdb", f"Ibis: {str(e).splitlines()[0]}")
            continue
        data = catalogue.synthetic(schemas, q.dataset, "native")
        out[q.id] = check(sql, data)
    return out


def main(argv: Sequence[str] | None = None) -> None:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("suites", nargs="*", default=list(BENCHMARKS))
    parser.add_argument("-v", "--verbose", action="store_true", help="each query's result")
    args = parser.parse_args(argv)
    results = score(args.suites)
    if args.verbose:
        for qid, c in results.items():
            print(f"{qid}: {c.stage}{': ' + c.detail if c.detail else ''}")
    stops = Counter(c.stage for c in results.values())
    print(f"{stops['agree']} of {len(results)} benchmark queries agree (oracles A and C)")
    for stage in STAGES[:-1]:
        if stops[stage]:
            print(f"  stopped at {stage}: {stops[stage]}")


if __name__ == "__main__":
    main()
