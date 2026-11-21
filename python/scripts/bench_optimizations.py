"""Benchmarks for the proved optimizations of `docs/optimizations.md`.

    uv run python scripts/bench_optimizations.py [rows]

* Guard elimination: a contract-verified transformation on Polars and on
  DuckDB, with the per-row checks and without them (`guards=False`, allowed
  because the contract report is `guard_free`).
* Sharded evaluation: a grouped aggregate on Polars over all the rows, and
  in two phases over 8 shards run in parallel threads.
* GROUP BY simplification (`Rel.fdAgg`): a TPC-H Q3-style join then group by
  `l_orderkey, o_date, o_prio`, as written and grouped by `l_orderkey` alone
  (the contract's key on `o_orderkey` determines the rest).
* Eager aggregation (`Rel.eagerAgg`): line items joined with orders on the
  order key and grouped by it, as written and aggregated before the join.
* Each other rule of `Rel.rule` (#1787, item 2's gate): one query it fires on,
  as written and rewritten, on Polars and DuckDB, with the written SQL's size.

`rules` alone runs the per-rule cases: `bench_optimizations.py [rows] rules`.

Prints the median of 5 runs of each.
"""

import json
import statistics
import sys
import time
from collections.abc import Callable

import ibis
import numpy as np
import pyarrow as pa
from ibis import _

import sverify as sv
from sverify.engine import connect, plan_json, substrait_json, written_plan
from sverify.partition import run_sharded
from sverify.sql import to_sql
from sverify_duckdb import engine as duckdb_engine
from sverify_duckdb.dialect import DUCKDB
from sverify_polars import engine as polars_engine


def median_ms(f: Callable[[], object], runs: int = 5) -> float:
    f()  # warm up
    times = []
    for _run in range(runs):
        t = time.perf_counter()
        f()
        times.append((time.perf_counter() - t) * 1000)
    return statistics.median(times)


def guards(n: int) -> None:
    t = ibis.table({"a": "int64", "b": "int64"}, name="t")
    expr = t.filter(t.a % t.b != 0).select(q=t.a // t.b, m=t.a % t.b, s=t.a * 3 + t.b)
    report = sv.verify(expr, requires={"t": [_.a >= 0, _.a <= 10**6, _.b >= 1, _.b <= 1000]})
    assert report._guard_free, str(report)
    rng = np.random.default_rng(0)
    data = {"t": pa.table({"a": rng.integers(0, 10**6, n), "b": rng.integers(1, 1000, n)})}
    p = plan_json(connect(), expr)
    w = written_plan(p)
    for name, run in [
        ("polars", lambda g: polars_engine.run(w, data, guards=g)),
        ("duckdb", lambda g: duckdb_engine.run(json.loads(p), data, guards=g)),
    ]:
        with_ = median_ms(lambda run=run: run(True))
        without = median_ms(lambda run=run: run(False))
        print(
            f"guards   {name:7} {n:>9} rows: {with_:8.1f} ms checked, {without:8.1f} ms unchecked"
            f" ({with_ / without:.1f}x)"
        )


def sharded(n: int, k: int = 8) -> None:
    con = connect()
    con.create("r", ibis.schema({"a": "int64", "b": "int64"}))
    sql = "SELECT b, COUNT(*) AS n, SUM(a) AS s, MAX(a) AS hi FROM r GROUP BY b"
    plan = substrait_json(con, sql)
    rng = np.random.default_rng(0)
    whole = pa.table({"a": rng.integers(0, 1000, n), "b": rng.integers(0, 50, n)})
    shards = [{"r": whole.slice(i * n // k, (i + 1) * n // k - i * n // k)} for i in range(k)]
    w = written_plan(plan)
    one = median_ms(lambda: polars_engine.run(w, {"r": whole}))
    many = median_ms(lambda: run_sharded(plan, shards, sharded=["r"]))
    print(
        f"sharded  polars  {n:>9} rows: {one:8.1f} ms whole,   {many:8.1f} ms in {k} shards"
        f" ({one / many:.1f}x)"
    )


def group_by_fd(n: int) -> None:
    line = ibis.table({"l_orderkey": "int64", "l_price": "int64"}, name="lineitem")
    orders = ibis.table({"o_orderkey": "int64", "o_date": "int64", "o_prio": "string"}, name="ord")
    expr = (
        line.join(orders, line.l_orderkey == orders.o_orderkey)
        .group_by([line.l_orderkey, orders.o_date, orders.o_prio])
        .agg(rev=line.l_price.sum())
    )
    report = sv.verify(expr, requires={"ord": [sv.unique("o_orderkey")]})
    assert report._optimized is not None and report._rewrites, str(report)
    rng = np.random.default_rng(0)
    m = n // 4
    data = {
        "lineitem": pa.table(
            {"l_orderkey": rng.integers(0, m, n), "l_price": rng.integers(0, 1000, n)}
        ),
        "ord": pa.table(
            {
                "o_orderkey": np.arange(m),
                "o_date": rng.integers(0, 3000, m),
                "o_prio": pa.array([f"{i % 5}-PRIO" for i in range(m)]),
            }
        ),
    }
    p = json.loads(plan_json(connect(), expr))
    for name, run in [("polars", polars_engine.run), ("duckdb", duckdb_engine.run)]:
        as_written = median_ms(lambda run=run: run(p, data))
        rewritten = median_ms(lambda run=run: run(report._optimized, data))
        print(
            f"group-fd {name:7} {n:>9} rows: {as_written:8.1f} ms as written, {rewritten:8.1f} ms"
            f" by key ({as_written / rewritten:.1f}x)"
        )


def eager(n: int) -> None:
    line = ibis.table({"l_orderkey": "int64", "l_price": "int64"}, name="lineitem")
    orders = ibis.table({"o_orderkey": "int64", "o_date": "int64"}, name="ord")
    expr = (
        line.join(orders, line.l_orderkey == orders.o_orderkey)
        .group_by(line.l_orderkey)
        .agg(rev=line.l_price.sum(), n=line.l_price.count())
    )
    report = sv.verify(expr, requires={"ord": [sv.unique("o_orderkey")]})
    assert report._optimized is not None and report._rewrites, str(report)
    rng = np.random.default_rng(0)
    m = n // 4
    data = {
        "lineitem": pa.table(
            {"l_orderkey": rng.integers(0, m, n), "l_price": rng.integers(0, 1000, n)}
        ),
        "ord": pa.table(
            {"o_orderkey": np.arange(0, m, 2), "o_date": rng.integers(0, 3000, m // 2)}
        ),
    }
    p = json.loads(written_plan(plan_json(connect(), expr)))
    for name, run in [("polars", polars_engine.run), ("duckdb", duckdb_engine.run)]:
        as_written = median_ms(lambda run=run: run(p, data))
        rewritten = median_ms(lambda run=run: run(report._optimized, data))
        print(
            f"eager    {name:7} {n:>9} rows: {as_written:8.1f} ms as written, {rewritten:8.1f} ms"
            f" aggregated first ({as_written / rewritten:.1f}x)"
        )


def spread_ms(f: Callable[[], object], runs: int = 7) -> tuple[float, float]:
    """The median of `runs` runs in ms, and their spread: (max - min) / median."""
    f()  # warm up
    times = []
    for _run in range(runs):
        t = time.perf_counter()
        f()
        times.append((time.perf_counter() - t) * 1000)
    med = statistics.median(times)
    return med, (max(times) - min(times)) / med


def spark_runner(data: dict[str, pa.Table]) -> Callable[[dict], object] | None:
    """A Spark run of a plan over `data`, registered as views once so that only
    the query is timed; None without `sverify-spark`."""
    try:
        from sverify_spark import engine as spark_engine
        from sverify_spark.dialect import SPARK
    except ImportError:
        return None
    spark = spark_engine.session()
    spark_engine.put_tables(data, spark)
    return lambda plan: spark.sql(to_sql(plan, SPARK)).toArrow()


def rule_case(
    label: str, expr: object, requires: dict, data: dict[str, pa.Table], rule: str
) -> None:
    """One rule of `Rel.rule`: the plan as written and as rewritten, on Polars,
    DuckDB and Spark, with the run-to-run spread, and the written SQL's
    characters."""
    report = sv.verify(expr, requires=requires)
    assert rule in report._rewrites, (label, report._rewrites)
    assert report.internal_plan is not None and report._optimized is not None
    p = json.loads(written_plan(report.internal_plan))
    q = report._optimized
    sql_p, sql_q = len(to_sql(p, DUCKDB)), len(to_sql(q, DUCKDB))
    runs: list[tuple[str, Callable[[dict], object]]] = [
        ("polars", lambda plan: polars_engine.run(plan, data)),
        ("duckdb", lambda plan: duckdb_engine.run(plan, data)),
    ]
    if (spark := spark_runner(data)) is not None:
        runs.append(("spark", spark))
    for name, run in runs:
        as_written, sp_w = spread_ms(lambda run=run: run(p))
        rewritten, sp_r = spread_ms(lambda run=run: run(q))
        print(
            f"rule {label:15} {name:7}: {as_written:8.1f} ms (±{sp_w:.0%}) as written,"
            f" {rewritten:8.1f} ms (±{sp_r:.0%}) rewritten ({as_written / rewritten:.2f}x);"
            f" SQL {sql_p} -> {sql_q} chars"
        )


def rules(n: int) -> None:
    rng = np.random.default_rng(0)
    m = max(n // 4, 1)
    t = ibis.table({"id": "int64", "g": "int64", "a": "int64"}, name="t")
    tdata = {
        "t": pa.table(
            {"id": np.arange(n), "g": rng.integers(0, 100, n), "a": rng.integers(0, 1000, n)}
        )
    }
    key = {"t": [sv.unique("id"), _.a >= 0, _.a <= 1000]}
    rule_case("implied-filter", t.filter(t.a >= 0), key, tdata, "filter implied by the contract")
    rule_case("empty-filter", t.filter(t.a < 0), key, tdata, "filter the contract rules out")
    rule_case("distinct-key", t.distinct(), key, tdata, "DISTINCT on a key")
    rule_case(
        "group-key",
        t.group_by(["id", (t.g + 1).name("h")]).aggregate(),
        key,
        tdata,
        "GROUP BY a key",
    )
    rule_case(
        "distinct-agg",
        t.group_by("g").aggregate(n=t.id.nunique()),
        key,
        tdata,
        "DISTINCT aggregate of a key",
    )
    o = ibis.table({"id": "int64", "cust": "int64", "amount": "int64"}, name="o")
    c = ibis.table({"cid": "int64", "name": "string"}, name="c")
    jdata = {
        "o": pa.table(
            {
                "id": np.arange(n),
                "cust": rng.integers(0, m, n),
                "amount": rng.integers(0, 1000, n),
            }
        ),
        "c": pa.table({"cid": np.arange(m), "name": pa.array([f"c{i % 97}" for i in range(m)])}),
    }
    fk = {
        "o": [_.cust.notnull(), sv.references("cust", to=("c", "cid"))],
        "c": [sv.unique("cid")],
    }
    rule_case(
        "left-fk",
        o.left_join(c, o.cust == c.cid).select(o.id, o.amount, c.name),
        fk,
        jdata,
        "left join on a foreign key",
    )
    rule_case(
        "left-null-rej",
        o.left_join(c, o.cust == c.cid).filter(c.name.notnull()).select(o.id, c.name),
        {},
        jdata,
        "left join under a filter rejecting NULLs",
    )
    rule_case(
        "join-fk-unused",
        o.join(c, o.cust == c.cid).select(o.id, o.amount),
        fk,
        jdata,
        "join on a foreign key, no column used",
    )
    rule_case(
        "left-key-unused",
        o.left_join(c, o.cust == c.cid).select(o.id, o.amount),
        {"c": [sv.unique("cid")]},
        jdata,
        "left join on a key, no column used",
    )


if __name__ == "__main__":
    rows = int(sys.argv[1]) if len(sys.argv) > 1 else 1_000_000
    if sys.argv[2:] == ["rules"]:
        rules(rows)
        sys.exit()
    guards(rows)
    sharded(rows)
    group_by_fd(rows)
    eager(rows)
    rules(rows)
