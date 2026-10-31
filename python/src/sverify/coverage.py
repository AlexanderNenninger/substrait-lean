"""Which parts of the Ibis API reach the Lean checker.

Each case is an Ibis expression over two unbound tables. It is compiled the way
`sverify` compiles Ibis expressions (the vendored producer,
`sverify.ibis_substrait`) and handed to `substrait-check`:

* `verified`: parsed into the Lean model and well-formed, so contracts and
  (where `incremental`) incremental views apply;
* `rejected`: the producer or the checker refuses it (an operation outside
  the model);
* `upstream`: Ibis fails before a plan exists.

Every verified case also runs on each engine (`ENGINES`): Polars and the SQL
of DuckDB, Snowflake and Spark translate the plan Lean writes back out. `REFUSED`
lists the cases an engine refuses, and why; `tests/test_backends.py` runs the
rest on random tables and compares the engines.

`tests/test_coverage.py` pins every case to its `expected` status and its
refusals, so a change in coverage is a deliberate edit here. Regenerate the
README tables with

    uv run python -m sverify.coverage --write-readme
"""

from __future__ import annotations

import datetime as dt
import json
import re
import sys
from collections.abc import Callable
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Literal

import ibis
import ibis.expr.operations as ops
import ibis.expr.types as ir
from ibis import _

from sverify.engine import run_checker, written_plan
from sverify.ibis_substrait import Unsupported, to_substrait_json

Status = Literal["verified", "rejected", "upstream"]

T = ibis.table(
    {
        "id": "int64",
        "name": "string",
        "amount": "float64",
        "qty": "int64",
        "ts": "timestamp",
        "flag": "boolean",
    },
    name="t",
)
U = ibis.table({"name": "string", "region": "string"}, name="u")
L = ibis.table({"k": "int64", "xs": "array<int64>"}, name="l")
t, u, ls = T, U, L
#: A date constant.
DAY0 = ibis.literal(dt.date(1970, 1, 5))
#: Every table the cases read.
TABLES = (T, U, L)
#: A memtable: its rows are part of the plan.
M = ibis.memtable(
    {"name": ["ada", "bob", None], "score": [1, None, 3]},
    schema={"name": "string", "score": "int64"},
)


def sql_view(table: ir.Table, query: str) -> ir.Table:
    """`table.alias("v").sql(query)` without a backend: `Table.sql` needs one
    to infer the schema, which DataFusion does here. (Ibis 12's DuckDB backend
    cannot: it calls a method DuckDB 2 no longer has.)"""
    from sverify.ibis_substrait import sql_view_schema

    parent: Any = table.alias("v").op()
    schema = sql_view_schema(parent, query)
    return ops.SQLStringView(parent=parent, query=query, schema=schema).to_expr()


class _Tables:
    """The schemas of `t` and `u`, as a backend gives them to `Backend.sql`."""

    def get_schema(self, name: str) -> ibis.Schema:
        return {"t": T, "u": U}[name].schema()


def sql_query(query: str, schema: dict[str, str]) -> ir.Table:
    """`backend.sql(query)` over `t` and `u`."""
    return ops.SQLQueryResult(query, ibis.schema(schema), _Tables()).to_expr()


def exists(table: ir.Table) -> ir.BooleanValue:
    """`EXISTS (table)`; Ibis builds it only from a correlated `.any()`."""
    rel: Any = table.op()
    return ops.ExistsSubquery(rel).to_expr()


@dataclass(frozen=True)
class Case:
    area: str
    label: str
    build: Callable[[], ir.Table]
    expected: Status


def case(area: str, label: str, expected: Status, build: Callable[[], ir.Table]) -> Case:
    return Case(area, label, build, expected)


V, R, X = "verified", "rejected", "upstream"

CASES: list[Case] = [
    # Rows and columns
    case("rows", "filter, select", V, lambda: t.filter(t.qty > 1).select("id", "qty")),
    case("rows", "mutate", V, lambda: t.mutate(y=t.qty + 1)),
    case("rows", "drop, rename", V, lambda: t.drop("flag").rename(q="qty")),
    case("rows", "drop_null", V, lambda: t.drop_null(["qty"])),
    case("rows", "isnull", V, lambda: t.filter(t.qty.isnull())),
    case("rows", "between", V, lambda: t.filter(t.qty.between(1, 5))),
    case("rows", "isin", V, lambda: t.filter(t.qty.isin([1, 2, 3]))),
    case("rows", "notin", V, lambda: t.filter(t.qty.notin([1, 2]))),
    case("rows", "ifelse", V, lambda: t.select(x=ibis.ifelse(t.flag, 1, 0))),
    case("rows", "cases", V, lambda: t.select(x=ibis.cases((t.qty > 5, "big"), else_="small"))),
    case("rows", "order_by", V, lambda: t.order_by("qty")),
    case("rows", "limit", V, lambda: t.limit(3)),
    case("rows", "limit with offset", V, lambda: t.limit(3, offset=1)),
    case("rows", "order_by + limit", V, lambda: t.order_by(ibis.desc("qty")).limit(3)),
    case("rows", "sample", R, lambda: t.sample(0.5)),
    case("rows", "order_by expression", V, lambda: t.order_by(t.qty + 1)),
    # Ibis's annotations are narrower than what it accepts.
    case("rows", "limit expression", R, lambda: t.limit(ibis.literal(2) + 1)),  # pyrefly: ignore
    case("rows", "limit count()", R, lambda: t.limit(t.count())),  # pyrefly: ignore
    case("rows", "fill_null table", V, lambda: t.fill_null({"qty": 0, "name": "?"})),  # pyrefly: ignore
    case("rows", "fill_null all", V, lambda: t.select("id", "qty").fill_null(0)),  # pyrefly: ignore
    case("rows", "memtable", V, lambda: t.join(M, t.name == M.name)),
    case("rows", "constant table", V, lambda: ibis.literal(1, "int64").name("one").as_table()),
    case("rows", "alias", V, lambda: t.alias("v").filter(_.qty > 1)),
    case("rows", "sql view", V, lambda: sql_view(t, "SELECT name, qty FROM v WHERE qty > 1")),
    case(
        "rows",
        "sql query",
        V,
        lambda: sql_query(
            "SELECT t.name, region FROM t JOIN u ON t.name = u.name",
            {"name": "string", "region": "string"},
        ),
    ),
    # Joins and set operations
    case("joins", "inner join", V, lambda: t.join(u, "name")),
    case("joins", "non-equi join", V, lambda: t.join(u, t.name < u.name)),
    case("joins", "cross join", V, lambda: t.cross_join(u)),
    case("joins", "left join", V, lambda: t.left_join(u, "name")),
    case("joins", "right join", V, lambda: t.right_join(u, "name")),
    case("joins", "outer join", V, lambda: t.outer_join(u, "name")),
    case("joins", "semi join", V, lambda: t.semi_join(u, "name")),
    case("joins", "anti join", V, lambda: t.anti_join(u, "name")),
    case("joins", "isin subquery", V, lambda: t.filter(t.name.isin(u.name))),
    case("joins", "isin subquery in select", V, lambda: t.select("id", x=t.name.isin(u.name))),
    case(
        "joins",
        "notin subquery",
        V,
        lambda: t.filter(t.name.notin(u.name) | t.flag),
    ),
    case("joins", "scalar subquery in select", V, lambda: t.select("id", n=u.count())),
    case(
        "joins",
        "scalar subquery, one row",
        V,
        lambda: t.select("id", r=u.order_by("name").limit(1).name.as_scalar()),
    ),
    case(
        "joins",
        "scalar subquery, many rows",
        R,
        lambda: t.select("id", r=u.filter(u.region == "eu").name.as_scalar()),
    ),
    case("joins", "exists", V, lambda: t.filter((u.name == t.name).any())),
    case("joins", "not exists", V, lambda: t.filter(~(u.name == t.name).any())),
    case(
        "joins",
        "exists, uncorrelated",
        V,
        lambda: t.select("id", e=exists(u.filter(u.region == "eu"))),
    ),
    case(
        "joins",
        "correlated scalar subquery",
        R,
        lambda: t.filter(u.filter(u.name == t.name).count() > 0),  # pyrefly: ignore
    ),
    case("joins", "union all", V, lambda: t.select("name").union(u.select("name"))),
    case(
        "joins",
        "union distinct",
        V,
        lambda: t.select("name").union(u.select("name"), distinct=True),
    ),
    case("joins", "intersect", V, lambda: t.select("name").intersect(u.select("name"))),
    case("joins", "difference", V, lambda: t.select("name").difference(u.select("name"))),
    case(
        "joins",
        "intersect all",
        V,
        lambda: t.select("name").intersect(u.select("name"), distinct=False),
    ),
    case(
        "joins",
        "difference all",
        V,
        lambda: t.select("name").difference(u.select("name"), distinct=False),
    ),
    # Aggregation
    case("aggregation", "count()", V, lambda: t.aggregate(n=t.count())),
    case("aggregation", "group_by sum", V, lambda: t.group_by("name").aggregate(s=t.qty.sum())),
    case(
        "aggregation",
        "count, max, mean",
        V,
        lambda: t.group_by("name").aggregate(n=t.count(), m=t.qty.max(), a=t.amount.mean()),
    ),
    case("aggregation", "nunique", V, lambda: t.group_by("name").aggregate(n=t.id.nunique())),
    case(
        "aggregation",
        "sum(where=)",
        V,
        lambda: t.group_by("name").aggregate(s=t.qty.sum(where=t.flag)),
    ),
    case(
        "aggregation",
        "having",
        V,
        # Ibis types `having` too narrowly; it accepts deferred conditions.
        lambda: t.group_by("name").having(_.count() > 1).aggregate(n=t.count()),  # pyrefly: ignore
    ),
    case("aggregation", "value_counts", V, lambda: t.name.value_counts()),
    case("aggregation", "distinct", V, lambda: t.select("name").distinct()),
    case("aggregation", "distinct(on=)", R, lambda: t.distinct(on="name", keep="first")),
    case("aggregation", "std", R, lambda: t.aggregate(s=t.amount.std())),
    case("aggregation", "collect", V, lambda: t.group_by("name").aggregate(xs=t.qty.collect())),
    case(
        "aggregation",
        "collect ordered",
        V,
        lambda: t.group_by("name").aggregate(xs=t.qty.collect(order_by="qty")),
    ),
    case(
        "aggregation",
        "collect include_null",
        R,
        lambda: t.group_by("name").aggregate(xs=t.qty.collect(include_null=True)),
    ),
    case("aggregation", "scalar subquery", V, lambda: t.filter(t.qty > t.qty.mean())),
    case(
        "aggregation",
        "unnest",
        V,
        lambda: t.group_by("name").aggregate(xs=t.qty.collect()).unnest("xs"),
    ),
    # Lists
    case("lists", "unnest column", V, lambda: ls.unnest("xs")),
    case("lists", "unnest keep_empty", R, lambda: ls.unnest("xs", keep_empty=True)),
    case(
        "lists",
        "list literal",
        V,
        lambda: t.select("id", xs=ibis.literal([1, 2], "array<int64>")),
    ),
    case("lists", "list column", V, lambda: ls.filter(ls.k > 0)),
    # Window functions
    case(
        "windows",
        "row_number",
        V,
        lambda: t.mutate(r=ibis.row_number().over(group_by="name", order_by="ts")),
    ),
    case("windows", "lag", V, lambda: t.mutate(p=t.qty.lag().over(group_by="name", order_by="ts"))),
    case(
        "windows", "rank", V, lambda: t.mutate(r=ibis.rank().over(group_by="name", order_by="ts"))
    ),
    case(
        "windows",
        "dense_rank",
        V,
        lambda: t.mutate(r=ibis.dense_rank().over(group_by="name", order_by="ts")),
    ),
    case("windows", "cumsum", V, lambda: t.mutate(c=t.qty.cumsum(order_by="ts"))),
    case("windows", "sum over group", V, lambda: t.mutate(s=t.qty.sum().over(group_by="name"))),
    case(
        "windows",
        "rolling mean (rows)",
        R,
        lambda: t.mutate(
            m=t.amount.mean().over(ibis.window(order_by="ts", preceding=2, following=0))
        ),
    ),
    case(
        "windows",
        "rolling mean (interval)",
        R,
        lambda: t.mutate(
            m=t.amount.mean().over(
                ibis.range_window(order_by="ts", preceding=ibis.interval(minutes=5), following=0)
            )
        ),
    ),
    case("windows", "ntile", V, lambda: t.mutate(q=ibis.ntile(4).over(order_by="ts"))),
    case(
        "windows",
        "first",
        V,
        lambda: t.mutate(f=t.qty.first().over(group_by="name", order_by="ts")),
    ),
    case(
        "windows",
        "percent_rank, cume_dist",
        V,
        lambda: t.mutate(
            p=ibis.percent_rank().over(order_by="qty"), c=ibis.cume_dist().over(order_by="qty")
        ),
    ),
    case(
        "windows",
        "running mean",
        V,
        lambda: t.mutate(m=t.amount.mean().over(ibis.window(order_by="ts", following=0))),
    ),
    case(
        "windows",
        "rolling sum (interval)",
        V,
        lambda: t.mutate(
            s=t.qty.sum().over(
                ibis.range_window(order_by="ts", preceding=ibis.interval(minutes=5), following=0)
            )
        ),
    ),
    case(
        "windows",
        "rolling sum (range)",
        V,
        lambda: t.mutate(
            s=t.id.sum().over(ibis.range_window(order_by="qty", preceding=2, following=0))
        ),
    ),
    case(
        "windows",
        "last, nth",
        V,
        lambda: t.mutate(
            l=t.qty.last().over(group_by="name", order_by="ts"),
            n=t.qty.nth(1).over(group_by="name", order_by="ts"),
        ),
    ),
    case(
        "windows",
        "max, count over frame",
        V,
        lambda: t.mutate(
            b=t.qty.max().over(ibis.window(order_by="ts", preceding=1, following=1)),
            c=t.qty.count().over(ibis.window(order_by="ts", preceding=1, following=1)),
        ),
    ),
    case(
        "windows",
        "min over a sliding frame",
        R,
        lambda: t.mutate(a=t.qty.min().over(ibis.window(order_by="ts", preceding=1, following=1))),
    ),
    case(
        "windows",
        "window sum of an expression",
        R,
        lambda: t.mutate(s=(t.qty * 2).sum().over(group_by="name")),
    ),
    # Numbers
    case("numbers", "+, -, *", V, lambda: t.select(x=t.qty * 2 - t.id + 1)),
    case("numbers", "float division", V, lambda: t.select(x=t.qty / 2)),
    case("numbers", "integer division", V, lambda: t.select(x=t.qty // 2)),
    case("numbers", "mod", V, lambda: t.select(x=t.qty % 3)),
    case("numbers", "abs", V, lambda: t.select(x=t.qty.abs())),
    case("numbers", "round", V, lambda: t.select(x=t.amount.round(1))),
    case("numbers", "ceil, floor", V, lambda: t.select(x=t.amount.ceil(), y=t.amount.floor())),
    case("numbers", "power", V, lambda: t.select(x=t.qty**2)),
    case("numbers", "greatest", V, lambda: t.select(x=ibis.greatest(t.qty, 0))),
    case("numbers", "least", V, lambda: t.select(x=ibis.least(t.qty, t.id))),
    case("numbers", "clip", V, lambda: t.select(x=t.qty.clip(0, 10))),
    case("numbers", "cast int → double", V, lambda: t.select(x=t.qty.cast("float64"))),
    case("numbers", "cast int → string", V, lambda: t.select(x=t.qty.cast("string"))),
    case("numbers", "cast double → int", V, lambda: t.select(x=t.amount.cast("int64"))),
    # Missing values
    case("nulls", "fill_null", V, lambda: t.select(x=t.qty.fill_null(0))),
    case("nulls", "coalesce", V, lambda: t.select(x=ibis.coalesce(t.qty, t.id))),
    case("nulls", "nullif", V, lambda: t.select(x=t.qty.nullif(0))),
    # Strings
    case("strings", "upper", V, lambda: t.select(x=t.name.upper())),
    case("strings", "length", V, lambda: t.select(x=t.name.length())),
    case("strings", "concat", V, lambda: t.select(x=t.name + "!")),
    case("strings", "substr", V, lambda: t.select(x=t.name.substr(0, 2))),
    case("strings", "contains", V, lambda: t.filter(t.name.contains("a"))),
    case("strings", "startswith", V, lambda: t.filter(t.name.startswith("a"))),
    case("strings", "like", V, lambda: t.filter(t.name.like("a%"))),
    case("strings", "re_search", V, lambda: t.filter(t.name.re_search("^a"))),
    case("strings", "strip", V, lambda: t.select(x=t.name.strip())),
    # Dates and times
    case("time", "timestamp + interval", V, lambda: t.select(x=t.ts + ibis.interval(hours=1))),
    case(
        "time",
        "compare with literal",
        V,
        lambda: t.filter(t.ts > ibis.timestamp("2024-01-01 00:00:00")),
    ),
    case("time", "year", V, lambda: t.select(x=t.ts.year())),
    case("time", "date", V, lambda: t.select(x=t.ts.date())),
    case("time", "truncate", V, lambda: t.select(x=t.ts.truncate("h"))),
    case("time", "date + days", V, lambda: t.select(x=t.ts.date() + ibis.interval(days=3))),
    case("time", "date - months", V, lambda: t.select(x=t.ts.date() - ibis.interval(months=1))),
    case("time", "date + years", V, lambda: t.select(x=t.ts.date() + ibis.interval(years=1))),
    case(
        "time",
        "date - column days",
        V,
        lambda: t.select(x=t.ts.date() - t.qty.as_interval("D")),
    ),
    case("time", "timestamp + months", V, lambda: t.select(x=t.ts + ibis.interval(months=13))),
    case(
        "time",
        "constant interval arithmetic",
        V,
        lambda: t.select(x=t.ts + (ibis.interval(days=1) + ibis.interval(hours=2))),
    ),
    case(
        "time",
        "date - date",
        V,
        lambda: t.filter(t.ts.date() - DAY0 > ibis.interval(days=3)),
    ),
    case("time", "date delta", V, lambda: t.select(x=t.ts.date().delta(DAY0, unit="day"))),
    case("time", "date parts", V, lambda: t.select(y=t.ts.date().year(), m=t.ts.date().month())),
    case("time", "date truncate", V, lambda: t.select(x=t.ts.date().truncate("M"))),
    case("time", "day_of_week", V, lambda: t.select(x=t.ts.day_of_week.index())),
    case("time", "day_of_week name", V, lambda: t.select(x=t.ts.date().day_of_week.full_name())),
    case("time", "iso_year", V, lambda: t.select(x=t.ts.iso_year())),
    case("time", "epoch_seconds", V, lambda: t.select(x=t.ts.epoch_seconds())),
    case(
        "time",
        "millisecond, microsecond",
        V,
        lambda: t.select(x=t.ts.millisecond(), y=t.ts.microsecond()),
    ),
    case(
        "time",
        "timestamp + column interval",
        R,
        lambda: t.select(x=t.ts + t.qty.as_interval("h")),
    ),
    case(
        "time",
        "date + column months",
        R,
        lambda: t.select(x=t.ts.date() + t.qty.as_interval("M")),
    ),
    case("time", "timestamp delta", R, lambda: t.select(x=t.ts.delta(t.ts, unit="hour"))),
    case("time", "bucket", R, lambda: t.select(x=t.ts.bucket(minutes=15))),
    case("time", "time of day", V, lambda: t.select(x=t.ts.time())),
    case("time", "time parts", V, lambda: t.select(h=t.ts.time().hour(), m=t.ts.time().minute())),
    case("time", "compare times", V, lambda: t.filter(t.ts.time() > dt.time(9, 30))),
    case("time", "strftime", V, lambda: t.select(x=t.ts.strftime("%Y-%m-%d %H:%M:%S"))),
    case("time", "timestamp from unix", V, lambda: t.select(x=t.qty.as_timestamp("ms"))),
    case(
        "time", "date from constants", V, lambda: t.select(x=t.ts.date() < ibis.date(2024, 2, 29))
    ),
    case(
        "time",
        "timestamp from constants",
        V,
        lambda: t.filter(t.ts < ibis.timestamp(2024, 1, 2, 3, 4, 5)),
    ),
    case("time", "date from columns", R, lambda: t.select(x=ibis.date(t.qty, 1, 1))),
    case("time", "string to timestamp", R, lambda: t.select(x=t.name.as_timestamp("%Y-%m-%d"))),
    case("time", "time + interval", R, lambda: t.select(x=t.ts.time() + ibis.interval(hours=1))),
    case("time", "time truncate", R, lambda: t.select(x=t.ts.time().truncate("h"))),
    case("time", "strftime other directives", R, lambda: t.select(x=t.ts.strftime("%A"))),
    case(
        "time",
        "between_time",
        X,
        lambda: t.filter(t.ts.time().between(dt.time(9), dt.time(17))),
    ),
]


#: Verified cases whose Ibis SQL DataFusion does not run, or runs wrongly:
#: the tests check them against the other engines, Lean and Python instead.
NO_DATAFUSION_SQL = {
    # `CAST(n || ' day' AS INTERVAL)` fails on a NULL count.
    "date - column days": "fails on NULL",
    # Python UDFs of Ibis's DataFusion backend.
    "epoch_seconds": "Ibis UDF",
    "millisecond, microsecond": "Ibis UDF",
    # No compilation rule.
    "iso_year": "no rule",
    "date delta": "no rule",
    # A duration is compared with `INTERVAL '3 DAYS'` as (months, days, ns).
    "date - date": "compares durations with days wrongly",
    # "frame offsets for RANGE must be …": Ibis writes the bound as a cast.
    "rolling sum (interval)": "refuses Ibis's interval frame",
}

#: The engines besides DataFusion, which runs Ibis's own plans.
ENGINES = ("polars", "duckdb", "snowflake", "spark")

#: Verified cases an engine refuses (`Unsupported`), with a pattern of the
#: reason. These are what cannot be expressed there:
#:
#: * `lt` on strings is undefined in the model (`BinFn.apply` has no case for
#:   it, so it is NULL, where SQL compares), so no engine may run it.
#: * Snowflake and Spark tables have no row order, which FETCH and a stable
#:   sort's or a window's ties follow. Sorts and windows run with
#:   `tie_free=True`. A `SUM` or `AVG` of doubles adds in that order too
#:   (rounding depends on it). So does a window frame's `SUM` or `AVG`.
#: * Spark has no TIME type before 4.1.
NO_ROW_ORDER = {"snowflake": "no row order", "spark": "no row order"}
#: A frame's doubles are added in frame order (`floatSum`), which only DuckDB's
#: and Polars' translations keep.
FRAME_DOUBLES = {"snowflake": "doubles in order", "spark": "doubles in order"}
REFUSED: dict[str, dict[str, str]] = {
    "count, max, mean": NO_ROW_ORDER,
    "non-equi join": {
        "polars": "lt of String",
        "duckdb": "ordering comparisons of str values",
        "snowflake": "ordering comparisons of str values",
        "spark": "ordering comparisons of str values",
    },
    "order_by": NO_ROW_ORDER,
    "scalar subquery": NO_ROW_ORDER,
    "scalar subquery, one row": NO_ROW_ORDER,
    "order_by expression": NO_ROW_ORDER,
    "limit": NO_ROW_ORDER,
    "limit with offset": NO_ROW_ORDER,
    "order_by + limit": NO_ROW_ORDER,
    "row_number": NO_ROW_ORDER,
    "lag": NO_ROW_ORDER,
    "time of day": {"spark": "no tod type"},
    "time parts": {"spark": "no tod type"},
    "compare times": {"spark": "no tod type"},
    "rank": NO_ROW_ORDER,
    "dense_rank": NO_ROW_ORDER,
    "cumsum": NO_ROW_ORDER,
    "sum over group": NO_ROW_ORDER,
    "ntile": NO_ROW_ORDER,
    "first": NO_ROW_ORDER,
    "percent_rank, cume_dist": NO_ROW_ORDER,
    "rolling sum (range)": NO_ROW_ORDER,
    "rolling sum (interval)": NO_ROW_ORDER,
    "running mean": FRAME_DOUBLES,
    "last, nth": NO_ROW_ORDER,
    "max, count over frame": NO_ROW_ORDER,
}
#: Of those, the cases Snowflake and Spark run when the caller promises no ties.
TIE_FREE = {
    "order_by", "order_by expression", "row_number", "lag", "rank", "dense_rank", "cumsum",
    "ntile", "first", "percent_rank, cume_dist", "rolling sum (range)", "rolling sum (interval)",
    "last, nth", "max, count over frame",
}  # fmt: skip

#: The SQL dialects have no lists yet (#94).
NO_LISTS = {
    "duckdb": "array_agg|unsupported relation|unsupported literal|unsupported column type",
    "snowflake": "array_agg|unsupported relation|unsupported literal|unsupported column type",
    "spark": "array_agg|unsupported relation|unsupported literal|unsupported column type",
}
REFUSED.update(
    {
        label: NO_LISTS
        for label in ("collect", "collect ordered", "unnest", "unnest column", "list literal")
    }
)
#: Lists built from rows in an order the plan does not fix: compared as bags.
UNORDERED_LISTS = {"collect"}


#: Verified cases where DataFusion running Ibis's own SQL means something else
#: than the plan (and SQL), or fails: the tests compare them with DuckDB running Ibis's
#: DuckDB SQL instead.
DATAFUSION_SQL = {
    "intersect all": "DataFusion 51 plans INTERSECT ALL as a semi join: every left copy stays",
    "difference all": "DataFusion 51 plans EXCEPT ALL as an anti join: every left copy goes",
    "isin subquery in select": "DataFusion 51 cannot run IN (subquery) outside a filter",
    "exists, uncorrelated": "DataFusion 51 cannot run EXISTS (subquery) outside a filter",
    "notin subquery": "DataFusion 51's NOT IN (subquery) ignores NULLs in the subquery",
    "unnest": "Ibis cannot compile TableUnnest for DataFusion",
    "unnest column": "Ibis cannot compile TableUnnest for DataFusion",
}

#: The memtables of the cases, by name: engines that run Ibis's SQL need them
#: as tables.
_M: Any = M.op()
MEMTABLES = {_M.name: _M.data.to_pyarrow(M.schema())}


def refusal(c: Case, engine: str, tie_free: bool = False) -> str | None:
    """Why `engine` refuses the plan of a verified case, or None if it runs it."""
    from sverify import polars_engine
    from sverify.sql import Unsupported as Untranslatable
    from sverify.sql import to_sql as plan_sql
    from sverify.sql.duckdb import DUCKDB
    from sverify.sql.snowflake import SNOWFLAKE
    from sverify.sql.spark import SPARK

    dialects = {"duckdb": DUCKDB, "snowflake": SNOWFLAKE, "spark": SPARK}
    plan = json.loads(written_plan(to_substrait_json(c.build())))
    try:
        if engine == "polars":
            tables = {t.get_name(): t.schema().to_pyarrow().empty_table() for t in TABLES}
            polars_engine.run(plan, tables)
        else:
            plan_sql(plan, dialects[engine], tie_free=tie_free)
    except (polars_engine.Unsupported, Untranslatable) as e:
        return str(e)
    return None


@dataclass(frozen=True)
class Result:
    case: Case
    status: Status
    incremental: bool
    detail: str
    refused: dict[str, str]
    """Engine → reason, for the engines that refuse a verified case."""


def check(c: Case) -> Result:
    try:
        expr = c.build()
    except Exception as e:  # noqa: BLE001 - any Ibis failure counts
        return Result(c, "upstream", False, str(e).splitlines()[0], {})
    try:
        plan = to_substrait_json(expr)
    except Unsupported as e:
        return Result(c, "rejected", False, str(e), {})
    code, stdout, stderr = run_checker((), plan)
    out = stdout + stderr
    if code == 0:
        refused = {e: why for e in ENGINES if (why := refusal(c, e)) is not None}
        return Result(c, "verified", "incremental: yes" in out, "", refused)
    lines = [ln for ln in out.splitlines() if ln.startswith(("error:", "well-formed: no"))]
    return Result(c, "rejected", False, (lines or [out.strip()])[-1], {})


def results() -> list[Result]:
    return [check(c) for c in CASES]


SYMBOL = {"verified": "✓", "rejected": "✗", "upstream": "–"}
START, END = "<!-- coverage:start -->", "<!-- coverage:end -->"
NAMES = {"polars": "Polars", "duckdb": "DuckDB", "snowflake": "Snowflake", "spark": "Spark"}


def table(rs: list[Result]) -> str:
    n = sum(r.status == "verified" for r in rs)
    lines = [
        f"{n} of {len(rs)} probed Ibis operations reach the checker "
        "(✓ verified, ✗ rejected by the checker, – fails in Ibis or DataFusion; "
        "*inc.* marks incremental maintenance).",
        "",
        "| Area | Operations |",
        "|---|---|",
    ]
    for area in dict.fromkeys(r.case.area for r in rs):
        ops = [
            f"{SYMBOL[r.status]} {r.case.label}" + (" *inc.*" if r.incremental else "")
            for r in rs
            if r.case.area == area
        ]
        lines.append(f"| {area} | {' · '.join(ops)} |")
    verified = [r for r in rs if r.status == "verified"]
    lines += [
        "",
        f"Every engine runs the plans of the {len(verified)} verified operations, except:",
        "",
        "| Engine | Runs | Refuses |",
        "|---|---|---|",
    ]
    for e in ENGINES:
        out = [r for r in verified if e in r.refused]
        refused = " · ".join(
            r.case.label + (" (with `tie_free=True` it runs)" if r.case.label in TIE_FREE else "")
            for r in out
        )
        lines.append(f"| {NAMES[e]} | {len(verified) - len(out)} | {refused or '—'} |")
    return "\n".join(lines)


def write_readme(rs: list[Result]) -> None:
    readme = Path(__file__).resolve().parents[3] / "README.md"
    text = readme.read_text()
    pattern = re.compile(re.escape(START) + ".*?" + re.escape(END), re.S)
    if not pattern.search(text):
        raise ValueError(f"{readme} has no {START} … {END} block")
    readme.write_text(pattern.sub(lambda _: f"{START}\n{table(rs)}\n{END}", text))


def main() -> None:
    rs = results()
    if "--write-readme" in sys.argv:
        write_readme(rs)
    else:
        print(table(rs))
    for r in rs:
        if r.status != r.case.expected:
            print(f"{r.case.label}: expected {r.case.expected}, got {r.status} {r.detail}")


if __name__ == "__main__":
    main()
