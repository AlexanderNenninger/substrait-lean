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

The cases probe every Ibis operation: each concrete class of
`ibis.expr.operations` (geospatial aside) occurs in some case's expression, or
`OUT_OF_SCOPE` says why not. `tests/test_coverage.py` checks that, and pins
every case to its `expected` status and its refusals, so a change in coverage
is a deliberate edit here. Regenerate the
README tables with

    uv run python -m sverify.coverage --write-readme
"""

from __future__ import annotations

import json
import re
import sys
from collections.abc import Callable
from dataclasses import dataclass
from pathlib import Path
from typing import Literal

import ibis
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
#: Nested types, for the operations on them.
N = ibis.table(
    {
        "xs": "array<int64>",
        "m": "map<string, int64>",
        "s": "struct<a: int64, b: string>",
        "j": "json",
    },
    name="n",
)
t, u, n = T, U, N


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
    case("joins", "union all", V, lambda: t.select("name").union(u.select("name"))),
    case(
        "joins",
        "union distinct",
        V,
        lambda: t.select("name").union(u.select("name"), distinct=True),
    ),
    case("joins", "intersect", V, lambda: t.select("name").intersect(u.select("name"))),
    case("joins", "difference", V, lambda: t.select("name").difference(u.select("name"))),
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
    case("statistics", "std", R, lambda: t.aggregate(s=t.amount.std())),
    # Window functions
    case(
        "windows",
        "row_number",
        V,
        lambda: t.mutate(r=ibis.row_number().over(group_by="name", order_by="ts")),
    ),
    case("windows", "lag", V, lambda: t.mutate(p=t.qty.lag().over(group_by="name", order_by="ts"))),
    case(
        "windows", "rank", R, lambda: t.mutate(r=ibis.rank().over(group_by="name", order_by="ts"))
    ),
    case(
        "windows",
        "dense_rank",
        R,
        lambda: t.mutate(r=ibis.dense_rank().over(group_by="name", order_by="ts")),
    ),
    case("windows", "cumsum", R, lambda: t.mutate(c=t.qty.cumsum(order_by="ts"))),
    case("windows", "sum over group", R, lambda: t.mutate(s=t.qty.sum().over(group_by="name"))),
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
    case("windows", "ntile", R, lambda: t.mutate(q=ibis.ntile(4).over(order_by="ts"))),
    case(
        "windows",
        "first",
        R,
        lambda: t.mutate(f=t.qty.first().over(group_by="name", order_by="ts")),
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
    # Logic
    case("logic", "comparisons", V, lambda: t.filter((t.qty != 1) & (t.qty <= 5) | (t.id >= 2))),
    case("logic", "xor", V, lambda: t.filter(t.flag ^ (t.qty > 1))),
    case("logic", "identical_to", V, lambda: t.filter(t.qty.identical_to(t.id))),
    case("logic", "notnull", V, lambda: t.filter(t.qty.notnull())),
    case("logic", "simple case", V, lambda: t.select(x=t.qty.cases((1, "one"), else_="many"))),
    # Relations
    case("relations", "table fill_null", R, lambda: t.fill_null({"qty": 0})),  # pyrefly: ignore
    case("relations", "self join", V, lambda: t.join(t.view(), "id")),
    case("relations", "memtable", R, lambda: ibis.memtable({"a": [1, 2]})),
    case("relations", "literal as table", R, lambda: ibis.literal(1).as_table()),
    case("relations", "database table", R, lambda: ibis.table(T.schema(), name="t").alias("x")),
    case("relations", "rowid", R, lambda: t.select(r=t.rowid())),
    # Subqueries
    case("subqueries", "scalar subquery", R, lambda: t.filter(t.qty > t.qty.mean())),
    case("subqueries", "exists", R, lambda: t.filter((u.name == t.name).any())),
    # Statistics
    case("statistics", "median", R, lambda: t.aggregate(m=t.amount.median())),
    case("statistics", "quantile", R, lambda: t.aggregate(q=t.amount.quantile(0.9))),
    case("statistics", "multi quantile", R, lambda: t.aggregate(q=t.amount.quantile([0.1, 0.9]))),
    case("statistics", "var", R, lambda: t.aggregate(v=t.amount.var())),
    case("statistics", "corr", R, lambda: t.aggregate(c=t.amount.corr(t.qty))),
    case("statistics", "cov", R, lambda: t.aggregate(c=t.amount.cov(t.qty))),
    case("statistics", "kurtosis", R, lambda: t.aggregate(k=t.amount.kurtosis())),
    case("statistics", "approx_nunique", R, lambda: t.aggregate(n=t.qty.approx_nunique())),
    case("statistics", "approx_median", R, lambda: t.aggregate(m=t.amount.approx_median())),
    case("statistics", "approx_quantile", R, lambda: t.aggregate(q=t.amount.approx_quantile(0.5))),
    case(
        "statistics",
        "approx multi quantile",
        R,
        lambda: t.aggregate(q=t.amount.approx_quantile([0.1, 0.9])),
    ),
    case("statistics", "histogram bucket", R, lambda: t.select(b=t.qty.bucket([0, 10, 100]))),
    # Numbers
    case("numbers", "negate", V, lambda: t.select(x=-t.qty)),
    case("numbers", "sign", V, lambda: t.select(x=t.amount.sign())),
    case("numbers", "sqrt", V, lambda: t.select(x=t.amount.sqrt())),
    case("numbers", "exp", V, lambda: t.select(x=t.amount.exp())),
    case(
        "numbers",
        "ln, log10, log2",
        V,
        lambda: t.select(a=t.amount.ln(), b=t.amount.log10(), c=t.amount.log2()),
    ),
    case("numbers", "log(base)", V, lambda: t.select(x=t.amount.log(3))),
    case(
        "numbers",
        "trigonometry",
        V,
        lambda: t.select(
            a=t.amount.sin(),
            b=t.amount.cos(),
            c=t.amount.tan(),
            d=t.amount.cot(),
            e=t.amount.asin(),
            f=t.amount.acos(),
            g=t.amount.atan(),
            h=t.amount.atan2(t.amount),
        ),
    ),
    case(
        "numbers",
        "degrees, radians",
        V,
        lambda: t.select(x=t.amount.degrees(), y=t.amount.radians()),
    ),
    case("numbers", "pi, e", V, lambda: t.select(x=t.amount * ibis.pi + ibis.e)),
    case("numbers", "isnan", V, lambda: t.filter(t.amount.isnan())),
    case("numbers", "isinf", V, lambda: t.filter(t.amount.isinf())),
    case(
        "numbers",
        "bitwise",
        V,
        lambda: t.select(a=t.qty & 3, b=t.qty | 3, c=t.qty ^ 3, d=~t.qty),
    ),
    case("numbers", "shifts", V, lambda: t.select(a=t.qty << 1, b=t.qty >> 1)),
    case("numbers", "convert_base", R, lambda: t.select(x=t.name.convert_base(16, 10))),
    case("numbers", "random", R, lambda: t.select(x=ibis.random())),
    # Strings
    case("strings", "lower", V, lambda: t.select(x=t.name.lower())),
    case("strings", "capitalize", R, lambda: t.select(x=t.name.capitalize())),
    case("strings", "endswith", V, lambda: t.filter(t.name.endswith("a"))),
    case("strings", "lstrip, rstrip", V, lambda: t.select(x=t.name.lstrip(), y=t.name.rstrip())),
    case("strings", "find", V, lambda: t.select(x=t.name.find("a"))),
    case(
        "strings", "lpad, rpad", R, lambda: t.select(x=t.name.lpad(5, "-"), y=t.name.rpad(5, "-"))
    ),
    case("strings", "slice", R, lambda: t.select(x=t.name[1:3])),
    case("strings", "repeat", R, lambda: t.select(x=t.name.repeat(2))),
    case("strings", "reverse", R, lambda: t.select(x=t.name.reverse())),
    case("strings", "right", R, lambda: t.select(x=t.name.right(2))),
    case("strings", "replace", R, lambda: t.select(x=t.name.replace("a", "b"))),
    case("strings", "translate", R, lambda: t.select(x=t.name.translate("ab", "ba"))),
    case("strings", "ilike", R, lambda: t.filter(t.name.ilike("a%"))),
    case("strings", "join", R, lambda: t.select(x=ibis.literal("-").join([t.name, t.name]))),  # pyrefly: ignore
    case("strings", "ascii_str", R, lambda: t.select(x=t.name.ascii_str())),
    case("strings", "find_in_set", R, lambda: t.select(x=t.name.find_in_set(["a", "b"]))),
    case("strings", "levenshtein", R, lambda: t.select(x=t.name.levenshtein("abc"))),
    case("strings", "re_extract", R, lambda: t.select(x=t.name.re_extract("a(b)", 1))),
    case("strings", "re_replace", R, lambda: t.select(x=t.name.re_replace("a+", "b"))),
    case("strings", "re_split", R, lambda: t.select(x=t.name.re_split(",").length())),
    case("strings", "split", R, lambda: t.select(x=t.name.split(",").length())),
    case(
        "strings",
        "URL parts",
        R,
        lambda: t.select(
            a=t.name.authority(),
            b=t.name.file(),
            c=t.name.fragment(),
            d=t.name.host(),
            e=t.name.path(),
            f=t.name.protocol(),
            g=t.name.query(),
            h=t.name.userinfo(),
        ),
    ),
    case("strings", "hash", R, lambda: t.select(x=t.name.hash())),
    case("strings", "hashbytes", R, lambda: t.select(x=t.name.hashbytes())),
    case("strings", "hexdigest", R, lambda: t.select(x=t.name.hexdigest())),
    case("strings", "uuid", R, lambda: t.select(x=ibis.uuid())),
    # Types
    case("types", "try_cast", R, lambda: t.select(x=t.name.try_cast("int64"))),
    case("types", "typeof", R, lambda: t.select(x=t.qty.typeof())),
    case("types", "param", R, lambda: t.filter(t.qty > ibis.param(ibis.dtype("int64")))),
    # Aggregation (more)
    case("aggregation", "count(col), min", V, lambda: t.aggregate(n=t.qty.count(), m=t.qty.min())),
    case("aggregation", "any, all", R, lambda: t.aggregate(a=t.flag.any(), b=t.flag.all())),
    case("aggregation", "arbitrary", R, lambda: t.aggregate(a=t.qty.arbitrary())),
    case(
        "aggregation",
        "argmin, argmax",
        R,
        lambda: t.aggregate(a=t.name.argmin(t.qty), b=t.name.argmax(t.qty)),
    ),
    case(
        "aggregation",
        "bit_and, bit_or, bit_xor",
        R,
        lambda: t.aggregate(a=t.qty.bit_and(), b=t.qty.bit_or(), c=t.qty.bit_xor()),
    ),
    case("aggregation", "first, last", R, lambda: t.aggregate(a=t.qty.first(), b=t.qty.last())),
    case("aggregation", "group_concat", R, lambda: t.aggregate(s=t.name.group_concat(","))),
    case("aggregation", "mode", R, lambda: t.aggregate(m=t.qty.mode())),
    case("aggregation", "table nunique", R, lambda: t.aggregate(n=t.nunique())),
    # Windows (more)
    case(
        "windows", "lead", V, lambda: t.mutate(p=t.qty.lead().over(group_by="name", order_by="ts"))
    ),
    case("windows", "percent_rank", R, lambda: t.mutate(r=ibis.percent_rank().over(order_by="ts"))),
    case("windows", "cume_dist", R, lambda: t.mutate(r=ibis.cume_dist().over(order_by="ts"))),
    case("windows", "nth", R, lambda: t.mutate(n=t.qty.nth(1).over(order_by="ts"))),
    case(
        "windows",
        "window_by tumble",
        R,
        lambda: t.window_by(t.ts).tumble(size=ibis.interval(minutes=5)).aggregate(n=t.qty.sum()),
    ),
    # Dates and times (more)
    case(
        "time",
        "day, hour, minute, ...",
        V,
        lambda: t.select(
            a=t.ts.quarter(),
            b=t.ts.month(),
            c=t.ts.day(),
            d=t.ts.day_of_year(),
            e=t.ts.week_of_year(),
            f=t.ts.hour(),
            g=t.ts.minute(),
            h=t.ts.second(),
        ),
    ),
    case(
        "time",
        "millisecond, microsecond",
        R,
        lambda: t.select(a=t.ts.millisecond(), b=t.ts.microsecond()),
    ),
    case("time", "epoch_seconds", R, lambda: t.select(x=t.ts.epoch_seconds())),
    case("time", "iso_year", R, lambda: t.select(x=t.ts.iso_year())),
    case(
        "time",
        "day_of_week",
        R,
        lambda: t.select(a=t.ts.day_of_week.index(), b=t.ts.day_of_week.full_name()),
    ),
    case("time", "timestamp - interval", V, lambda: t.select(x=t.ts - ibis.interval(hours=1))),
    case("time", "timestamp - timestamp", V, lambda: t.select(x=t.ts - t.ts)),
    case("time", "timestamp delta", R, lambda: t.select(x=t.ts.delta(t.ts, unit="hour"))),
    case("time", "timestamp bucket", R, lambda: t.select(x=t.ts.bucket(minutes=5))),
    case("time", "date + interval", R, lambda: t.select(x=t.ts.date() + ibis.interval(days=1))),
    case("time", "date - interval", R, lambda: t.select(x=t.ts.date() - ibis.interval(days=1))),
    case("time", "date - date", R, lambda: t.select(x=t.ts.date() - t.ts.date())),
    case("time", "date delta", R, lambda: t.select(x=t.ts.date().delta(t.ts.date(), unit="day"))),
    case("time", "date truncate", R, lambda: t.select(x=t.ts.date().truncate("M"))),
    case(
        "time",
        "interval arithmetic",
        R,
        lambda: t.select(
            a=t.ts + (ibis.interval(days=1) + ibis.interval(hours=1)),
            b=t.ts + (ibis.interval(days=1) - ibis.interval(hours=1)),
            c=t.ts + ibis.interval(days=1) * 2,
            d=t.ts + ibis.interval(days=4) // 2,  # pyrefly: ignore
        ),
    ),
    case("time", "as_interval", R, lambda: t.select(x=t.ts + t.qty.as_interval("D"))),
    case("time", "as_timestamp (unix)", R, lambda: t.select(x=t.qty.as_timestamp("s"))),
    case("time", "date(y, m, d)", R, lambda: t.select(x=ibis.date(t.qty, 1, 1))),
    case(
        "time", "timestamp(y, ..., s)", R, lambda: t.select(x=ibis.timestamp(t.qty, 1, 1, 0, 0, 0))
    ),
    case("time", "time(h, m, s)", R, lambda: t.select(x=ibis.time(t.qty, 0, 0))),
    case("time", "strftime", R, lambda: t.select(x=t.ts.strftime("%Y-%m"))),
    case("time", "string as_date", R, lambda: t.select(x=t.name.as_date("%Y-%m-%d"))),
    case("time", "string as_time", R, lambda: t.select(x=t.name.as_time("%H:%M"))),
    case("time", "string as_timestamp", R, lambda: t.select(x=t.name.as_timestamp("%Y-%m-%d"))),
    case("time", "time", R, lambda: t.select(x=t.ts.time())),
    case(
        "time",
        "time arithmetic",
        R,
        lambda: t.select(
            a=t.ts.time() + ibis.interval(hours=1),
            b=t.ts.time() - ibis.interval(hours=1),
            c=t.ts.time() - t.ts.time(),
            d=t.ts.time().delta(t.ts.time(), unit="hour"),
        ),
    ),
    case("time", "time truncate", R, lambda: t.select(x=t.ts.time().truncate("h"))),
    case(
        "time",
        "between times",
        R,
        lambda: t.filter(t.ts.time().between("01:00", "02:00")),
    ),
    case("time", "today, now", R, lambda: t.select(a=ibis.today(), b=ibis.now())),
    case(
        "time",
        "range of timestamps",
        R,
        lambda: t.select(
            x=ibis.range(t.ts, t.ts + ibis.interval(days=2), ibis.interval(days=1)).length()
        ),
    ),
    # Nested types
    case("nested", "collect", R, lambda: t.group_by("name").aggregate(xs=t.qty.collect())),
    case(
        "nested", "unnest", R, lambda: t.group_by("name").aggregate(xs=t.qty.collect()).unnest("xs")
    ),
    case("nested", "array", R, lambda: t.select(x=ibis.array([t.qty, t.id]))),
    case("nested", "range", R, lambda: t.select(x=ibis.range(0, t.qty, 1))),
    case(
        "nested",
        "array length, index, slice",
        R,
        lambda: n.select(a=n.xs.length(), b=n.xs[0], c=n.xs[1:2]),
    ),
    case(
        "nested",
        "array aggregates",
        R,
        lambda: n.select(
            a=n.xs.sums(), b=n.xs.mins(), c=n.xs.maxs(), d=n.xs.means(), e=n.xs.modes()
        ),
    ),
    case(
        "nested",
        "array predicates",
        R,
        lambda: n.select(
            a=n.xs.contains(1),
            b=n.xs.index(1),
            c=n.xs.map(lambda x: x > 1).anys(),
            d=n.xs.map(lambda x: x > 1).alls(),
        ),
    ),
    case(
        "nested",
        "array transforms",
        R,
        lambda: n.select(
            a=n.xs.map(lambda x: x + 1),
            b=n.xs.filter(lambda x: x > 1),
            c=n.xs.sort(),
            d=n.xs.unique(),
            e=n.xs.remove(1),
            f=ibis.array([n.xs]).flatten(),
            g=n.xs * 2,
        ),
    ),
    case(
        "nested",
        "array set operations",
        R,
        lambda: n.select(
            a=n.xs.concat(n.xs), b=n.xs.union(n.xs), c=n.xs.intersect(n.xs), d=n.xs.zip(n.xs)
        ),
    ),
    case("nested", "array unnest", R, lambda: n.select(x=n.xs.unnest())),
    case(
        "nested",
        "array join",
        R,
        lambda: n.select(x=n.xs.map(lambda x: x.cast("string")).join(",")),
    ),
    case("nested", "map", R, lambda: t.select(x=ibis.map(ibis.array(["a"]), ibis.array([t.qty])))),
    case(
        "nested",
        "map access",
        R,
        lambda: n.select(
            a=n.m.contains("a"),
            b=n.m.get("a"),
            c=n.m.keys(),
            d=n.m.values(),
            e=n.m.length(),
            f=n.m + n.m,
        ),
    ),
    case("nested", "struct", R, lambda: t.select(x=ibis.struct({"a": t.qty}))),
    case("nested", "struct field", R, lambda: n.select(x=n.s.a)),
    case("nested", "json get", R, lambda: n.select(x=n.j["a"])),
    case(
        "nested",
        "json unwrap",
        R,
        lambda: n.select(a=n.j.bool, b=n.j.float, c=n.j.int, d=n.j.str, e=n.j.array, f=n.j.map),
    ),
]


#: The Ibis operations no case probes, with the reason. Geospatial operations
#: (`ibis.expr.operations.geospatial`) are out of scope as a whole.
OUT_OF_SCOPE: dict[str, str] = {
    **dict.fromkeys(
        [
            "ScalarUDF",
            "AggUDF",
            "ElementWiseVectorizedUDF",
            "ReductionVectorizedUDF",
            "AnalyticVectorizedUDF",
        ],
        "user-defined functions run code the checker cannot see",
    ),
    **dict.fromkeys(
        ["SQLQueryResult", "SQLStringView"],
        "SQL text needs a connected backend and is not an Ibis expression",
    ),
    "DatabaseTable": "a connected backend's table; the producer reads it like an unbound one",
    "Alias": "Ibis's SQL compilers name values with it; table expressions never contain it",
}


def ibis_operations() -> set[str]:
    """The concrete Ibis operations: the leaves of `ibis.expr.operations`'
    class tree (the bases are abstract), without geospatial ones."""
    import inspect

    import ibis.expr.operations as ops

    nodes = {c for c in vars(ops).values() if inspect.isclass(c) and issubclass(c, ops.Node)}
    return {
        c.__name__
        for c in nodes
        if not any(d is not c and issubclass(d, c) for d in nodes)
        and not c.__module__.endswith("geospatial")
    }


def probed_operations(c: Case) -> set[str]:
    """The Ibis operations in the expression of `c` (none if Ibis fails)."""
    import ibis.expr.operations as ops

    try:
        expr = c.build()
    except Exception:  # noqa: BLE001 - an upstream case probes nothing
        return set()
    return {type(node).__name__ for node in expr.op().find(ops.Node)}


#: The engines besides DataFusion, which runs Ibis's own plans.
ENGINES = ("polars", "duckdb", "snowflake", "spark")

#: Verified cases an engine refuses (`Unsupported`), with a pattern of the
#: reason. These are what cannot be expressed there:
#:
#: * `lt` on strings is undefined in the model (`BinFn.apply` has no case for
#:   it, so it is NULL, where SQL compares), so no engine may run it.
#: * The elementary functions of doubles (`LN`, `SIN`, …) round as C's `libm`
#:   does; Snowflake's and Spark's (Java's `StrictMath`) may differ in the
#:   last bit. Square roots are correctly rounded everywhere.
#: * Snowflake and Spark tables have no row order, which FETCH and a stable
#:   sort's or a window's ties follow. Sorts and windows run with
#:   `tie_free=True`. A `SUM` or `AVG` of doubles adds in that order too
#:   (rounding depends on it).
NO_ROW_ORDER = {"snowflake": "no row order", "spark": "no row order"}
LIBM = {"snowflake": "libm", "spark": "StrictMath"}
REFUSED: dict[str, dict[str, str]] = {
    "count, max, mean": NO_ROW_ORDER,
    "non-equi join": {
        "polars": "lt of String",
        "duckdb": "ordering comparisons of str values",
        "snowflake": "ordering comparisons of str values",
        "spark": "ordering comparisons of str values",
    },
    "order_by": NO_ROW_ORDER,
    "limit": NO_ROW_ORDER,
    "limit with offset": NO_ROW_ORDER,
    "order_by + limit": NO_ROW_ORDER,
    "row_number": NO_ROW_ORDER,
    "lag": NO_ROW_ORDER,
    "lead": NO_ROW_ORDER,
    "timestamp - timestamp": {"snowflake": "no interval values"},
    "sqrt": {"snowflake": "libm"},
    "exp": LIBM,
    "ln, log10, log2": LIBM,
    "log(base)": LIBM,
    "trigonometry": LIBM,
    "pi, e": LIBM,
    "shifts": {"snowflake": "shifts by 64 or more bits"},
}
#: Of those, the cases Snowflake and Spark run when the caller promises no ties.
TIE_FREE = {"order_by", "row_number", "lag", "lead"}


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
            tables = {t.get_name(): t.schema().to_pyarrow().empty_table() for t in (T, U)}
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
    # An operation in a verified case is translated: any other fails the case.
    in_scope = ibis_operations() - set(OUT_OF_SCOPE)
    translated = in_scope & set().union(
        *(probed_operations(r.case) for r in rs if r.status == "verified")
    )
    lines = [
        f"{n} of {len(rs)} probes reach the checker; they use {len(translated)} of the "
        f"{len(in_scope)} Ibis operations (`ibis.expr.operations`, without geospatial "
        "ones and the few `OUT_OF_SCOPE` lists). "
        "✓ verified, ✗ rejected by the checker, – fails in Ibis or DataFusion; "
        "*inc.* marks incremental maintenance.",
        "",
        "| Area | Verified | Probes |",
        "|---|---|---|",
    ]
    for area in dict.fromkeys(r.case.area for r in rs):
        here = [r for r in rs if r.case.area == area]
        ops = [
            f"{SYMBOL[r.status]} {r.case.label}" + (" *inc.*" if r.incremental else "")
            for r in here
        ]
        ok = sum(r.status == "verified" for r in here)
        lines.append(f"| {area} | {ok} / {len(here)} | {' · '.join(ops)} |")
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
