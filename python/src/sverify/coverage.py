"""Which parts of the Ibis API reach the Lean checker.

Each case is an Ibis expression over two unbound tables. It is compiled the way
`sverify` compiles everything (Ibis → SQL → DataFusion → Substrait) and handed
to `substrait-check`:

* `verified`: parsed into the Lean model and well-formed, so contracts and
  (where `incremental`) incremental views apply;
* `rejected`: the checker refuses the plan (an operation outside the model);
* `upstream`: Ibis or DataFusion fails before a plan exists.

`tests/test_coverage.py` pins every case to its `expected` status, so a change
in coverage is a deliberate edit here. Regenerate the README table with

    uv run python -m sverify.coverage --write-readme
"""

from __future__ import annotations

import re
import subprocess
import sys
import tempfile
from collections.abc import Callable
from dataclasses import dataclass
from pathlib import Path
from typing import Literal

import ibis
import ibis.expr.types as ir
from ibis import _

from sverify.engine import Backend, connect, create_table, substrait_json, to_sql
from sverify.incremental import checker_path

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
t, u = T, U


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
    case("rows", "order_by", R, lambda: t.order_by("qty")),
    case("rows", "limit", V, lambda: t.limit(3)),
    case("rows", "limit with offset", V, lambda: t.limit(3, offset=1)),
    case("rows", "order_by + limit", R, lambda: t.order_by(ibis.desc("qty")).limit(3)),
    case("rows", "sample", R, lambda: t.sample(0.5)),
    # Joins and set operations
    case("joins", "inner join", V, lambda: t.join(u, "name")),
    case("joins", "non-equi join", V, lambda: t.join(u, t.name < u.name)),
    case("joins", "cross join", V, lambda: t.cross_join(u)),
    case("joins", "left join", V, lambda: t.left_join(u, "name")),
    case("joins", "right join", V, lambda: t.right_join(u, "name")),
    case("joins", "outer join", R, lambda: t.outer_join(u, "name")),
    case("joins", "semi join", R, lambda: t.semi_join(u, "name")),
    case("joins", "anti join", R, lambda: t.anti_join(u, "name")),
    case("joins", "isin subquery", R, lambda: t.filter(t.name.isin(u.name))),
    case("joins", "union all", V, lambda: t.select("name").union(u.select("name"))),
    case(
        "joins",
        "union distinct",
        R,
        lambda: t.select("name").union(u.select("name"), distinct=True),
    ),
    case("joins", "intersect", R, lambda: t.select("name").intersect(u.select("name"))),
    case("joins", "difference", R, lambda: t.select("name").difference(u.select("name"))),
    # Aggregation
    case("aggregation", "count()", R, lambda: t.aggregate(n=t.count())),
    case("aggregation", "group_by sum", R, lambda: t.group_by("name").aggregate(s=t.qty.sum())),
    case(
        "aggregation",
        "count, max, mean",
        R,
        lambda: t.group_by("name").aggregate(n=t.count(), m=t.qty.max(), a=t.amount.mean()),
    ),
    case("aggregation", "nunique", R, lambda: t.group_by("name").aggregate(n=t.id.nunique())),
    case(
        "aggregation",
        "sum(where=)",
        R,
        lambda: t.group_by("name").aggregate(s=t.qty.sum(where=t.flag)),
    ),
    case(
        "aggregation",
        "having",
        R,
        # Ibis types `having` too narrowly; it accepts deferred conditions.
        lambda: t.group_by("name").having(_.count() > 1).aggregate(n=t.count()),  # pyrefly: ignore
    ),
    case("aggregation", "value_counts", R, lambda: t.name.value_counts()),
    case("aggregation", "distinct", R, lambda: t.select("name").distinct()),
    case("aggregation", "distinct(on=)", R, lambda: t.distinct(on="name", keep="first")),
    case("aggregation", "std", R, lambda: t.aggregate(s=t.amount.std())),
    case("aggregation", "collect", R, lambda: t.group_by("name").aggregate(xs=t.qty.collect())),
    case("aggregation", "scalar subquery", X, lambda: t.filter(t.qty > t.qty.mean())),
    case(
        "aggregation",
        "unnest",
        X,
        lambda: t.group_by("name").aggregate(xs=t.qty.collect()).unnest("xs"),
    ),
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
        X,
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
    case("strings", "upper", R, lambda: t.select(x=t.name.upper())),
    case("strings", "length", R, lambda: t.select(x=t.name.length())),
    case("strings", "concat", R, lambda: t.select(x=t.name + "!")),
    case("strings", "substr", R, lambda: t.select(x=t.name.substr(0, 2))),
    case("strings", "contains", R, lambda: t.filter(t.name.contains("a"))),
    case("strings", "startswith", R, lambda: t.filter(t.name.startswith("a"))),
    case("strings", "like", R, lambda: t.filter(t.name.like("a%"))),
    case("strings", "re_search", R, lambda: t.filter(t.name.re_search("^a"))),
    case("strings", "strip", R, lambda: t.select(x=t.name.strip())),
    # Dates and times
    case("time", "timestamp + interval", V, lambda: t.select(x=t.ts + ibis.interval(hours=1))),
    case(
        "time",
        "compare with literal",
        V,
        lambda: t.filter(t.ts > ibis.timestamp("2024-01-01 00:00:00")),
    ),
    case("time", "year", R, lambda: t.select(x=t.ts.year())),
    case("time", "date", R, lambda: t.select(x=t.ts.date())),
    case("time", "truncate", R, lambda: t.select(x=t.ts.truncate("h"))),
]


@dataclass(frozen=True)
class Result:
    case: Case
    status: Status
    incremental: bool
    detail: str


def setup() -> Backend:
    con = connect()
    for table in (T, U):
        create_table(con, table.get_name(), table.schema())
    return con


def check(con: Backend, c: Case) -> Result:
    try:
        plan = substrait_json(con, to_sql(c.build()))
    except Exception as e:  # noqa: BLE001 - any producer failure counts
        return Result(c, "upstream", False, str(e).splitlines()[0])
    with tempfile.NamedTemporaryFile("w", suffix=".json") as f:
        f.write(plan)
        f.flush()
        proc = subprocess.run([str(checker_path()), f.name], capture_output=True, text=True)
    out = proc.stdout + proc.stderr
    if proc.returncode == 0:
        return Result(c, "verified", "incremental: yes" in out, "")
    lines = [ln for ln in out.splitlines() if ln.startswith(("error:", "well-formed: no"))]
    return Result(c, "rejected", False, (lines or [out.strip()])[-1])


def results() -> list[Result]:
    con = setup()
    return [check(con, c) for c in CASES]


SYMBOL = {"verified": "✓", "rejected": "✗", "upstream": "–"}
START, END = "<!-- coverage:start -->", "<!-- coverage:end -->"


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
