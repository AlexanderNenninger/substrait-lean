"""SQL generation: every golden fixture and every delta plan runs on DataFusion
and on DuckDB (through `sverify.sql.to_sql`) with the same result, which is
also Lean's (`Rel.eval`); the semantic traps between engines are pinned down;
and the generated SQL of a few fixtures is kept as snapshots.

Results compare as bags, except where FETCH or a window makes order part of
the meaning: there DuckDB must give Lean's rows in Lean's order (DataFusion
promises no order, so it still compares as a bag).
"""

import copy
import datetime as dt
import json
import math
import os
import re
import subprocess
from dataclasses import dataclass
from decimal import Decimal
from pathlib import Path

import duckdb
import ibis
import pyarrow as pa
import pytest
from hypothesis import HealthCheck, given, settings
from hypothesis import strategies as st

import sverify as sv
from sverify.engine import connect, put_table, run_substrait_json, substrait_json
from sverify.examples import PIPELINES
from sverify.executors import DuckDBExecutor
from sverify.incremental import arrow_rows, checker_path, delta_plans, read_tables
from sverify.sql import Unsupported, parse_plan, to_sql
from sverify.sql.core import Fetch, kinds, order_matters
from sverify.sql.duckdb import DUCKDB, DuckDBDialect
from sverify.testing import EPOCH, canonical, duckdb_rows, inline_tables, lean_rows, parse_rows

ROOT = Path(__file__).resolve().parents[2]
FIXTURES = ROOT / "tests" / "fixtures"
SNAPSHOTS = Path(__file__).parent / "sql_snapshots"

#: Fixtures the checker accepts (the others are refused by `to_sql` too).
ACCEPTED = sorted(
    f.stem
    for f in FIXTURES.glob("*.json")
    if f.with_suffix(".expected").read_text().rstrip().endswith("[exit 0]")
)
REFUSED = sorted(f.stem for f in FIXTURES.glob("*.json") if f.stem not in ACCEPTED)


def fixture(name: str) -> dict:
    return json.loads((FIXTURES / f"{name}.json").read_text())


def golden(name: str) -> str:
    return (FIXTURES / f"{name}.expected").read_text()


def schemas(plan: dict) -> dict[str, dict]:
    """Named tables of a plan with their `baseSchema`s."""
    found: dict[str, dict] = {}

    def walk(node: object) -> None:
        if isinstance(node, dict):
            if "namedTable" in node:
                found[".".join(node["namedTable"]["names"])] = node["baseSchema"]
            for v in node.values():
                walk(v)
        elif isinstance(node, list):
            for v in node:
                walk(v)

    walk(plan)
    return found


T0 = dt.datetime(2024, 5, 1, 7, 0)
NEG_NAN = math.copysign(math.nan, -1.0)
DOUBLES = [None, 0.0, -0.0, 0.5, 1.5, -9999.0, math.nan, NEG_NAN, math.inf, -math.inf]
ARROW = {
    "i64": pa.int64(),
    "string": pa.string(),
    "fp64": pa.float64(),
    "precisionTimestamp": pa.timestamp("us"),
    "bool": pa.bool_(),
}


def values_of(ty: str) -> st.SearchStrategy:
    return {
        "i64": st.one_of(st.none(), st.integers(-3, 3)),
        "string": st.sampled_from(["ada", "bob", "", None]),
        "fp64": st.sampled_from(DOUBLES),
        "precisionTimestamp": st.sampled_from(
            [None] + [T0 + dt.timedelta(minutes=k) for k in range(4)]
        ),
        "bool": st.sampled_from([True, False, None]),
    }[ty]


def type_names(schema: dict) -> list[str]:
    return [next(iter(t)) for t in schema["struct"]["types"]]


@st.composite
def table_for(draw, schema: dict, weight: bool = False) -> pa.Table:
    """Random rows for a `baseSchema`. Timestamps are distinct within a table
    (all window sorts in the fixtures are on them), so no two rows tie."""
    types = type_names(schema)
    rows = draw(
        st.lists(
            st.tuples(*(values_of(t) for t in types)),
            max_size=6,
            unique_by=tuple(
                (lambda r, i=i: r[i]) for i, t in enumerate(types) if t == "precisionTimestamp"
            )
            or None,
        )
    )
    names = list(schema["names"])
    fields = [pa.field(n, ARROW[t]) for n, t in zip(names, types, strict=True)]
    if weight:
        # A change table: the base columns and a weight (`__weight` is part of
        # the delta plan's schema already).
        rows = [(*r[:-1], draw(st.sampled_from([1, -1]))) for r in rows]
    return pa.Table.from_pylist(
        [dict(zip(names, r, strict=True)) for r in rows], schema=pa.schema(fields)
    )


def written(plan_json: str) -> str:
    """The plan as `substrait-check --write` writes it back out, with FETCH in
    the current encoding (Lean writes the deprecated `offset`/`count`, which
    DataFusion's protobuf no longer has; the parser reads both alike)."""
    out = subprocess.run(
        [str(checker_path()), "--write", "/dev/stdin"],
        input=plan_json,
        capture_output=True,
        text=True,
        check=True,
    ).stdout

    def walk(node: object) -> None:
        if isinstance(node, dict):
            fetch = node.get("fetch")
            if isinstance(fetch, dict):
                for key in ("offset", "count"):
                    if key in fetch:
                        fetch[key + "Expr"] = {"literal": {"i64": fetch.pop(key)}}
            for v in node.values():
                walk(v)
        elif isinstance(node, list):
            for v in node:
                walk(v)

    plan = json.loads(out)
    walk(plan)
    return json.dumps(plan)


def integral(v: object) -> object:
    # DataFusion's consumer types `ROW_NUMBER() - 1` as a DECIMAL.
    return int(v) if isinstance(v, Decimal) and v == int(v) else v


def both(plan_json: str, tables: dict[str, pa.Table]) -> tuple[list[tuple], list[tuple]]:
    """The plan's rows on DataFusion and on DuckDB. DataFusion runs Lean's
    rewrite of the plan: some fixtures are hand-written in encodings its
    protobuf parser no longer reads."""
    con = connect()
    for name, t in tables.items():
        put_table(con, name, t)
    df = [tuple(map(integral, r)) for r in arrow_rows(run_substrait_json(con, written(plan_json)))]
    return df, duckdb_rows(plan_json, tables)


def lean_printable(plan: dict) -> bool:
    """Can Lean's output be compared value by value (no doubles in or out)?"""
    tables_ok = all("fp64" not in type_names(s) for s in schemas(plan).values())
    return tables_ok and "float" not in kinds(parse_plan(plan).root)


def from_lean(plan: dict, rows: list[tuple]) -> list[tuple]:
    """Lean's integers as the values they stand for (timestamps)."""
    ks = kinds(parse_plan(plan).root)
    us = dt.timedelta(microseconds=1)
    return [
        tuple(
            EPOCH + v * us if k == "time" and v is not None else v
            for v, k in zip(r, ks, strict=True)
        )
        for r in rows
    ]


def lean_on(plan: dict, tables: dict[str, pa.Table]) -> list[tuple]:
    rows = {name: arrow_rows(t) for name, t in tables.items()}
    inlined = inline_tables(copy.deepcopy(plan), rows)
    return from_lean(plan, lean_rows(json.dumps(inlined)))


def has_fetch(r: object) -> bool:
    if isinstance(r, Fetch):
        return True
    return any(has_fetch(getattr(r, k)) for k in ("input", "left", "right") if hasattr(r, k))


def agree(plan: dict, df: list[tuple] | None, duck: list[tuple], lean: list[tuple] | None) -> None:
    """DuckDB agrees with DataFusion as bags, and with Lean (in Lean's order
    where order matters). FETCH takes whichever rows come first, and
    DataFusion's order is not Lean's, so there only Lean is the reference."""
    if df is not None and not has_fetch(parse_plan(plan).root):
        assert canonical(duck) == canonical(df)
    if lean is not None:
        if order_matters(parse_plan(plan).root):
            assert duck == lean
        else:
            assert canonical(duck) == canonical(lean)


# --------------------------------------------------------------------------
# Golden fixtures


def test_fixture_lists_are_complete():
    assert {"filter_project", "virtual_left_join", "union_fetch", "df_window"} <= set(ACCEPTED)
    assert set(REFUSED) == {"bad_field_ref", "df_aggregate", "unsupported_aggregate"}


@pytest.mark.parametrize("name", REFUSED)
def test_refused_fixtures_are_refused(name):
    with pytest.raises(Unsupported):
        to_sql(fixture(name), DUCKDB)


#: DataFusion cannot read the plan, nor Lean's rewrite of it (which types
#: virtual-table columns as placeholder `i64`s).
DATAFUSION_CANNOT_READ = {"virtual_left_join"}


@pytest.mark.parametrize("name", [n for n in ACCEPTED if not schemas(fixture(n))])
def test_virtual_fixtures_match_the_golden_rows(name):
    plan = fixture(name)
    if name in DATAFUSION_CANNOT_READ:
        df, duck = None, duckdb_rows(json.dumps(plan))
    else:
        df, duck = both(json.dumps(plan), {})
    agree(plan, df, duck, parse_rows(golden(name)))


@pytest.mark.parametrize("name", [n for n in ACCEPTED if schemas(fixture(n))])
@settings(max_examples=30, deadline=None, suppress_health_check=[HealthCheck.too_slow])
@given(data=st.data())
def test_fixtures_agree_on_random_tables(name, data):
    plan = fixture(name)
    tables = {t: data.draw(table_for(s)) for t, s in schemas(plan).items()}
    df, duck = both(json.dumps(plan), tables)
    agree(plan, df, duck, lean_on(plan, tables) if lean_printable(plan) else None)


@pytest.mark.parametrize("name", ACCEPTED)
def test_lean_written_fixtures_give_the_same_sql_results(name):
    """The plan `substrait-check --write` makes of a fixture means the same."""
    plan = fixture(name)
    tables = {
        t: pa.Table.from_pylist(
            [],
            schema=pa.schema(
                [pa.field(n, ARROW[ty]) for n, ty in zip(s["names"], type_names(s), strict=True)]
            ),
        )
        for t, s in schemas(plan).items()
    }
    assert duckdb_rows(written(json.dumps(plan)), tables) == duckdb_rows(json.dumps(plan), tables)


# --------------------------------------------------------------------------
# Delta plans


def incremental_plans() -> dict[str, str]:
    """Every plan the suite maintains incrementally: the incremental fixtures
    and the example pipelines."""
    plans = {n: json.dumps(fixture(n)) for n in ACCEPTED if "incremental: yes" in golden(n)}
    con = connect()
    sv.examples.create_tables(con)
    for name, expr in PIPELINES.items():
        plans[f"pipeline_{name}"] = substrait_json(con, ibis.to_sql(expr, dialect="datafusion"))
    return plans


INCREMENTAL = incremental_plans()


@pytest.mark.parametrize("name", sorted(INCREMENTAL))
@settings(max_examples=20, deadline=None, suppress_health_check=[HealthCheck.too_slow])
@given(data=st.data())
def test_delta_plans_agree(name, data):
    plan_json = INCREMENTAL[name]
    deltas = delta_plans(plan_json)
    assert deltas
    base = schemas(json.loads(plan_json))
    tables = {t: data.draw(table_for(s)) for t, s in base.items()}
    for d in deltas:
        for t, s in schemas(json.loads(d)).items():
            if t.endswith("$delta") and t not in tables:
                tables[t] = data.draw(table_for(s, weight=True))
    for d in deltas:
        plan = json.loads(d)
        needed = {t: tables[t] for t in read_tables(plan)}
        df, duck = both(d, needed)
        agree(plan, df, duck, lean_on(plan, needed) if lean_printable(plan) else None)


# --------------------------------------------------------------------------
# Semantic traps


def plan_of(sql: str, tables: dict[str, pa.Table]) -> str:
    con = connect()
    for name, t in tables.items():
        put_table(con, name, t)
    return substrait_json(con, sql)


def ints(**cols: list) -> pa.Table:
    return pa.table({k: pa.array(v, pa.int64()) for k, v in cols.items()})


def check_three_ways(sql: str, tables: dict[str, pa.Table]) -> list[tuple]:
    """DuckDB, DataFusion and Lean agree on `sql`; returns DuckDB's rows."""
    plan_json = plan_of(sql, tables)
    plan = json.loads(plan_json)
    df, duck = both(plan_json, tables)
    agree(plan, df, duck, lean_on(plan, tables))
    return duck


def test_null_join_keys_never_match():
    a = ints(k=[1, None, 2], x=[10, 20, 30])
    b = ints(k=[None, 1, None], y=[100, 200, 300])
    tables = {"a": a, "b": b}
    inner = check_three_ways("SELECT a.x, b.y FROM a JOIN b ON a.k = b.k", tables)
    assert inner == [(10, 200)]
    left = check_three_ways("SELECT a.x, b.y FROM a LEFT JOIN b ON a.k = b.k", tables)
    assert canonical(left) == canonical([(10, 200), (20, None), (30, None)])
    sql = to_sql(json.loads(plan_of("SELECT a.x FROM a JOIN b ON a.k = b.k", tables)), DUCKDB)
    assert "IS NOT DISTINCT FROM" not in sql


def test_three_valued_logic():
    vals = [True, False, None]
    r = pa.table(
        {
            "a": pa.array([a for a in vals for _ in vals], pa.bool_()),
            "b": pa.array([b for _ in vals for b in vals], pa.bool_()),
        }
    )
    rows = check_three_ways("SELECT a, b, a AND b AS x, a OR b AS y, NOT a AS z FROM r", {"r": r})
    for a, b, x, y, z in rows:
        assert x == (False if False in (a, b) else None if None in (a, b) else True)
        assert y == (True if True in (a, b) else None if None in (a, b) else False)
        assert z == (None if a is None else not a)
    # A filter keeps only TRUE rows, not NULL ones.
    kept = check_three_ways("SELECT a, b FROM r WHERE a OR b", {"r": r})
    assert all(True in row for row in kept) and len(kept) == 5


@pytest.mark.parametrize(
    "order",
    [
        "t ASC NULLS FIRST",
        "t ASC NULLS LAST",
        "t DESC NULLS FIRST",
        "t DESC NULLS LAST",
        "t",
        "t DESC",
    ],
)
def test_null_ordering_in_windows(order):
    r = ints(s=[1, 1, 1, 2, 2], t=[3, None, 1, None, 5])
    w = f"OVER (PARTITION BY s ORDER BY {order})"
    sql = f"SELECT s, t, ROW_NUMBER() {w} AS n, LAG(t) {w} AS p FROM r"
    check_three_ways(sql, {"r": r})
    text = to_sql(json.loads(plan_of(sql, {"r": r})), DUCKDB)
    # Every sort key says where NULLs go.
    assert not re.search(r"\b(ASC|DESC)\b(?! NULLS (FIRST|LAST))", text)


def test_integer_division_is_refused():
    r = ints(a=[7, -7], b=[2, 2])
    with pytest.raises(Unsupported, match="divide"):
        to_sql(json.loads(plan_of("SELECT a / b AS q FROM r", {"r": r})), DUCKDB)


def test_double_division_follows_ieee():
    r = ints(a=[7, -7, 0, 1], b=[2, 0, 0, 3])
    sql = "SELECT CAST(a AS DOUBLE) / CAST(b AS DOUBLE) AS q FROM r"
    plan_json = plan_of(sql, {"r": r})
    df, duck = both(plan_json, {"r": r})
    assert canonical(df) == canonical(duck)
    assert [repr(q) for (q,) in duck] == ["3.5", "-inf", "nan", repr(1 / 3)]
    assert "CAST(" in to_sql(json.loads(plan_json), DUCKDB)


@pytest.mark.parametrize(
    ("sql", "rows"),
    [
        ("SELECT a + b AS x FROM r", ([2**63 - 1], [1])),
        ("SELECT a - b AS x FROM r", ([-(2**63)], [1])),
        ("SELECT a * b AS x FROM r", ([2**62], [2])),
        ("SELECT -a AS x FROM r", ([-(2**63)], [0])),
    ],
)
def test_integer_overflow_raises(sql, rows):
    """DataFusion wraps around; Lean's integers are unbounded, so a wrapped
    result would be wrong. DuckDB's SQL raises instead."""
    r = ints(a=rows[0], b=rows[1])
    plan_json = plan_of(sql, {"r": r})
    with pytest.raises((duckdb.OutOfRangeException, duckdb.ConversionException)):
        duckdb_rows(plan_json, {"r": r})


def test_narrow_integers_are_widened_before_arithmetic():
    """An `INTEGER` column sums past 2^31 like Lean's integers do."""
    r = pa.table({"a": pa.array([2**31 - 1], pa.int32())})
    plan_json = plan_of("SELECT CAST(a AS BIGINT) + 1 AS x FROM r", {"r": r})
    assert duckdb_rows(plan_json, {"r": r}) == [(2**31,)]


def doubles_table() -> pa.Table:
    pairs = [(v, w) for v in DOUBLES for w in DOUBLES]
    return pa.table(
        {
            "v": pa.array([v for v, _ in pairs], pa.float64()),
            "w": pa.array([w for _, w in pairs], pa.float64()),
        }
    )


@pytest.mark.parametrize(
    "sql",
    [
        "SELECT v, w, v = w AS eq, v < w AS lt, v <= w AS le, v <> w AS ne FROM f",
        "SELECT v, w FROM f WHERE v > w",
        "SELECT v FROM f WHERE v > 0",
        "SELECT v, isnan(v) AS n, -v AS m, ABS(v) AS a FROM f",
        "SELECT v, w, GREATEST(v, w) AS g, LEAST(v, w) AS l FROM f",
        "SELECT v, w FROM f WHERE v IN (0.0, 1.5, w)",
    ],
)
def test_doubles_compare_by_the_total_order(sql):
    """-NaN < -inf < … < -0.0 < +0.0 < … < inf < NaN, NaN = NaN: DuckDB's own
    `=` says -0.0 = +0.0, so the SQL must not use it unguarded."""
    f = doubles_table()
    df, duck = both(plan_of(sql, {"f": f}), {"f": f})
    assert canonical(duck) == canonical(df)


def test_double_window_order_and_partitions():
    values = [v for v in DOUBLES if v is not None] + [None]
    f = pa.table({"v": pa.array(values, pa.float64()), "w": pa.array(values[::-1], pa.float64())})
    for sql in [
        "SELECT v, ROW_NUMBER() OVER (ORDER BY v ASC NULLS FIRST) AS n FROM f",
        "SELECT v, ROW_NUMBER() OVER (ORDER BY v DESC NULLS LAST) AS n FROM f",
        "SELECT v, w, LAG(w) OVER (ORDER BY v DESC NULLS FIRST) AS n FROM f",
    ]:
        df, duck = both(plan_of(sql, {"f": f}), {"f": f})
        assert canonical(duck) == canonical(df), sql


def test_signed_zeros_partition_apart():
    f = pa.table(
        {
            "v": pa.array([0.0, -0.0, 0.0, NEG_NAN, math.nan], pa.float64()),
            "t": pa.array([1, 2, 3, 4, 5], pa.int64()),
        }
    )
    sql = "SELECT v, t, ROW_NUMBER() OVER (PARTITION BY v ORDER BY t) AS n FROM f"
    df, duck = both(plan_of(sql, {"f": f}), {"f": f})
    assert canonical(duck) == canonical(df)
    assert sorted(n for _, t, n in duck) == [1, 1, 1, 1, 2]


def test_fetch_takes_lean_rows_after_a_union_and_join():
    a = ints(x=[3, 1, 2])
    b = ints(y=[20, 10])
    sql = (
        "SELECT x, y FROM (SELECT x FROM a UNION ALL SELECT x + 10 FROM a) CROSS JOIN b"
        " LIMIT 4 OFFSET 1"
    )
    plan_json = plan_of(sql, {"a": a, "b": b})
    plan = json.loads(plan_json)
    lean = lean_on(plan, {"a": a, "b": b})
    assert duckdb_rows(plan_json, {"a": a, "b": b}) == lean
    assert len(lean) == 4


@dataclass(frozen=True)
class NoScanOrder(DuckDBDialect):
    """DuckDB without `rowid`, like an engine with no stable scan order."""

    def row_ordinal(self) -> str:
        raise Unsupported("no scan order")


def test_tie_free_windows_need_no_scan_order():
    r = ints(s=[1, 1, 2, None], t=[3, 1, 2, 4], v=[10, 20, 30, 40])
    sql = "SELECT s, t, LAG(v) OVER (PARTITION BY s ORDER BY t DESC NULLS LAST) AS p FROM r"
    plan = json.loads(plan_of(sql, {"r": r}))
    with pytest.raises(Unsupported, match="no scan order"):
        to_sql(plan, NoScanOrder("no-scan-order"))
    text = to_sql(plan, NoScanOrder("no-scan-order"), tie_free=True)
    db = duckdb.connect()
    db.register("r", r)
    got = [tuple(x) for x in db.sql(text).fetchall()]
    assert got == duckdb_rows(json.dumps(plan), {"r": r}) == lean_on(plan, {"r": r})
    # FETCH still needs the scan order.
    fetch = json.loads(plan_of("SELECT s FROM r LIMIT 2", {"r": r}))
    with pytest.raises(Unsupported, match="no scan order"):
        to_sql(fetch, NoScanOrder("no-scan-order"), tie_free=True)


def test_unsupported_constructs_raise():
    r = ints(a=[1], b=[2])
    s = pa.table({"name": ["a"]})
    for sql, tables, match in [
        ("SELECT a, SUM(b) AS s FROM r GROUP BY a", {"r": r}, "unsupported relation"),
        ("SELECT a FROM r ORDER BY a", {"r": r}, "unsupported relation"),
        ("SELECT name FROM s WHERE name < 'b'", {"s": s}, "ordering comparisons of str"),
        ("SELECT a % b AS m FROM r", {"r": r}, "unsupported function"),
    ]:
        with pytest.raises(Unsupported, match=match):
            to_sql(json.loads(plan_of(sql, tables)), DUCKDB)


# --------------------------------------------------------------------------
# Engines behind the incremental-view and contract interfaces


def test_incremental_view_on_duckdb():
    con = sv.connect()
    sv.examples.create_tables(con, [(1, "ada", 30), (2, "bob", 5)], [("ada", "Paris")])
    view = sv.IncrementalView(con, PIPELINES["inner_join"], "v", engine="duckdb")
    assert view.rows() == view.recompute() == [(1, "Paris")]
    view.apply({"orders": sv.Changes(inserts=[(3, "ada", 1)], deletes=[(1, "ada", 30)])})
    assert view.rows() == view.recompute() == [(3, "Paris")]
    # The base table changed in `con` too.
    assert sorted(sv.table_rows(con, "orders")) == [(2, "bob", 5), (3, "ada", 1)]


def test_contract_checks_on_duckdb():
    from ibis import _

    @sv.transform(
        requires={"orders": [_.amount >= 0]},
        ensures=[_.amount < 100],
        on_unproved="runtime",
        engine="duckdb",
    )
    def passthrough(orders):
        return orders.select(orders.amount)

    con = sv.connect()
    sv.examples.create_tables(con, [(1, "ada", 30)])
    passthrough(con.table("orders"))
    sv.examples.create_tables(con, [(1, "ada", 300)])
    with pytest.raises(sv.PostconditionError):
        passthrough(con.table("orders"))
    sv.examples.create_tables(con, [(1, "ada", -1)])
    with pytest.raises(sv.PreconditionError):
        passthrough(con.table("orders"))


def test_engine_executes_on_its_own_copy():
    ex = DuckDBExecutor()
    ex.put("t", ints(x=[2, 1]))
    assert arrow_rows(ex.get("t")) == [(2,), (1,)]
    ex.drop("t")
    with pytest.raises(duckdb.CatalogException):
        ex.get("t")


# --------------------------------------------------------------------------
# Snapshots of the generated SQL

SNAPSHOT_FIXTURES = [
    "filter_project",
    "virtual_left_join",
    "union_fetch",
    "df_window",
    "df_float_timestamp",
]


@pytest.mark.parametrize("name", SNAPSHOT_FIXTURES)
def test_sql_snapshot(name):
    """Set SVERIFY_UPDATE_SNAPSHOTS=1 to re-record."""
    sql = to_sql(fixture(name), DUCKDB) + "\n"
    path = SNAPSHOTS / f"{name}.duckdb.sql"
    if os.environ.get("SVERIFY_UPDATE_SNAPSHOTS"):
        SNAPSHOTS.mkdir(exist_ok=True)
        path.write_text(sql)
    assert path.read_text() == sql
