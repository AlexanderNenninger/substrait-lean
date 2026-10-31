"""Polars against DataFusion and against Lean's `Rel.eval`.

Polars runs the plan Lean writes back out (`written_plan`, and the delta plans
of `--delta`). Results must agree with DataFusion as bags and with Lean
exactly, row order included: the translator keeps `Rel.eval`'s list order,
which is what makes `FetchRel` and windows meaningful.
"""

import datetime as dt
import json
import math
from decimal import Decimal
from pathlib import Path

import ibis
import pyarrow as pa
import pytest
from hypothesis import HealthCheck, given, settings
from hypothesis import strategies as st

import sverify as sv
from sverify import polars_engine
from sverify.engine import (
    connect,
    create_table,
    put_table,
    read_tables,
    run_checker,
    run_plan,
    run_sql,
    run_substrait_json,
    substrait_json,
    to_sql,
    written_plan,
)
from sverify.examples import PIPELINES, create_tables
from sverify.incremental import WEIGHT
from sverify.testing import canonical, inline_tables, lean_rows, lean_values
from test_numeric import DOUBLES, INT_QUERIES, MIN, F
from test_numeric import PIPELINES as NUMERIC_PIPELINES
from test_numeric import R as NUMERIC_R
from test_numeric import values as numeric_values
from test_rewrites import QUERIES as REWRITE_QUERIES
from test_rewrites import R, S
from test_windows import QUERIES as WINDOW_QUERIES
from test_windows import SCHEMA as WINDOW_SCHEMA

pytestmark = pytest.mark.backend("polars")

#: The repository's golden fixtures; absent when the tests run against a wheel.
FIXTURES = sorted((Path(__file__).parents[2] / "tests" / "fixtures").glob("*.json"))
SETTINGS = settings(
    max_examples=25,
    deadline=None,
    suppress_health_check=[HealthCheck.function_scoped_fixture, HealthCheck.too_slow],
)


def rows_of(table: pa.Table) -> list[tuple]:
    return [tuple(r.values()) for r in table.to_pylist()]


def datafusion_rows(table: pa.Table) -> list[tuple]:
    """DataFusion types `ROW_NUMBER() - 1` (unsigned minus signed) as a
    decimal; the model has one integer type."""
    return [tuple(int(v) if isinstance(v, Decimal) else v for v in r) for r in rows_of(table)]


def on_both(con, plan: str) -> tuple[list[tuple], list[tuple]]:
    df = datafusion_rows(run_plan(con, plan, "datafusion"))
    return df, rows_of(run_plan(con, plan, "polars"))


# --- Golden fixtures -------------------------------------------------------


def expected(fixture: Path) -> tuple[int, list[str]]:
    """Exit code and rendered rows of a golden `.expected` file."""
    lines = fixture.with_suffix(".expected").read_text().splitlines()
    code = int(lines[-1].removeprefix("[exit ").removesuffix("]"))
    start = next((i for i, x in enumerate(lines) if x.startswith("rows (")), None)
    rows = [] if start is None else [x.strip() for x in lines[start + 1 : -1]]
    return code, rows


def render(v: object) -> str:
    """`Value.render` for the values in virtual tables."""
    if v is None:
        return "NULL"
    if isinstance(v, bool):
        return str(v).lower()
    if isinstance(v, str):
        return json.dumps(v)
    return str(v)


def arrow_type(t: dict) -> pa.DataType:
    if any(k in t for k in ("i8", "i16", "i32", "i64")):
        return pa.int64()
    if "fp64" in t or "fp32" in t:
        return pa.float64()
    if "string" in t:
        return pa.string()
    if "bool" in t:
        return pa.bool_()
    if "precisionTimestamp" in t or "timestamp" in t:
        return pa.timestamp("us")
    if "date" in t:
        return pa.date32()
    raise AssertionError(f"no test data for {t}")


T0 = dt.datetime(2024, 1, 1)
POOLS = {
    pa.int64(): [0, 1, 2, 3, -1, 40],
    pa.float64(): [0.0, -0.0, 0.5, 1.5, -9999.0, math.nan, -math.nan, math.inf, -math.inf],
    pa.string(): ["ada", "bob", "cy"],
    pa.bool_(): [True, False],
    pa.timestamp("us"): [T0 + dt.timedelta(seconds=s) for s in (0, 30, 60, 90, 120)],
    pa.date32(): [dt.date(2024, 1, d) for d in (1, 2, 3)],
}


def table_schemas(plan: dict) -> dict[str, pa.Schema]:
    found: dict[str, pa.Schema] = {}

    def walk(node: object) -> None:
        if isinstance(node, dict):
            if "namedTable" in node:
                s = node["baseSchema"]
                found[".".join(node["namedTable"]["names"])] = pa.schema(
                    [
                        (n, arrow_type(t))
                        for n, t in zip(s["names"], s["struct"]["types"], strict=True)
                    ]
                )
            for v in node.values():
                walk(v)
        elif isinstance(node, list):
            for v in node:
                walk(v)

    walk(plan)
    return found


def distinct(v: object) -> object:
    """Values as the model tells them apart (-0.0 from 0.0, -NaN from NaN)."""
    return (repr(v), math.copysign(1.0, v)) if isinstance(v, float) else repr(v)


@st.composite
def table_data(draw, schema: pa.Schema) -> pa.Table:
    """Rows whose every column is free of repeats (one NULL at most), so no
    window ORDER BY ties and the result is determined."""
    n = draw(st.integers(0, min(len(POOLS[f.type]) + 1 for f in schema)))
    cols = {}
    for f in schema:
        pool = [*POOLS[f.type], None]
        vals = draw(st.lists(st.sampled_from(pool), min_size=n, max_size=n, unique_by=distinct))
        cols[f.name] = pa.array(vals, type=f.type)
    return pa.table(cols, schema=schema)


#: DataFusion writes `DISTINCT` as an aggregate with one empty grouping, which
#: its own consumer rejects.
DATAFUSION_CANNOT_READ = {"df_distinct"}


def same_bag(a: list[tuple], b: list[tuple]) -> bool:
    return canonical(a) == canonical(b)


@pytest.mark.parametrize("fixture", FIXTURES, ids=lambda p: p.stem)
@SETTINGS
@given(data=st.data())
def test_golden_fixtures(fixture, data):
    code, rows = expected(fixture)
    source = fixture.read_text()
    if code != 0:
        with pytest.raises(ValueError, match="rejects the plan"):
            written_plan(source)
        return
    plan = written_plan(source)
    schemas = table_schemas(json.loads(plan))
    if not schemas:
        # Only virtual tables: Lean evaluated it for the golden file.
        got = rows_of(polars_engine.run(plan, {}))
        assert [f"({', '.join(map(render, r))})" for r in got] == rows
        # No DataFusion run: Lean writes virtual tables with placeholder
        # `i64` column types and `FetchRel`'s deprecated `offset`/`count`,
        # both of which DataFusion rejects.

        return
    con = connect()
    tables = {t: data.draw(table_data(s)) for t, s in schemas.items()}
    for t, table in tables.items():
        put_table(con, t, table)
    if '"fetch"' in plan:
        # DataFusion reads the current `offsetExpr`/`countExpr`, not the
        # deprecated fields Lean writes: it runs the fixture itself.
        df = datafusion_rows(run_substrait_json(con, source))
        pl_rows = rows_of(run_plan(con, plan, "polars"))
    else:
        df, pl_rows = on_both(con, plan)
    assert same_bag(df, pl_rows)
    if fixture.stem.startswith("df_") and fixture.stem not in DATAFUSION_CANNOT_READ:
        # DataFusion's own plan (captured from it), not just Lean's rewrite.
        assert same_bag(datafusion_rows(run_substrait_json(con, source)), pl_rows)
    if all(f.type == pa.int64() for s in schemas.values() for f in s):
        inlined = inline_tables(json.loads(plan), {t: rows_of(x) for t, x in tables.items()})
        assert lean_rows(json.dumps(inlined)) == pl_rows


# --- Queries the other suites check against Lean ---------------------------

small = st.one_of(st.none(), st.integers(-3, 3))


def lean_and_polars(con, sql: str, rows: dict[str, list[tuple]]) -> tuple[list, list]:
    plan = written_plan(substrait_json(con, sql))
    inlined = inline_tables(json.loads(plan), rows)
    return lean_rows(json.dumps(inlined)), rows_of(run_plan(con, plan, "polars"))


@pytest.mark.parametrize("sql", WINDOW_QUERIES)
@SETTINGS
@given(rows=st.lists(st.tuples(small, small, small), max_size=10, unique_by=lambda r: (r[0], r[1])))
def test_windows_match_lean_in_order(sql, rows):
    con = connect()
    create_table(con, "r", WINDOW_SCHEMA, rows)
    lean, polars = lean_and_polars(con, sql, {"r": rows})
    assert lean == polars
    assert same_bag(rows_of(run_sql(con, sql)), polars)


@pytest.mark.parametrize("sql", REWRITE_QUERIES)
@SETTINGS
@given(
    r=st.lists(st.tuples(small, small, small), max_size=8),
    s=st.lists(st.tuples(small, small), max_size=5),
)
def test_rewrites_match_lean_in_order(sql, r, s):
    con = connect()
    create_table(con, "r", R, r)
    create_table(con, "s", S, s)
    lean, polars = lean_and_polars(con, sql, {"r": r, "s": s})
    assert lean == polars
    assert same_bag(rows_of(run_sql(con, sql)), polars)


# --- Delta plans -------------------------------------------------------------

names = st.sampled_from(["ada", "bob", "cy", None])
orders_row = st.tuples(st.integers(0, 5), names, st.one_of(st.none(), st.integers(0, 40)))
customers_row = st.tuples(names, st.sampled_from(["Paris", "Rome", None]))
weights = st.sampled_from([1, -1, 2])


def with_weights(rows: list[tuple], ws: list[int], schema: pa.Schema) -> pa.Table:
    full = pa.schema([*schema, pa.field(WEIGHT, pa.int64())])
    return pa.Table.from_pylist(
        [dict(zip(full.names, (*r, w), strict=True)) for r, w in zip(rows, ws, strict=False)],
        schema=full,
    )


@pytest.mark.parametrize("name", PIPELINES)
@SETTINGS
@given(data=st.data())
def test_delta_plans_agree(name, data):
    """Every delta term on arbitrary change tables (weights included), on both
    engines."""
    con = connect()
    create_tables(
        con,
        data.draw(st.lists(orders_row, max_size=5)),
        data.draw(st.lists(customers_row, max_size=4)),
    )
    plan = substrait_json(con, ibis.to_sql(PIPELINES[name], dialect="datafusion"))
    for t, row in [("orders", orders_row), ("customers", customers_row)]:
        rows = data.draw(st.lists(row, max_size=4))
        ws = data.draw(st.lists(weights, min_size=len(rows), max_size=len(rows)))
        put_table(con, t + "$delta", with_weights(rows, ws, con.con.table(t).schema()))
    deltas = sv.delta_plans(plan)
    assert deltas
    for d in deltas:
        assert set(read_tables(json.loads(d))) <= {
            "orders",
            "customers",
            "orders$delta",
            "customers$delta",
        }
        df, pl_rows = on_both(con, d)
        assert same_bag(df, pl_rows)


@pytest.mark.parametrize("name", PIPELINES)
@SETTINGS
@given(data=st.data())
def test_polars_view_matches_datafusion_view(name, data):
    """The same batches maintained by each engine give the same view."""
    orders = data.draw(st.lists(orders_row, max_size=6))
    customers = data.draw(st.lists(customers_row, max_size=4))
    views = {}
    for engine in sv.ENGINES:
        con = connect()
        create_tables(con, orders, customers)
        views[engine] = sv.IncrementalView(con, PIPELINES[name], "v", engine=engine)
    for _ in range(data.draw(st.integers(1, 3))):
        changes = {
            t: sv.Changes(
                inserts=data.draw(
                    st.lists(orders_row if t == "orders" else customers_row, max_size=3)
                )
            )
            for t in views["polars"].tables
        }
        for view in views.values():
            view.apply(changes)
            assert view.rows() == view.recompute()
        assert views["polars"].rows() == views["datafusion"].rows()


# --- Semantic traps ------------------------------------------------------------


def polars_rows(con, sql: str) -> list[tuple]:
    return rows_of(run_plan(con, written_plan(substrait_json(con, sql)), "polars"))


def test_null_join_keys_never_match():
    con = connect()
    create_table(con, "r", R, [(1, None, 0), (2, 5, 0)])
    create_table(con, "s", S, [(None, 7), (5, 8)])
    inner = "SELECT r.a, s.d FROM r JOIN s ON r.b = s.b"
    left = "SELECT r.a, s.d FROM r LEFT JOIN s ON r.b = s.b"
    assert polars_rows(con, inner) == [(2, 8)]
    assert polars_rows(con, left) == [(1, None), (2, 8)]
    for sql in (inner, left):
        lean, polars = lean_and_polars(
            con, sql, {"r": [(1, None, 0), (2, 5, 0)], "s": [(None, 7), (5, 8)]}
        )
        assert lean == polars


def test_left_join_keeps_lean_order():
    """Each left row in place: its matches in right order, or one padded row."""
    con = connect()
    r = [(1, 1, 0), (2, 9, 0), (3, 1, 0)]
    s = [(1, 20), (1, 10)]
    create_table(con, "r", R, r)
    create_table(con, "s", S, s)
    sql = "SELECT r.a, s.d FROM r LEFT JOIN s ON r.b = s.b AND s.d > 0"
    assert polars_rows(con, sql) == [(1, 20), (1, 10), (2, None), (3, 20), (3, 10)]


def test_float_join_keys_use_the_total_order():
    """As in DataFusion and the float codes: NaN matches NaN, -0.0 not 0.0."""
    con = connect()
    schema = ibis.schema({"k": "float64", "v": "int64"})
    create_table(con, "a", schema, [(math.nan, 1), (-0.0, 2), (0.0, 3), (None, 4)])
    create_table(con, "b", schema, [(math.nan, 10), (0.0, 30), (None, 40)])
    sql = "SELECT a.v, b.v AS w FROM a JOIN b ON a.k = b.k"
    df, pl_rows = on_both(con, written_plan(substrait_json(con, sql)))
    assert pl_rows == [(1, 10), (3, 30)]
    assert same_bag(df, pl_rows)


def test_three_valued_logic_in_filters():
    con = connect()
    rows = [(a, b, 0) for a in (None, -1, 1) for b in (None, -1, 1)]
    create_table(con, "r", R, rows)
    cases = {
        # NOT (NULL AND FALSE) = TRUE keeps the row; NOT (NULL AND TRUE) = NULL drops it.
        "SELECT a, b FROM r WHERE NOT (a > 0 AND b > 0)": [
            (None, -1),
            (-1, None),
            (-1, -1),
            (-1, 1),
            (1, -1),
        ],
        "SELECT a, b FROM r WHERE a > 0 OR b > 0": [
            (None, 1),
            (-1, 1),
            (1, None),
            (1, -1),
            (1, 1),
        ],
        "SELECT a, b FROM r WHERE NOT (a > 0 OR b > 0)": [(-1, -1)],
    }
    for sql, want in cases.items():
        assert polars_rows(con, sql) == want, sql
        assert lean_and_polars(con, sql, {"r": rows})[0] == want, sql
        assert same_bag(rows_of(run_sql(con, sql)), want), sql


@pytest.mark.parametrize(
    "direction", ["ASC NULLS FIRST", "ASC NULLS LAST", "DESC NULLS FIRST", "DESC NULLS LAST"]
)
def test_null_order_in_windows(direction):
    con = connect()
    rows = [(1, 2, 0), (1, None, 1), (1, 0, 2), (2, None, 3), (None, 1, 4), (None, None, 5)]
    create_table(con, "r", WINDOW_SCHEMA, rows)
    sql = (
        f"SELECT s, t, ROW_NUMBER() OVER (PARTITION BY s ORDER BY t {direction}) AS n,"
        f" LAG(v) OVER (PARTITION BY s ORDER BY t {direction}) AS p FROM r"
    )
    lean, polars = lean_and_polars(con, sql, {"r": rows})
    assert lean == polars
    assert same_bag(rows_of(run_sql(con, sql)), polars)
    first = [r[1] for r in polars if r[0] == 1 and r[2] == 1]
    assert first == ([None] if "NULLS FIRST" in direction else [0 if "ASC" in direction else 2])


def test_float_window_order_is_total():
    """-NaN < -inf < -0.0 < 0.0 < inf < NaN, as DataFusion sorts doubles."""
    con = connect()
    schema = ibis.schema({"x": "float64"})
    xs = [math.nan, 0.0, -math.inf, -0.0, math.inf, -math.nan, None]
    create_table(con, "f", schema, [(x,) for x in xs])
    sql = "SELECT x, ROW_NUMBER() OVER (ORDER BY x ASC NULLS LAST) AS n FROM f"
    df, pl_rows = on_both(con, written_plan(substrait_json(con, sql)))
    assert repr(pl_rows) == repr(
        [
            (-math.nan, 1),
            (-math.inf, 2),
            (-0.0, 3),
            (0.0, 4),
            (math.inf, 5),
            (math.nan, 6),
            (None, 7),
        ]
    )
    assert canonical(df) == canonical(pl_rows)


def test_integer_overflow_raises():
    """Lean's integers are unbounded; a 64-bit engine must not wrap."""
    con = connect()
    big = 2**62
    create_table(con, "r", R, [(big, big, -(2**63))])
    for sql in [
        "SELECT a + b AS x FROM r",
        "SELECT a * b AS x FROM r",
        "SELECT c - 1 AS x FROM r",
        "SELECT -c AS x FROM r",
    ]:
        with pytest.raises(polars_engine.IntegerOverflow):
            polars_rows(con, sql)
    assert polars_rows(con, "SELECT a + (b - 1) AS x FROM r") == [(2**63 - 1,)]


def test_timestamp_arithmetic_is_checked_too():
    con = connect()
    schema = ibis.schema({"ts": "timestamp"})
    create_table(con, "t", schema, [(dt.datetime(2024, 1, 1),)])
    sql = "SELECT ts + INTERVAL 90 SECOND AS x, ts - ts AS d FROM t"
    df, pl_rows = on_both(con, written_plan(substrait_json(con, sql)))
    assert pl_rows == [(dt.datetime(2024, 1, 1, 0, 1, 30), dt.timedelta(0))]
    assert df == pl_rows


# --- Refusals ----------------------------------------------------------------------


def test_unwritten_plans_are_refused():
    """DataFusion's own plans use constructs Lean rewrites away (`gt`, casts,
    `ReadRel.projection`, …); the translator refuses them instead of guessing."""
    con = connect()
    create_table(con, "r", R, [])
    raw = substrait_json(con, "SELECT a FROM r WHERE a > 1")
    with pytest.raises(polars_engine.Unsupported):
        polars_engine.to_lazy(raw, {"r": pa.table({"a": [1], "b": [1], "c": [1]})})


def test_string_order_is_refused():
    """`BinFn.lt` is undefined on strings in the model, unlike in SQL."""
    con = connect()
    create_table(con, "o", ibis.schema({"name": "string"}), [("ada",)])
    with pytest.raises(polars_engine.Unsupported, match="lt of String"):
        polars_rows(con, "SELECT name FROM o WHERE name < 'b'")


def test_unknown_function_is_refused():
    con = connect()
    create_tables(con)
    plan = json.loads(written_plan(substrait_json(con, "SELECT id FROM orders WHERE amount > 10")))
    plan["extensions"][0]["extensionFunction"]["name"] = "sqrt"
    filt = plan["relations"][0]["root"]["input"]["project"]["input"]["filter"]
    filt["condition"] = {
        "scalarFunction": {
            "functionReference": 1,
            "arguments": [filt["condition"]["scalarFunction"]["arguments"][0]],
        }
    }
    with pytest.raises(polars_engine.Unsupported, match="sqrt"):
        polars_engine.to_lazy(plan, {"orders": con.con.table("orders").to_arrow_table()})


def test_integer_sum_overflow_raises():
    """`SUM` of integers is exact in Lean; DataFusion wraps around (`Issue.wraps`)."""
    con = connect()
    create_table(con, "r", R, [(2**62, 1, 0), (2**62, 1, 0), (1, 2, 0)])
    with pytest.raises(polars_engine.IntegerOverflow):
        polars_rows(con, "SELECT b, SUM(a) AS s FROM r GROUP BY b")
    assert polars_rows(con, "SELECT b, SUM(a - 1) AS s FROM r GROUP BY b") == [
        (1, 2**63 - 2),
        (2, 0),
    ]


def test_checker_writes_what_polars_reads():
    """`--write` output is a fixed point of the round trip the translator relies on."""
    con = connect()
    create_table(con, "r", WINDOW_SCHEMA, [])
    once = written_plan(substrait_json(con, WINDOW_QUERIES[-1]))
    code, twice, err = run_checker(("--write",), once)
    assert code == 0, err
    assert json.loads(twice) == json.loads(once)


# --- Integer division, powers, rounding and runtime errors --------------------


@pytest.mark.parametrize("sql", INT_QUERIES)
@SETTINGS
@given(rows=st.lists(st.tuples(small, small), max_size=8))
def test_integer_functions_match_lean_in_order(sql, rows):
    con = connect()
    create_table(con, "r", NUMERIC_R, rows)
    plan = written_plan(substrait_json(con, sql))
    inlined = inline_tables(json.loads(plan), {"r": rows})
    polars = rows_of(run_plan(con, plan, "polars"))
    assert lean_values(json.dumps(inlined)) == polars
    assert same_bag(rows_of(run_sql(con, sql)), polars)


def test_rounding_matches_datafusion_bit_for_bit():
    """Halves away from zero, `CEIL(-0.5)` is -0.0, NaN and ±∞ stay."""
    con = connect()
    xs = [*DOUBLES, -0.0, -0.4, math.nan, math.inf, -math.inf, None]
    create_table(con, "r", F, [(x,) for x in xs])
    for sql in [
        "SELECT f, floor(f) AS x, ceil(f) AS y, round(f) AS z FROM r",
        "SELECT f, round(f, 1) AS x, round(f, -1) AS y FROM r",
        "SELECT f, power(f, 2.0) AS p FROM r",
        "SELECT f, f / 10.0 AS x, 3.0 / f AS y FROM r",
    ]:
        df, pl_rows = on_both(con, written_plan(substrait_json(con, sql)))
        assert repr(df) == repr(pl_rows), sql
        assert [math.copysign(1, v) for r in pl_rows for v in r if v is not None] == [
            math.copysign(1, v) for r in df for v in r if v is not None
        ], sql


def test_casts_to_bigint_truncate_and_refuse_nan():
    con = connect()
    create_table(con, "r", F, [(x,) for x in DOUBLES])
    sql = "SELECT f, CAST(f AS BIGINT) AS i FROM r"
    df, pl_rows = on_both(con, written_plan(substrait_json(con, sql)))
    assert df == pl_rows
    create_table(con, "r", F, [(1.0,), (math.nan,)])
    with pytest.raises(polars_engine.BadCast):
        polars_rows(con, sql)
    create_table(con, "r", F, [(2.0**63,)])
    with pytest.raises(polars_engine.BadCast):
        polars_rows(con, sql)


@pytest.mark.parametrize(
    ("sql", "error"),
    [
        ("SELECT a / b AS q FROM r WHERE a = 5", polars_engine.DivisionByZero),
        ("SELECT a % b AS q FROM r WHERE a = 5", polars_engine.DivisionByZero),
        ("SELECT a / b AS q FROM r WHERE b = -1", polars_engine.Overflow),
        ("SELECT power(a, 2) AS p FROM r WHERE b = -1", polars_engine.Overflow),
        ("SELECT power(a, b) AS p FROM r WHERE b = -1", polars_engine.NegativeExponent),
        # Both sides of AND are evaluated.
        ("SELECT a FROM r WHERE b <> 0 AND a % b > 1", polars_engine.DivisionByZero),
        # An unused column is still computed.
        ("SELECT a FROM (SELECT a, a % b AS q FROM r)", polars_engine.DivisionByZero),
        # Wrapping, which DataFusion does silently.
        ("SELECT a - 1 AS x FROM r WHERE b = -1", polars_engine.IntegerOverflow),
        ("SELECT -a AS x FROM r WHERE b = -1", polars_engine.IntegerOverflow),
    ],
)
def test_runtime_errors_raise(sql, error):
    con = connect()
    create_table(con, "r", NUMERIC_R, [(5, 0), (MIN, -1), (7, 2)])
    with pytest.raises(error):
        polars_rows(con, sql)


@pytest.mark.parametrize(
    "sql",
    [
        "SELECT CASE WHEN b <> 0 THEN a / b END AS q FROM r",
        "SELECT a / NULLIF(b, 0) AS q, a % NULLIF(b, 0) AS m FROM r",
        "SELECT a / b AS q FROM r WHERE b > 0",
        "SELECT CASE WHEN b > 0 THEN power(a, b) ELSE 0 END AS p FROM r WHERE a = 7",
    ],
)
def test_guarded_operations_do_not_raise(sql):
    """A `CASE` branch counts only on the rows that take it, and a filter's
    rows are the only ones a later projection sees."""
    con = connect()
    # Lean prints integers of magnitude 2^63 as double codes, so not MIN itself.
    rows = [(5, 0), (-7, 2), (7, -2), (None, 0), (MIN + 1, 1)]
    create_table(con, "r", NUMERIC_R, rows)
    plan = written_plan(substrait_json(con, sql))
    polars = rows_of(run_plan(con, plan, "polars"))
    assert lean_values(json.dumps(inline_tables(json.loads(plan), {"r": rows}))) == polars


@pytest.mark.parametrize("i", range(len(NUMERIC_PIPELINES)))
@SETTINGS
@given(rows=st.lists(st.tuples(numeric_values, numeric_values), max_size=6))
def test_polars_fails_only_where_reported(i, rows):
    """Polars raises an error only where `Rel.mayIssues` reports one (and
    `IntegerOverflow` only where it warns of wrapping). When neither engine
    fails and nothing wraps, they agree."""
    expr = NUMERIC_PIPELINES[i]
    report = sv.verify(expr)
    con = connect()
    put_table(
        con,
        "t",
        pa.table(
            {
                "qty": pa.array([q for q, _ in rows], pa.int64()),
                "n": pa.array([n for _, n in rows], pa.int64()),
                "amount": pa.array([1.0 for _ in rows], pa.float64()),
            }
        ),
    )
    plan = written_plan(substrait_json(con, to_sql(expr)))
    try:
        polars = rows_of(run_plan(con, plan, "polars"))
    except polars_engine.IntegerOverflow:
        assert [w.kind for w in report.warnings] == ["may wrap around"]
        return
    except polars_engine.RuntimeIssue as e:
        assert report.errors, f"Polars failed ({e}) but no error was reported"
        return
    try:
        df = rows_of(run_sql(con, to_sql(expr)))
    except Exception:  # noqa: BLE001 - DataFusion evaluates more rows (`Rel.loose`)
        return
    assert same_bag(df, polars)
