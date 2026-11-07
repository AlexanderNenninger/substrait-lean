"""The meaning `verify` gives the Ibis operations whose result depends on the
Ibis backend (`docs/reference-semantics.md`, "The Ibis frontend").

Each expression goes through the vendored producer, as `verify` compiles it,
and Lean's evaluation (`Rel.eval`) must give the documented rows: the meaning
is the producer's, not any backend's. Where the documented meaning is an
error, Lean's contract report must say so; where it is a refusal, the
producer or the checker must refuse.
"""

import json
import math

import ibis
import pyarrow as pa
import pytest

import sverify as sv
from sverify.engine import connect, plan_json, put_table, run_checker
from sverify.ibis_substrait import Unsupported, to_substrait_json
from sverify.testing import duckdb_sql, inline_tables, lean_values

T = pa.table(
    {
        "a": pa.array([-7, 7, 5], pa.int64()),
        "b": pa.array([2, -2, 3], pa.int64()),
        "s": ["é", "🎉", None],
        "v": [2.5, -2.5, -0.0],
        "x": pa.array([1, None, 1], pa.int64()),
    }
)


@pytest.fixture(scope="module")
def con():
    c = connect()
    put_table(c, "t", T)
    return c


def lean(con, expr) -> list[tuple]:
    rows = [tuple(r.values()) for r in con._arrow["t"].to_pylist()]
    plan = inline_tables(json.loads(plan_json(con, expr)), {"t": rows})
    return lean_values(json.dumps(plan))


def close(got: list[tuple], expected: list[tuple]) -> bool:
    """Lean prints doubles with six decimals."""

    def same(g: object, e: object) -> bool:
        if isinstance(e, float) and isinstance(g, float):
            return math.isclose(g, e, abs_tol=1e-6)
        return g == e

    return len(got) == len(expected) and all(
        len(g) == len(e) and all(same(x, y) for x, y in zip(g, e, strict=True))
        for g, e in zip(got, expected, strict=True)
    )


#: (label, expression over `t`, the documented rows)
MEANINGS = [
    ("mod truncates", lambda t: t.select(r=t.a % t.b), [(-1,), (1,), (2,)]),
    ("floor division", lambda t: t.select(r=t.a // t.b), [(-4,), (-4,), (1,)]),
    ("length counts code points", lambda t: t.select(r=t.s.length()), [(1,), (1,), (None,)]),
    (
        "find is 0-based, NULL for NULL",
        lambda t: t.select(r=t.s.find("🎉")),
        [(-1,), (0,), (None,)],
    ),
    ("substr is 0-based", lambda t: t.select(r=t.s.substr(0, 1)), [("é",), ("🎉",), (None,)]),
    (
        "like escapes with a backslash",
        lambda t: t.select(r=t.s.like("\\%")),
        [(False,), (False,), (None,)],
    ),
    ("nunique skips NULL", lambda t: t.aggregate(r=t.x.nunique()), [(1,)]),
    (
        "any and all are BOOL_OR and BOOL_AND",
        lambda t: t.aggregate(p=(t.a > 6).any(), q=(t.a > 0).all(), n=t.x.isnull().any()),
        [(True, False, True)],
    ),
    (
        "any and all of no rows are NULL",
        lambda t: t.aggregate(p=(t.a > 0).any(where=t.a > 100), q=(t.a > 0).all(where=t.a < 0)),
        [(None, False)],
    ),
    (
        "bit aggregates of 64-bit integers, NULLs skipped",
        lambda t: t.aggregate(
            p=t.a.bit_and(),
            q=t.a.bit_or(),
            r=t.a.bit_xor(),
            s=t.x.bit_xor(),
            e=t.a.bit_and(where=t.a > 100),
        ),
        [(1, -1, -5, 0, None)],
    ),
    ("round half away from zero", lambda t: t.select(r=t.v.round()), [(3,), (-3,), (0,)]),
    ("cast to int64 truncates", lambda t: t.select(r=t.v.cast("int64")), [(2,), (-2,), (0,)]),
    ("one zero", lambda t: t.select(r=t.v == 0.0), [(False,), (False,), (True,)]),
    ("== null is IS NULL", lambda t: t.select(r=t.x == ibis.null()), [(False,), (True,), (False,)]),
    (
        "row_number is 0-based",
        lambda t: t.select("a", r=ibis.row_number().over(order_by=t.a)).order_by("a"),
        [(-7, 0), (5, 1), (7, 2)],
    ),
    (
        "NULLs last in a descending sort",
        lambda t: t.select("x").order_by(ibis.desc("x")),
        [(1,), (1,), (None,)],
    ),
]


@pytest.mark.parametrize(("label", "build", "rows"), MEANINGS, ids=[m[0] for m in MEANINGS])
def test_producer_gives_the_documented_meaning(con, label, build, rows):
    got = lean(con, build(con.table("t")))
    assert close(got, rows), f"{label}: {got}"


def test_division_by_zero_is_an_error(con):
    t = con.table("t")
    for expr in (t.select(r=t.a % (t.b - t.b)), t.select(r=t.a // (t.b - t.b))):
        assert "division by zero" in [i.kind for i in sv.verify(expr).errors]


def test_cast_of_a_double_out_of_range_is_an_error(con):
    t = con.table("t")
    report = sv.verify(t.select(r=t.v.cast("int64")), on_inferred="off")
    assert "cast out of range" in [i.kind for i in report.errors]


def test_refused_operations(con):
    t = con.table("t")
    # MAX of doubles is accepted (#371): DuckDB orders doubles as the model does.
    code, _, _ = run_checker((), plan_json(con, t.aggregate(r=t.v.max())))
    assert code == 0
    ts = ibis.timestamp("2024-05-05 00:00:00")
    with pytest.raises(Unsupported, match="TimestampDelta"):
        plan_json(con, t.select(r=ts.delta(ibis.timestamp("2024-05-06 00:00:00"), unit="hour")))
    # Each engine estimates it its own way; it used to be read as `nunique`.
    with pytest.raises(Unsupported, match="approx_nunique is not supported"):
        plan_json(con, t.aggregate(r=t.v.approx_nunique()))


@pytest.mark.parametrize(
    ("build", "reason"),
    [
        (lambda t: t.select(r=ibis.random()), "each run gives another value"),
        (lambda t: t.select(r=ibis.now()), "pass the time in"),
        (lambda t: t.select(r=ibis.today()), "pass the date in"),
        # DuckDB types an expression its own way (`typeof(1)` is INTEGER).
        (lambda t: t.select(r=(t.a + 1).typeof()), "only supported of a column"),
        (lambda t: t.filter(t.v > ibis.param(ibis.dtype("float64"))), "pass params"),
    ],
)
def test_refusals_say_why(con, build, reason):
    """#58: each refused operation says why, and what to do instead."""
    with pytest.raises(Unsupported, match=reason):
        plan_json(con, build(con.table("t")))


def test_typeof_folds_to_duckdbs_name(con):
    """#508: `typeof` of a column is a constant, DuckDB's name of its type
    (`duckdb-typeof-names`)."""
    t = con.table("t")
    expr = t.select(a=t.a.typeof(), s=t.s.typeof(), v=t.v.typeof())
    expected = duckdb_sql(con, "SELECT typeof(a), typeof(s), typeof(v) FROM t")
    assert lean(con, expr) == [tuple(r.values()) for r in expected.to_pylist()]
    assert lean(con, expr) == [("BIGINT", "VARCHAR", "DOUBLE")] * 3


@pytest.mark.parametrize(
    "dtype",
    [
        "int8", "int16", "int32", "int64", "uint8", "uint16", "uint32", "uint64", "float32",
        "float64", "decimal(10, 2)", "decimal(38, 10)", "string", "boolean", "date", "time",
        "binary", "uuid", "interval('s')", "timestamp", "timestamp(0)", "timestamp(3)",
        "timestamp(9)", "timestamp('UTC')", "array<int64>", "array<array<string>>",
    ],
)  # fmt: skip
def test_typeof_names_are_duckdbs(dtype):
    """`duckdb_type_name` is what DuckDB's `typeof` says of a value of that
    type, as Ibis writes the type for DuckDB."""
    import duckdb
    from ibis.backends.sql.datatypes import DuckDBType

    from sverify.ibis_substrait.casts import duckdb_type_name

    t = ibis.dtype(dtype)
    [(name,)] = duckdb.execute(f"SELECT typeof(NULL::{DuckDBType.to_string(t)})").fetchall()
    assert duckdb_type_name(t) == name


def test_day_of_week_index_starts_on_monday(con):
    t = con.table("t")
    sunday, monday = ibis.timestamp("2024-05-05 00:00:00"), ibis.timestamp("2024-05-06 00:00:00")
    expr = t.select(s=sunday.day_of_week.index(), m=monday.day_of_week.index())
    assert lean(con, expr) == [(6, 0)] * 3


# #58: `ibis.param`s are bound at verification time, as Ibis's
# `execute(params=...)` binds them.
def test_params_are_bound_for_verify():
    t = ibis.table({"qty": "int64", "name": "string"}, name="t")
    p, q = ibis.param(ibis.dtype("int64")), ibis.param(ibis.dtype("string"))
    expr = t.filter((t.qty > p) & (t.name != q))
    report = sv.verify(expr, params={p: 5, q: "x"}, ensures=[ibis._.qty > 5])
    assert report.proved, str(report)
    # The proof is for these values only, and the report says so.
    assert report._params == ["param1 (int64) = 5", "param2 (string) = 'x'"]
    assert "proved for these parameter values only" in str(report)
    assert not sv.verify(expr, params={p: 0, q: "x"}, ensures=[ibis._.qty > 5]).proved
    with pytest.raises(ValueError, match="pass params"):
        sv.verify(expr, params={p: 5})
    with pytest.raises(TypeError, match="parameter's type"):
        sv.verify(expr, params={p: "five", q: "x"})
    with pytest.raises(TypeError, match="ibis.param"):
        sv.verify(expr, params={t.qty: 5, q: "x"})
    with pytest.raises(TypeError, match="not SQL"):
        sv.verify("SELECT qty FROM t", tables={"t": t}, params={p: 5})


def test_bound_params_mean_what_ibis_execute_gives():
    rows = [(1, "a"), (7, "b"), (9, "x"), (None, "c")]
    p, q = ibis.param(ibis.dtype("int64")), ibis.param(ibis.dtype("string"))
    params = {p: 5, q: "x"}

    def build(t):
        return t.filter((t.qty > p) & (t.name != q)).select("qty", "name", r=t.qty + p)

    t = ibis.table({"qty": "int64", "name": "string"}, name="t")
    plan = to_substrait_json(sv.contracts.bind_params(build(t), params))
    lean = lean_values(json.dumps(inline_tables(json.loads(plan), {"t": rows})))
    # Ibis binds them itself in its own DuckDB SQL.
    con = connect()
    con.create("t", t.schema(), rows)
    native = duckdb_sql(con, ibis.to_sql(build(t), dialect="duckdb", params=params))
    assert sorted(lean, key=repr) == sorted(native_rows(native), key=repr)


def native_rows(table: pa.Table) -> list[tuple]:
    return [tuple(r.values()) for r in table.to_pylist()]
