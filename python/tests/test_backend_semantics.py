"""One expression on many engines, pinned (`notebooks/17_backend_semantics.py`).

First, what the native engines do where it differs from the Lean model and
sverify's translators work around it (Polars' floor `%`, DuckDB's IEEE zeros,
…), so an upgrade that changes one of them shows up here. Then the Ibis
expressions whose meaning depends on the backend, so a new Ibis that changes
them shows up too. Then the translators on the notebook's edge rows: Polars
and DuckDB must agree with each other.

Last, the sverify gaps the notebook found, now fixed: constant casts fold as
DataFusion casts, and the Polars translator keeps repeated output names.
"""

import json
import math

import duckdb
import ibis
import polars as pl
import pyarrow as pa
import pytest

import sverify as sv
from sverify import duckdb_engine, polars_engine
from sverify.engine import connect, put_table, read_tables, substrait_json, written_plan


def ints(**cols: list) -> pa.Table:
    return pa.table({k: pa.array(v, pa.int64()) for k, v in cols.items()})


TABLES = {
    "n": ints(x=[1, None, 2]),
    "j": ints(a=[1, None]),
    "k": ints(g=[1, 1, 2, None], v=[None, None, 3, 4]),
    "dm": ints(a=[-7, 7, -7], b=[2, -2, -2]),
    "z": ints(a=[1, 0], b=[0, 0]),
    "mx": ints(a=[2**63 - 1, -(2**63)]),
    "r": pa.table({"v": [2.5, -2.5, 0.5, 1.5, 2.7]}),
    "f": pa.table({"v": [math.nan, 0.0, 1.0, None, -math.inf]}),
    "f0": pa.table({"v": [-0.0, 0.0]}),
    "s": pa.table({"s": ["hello", "é", "🎉", "", None]}),
    "ss": pa.table({"s": ["Straße", "a\\b"]}),
    "u": pa.table({"s": ["٣", "3", "a b"]}),
    "w": ints(g=[1, 1, 1, 2], o=[1, 2, 2, 1], v=[10, 20, 30, 40]),
}
P = {k: pl.DataFrame(t) for k, t in TABLES.items()}


def positional(t: pa.Table) -> list[tuple]:
    return list(zip(*[c.to_pylist() for c in t.columns], strict=True))


@pytest.fixture(scope="module")
def con():
    """The tables as the model has them (`put_table`: one zero, one NaN), and
    in DataFusion as they are, so that its own answers show its own order."""
    c = connect()
    for name, t in TABLES.items():
        put_table(c, name, t)
    ctx = c.datafusion
    for name, t in TABLES.items():
        ctx.deregister_table(name)
        ctx.register_record_batches(name, [t.to_batches()])
    return c


@pytest.fixture(scope="module")
def duck():
    db = duckdb.connect()
    for name, t in TABLES.items():
        db.register(name, t)
    return db


# --- Native engines -----------------------------------------------------------


@pytest.mark.parametrize(
    ("expr", "expected"),
    [
        # Floor remainder, the sign of the divisor (SQL: of the dividend).
        (lambda: P["dm"].select(pl.col("a") % pl.col("b")), [(1,), (-1,), (-1,)]),
        # Integer division and remainder by zero are NULL, not an error.
        (lambda: P["z"].select(pl.col("a") // pl.col("b")), [(None,), (None,)]),
        (lambda: P["z"].select(pl.col("a") % pl.col("b")), [(None,), (None,)]),
        # 64-bit overflow wraps.
        (lambda: P["mx"].head(1).select(pl.col("a") + 1), [(-(2**63),)]),
        # NULLs sort first in both directions.
        (lambda: P["n"].sort("x"), [(None,), (1,), (2,)]),
        (lambda: P["n"].sort("x", descending=True), [(None,), (2,), (1,)]),
        # `is_in` ignores a NULL in the list: FALSE where SQL says NULL.
        (lambda: P["n"].select(pl.col("x").is_in([1, None])), [(True,), (None,), (False,)]),
        # Aggregates: the sum of nothing is 0, n_unique counts NULL, max skips NaN.
        (lambda: P["k"].filter(pl.col("g") == 1).select(pl.col("v").sum()), [(0,)]),
        (lambda: P["k"].select(pl.col("v").n_unique()), [(3,)]),
        (lambda: P["f"].select(pl.col("v").max()), [(1.0,)]),
        # Rounding is half to even; the cast truncates.
        (lambda: P["r"].select(pl.col("v").round()), [(2.0,), (-2.0,), (0.0,), (2.0,), (3.0,)]),
        (lambda: P["r"].select(pl.col("v").cast(pl.Int64)), [(2,), (-2,), (0,), (1,), (2,)]),
        # IEEE zeros: -0.0 = 0.0.
        (lambda: P["f0"].select(pl.col("v") == 0.0), [(True,), (True,)]),
        # Ibis's 0-based `find` is Polars' native one, with NULL for "absent".
        (lambda: P["s"].head(2).select(pl.col("s").str.find("l")), [(2,), (None,)]),
    ],
)
def test_polars_native(expr, expected):
    assert expr().rows() == expected


@pytest.mark.parametrize(
    ("sql", "expected"),
    [
        # `/` on integers is double division, and so divides by zero as IEEE.
        ("SELECT a / b FROM dm", [(-3.5,), (-3.5,), (3.5,)]),
        ("SELECT a / b FROM z", [(math.inf,), ("NaN",)]),
        # `//` on integers truncates (sverify's `trunc_div` is exact either way).
        ("SELECT a // b FROM dm", [(-3,), (-3,), (3,)]),
        # BIGINT overflow raises; SUM goes to HUGEINT.
        ("SELECT sum(a) FROM (VALUES (9223372036854775807), (1)) v(a)", [(2**63,)]),
        # NULLs sort last in both directions.
        ("SELECT x FROM n ORDER BY x DESC", [(2,), (1,), (None,)]),
        # IEEE zeros, merged by DISTINCT.
        ("SELECT v = 0.0 FROM f0", [(True,), (True,)]),
        ("SELECT count(*) FROM (SELECT DISTINCT v FROM f0)", [(1,)]),
        # A double cast to BIGINT rounds half to even.
        ("SELECT CAST(v AS BIGINT) FROM r", [(2,), (-2,), (0,), (2,), (3,)]),
        # The standard's casts: spaces are allowed.
        ("SELECT CAST(' 12' AS BIGINT)", [(12,)]),
        # Negative SUBSTR starts count from the end.
        ("SELECT substr('hello', -1, 3)", [("o",)]),
        # LIKE has no default escape character.
        ("SELECT s LIKE 'a\\b' FROM ss", [(False,), (True,)]),
        # utf8proc's case mapping and RE2's ASCII-only classes.
        ("SELECT upper('ß'), regexp_matches('٣', '\\d')", [("ẞ", False)]),
        # AVG of BIGINT is exact.
        ("SELECT avg(a) FROM mx", [(-0.5,)]),
    ],
)
def test_duckdb_native(duck, sql, expected):
    got = [
        tuple("NaN" if isinstance(v, float) and v != v else v for v in r)
        for r in duck.sql(sql).fetchall()
    ]
    assert got == expected


def test_duckdb_overflow_raises(duck):
    with pytest.raises(duckdb.OutOfRangeException):
        duck.sql("SELECT a + 1 FROM mx WHERE a > 0").fetchall()


@pytest.mark.parametrize(
    ("sql", "expected"),
    [
        # Backslash is LIKE's default escape (DuckDB and the standard have none).
        ("SELECT s LIKE 'a\\b' FROM ss", [(False,), (False,)]),
        # concat() skips NULLs; || propagates.
        ("SELECT concat(s, 'x'), s || 'x' FROM s WHERE s IS NULL", [("x", None)]),
        # The total order on doubles: -0.0 < 0.0, so DISTINCT keeps both.
        ("SELECT v = 0.0 FROM f0", [(False,), (True,)]),
        ("SELECT count(*) FROM (SELECT DISTINCT v FROM f0)", [(2,)]),
        # NULL is the largest value.
        ("SELECT x FROM n ORDER BY x DESC", [(None,), (2,), (1,)]),
        # Rust's case mapping and Unicode regex classes.
        ("SELECT upper(s) FROM ss", [("STRASSE",), ("A\\B",)]),
        ("SELECT array_length(regexp_match(s, '\\d')) FROM u", [(1,), (1,), (None,)]),
        # AVG converts to doubles first.
        ("SELECT avg(a) FROM mx", [(0.0,)]),
        # Constant casts truncate, like column casts.
        ("SELECT CAST(2.7 AS BIGINT) AS c", [(2,)]),
    ],
)
def test_datafusion_native(con, sql, expected):
    assert positional(con.datafusion.sql(sql).to_arrow_table()) == expected


def test_datafusion_rejects_spaces_in_an_integer(con):
    with pytest.raises(Exception, match="Cannot cast string ' 12'"):
        con.datafusion.sql("SELECT CAST(' 12' AS BIGINT) AS c").to_arrow_table()


# --- Ibis: one expression, a backend-dependent meaning -------------------------

BACKENDS = ("datafusion", "duckdb", "polars")


@pytest.fixture(scope="module")
def ibis_backends():
    return {b: getattr(ibis, b).connect() for b in BACKENDS}


def on_each(backends, build, table: str) -> dict[str, list[tuple]]:
    expr = build(ibis.memtable(TABLES[table]))
    return {b: positional(c.to_pyarrow(expr)) for b, c in backends.items()}


@pytest.mark.parametrize(
    ("build", "table", "expected"),
    [
        # `%` passes the backend's convention through.
        (
            lambda t: t.select(q=t.a % t.b),
            "dm",
            {"datafusion": [(-1,), (1,), (-1,)], "polars": [(1,), (-1,), (-1,)]},
        ),
        # `length` counts bytes on Polars.
        (
            lambda t: t.select(l=t.s.length()),
            "s",
            {
                "datafusion": [(5,), (1,), (1,), (0,), (None,)],
                "polars": [(5,), (2,), (4,), (0,), (None,)],
            },
        ),
        # `nunique` counts NULL on Polars.
        (lambda t: t.aggregate(n=t.v.nunique()), "k", {"datafusion": [(2,)], "polars": [(3,)]}),
        # `max` skips NaN on Polars.
        (lambda t: t.aggregate(m=t.v.max()), "f", {"polars": [(1.0,)]}),
        # `round` and `cast('int64')` inherit each backend's rounding.
        (
            lambda t: t.select(q=t.v.round()),
            "r",
            {
                "datafusion": [(3,), (-3,), (1,), (2,), (3,)],
                "polars": [(2,), (-2,), (0,), (2,), (3,)],
            },
        ),
        (
            lambda t: t.select(q=t.v.cast("int64")),
            "r",
            {
                "datafusion": [(2,), (-2,), (0,), (1,), (2,)],
                "duckdb": [(2,), (-2,), (0,), (2,), (3,)],
            },
        ),
        # `== ` against ±0.0 follows the backend.
        (
            lambda t: t.select(q=t.v == 0.0),
            "f0",
            {"datafusion": [(False,), (True,)], "duckdb": [(True,), (True,)]},
        ),
        # `find` gives -1 for a NULL string on Polars.
        (
            lambda t: t.select(p=t.s.find("l")),
            "s",
            {
                "datafusion": [(2,), (-1,), (-1,), (-1,), (None,)],
                "polars": [(2,), (-1,), (-1,), (-1,), (-1,)],
            },
        ),
    ],
)
def test_ibis_is_leaky(ibis_backends, build, table, expected):
    got = on_each(ibis_backends, build, table)
    for backend, rows in expected.items():
        assert got[backend] == rows, backend


def test_ibis_max_with_nan_on_sql_backends(ibis_backends):
    expr = (t := ibis.memtable(TABLES["f"])).aggregate(m=t.v.max())
    for b in ("datafusion", "duckdb"):
        assert math.isnan(positional(ibis_backends[b].to_pyarrow(expr))[0][0])


@pytest.mark.parametrize(
    ("build", "table", "expected"),
    [
        # `== null` is IS NULL, not SQL's NULL.
        (lambda t: t.select(q=t.x == ibis.null()), "n", [(False,), (True,), (False,)]),
        # Sorts put NULLs last in both directions.
        (lambda t: t.order_by(ibis.desc("x")), "n", [(2,), (1,), (None,)]),
        # Ibis's 0-based positions.
        (lambda t: t.select(a=t.s.substr(0, 2)).limit(1), "s", [("he",)]),
    ],
)
def test_ibis_is_portable_but_not_sql(ibis_backends, build, table, expected):
    got = on_each(ibis_backends, build, table)
    assert got == dict.fromkeys(BACKENDS, expected)


def test_ibis_window_frames_and_row_numbers(ibis_backends):
    """An `order_by` without a frame covers the whole partition, and
    `row_number` starts at 0 (Ibis-on-Polars has no window functions)."""
    t = ibis.memtable(TABLES["w"])
    expr = t.select(
        "g",
        "o",
        "v",
        s=t.v.sum().over(group_by="g", order_by="o"),
        r=ibis.row_number().over(order_by=["g", "o", "v"]),
    ).order_by(["g", "o", "v"])
    for b in ("datafusion", "duckdb"):
        assert positional(ibis_backends[b].to_pyarrow(expr)) == [
            (1, 1, 10, 60, 0),
            (1, 2, 20, 60, 1),
            (1, 2, 30, 60, 2),
            (2, 1, 40, 40, 3),
        ]
    assert "UNBOUNDED FOLLOWING" in ibis.to_sql(expr, dialect="snowflake")


# --- sverify's translators on the notebook's edge rows -------------------------

FAITHFUL = [
    "SELECT x, x = NULL FROM n",
    "SELECT x, x IN (1, NULL), x NOT IN (2, NULL) FROM n",
    "SELECT x, x > 1 OR NULL, x > 1 AND NULL FROM n",
    "SELECT a, a IS DISTINCT FROM NULL, a IS NOT DISTINCT FROM 1 FROM j",
    "SELECT x FROM n ORDER BY x",
    "SELECT x FROM n ORDER BY x DESC",
    "SELECT g, v, row_number() OVER (ORDER BY g, v) FROM w",
    "SELECT g, o, v, lag(v) OVER (PARTITION BY g ORDER BY o, v) FROM w ORDER BY g, o, v",
    "SELECT a / b FROM dm",
    "SELECT a % b FROM dm",
    "SELECT v, v = 0.0, v < 0.0 FROM f0",
    "SELECT v / 0.0 FROM f",
    "SELECT v, CAST(v AS BIGINT) AS c FROM r",
    "SELECT v, round(v) FROM r",
    "SELECT s, length(s) FROM s",
    "SELECT s, substr(s, 0, 2), substr(s, -1, 3) FROM s",
    "SELECT s, strpos(s, 'l') FROM s",
    "SELECT s, s LIKE 'a\\b', s LIKE 'a\\\\b' FROM ss",
]


def translated(con, sql: str) -> tuple[list[tuple], list[tuple]]:
    plan = written_plan(substrait_json(con, sql))
    tabs = {n: TABLES[n] for n in read_tables(json.loads(plan))}
    return positional(polars_engine.run(plan, tabs)), positional(duckdb_engine.run(plan, tabs))


def key(v: object) -> object:
    """NaN equal to NaN, and -0.0 told apart from 0.0."""
    if isinstance(v, float):
        return ("NaN",) if v != v else (v, math.copysign(1, v))
    return v


def same(a: list[tuple], b: list[tuple]) -> bool:
    return [tuple(map(key, r)) for r in a] == [tuple(map(key, r)) for r in b]


@pytest.mark.parametrize("sql", FAITHFUL)
def test_translators_agree(con, sql):
    by_polars, by_duckdb = translated(con, sql)
    assert same(by_polars, by_duckdb)


@pytest.mark.parametrize(
    ("sql", "expected"),
    [
        # Opaque in Lean, so no proof depends on it, but the translators differ.
        ("SELECT upper(s) FROM ss", ([("STRASSE",), ("A\\B",)], [("STRAẞE",), ("A\\B",)])),
        (
            "SELECT array_length(regexp_match(s, '\\d')) FROM u",
            ([(1,), (1,), (None,)], [(None,), (1,), (None,)]),
        ),
    ],
)
def test_translators_disagree_on_opaque_functions(con, sql, expected):
    assert translated(con, sql) == expected


# --- sverify gaps, fixed ---------------------------------------------------------


def test_polars_translator_keeps_duplicate_output_names(con):
    """N4: two output columns with one name are legal SQL and Substrait."""
    sql = "SELECT a.a, b.a FROM j a JOIN j b ON a.a = b.a"
    by_polars, by_duckdb = translated(con, sql)
    assert by_polars == by_duckdb == [(1, 1)]
    plan = written_plan(substrait_json(con, sql))
    assert polars_engine.run(plan, {"j": TABLES["j"]}).column_names == ["a", "a"]
    with pytest.raises(polars_engine.Unsupported, match="repeat a name"):
        polars_engine.to_lazy(plan, {"j": TABLES["j"]})


def proves(sql: str, ensures: str) -> bool:
    r = sv.verify(sql, ensures=[ensures], tables={"j": {"a": "int64"}})
    return r.proved and r.ensures[0].proved


def test_constant_casts_truncate_like_datafusion(con):
    """F9: constant casts fold as DataFusion casts (truncating), not rounded."""
    for value, truncated in [("2.7", 2), ("-2.5", -2), ("CAST(2.5 AS DOUBLE)", 2)]:
        sql = f"SELECT CAST({value} AS BIGINT) AS c FROM j"
        assert positional(con.datafusion.sql(sql).to_arrow_table()) == [(truncated,), (truncated,)]
        assert proves(sql, f"c = {truncated}")
        assert not proves(sql, f"c = {truncated + (1 if truncated > 0 else -1)}")


@pytest.mark.parametrize(
    ("value", "kind"),
    [
        ("' 12'", "BIGINT"),
        ("'1_000'", "BIGINT"),
        ("' 1.5'", "DOUBLE"),
        ("' 2024-01-01'", "TIMESTAMP"),
        ("'2024-01-01 '", "DATE"),
    ],
)
def test_constant_strings_datafusion_cannot_cast_are_refused(con, value, kind):
    """S8: strings with spaces or `_` fail DataFusion's cast at run time, so
    the checker refuses them instead of reading them its own way."""
    sql = f"SELECT CAST({value} AS {kind}) AS c FROM j"
    with pytest.raises(Exception, match="Cannot cast|Error parsing|cast"):
        con.datafusion.sql(sql).to_arrow_table()
    with pytest.raises(ValueError, match="cannot (cast|parse)"):
        sv.verify(sql, tables={"j": {"a": "int64"}})
