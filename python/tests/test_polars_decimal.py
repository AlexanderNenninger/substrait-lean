"""Polars runs decimal plans as the reference computes them (#27).

Each decimal operation's written plan runs on Polars and on DuckDB, and both
give `Rel.eval`'s rows: decimals exactly, at their scale, doubles as Lean
prints them. Where Polars's own choice differs from the reference's
(polars-decimal-arith, polars-decimal-casts), these cases are the ones that
tell them apart: halves, a product's scale, an `AVG`'s rounding.
"""

import json
from decimal import Decimal as D

import ibis
import polars as pl
import pyarrow as pa
import pytest

from sverify import _polars_shims as shims
from sverify import polars_engine
from sverify.engine import connect, put_table, run_plan, substrait_json, written_plan
from sverify.ibis_substrait import to_substrait_json
from sverify.testing import inline_tables, lean_values

TABLES = {
    "t": pa.table(
        {
            "a": pa.array(
                [D("12.35"), D("-0.05"), D("-12.35"), None, D("0.25")], pa.decimal128(10, 2)
            ),
            "b": pa.array(
                [D("1.5"), D("2.5"), D("-3.5"), D("3.0"), D("-0.5")], pa.decimal128(5, 1)
            ),
            "c": pa.array(
                [D("12.350"), D("0.001"), D("-12.345"), D("1.000"), None], pa.decimal128(7, 3)
            ),
            "i": pa.array([3, -7, 2, 0, None], pa.int64()),
            "f": pa.array([0.125, -2.675, 0.145, 2.5, 0.625], pa.float64()),
        }
    ),  # fmt: skip
    "g": pa.table(
        {
            "k": pa.array([1, 1, 1, 2, 2, 3, 4, 4, 4, 4], pa.int64()),
            "x": pa.array(
                [
                    D("0.01"),
                    D("0.01"),
                    D("0.00"),
                    D("-0.05"),
                    None,
                    None,
                    D("0.01"),
                    D("0.00"),
                    D("0.00"),
                    D("0.00"),
                ],
                pa.decimal128(10, 2),
            ),
        }
    ),  # fmt: skip
    "w": pa.table({"x": pa.array([D("9" * 19 + ".00"), D("1.00")], pa.decimal128(21, 2))}),
}
ROWS = {name: [tuple(r.values()) for r in t.to_pylist()] for name, t in TABLES.items()}
T = ibis.table({"a": "decimal(10,2)", "b": "decimal(5,1)", "c": "decimal(7,3)",
                "i": "int64", "f": "float64"}, name="t")  # fmt: skip
G = ibis.table({"k": "int64", "x": "decimal(10,2)"}, name="g")

CASES: dict[str, str | ibis.Table] = {
    # Exact, at the larger scale (`+`, `-`) and the sum of the scales (`×`):
    # Polars's product would round to the larger scale, half to even.
    "add": "SELECT a + b AS r FROM t",
    "add of scales 2 and 3": "SELECT a + c AS r FROM t",
    "subtract": "SELECT a - b AS r FROM t",
    "multiply": "SELECT a * b AS r FROM t",
    "multiply of scales 2 and 3": "SELECT a * c AS r FROM t",
    "multiply by an integer": "SELECT a * i AS r FROM t",
    "multiply three": "SELECT a * b * c AS r FROM t",
    "add an integer": "SELECT a + i AS r FROM t",
    "negate": "SELECT -a AS r FROM t",
    "abs": T.select(r=T.a.abs()),
    # Compared exactly, across scales and with integers.
    "greater": "SELECT a > b AS r FROM t",
    "equal across scales": "SELECT a = c AS r, a < c AS s FROM t",
    "compare with an integer": "SELECT a > i AS r, a = 0 AS s FROM t",
    "compare with a literal": "SELECT a = CAST('12.35' AS DECIMAL(10,2)) AS r FROM t",
    "filter": "SELECT a FROM t WHERE a * b > 1",
    # Casts: a smaller scale rounds half away from zero (Polars: to even),
    # an integer truncates, a double is `round(x · 10ˢ)` in doubles.
    "to a smaller scale": T.select(r=T.a.cast("decimal(10, 1)"), s=T.c.cast("decimal(7, 2)")),
    "to a larger scale": T.select(r=T.a.cast("decimal(12, 4)")),
    "to an integer": T.select(r=T.a.cast("int64"), s=T.c.cast("int64")),
    "integer to decimal": "SELECT CAST(i AS DECIMAL(10,2)) AS r FROM t",
    "to a double": "SELECT CAST(a AS DOUBLE) AS r, CAST(c AS DOUBLE) AS s FROM t",
    "double to decimal": (
        "SELECT CAST(f AS DECIMAL(10,2)) AS r, CAST(f AS DECIMAL(10,1)) AS s FROM t"
    ),
    # One scale: the integer path.
    "case": "SELECT CASE WHEN i > 0 THEN a ELSE -a END AS r FROM t",
    "coalesce": T.select(r=T.a.fill_null(0) + T.b),
    "greatest": "SELECT greatest(a, CAST(1 AS DECIMAL(10,2))) AS r FROM t",
    # Aggregates: `SUM` exact, `AVG` at scale + 4, half away from zero.
    "sum min max": "SELECT sum(a) AS s, min(a) AS lo, max(c) AS hi, count(a) AS n FROM t",
    "sum of a product": "SELECT sum(a * b) AS s FROM t",
    "grouped": G.group_by("k").aggregate(
        v=G.x.mean(), s=G.x.sum(), n=G.x.count(), lo=G.x.min(), hi=G.x.max()
    ),
    "avg of everything": G.aggregate(v=G.x.mean()),
    "sum distinct": "SELECT sum(DISTINCT x) AS s FROM g",
    # Windows: `SUM` and `AVG` (the frame's `SUM` by its `COUNT`).
    "avg over a window": G.select("k", "x", v=G.x.mean().over(group_by="k")),
    "running sum": G.select(
        "k", "x", s=G.x.sum().over(ibis.window(group_by="k", order_by="x", preceding=None))
    ),
    "min over a window": G.select("k", "x", lo=G.x.min().over(group_by="k")),
}


@pytest.fixture(scope="module")
def con():
    c = connect()
    for name, t in TABLES.items():
        put_table(c, name, t)
    return c


def plan_of(con, query: str | ibis.Table) -> str:
    return (
        substrait_json(con, query, semantics="duckdb")
        if isinstance(query, str)
        else to_substrait_json(query)
    )


def canonical(rows: list[tuple]) -> list[tuple]:
    """Decimals at their scale, doubles to the 6 places Lean prints them."""

    def v(x: object) -> object:
        if isinstance(x, D):
            return str(x)
        return round(x, 6) if isinstance(x, float) else x

    return sorted((tuple(v(x) for x in r) for r in rows), key=repr)


def engine_rows(con, plan: str, engine: str) -> list[tuple]:
    out = run_plan(con, written_plan(plan), engine)
    return canonical([tuple(r.values()) for r in out.to_pylist()])


@pytest.mark.parametrize("label", list(CASES))
def test_polars_runs_decimal_plans_as_the_reference(con, label):
    plan = plan_of(con, CASES[label])
    lean = canonical(lean_values(json.dumps(inline_tables(json.loads(plan), ROWS))))
    assert engine_rows(con, plan, "polars") == lean
    assert engine_rows(con, plan, "duckdb") == lean


def test_the_cases_tell_polars_choices_apart():
    """Natively, Polars rounds these halves to even and a product to the
    larger scale (polars-decimal-arith, polars-decimal-casts): the cases
    above would fail without the shims."""
    a = pl.Series([D("12.35"), D("-0.05"), D("0.25")], dtype=pl.Decimal(10, 2))
    assert a.cast(pl.Decimal(10, 1)).to_list() == [D("12.4"), D("-0.0"), D("0.2")]
    assert (a * pl.Series([D("1.5"), D("2.5"), D("-0.5")], dtype=pl.Decimal(5, 1))).to_list() == [
        D("18.52"), D("-0.12"), D("-0.12")
    ]  # fmt: skip
    assert pl.Series([0.625]).cast(pl.Decimal(10, 2)).to_list() == [D("0.62")]
    assert pl.Series([D("0.01"), D("0.00")], dtype=pl.Decimal(10, 2)).mean() == 0.005


@pytest.mark.parametrize(
    ("u", "k", "expected"),
    [(125, 1, 13), (-125, 1, -13), (135, 1, 14), (124, 1, 12), (-5, 1, -1), (4, 1, 0),
     (250, 2, 3), (-250, 2, -3), (10**38 - 1, 38, 1), (-(10**38 - 1), 1, -(10**37))],
)  # fmt: skip
def test_rescale_rounds_half_away_from_zero(u, k, expected):
    s = pl.DataFrame({"u": [u]}, schema={"u": pl.Int128})
    assert s.select(shims.decimal_round_half_away(pl.col("u"), k)).item() == expected


@pytest.mark.parametrize(
    ("x", "n", "k"),
    [(20000, 3, 0), (-20000, 3, 0), (5, 2, 0), (-5, 2, 0), (1, -2, 4), (-1, 32, 4),
     (10**37, 7, 0), (10**33 + 1, 3, 4), (2**63, -(2**63), 18), (123, 2**63 - 1, 18)],
)  # fmt: skip
def test_division_rounds_half_away_from_zero(x, n, k):
    """`roundDivInt? (x · 10ᵏ) n`, without leaving 128 bits on the way."""
    df = pl.DataFrame({"x": [x], "n": [n]}, schema={"x": pl.Int128, "n": pl.Int128})
    q, bad = shims.decimal_div_half_away(pl.col("x"), pl.col("n"), k)
    got, flagged = df.select(q.alias("q"), bad.alias("b")).row(0)
    num, den = abs(x) * 10**k, abs(n)
    expected = (2 * num + den) // (2 * den) * (1 if (x < 0) == (n < 0) else -1)
    assert not flagged
    assert got == expected


@pytest.mark.parametrize(
    ("sql", "issue"),
    [
        # 12.35 needs four digits.
        ("SELECT CAST(a AS DECIMAL(3,2)) AS r FROM t", polars_engine.IntegerOverflow),
        ("SELECT CAST(i AS DECIMAL(2,2)) AS r FROM t", polars_engine.IntegerOverflow),
        ("SELECT CAST(f * 1e30 AS DECIMAL(38,10)) AS r FROM t", polars_engine.IntegerOverflow),
        ("SELECT CAST(f / 0.0 AS DECIMAL(10,2)) AS r FROM t", polars_engine.RuntimeIssue),
    ],
)
def test_overflow_raises_where_the_reference_does(con, sql, issue):
    plan = written_plan(plan_of(con, sql))
    with pytest.raises(issue):
        run_plan(con, plan, "polars")


def test_a_product_past_38_digits_raises(con):
    """The product is computed only where it fits the result's precision, so
    its `Int128` never wraps: (10¹⁹ − 1)² at scale 4 has 42 digits."""
    plan = written_plan(plan_of(con, "SELECT x * x AS r FROM w"))
    with pytest.raises(polars_engine.IntegerOverflow, match="multiply leaves DECIMAL"):
        run_plan(con, plan, "polars")
