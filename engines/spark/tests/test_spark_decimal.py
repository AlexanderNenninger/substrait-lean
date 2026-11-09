"""Decimals on Spark (#27, #739): the reference's decimal cases of
`test_decimal.py`, run on a local Spark session and compared with `Rel.eval`,
and SP-1's negation past 34 digits.

Spark's decimal types are the reference's up to 38 digits; past them Spark
cuts the scale (spark-decimal-arith), and `-x` rounds past 34 significant
digits (spark-decimal-negate, SP-1). `sverify_spark.dialect` writes `0 - x`
where that is exact and refuses the rest, naming the construct.
"""

from __future__ import annotations

import json
from decimal import Decimal as D

import ibis
import pyarrow as pa
import pytest

from spark_session import session
from sverify.engine import connect, put_table, substrait_json, written_plan
from sverify.ibis_substrait import to_substrait_json
from sverify.sql import Unsupported, to_sql
from sverify.sql.core import Dec
from sverify.testing import inline_tables, lean_values
from sverify_spark.dialect import SPARK
from test_decimal import TABLES, T, lean

pytestmark = pytest.mark.backend("spark")


def _plan(con, query: str | ibis.Table) -> dict:
    return json.loads(
        substrait_json(con, query, semantics="duckdb")
        if isinstance(query, str)
        else to_substrait_json(query)
    )


def spark_rows(con, query: str | ibis.Table) -> list[tuple]:
    """The query's rows on Spark, decimals printed at their scale."""
    from sverify_spark import engine as spark_engine

    out = spark_engine.run(written_plan(json.dumps(_plan(con, query))), TABLES, session())
    return [tuple(str(v) if isinstance(v, D) else v for v in r.values()) for r in out.to_pylist()]


CASES = [
    "SELECT a + b AS r FROM t",
    "SELECT a - b AS r FROM t",
    "SELECT a * b AS r FROM t",
    "SELECT a * i AS r FROM t",
    "SELECT -a AS r FROM t",
    T.select(r=T.a.abs()),
    "SELECT a > b AS r FROM t",
    "SELECT a = CAST('12.35' AS DECIMAL(10,2)) AS r FROM t",
    T.select(r=T.a.cast("decimal(10, 1)")),
    T.select(r=T.a.cast("int64")),
    "SELECT CAST(i AS DECIMAL(10,2)) AS r FROM t",
    "SELECT CAST(a AS DOUBLE) AS r FROM t",
    # `round(x · 10ˢ)` in doubles: -2.675 · 100 is -267.5, 0.145 · 100 just
    # below 14.5, where Spark's own cast reads "0.145" and gives 0.15.
    "SELECT CAST(f AS DECIMAL(10,2)) AS r FROM t",
    "SELECT sum(a) AS s, min(a) AS lo, max(b) AS hi FROM t",
]


@pytest.fixture(scope="module")
def con():
    c = connect()
    for name, t in TABLES.items():
        put_table(c, name, t)
    return c


@pytest.mark.parametrize("query", CASES, ids=lambda q: q if isinstance(q, str) else "ibis")
def test_spark_computes_the_reference(con, query) -> None:
    assert sorted(spark_rows(con, query), key=repr) == sorted(lean(con, query), key=repr)


#: Unscaled 38-digit values past SP-1's 34 digits, a tie among them.
WIDE = [
    12345678901234567890123456789012345678,
    -88926501604876820962013312199159205000,
    99999999999999999999999999999999999999,
]


@pytest.mark.parametrize(("p", "s"), [(38, 0), (38, 6), (37, 20), (35, 3)])
def test_negation_past_34_digits_is_exact(p: int, s: int) -> None:
    """SP-1: Spark's `-x` gives -12345678901234567890123456789012350000 for
    the first value; the written `0 - x` keeps every digit."""
    from sverify_spark import engine as spark_engine

    # `copy_negate` and `copy_abs` are exact, where Python's 28-digit context rounds.
    units = [int(str(u).lstrip("-")[:p]) * (1 if u > 0 else -1) for u in WIDE]
    xs = [D(f"{u}E-{s}") for u in units]
    xs += [x.copy_negate() for x in xs]
    w = ibis.table({"x": f"decimal({p}, {s})"}, name="w")
    planned = written_plan(to_substrait_json(w.select(n=-w.x, a=w.x.abs())))
    data = {"w": pa.table({"x": pa.array(xs, pa.decimal128(p, s))})}
    out = spark_engine.run(planned, data, session()).to_pylist()
    assert [r["n"] for r in out] == [x.copy_negate() for x in xs]
    assert [r["a"] for r in out] == [x.copy_abs() for x in xs]
    rows = lean_values(json.dumps(inline_tables(json.loads(planned), {"w": [(x,) for x in xs]})))
    assert [r[0] for r in rows] == [x.copy_negate() for x in xs]


def test_refusals_name_the_construct() -> None:
    k = Dec(38, 10)
    with pytest.raises(Unsupported, match=r"negation of a DECIMAL\(38, 10\).*SP-1"):
        SPARK.decimal_neg("x", k)
    with pytest.raises(Unsupported, match=r"DECIMAL\(39, 20\) has more than 38 digits"):
        SPARK.decimal_arith("*", "a", "b", 10, Dec(38, 20), (Dec(19, 10), Dec(19, 10)))
    # At a scale of 6 or less Spark keeps every decimal place.
    assert SPARK.decimal_arith("+", "a", "b", 6, Dec(38, 6), (Dec(38, 6), Dec(38, 6)))
    with pytest.raises(Unsupported, match="AVG of decimals"):
        SPARK.decimal_div("a", "b", 2, Dec(14, 6))
    with pytest.raises(Unsupported, match=r"DECIMAL\(20, 2\) on Spark"):
        SPARK.decimal_cast("f", Dec(20, 2), "float")


def test_an_avg_of_decimals_is_refused_on_spark(con) -> None:
    g = ibis.table({"k": "int64", "x": "decimal(10,2)"}, name="g")
    with pytest.raises(Unsupported, match="AVG of decimals"):
        to_sql(written_plan(to_substrait_json(g.aggregate(v=g.x.mean()))), SPARK)
