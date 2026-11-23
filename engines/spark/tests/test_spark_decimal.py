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
from test_decimal import TABLES, G, T, lean

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
    # An AVG of decimals: the exact quotient at scale + 4, half away from zero.
    G.group_by("k").aggregate(v=G.x.mean(), s=G.x.sum(), n=G.x.count()).order_by("k"),
    G.aggregate(v=G.x.mean()),
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
    with pytest.raises(Unsupported, match=r"AVG of decimals\) to DECIMAL\(38, 10\)"):
        SPARK.decimal_div("a", "b", 6, Dec(38, 10))
    with pytest.raises(Unsupported, match=r"DECIMAL\(20, 2\) on Spark"):
        SPARK.decimal_cast("f", Dec(20, 2), "float")


def test_a_comparison_whose_common_type_passes_38_digits_is_refused() -> None:
    """Spark rounds the operand of the higher scale there (spark-decimal-compare-scale):
    `2 = 1.5` of DECIMAL(38, 0) and DECIMAL(38, 10) is true. A pair that fits is exact."""
    with pytest.raises(Unsupported, match=r"has 48 digits.*spark-decimal-compare-scale"):
        SPARK.decimal_compare("eq", "a", Dec(38, 0), "b", Dec(38, 10))
    with pytest.raises(Unsupported, match=r"DECIMAL\(20, 0\) with DECIMAL\(38, 20\)"):
        SPARK.decimal_compare("lt", "a", "int", "b", Dec(38, 20))
    assert SPARK.decimal_compare("eq", "a", Dec(28, 0), "b", Dec(38, 10))  # 28 + 10 = 38
    assert SPARK.decimal_compare("lt", "a", "int", "b", Dec(38, 10))  # a BIGINT: 28 + 10
    assert SPARK.decimal_compare("eq", "a", Dec(38, 10), "b", Dec(38, 10))  # one scale


def test_greatest_least_in_and_join_keys_reach_the_same_check() -> None:
    """They bring the two decimals to the same common type (`GREATEST` of `1.50` and
    `1.5000000001` is `1.50` on Spark), and a `NULL` literal has no kind to check."""
    for what in ("GREATEST", "LEAST"):
        with pytest.raises(
            Unsupported, match=rf"{what} of DECIMAL\(38, 2\) with DECIMAL\(38, 10\)"
        ):
            SPARK.decimal_pair(what, Dec(38, 2), Dec(38, 10))
    assert SPARK.decimal_pair("GREATEST", Dec(10, 2), Dec(10, 4)) is None  # 8 + 4: fits
    assert SPARK.decimal_pair("comparison", Dec(38, 0), None) is None  # `x = NULL`
    t = ibis.table({"a": "decimal(38, 0)", "b": "decimal(38, 10)"}, name="t")
    u = ibis.table({"b": "decimal(38, 10)"}, name="u")
    # A join key and a filter reach it through `eq`. Ibis writes an explicit cast to the
    # common type for `GREATEST` and `IN`, which is `CAST(a AS DECIMAL(38, 10))` in the
    # SQL (an overflow, as the reference's cast); a plan or a lift that states the two
    # kinds reaches `decimal_pair` as above.
    for expr in (t.join(u, t.a == u.b), t.filter(t.a == t.b)):
        with pytest.raises(Unsupported, match="spark-decimal-compare-scale"):
            to_sql(written_plan(to_substrait_json(expr)), SPARK)


def _round_div(u: int, n: int) -> int | None:
    """`roundDivInt?`: `u / n` rounded half away from zero, None for `n = 0`."""
    if n == 0:
        return None
    q = (2 * abs(u) + abs(n)) // (2 * abs(n))
    return q if (u < 0) == (n < 0) else -q


#: Unscaled dividends and divisors: ties both ways, signs, the bounds of 64
#: bits, and a remainder just below and above a half.
UNITS = [0, 1, -1, 5, -5, 25, 15, -15, 999_999, 10**17 - 1, -(10**17) + 3, 2**62 + 1]
DIVISORS = [1, -1, 2, -2, 3, 7, -8, 2, 0, 2**63 - 1, -(2**63), 10**18 + 1]


@pytest.mark.parametrize(
    ("p", "s", "k"),
    [
        (10, 2, Dec(14, 6)),
        (20, 0, Dec(24, 4)),
        (30, 8, Dec(34, 12)),
        (18, 3, Dec(38, 6)),
        (21, 5, Dec(37, 12)),
        (6, 0, Dec(6, 0)),
    ],
)
def test_decimal_division_is_the_exact_quotient_rounded_half_away(p: int, s: int, k: Dec) -> None:
    """`decimal_div` on Spark is `roundDivInt?` of the unscaled values at
    every divisor, where Spark's own `/` rounds at a scale of its own first
    (spark-decimal-arith)."""
    us = [u for u in UNITS if abs(u) < 10**p] + [10**p - 1, -(10**p) + 1]
    # A quotient past `k` raises on Spark and in the reference, and would fail
    # the whole query here.
    fits = [(u, n, _round_div(u * 10 ** (k.s - s), n)) for u in us for n in DIVISORS]
    pairs = [(u, n, w) for u, n, w in fits if w is None or abs(w) < 10**k.p]
    data = pa.table(
        {
            "a": pa.array([D(f"{u}E-{s}") for u, _, _ in pairs], pa.decimal128(p, s)),
            "n": pa.array([n for _, n, _ in pairs], pa.int64()),
        }
    )
    from sverify_spark import engine as spark_engine

    spark = session()
    spark_engine.put_tables({"dd": data}, spark)
    sql = f"SELECT {SPARK.decimal_div(f'CAST(a AS DECIMAL({p}, {s}))', 'n', s, k)} AS q FROM dd"
    got = [r.q for r in spark.sql(sql).collect()]
    for (u, n, want), g in zip(pairs, got, strict=True):
        assert g == (None if want is None else D(f"{want}E-{k.s}")), (u, n, g, want)


def test_a_product_after_a_wide_integer_decimal_cast_is_exact_on_spark() -> None:
    """#1876 (ruling 177, W2): `CAST(i AS DECIMAL(38,0)) * j` above 2⁶³ is the
    exact product at 38 digits on Spark, typed `DECIMAL(38, 0)`, where the cast
    used to be dropped and the product run at 64 bits."""
    from sverify_spark import engine as spark_engine

    t = ibis.table({"i": "int64", "j": "int64"}, name="w")
    q = t.select(p=t.i.cast("decimal(38, 0)") * t.j)
    plan = written_plan(json.dumps(json.loads(to_substrait_json(q))))
    rows = pa.table({"i": [2**40, 3], "j": [2**30, -4]})
    out = spark_engine.run(plan, {"w": rows}, session())
    assert pa.types.is_decimal(out.schema.field("p").type)
    assert [int(v) for v in out.column("p").to_pylist()] == [2**70, -12]


def test_a_double_to_decimal_cast_is_not_spark_native() -> None:
    """Ruling 278: Spark's own cast of a double to a decimal rounds the double's
    shortest text (1.005 → 1.01), the reference the product `1.005 · 100`, just
    below 100.5 (→ 1.00). The generated lowering's `ftod` entry is native, so the
    writer keeps the dialect's `decimal_cast` (`ROUND(x · 10ˢ)` in doubles) and
    never Spark's cast of the double."""
    from sverify_spark import engine as spark_engine

    v = ibis.table({"x": "float64"}, name="v")
    plan = to_substrait_json(v.select(r=v.x.cast("decimal(3, 2)")))
    sql = to_sql(plan, "spark")
    assert "ROUND(" in sql, sql
    assert "CAST(`x` AS DECIMAL(3,2))" not in sql.replace(" ", ""), sql
    tables = {"v": pa.table({"x": pa.array([1.005, -1.005, 2.675], pa.float64())})}
    out = spark_engine.run(written_plan(plan), tables, session())
    assert [str(r["r"]) for r in out.to_pylist()] == ["1.00", "-1.00", "2.68"]
