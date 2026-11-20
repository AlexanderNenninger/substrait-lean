"""An integer cast to `DECIMAL(p, 0)` is a decimal, whatever `p` (#1876,
ruling 177).

Until #1876 the frontend and the writers read a cast of an integer to a
`DECIMAL(p ≥ 19, 0)` as the integer itself, so a product after it was checked
and written at 64 bits where the plan computes it at `p` digits. Now no code
tells a scale-0 decimal of 19 or more digits from one of 18 or fewer: the
patterns below behave alike at p = 18, 19 and 38, and every engine computes
the product exactly, typed `DECIMAL(38, 0)`."""

from __future__ import annotations

from decimal import Decimal

import ibis
import pyarrow as pa
import pytest

import sverify as sv
from sverify.engine import plan_json_over, written_plan

T = ibis.table({"i": "int64", "j": "int64"}, name="t")
U = ibis.table({"k": "int64", "v": "int64"}, name="u")
WIDE = ibis.dtype("decimal(38, 0)")
BIG = (2**40, 2**30)  # a product of 2⁷⁰, above 2⁶³


def _con(rows: list[tuple[int | None, int | None]]) -> sv.engine.Connection:
    con = sv.connect()
    con.put("t", pa.table({"i": [r[0] for r in rows], "j": [r[1] for r in rows]}))
    con.put("u", pa.table({"k": [1, 2, 3], "v": [10, 20, 30]}))
    return con


@pytest.mark.parametrize("engine", ["duckdb", "polars"])
def test_a_product_after_the_cast_is_exact_at_38_digits(engine):
    """W2: `CAST(i AS DECIMAL(38,0)) * j` above 2⁶³ proves and runs exactly."""
    report = sv.verify(T.select(p=T.i.cast(WIDE) * T.j))
    assert report.verdict == sv.Verdict.PROVED, str(report)
    assert str(report.output["p"]) == "decimal(38, 0)"
    out = report.run(_con([BIG, (3, -4)]), engine)
    assert pa.types.is_decimal(out.schema.field("p").type)
    assert [int(v) for v in out.column("p").to_pylist()] == [2**70, -12]


def test_the_snowflake_writer_refuses_where_it_dropped_the_cast():
    """W2 on the public Snowflake writer, which computes no decimal as the
    reference does yet (#27): it refuses the product, where it wrote it at
    64 bits before #1876."""
    import json

    from sverify.sql import Unsupported, to_sql
    from sverify.sql.snowflake import SNOWFLAKE

    plan = json.loads(written_plan(plan_json_over({}, T.select(p=T.i.cast(WIDE) * T.j))))
    with pytest.raises(Unsupported, match="decimals"):
        to_sql(plan, SNOWFLAKE)


def _patterns(p: int) -> dict[str, ibis.Table]:
    d = ibis.dtype(f"decimal({p}, 0)")
    c = T.i.cast(d)
    return {
        "compare": T.filter(c > T.j).select("i"),
        "join key": T.join(U, c == U.k.cast(d)).select("i", "v"),
        "group key": T.group_by(g=c).aggregate(n=T.j.count()),
        "sort key": T.order_by([c.desc(), T.j]).select("i"),
        "case": T.select(r=ibis.ifelse(T.j > 0, c, T.j.cast(d))),
        "coalesce": T.select(r=ibis.coalesce(c, T.j.cast(d))),
        "constant": T.select(r=ibis.literal(7).cast(d) * T.j),
    }


def _rows(t: pa.Table) -> list[tuple]:
    """The rows as a multiset (a group's order is open), decimals as integers."""
    rows = [
        tuple(int(v) if isinstance(v, Decimal) else v for v in r.values()) for r in t.to_pylist()
    ]
    return sorted(rows, key=repr)


@pytest.mark.parametrize("name", list(_patterns(18)))
def test_scale_zero_decimals_behave_alike_at_18_19_and_38_digits(name):
    """W3: no rule tells `DECIMAL(19, 0)` or `DECIMAL(38, 0)` from
    `DECIMAL(18, 0)`: the same verdict and the same rows on DuckDB."""
    con = _con([(1, 5), (2, -1), (3, 3), (None, 2), (2, None)])
    got = {}
    for p in (18, 19, 38):
        report = sv.verify(_patterns(p)[name], on_inferred="warn")
        rows = _rows(report.run(con, "duckdb")) if report.verdict != sv.Verdict.UNPROVED else None
        got[p] = (report.verdict, rows)
    assert got[19] == got[18] and got[38] == got[18], got


@pytest.mark.parametrize(("p", "inferred"), [(18, True), (19, False), (38, False)])
def test_a_round_trip_through_the_decimal_proves(p, inferred):
    """W6, ruling 179: truncating a decimal back to an integer keeps its
    operand's bound, so `CAST(CAST(i AS DECIMAL(p, 0)) AS BIGINT)` proves. At
    18 digits a `BIGINT` needs a bound to fit the decimal at all, which is
    inferred; at 19 and 38 none is."""
    report = sv.verify(T.select(x=T.i.cast(f"decimal({p}, 0)").cast("int64")), on_inferred="warn")
    assert report.verdict == sv.Verdict.PROVED, str(report)
    assert bool(report._inferred) == inferred, report._inferred


def test_the_bound_is_the_operands():
    """The control: a product of two `BIGINT`s at 38 digits may leave 64 bits,
    so its cast back to `BIGINT` is not proved."""
    report = sv.verify(T.select(x=(T.i.cast(WIDE) * T.j).cast("int64")), on_inferred="warn")
    assert report.verdict == sv.Verdict.UNPROVED
    assert [i.kind for i in report.errors] == ["cast out of range"]


def test_a_scaled_decimal_of_a_bounded_integer_casts_back():
    """A `DECIMAL(20, 2)` of an integer in [-1000, 1000] truncates back into a
    `BIGINT`."""
    from ibis import _

    q = T.select(x=T.i.cast("decimal(20, 2)").cast("int64"))
    report = sv.verify(q, requires={"t": [_.i.between(-1000, 1000)]}, on_inferred="warn")
    assert report.verdict == sv.Verdict.PROVED, str(report)
