"""#693: Ibis `//` floors and `%` truncates, so a plan that uses both on the
same operands gets a hint; the guide's table is what the engines compute."""

from __future__ import annotations

import ibis
import pyarrow as pa
from ibis import _

import sverify as sv
from sverify.contracts import Semantics

T = ibis.table({"x": "int64", "d": "int64"}, name="t")
REQUIRES = {"t": [_.x.between(-1000, 1000), _.d.between(1, 10)]}


def hints(expr, semantics: Semantics = "reference"):
    return sv.verify(expr, requires=REQUIRES, semantics=semantics)._hints


def test_floor_division_and_modulus_on_the_same_operands_get_a_hint():
    [hint] = [h for h in hints(T.select(q=T.x // 2, r=T.x % 2)) if "floors" in h]
    assert "(x // 2) * 2 + x % 2 == x" in hint
    assert "Integer division in Ibis and SQL" in hint


def test_the_hint_is_for_the_pair_only():
    assert not hints(T.select(q=T.x // 2))
    assert not hints(T.select(r=T.x % 2))
    assert not hints(T.select(q=T.x // 2, r=T.x % 3))
    assert not hints(T.select(q=T.x // T.d, r=T.x % 2))


def test_the_hint_names_columns_and_skips_polars_semantics():
    assert any("(x // d) * d + x % d == x" in h for h in hints(T.select(q=T.x // T.d, r=T.x % T.d)))
    assert not hints(T.select(q=T.x // 2, r=T.x % 2), semantics="polars")


def test_sql_does_not_get_the_hint():
    t = ibis.table({"x": "int64"}, name="t")
    report = sv.verify(
        "SELECT x // 2 AS q, x % 2 AS r FROM t",
        tables={"t": t},
        requires={"t": ["x BETWEEN -1000 AND 1000"]},
    )
    assert not report._hints


def test_the_guides_table():
    con = sv.connect()
    con.put("t", pa.table({"x": pa.array([-7], pa.int64())}))
    t = con.table("t")
    req = {"t": [_.x.between(-1000, 1000)]}

    def row(rep, engine="duckdb"):
        [r] = rep.run(con, engine).to_pylist()
        return r["q"], r["r"]

    ibis_pair = t.select(q=t.x // 2, r=t.x % 2)
    assert row(sv.verify(ibis_pair, requires=req)) == (-4, -1)
    assert row(sv.verify(ibis_pair, requires=req, semantics="duckdb")) == (-4, -1)
    assert row(sv.verify(ibis_pair, requires=req, semantics="polars"), "polars") == (-4, 1)
    sql = sv.verify(
        "SELECT x // 2 AS q, x % 2 AS r FROM t",
        tables={"t": t},
        requires={"t": ["x BETWEEN -1000 AND 1000"]},
    )
    assert row(sql) == (-3, -1)
