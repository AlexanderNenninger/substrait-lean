"""A double divided by an integer, as a double, does not overflow to `±inf`
(#1787): a zero divisor raises first, and any other is at least 1 in size, so
the quotient is at most the dividend (`FloatCode.fdiv_ofInt_fin`,
`Expr.mayInfBin_sound`). The checker assumes no overflow there, and the
written SQL holds no check against `±inf`."""

import sys

import ibis
import pytest

import sverify as sv
from sverify.engine import written_plan
from sverify.sql import to_sql
from sverify_duckdb.dialect import DUCKDB

pytestmark = pytest.mark.backend("duckdb")

T = ibis.table({"x": "float64", "n": "int64"}, name="t")
Q = T.select(r=T.x / T.n.cast("float64"))


def test_no_overflow_is_assumed_and_none_is_checked():
    report = sv.verify(Q)
    assert not [i for i in report.assumed if i.kind == "overflow to infinity"]
    assert report.internal_plan is not None
    sql = to_sql(written_plan(report.internal_plan), DUCKDB)
    assert "overflow to infinity" not in sql
    assert "division by zero" in sql


def test_the_largest_double_over_one_stays_finite_and_zero_raises():
    import duckdb

    report = sv.verify(Q)
    assert report.internal_plan is not None
    sql = to_sql(written_plan(report.internal_plan), DUCKDB)
    big = sys.float_info.max
    con = duckdb.connect()
    con.execute("CREATE TABLE t(x DOUBLE, n BIGINT)")
    con.executemany("INSERT INTO t VALUES (?, ?)", [(big, 1), (-big, 2), (3.0, -7)])
    got = sorted(r for (r,) in con.execute(sql).fetchall())
    assert got == sorted([big, -big / 2, 3.0 / -7])
    con.execute("INSERT INTO t VALUES (1.0, 0)")
    with pytest.raises(duckdb.Error, match="division by zero"):
        con.execute(sql).fetchall()
