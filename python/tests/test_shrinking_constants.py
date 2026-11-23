"""A double divided by one of at least 1 in size, or multiplied by one of at
most 1, does not overflow to `±inf` (#1787): the result is at most the first
operand in size, and the largest double rounds to itself
(`FloatCode.fdiv_fin_of_one_le`, `FloatCode.fmul_fin_of_le_one`,
`BinFn.shrinks_fin`). The checker reads the sizes from bounds, so a literal
and a column whose contract bounds it both count."""

import sys

import ibis
import pytest
from ibis import _

import sverify as sv
from sverify.engine import written_plan
from sverify.sql import to_sql
from sverify_duckdb.dialect import DUCKDB

pytestmark = pytest.mark.backend("duckdb")

T = ibis.table({"x": "float64", "y": "float64"}, name="t")
INF = "overflow to infinity"


def _assumed(expr, requires=None):
    report = sv.verify(T.select(r=expr), requires=requires)
    return [i for i in report.assumed if i.kind == INF]


@pytest.mark.parametrize(
    "expr",
    [T.x / 100.0, T.x / -2.5, T.x / 1.0, T.x * 0.01, 0.5 * T.x, T.x * -1.0],
    ids=["div-100", "div-neg", "div-one", "mul-small", "mul-left", "mul-neg-one"],
)
def test_a_shrinking_constant_assumes_no_overflow(expr):
    assert not _assumed(expr)


@pytest.mark.parametrize(
    "expr",
    [T.x / 0.5, T.x * 2.0, T.x * 1.0000001, T.x / T.y, T.x * T.y],
    ids=["div-half", "mul-two", "mul-above-one", "div-col", "mul-col"],
)
def test_a_growing_or_unbounded_operand_still_assumes_overflow(expr):
    assert _assumed(expr)


def test_a_contract_range_counts():
    assert not _assumed(T.x / T.y, requires={"t": [_.y >= 1.0]})
    assert not _assumed(T.x * T.y, requires={"t": [_.y.between(-1.0, 1.0)]})
    assert _assumed(T.x / T.y, requires={"t": [_.y >= 0.5]})


def test_the_largest_double_stays_finite_on_duckdb():
    import duckdb

    big = sys.float_info.max
    con = duckdb.connect()
    con.execute("CREATE TABLE t(x DOUBLE, y DOUBLE)")
    con.executemany("INSERT INTO t VALUES (?, ?)", [(big, 1.0), (-big, -3.0)])
    for expr, want in [(T.x / 1.0, [big, -big]), (T.x * 0.5, [big / 2, -big / 2])]:
        report = sv.verify(T.select(r=expr))
        assert report.internal_plan is not None
        sql = to_sql(written_plan(report.internal_plan), DUCKDB)
        assert INF not in sql
        assert sorted(r for (r,) in con.execute(sql).fetchall()) == sorted(want)
