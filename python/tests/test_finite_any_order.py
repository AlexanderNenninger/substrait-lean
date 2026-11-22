"""A double `SUM` or `AVG` no summation order overflows runs on DuckDB as
its plain sum, without the two-stage check against `±∞` (#1787 item 4,
rulings 238 and 242): its argument is bounded, its input has a `max_rows`
cap, and `Measure.finiteAnyOrder` holds (`Rel.marks_measure_finite`)."""

import ibis
import pyarrow as pa
import pytest
from ibis import _

import sverify as sv
from sverify.sql import to_sql
from sverify_duckdb.dialect import DUCKDB

pytestmark = pytest.mark.backend("duckdb")

T = ibis.table({"k": "int64", "x": "float64"}, name="t")
Q = T.group_by("k").agg(s=T.x.sum(), a=T.x.mean())
CAPPED = {"t": [_.x.between(0, 1e6), sv.max_rows(10**6)]}


def _report(requires: dict) -> sv.Report:
    return sv.verify(Q, requires=requires)


def _measure_slots(report: sv.Report) -> set[int]:
    """The marked measure slots (`1 + i`) of the plan's aggregate."""
    plan = report._plan_to_run("translated", checked=True, engine="duckdb")
    marks = report._marks_of(plan)
    found: set[int] = set()

    def walk(m: dict) -> None:
        if m.get("node") == "Aggregate":
            found.update(k for k in m.get("slots", ()) if k > 0)
        for x in m.get("inputs", ()):
            walk(x)

    if marks is not None:
        walk(marks)
    return found


def _sql(report: sv.Report) -> str:
    plan = report._plan_to_run("translated", checked=True, engine="duckdb")
    return to_sql(plan, DUCKDB, unchecked=report._marks_of(plan))


def _con(xs: list[float], ks: list[int] | None = None):
    con = sv.connect()
    ks = ks or [i % 3 for i in range(len(xs))]
    con.put("t", pa.table({"k": pa.array(ks, pa.int64()), "x": pa.array(xs, pa.float64())}))
    return con


def test_a_capped_bounded_sum_and_mean_are_marked_and_written_plainly():
    report = _report(CAPPED)
    assert _measure_slots(report) == {1, 2}
    sql = _sql(report)
    assert "overflow to infinity" not in sql and "WITH" not in sql


def test_without_a_row_cap_the_measures_keep_both_stages():
    report = _report({"t": [_.x.between(0, 1e6)]})
    assert _measure_slots(report) == set()
    assert "overflow to infinity" in _sql(report)


def test_the_boundary_where_crbound_passes_and_the_margin_does_not():
    """`10⁸ · 10³⁰⁰` lies under the largest double, so the reference's sum,
    rounded once, is finite (`Measure.mayInf` is false). Twice that does not:
    an order that rounds at every step could overflow, so the measures keep
    their checks (ruling 238)."""
    report = _report({"t": [_.x.between(0, 1e300), sv.max_rows(10**8)]})
    assert not any(i.kind == "overflow to infinity" for i in report.issues)
    assert _measure_slots(report) == set()


@pytest.mark.parametrize(
    "xs",
    [
        [1.5, 2.0, 0.25, 7.0, 3.0, 9.5],
        [-0.0, -0.0, -0.0],  # a group of -0.0 only (ruling 242, K10)
        [-0.0, 0.0, 2.5, -0.0, 1.0, 0.0],  # mixed zeros under x >= 0
        [],
    ],
    ids=["positive", "negative zeros", "mixed zeros", "empty"],
)
def test_the_marked_run_gives_the_checked_rows(xs):
    report = _report(CAPPED)
    marked = report.run(_con(xs), "duckdb")
    checked = report.run(_con(xs), "duckdb", check_requires=False)
    assert marked.sort_by("k").to_pylist() == checked.sort_by("k").to_pylist()
