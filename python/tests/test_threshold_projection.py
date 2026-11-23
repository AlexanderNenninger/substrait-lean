"""A projection that rounds, casts or compares a double (ruling 275, #1849).

#568's threshold rule refuses a filter, grouping key or sort on a double an
engine computes only within a bound. A projection that sends such a double
through a function that jumps (`floor`, a cast to an integer, `=`) decides a
value the same way: Polars divides by a constant through its reciprocal
(polars-scalar-divisor), so `49.0 / 49.0` is one ulp below `1` there, and
`floor` of it is `0`. These plans were PROVED and ran on Polars with the wrong
value; the route now refuses them where the double is not exact, and runs
them where it is (DuckDB's division is IEEE's). The frames have 2,000 rows, so
Polars's streaming engine takes the reciprocal kernel (a frame shorter than its
thread count divides exactly)."""

import ibis
import pyarrow as pa
import pytest
from ibis import _

import sverify as sv

ROWS = 2000
REQUIRES = {"t": [_.x.between(1, 100), sv.max_rows(10**6)]}

#: Each plan, with the reference's value of its one column.
JUMPS = {
    "floor of a quotient": (lambda t: t.x // 49.0, 1),
    "cast of a quotient to an integer": (lambda t: (t.x / 49.0).cast("int64"), 1),
    "comparison of a quotient": (lambda t: (t.x / 49.0) == 1.0, True),
}


def connection():
    con = sv.connect()
    con.put("t", pa.table({"x": [49.0] * ROWS}))
    return con


@pytest.mark.parametrize("name", JUMPS)
def test_a_jump_of_a_reciprocal_quotient_is_refused_on_polars(name):
    pytest.importorskip("polars")
    make, _want = JUMPS[name]
    con = connection()
    report = sv.verify(con.table("t").select(q=make(con.table("t"))), requires=REQUIRES)
    with pytest.raises(sv.errors.RouteError, match="rounds, casts or compares"):
        report.run(con, "polars")


@pytest.mark.parametrize("name", JUMPS)
def test_the_same_plan_runs_where_the_division_is_exact(name):
    make, want = JUMPS[name]
    con = connection()
    report = sv.verify(con.table("t").select(q=make(con.table("t"))), requires=REQUIRES)
    assert report.verdict == sv.Verdict.PROVED
    assert set(report.run(con, "duckdb").column("q").to_pylist()) == {want}


def test_a_precondition_away_from_the_threshold_lifts_the_refusal():
    """`rule_threshold`: `x / 49.0` within its bound of `[2.04, 4.09]` never meets `1`."""
    pytest.importorskip("polars")
    con = sv.connect()
    con.put("t", pa.table({"x": [100.0 + i % 100 for i in range(ROWS)]}))
    t = con.table("t")
    report = sv.verify(
        t.select(q=(t.x / 49.0) == 1.0), requires={"t": [_.x.between(100, 200), sv.max_rows(10**6)]}
    )
    assert set(report.run(con, "polars").column("q").to_pylist()) == {False}


@pytest.mark.parametrize(
    "make",
    [
        pytest.param(lambda t: t.x.sum().cast("int64"), id="cast(sum(x) AS BIGINT)"),
        pytest.param(lambda t: t.x.mean().round(), id="round(avg(x))"),
    ],
)
def test_a_jump_of_a_double_aggregate_is_refused_where_its_bound_is_positive(make):
    """A double `SUM` or `AVG` adds in the engine's order, within the plan's bound of
    the reference's correctly rounded value: an integer or rounded value of it is
    not decided by that bound."""
    t = ibis.table({"x": "float64"}, name="t")
    report = sv.verify(t.aggregate(q=make(t)), requires=REQUIRES)
    con = sv.connect()
    con.put("t", pa.table({"x": [0.1] * ROWS}))
    with pytest.raises(sv.errors.RouteError, match="rounds, casts or compares"):
        report.run(con, "duckdb")
