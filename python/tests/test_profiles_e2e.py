"""#444's prototype, end to end: a plan verified under the reference runs on
DuckDB and on Polars by a reported route, and a plan verified under DuckDB's
profile reaches Polars only by the option-wise transfer check, or is refused
with the reason (`docs/core-semantics.md`, "Which plans run on an engine").

The second test waits for Lean's `Profile.duckdb` and `Profile.polars`
choice tables (`substrait-check --options`, steps 3a and 3c); it is an
expected failure until the checker reports them, and passes from then on.
"""

from __future__ import annotations

import ibis
import pyarrow as pa
import pytest
from ibis import _

import sverify as sv
from sverify import routes

ROWS = {
    "k": [1, 1, 1, 2, 2, None, None],
    "i": [-7, 2, 4, 3, -1, 5, 6],
    "x": [0.1, 0.2, 0.3, 1e-3, 1e3, 2.5, -2.5],
}


@pytest.fixture
def con() -> sv.engine.Connection:
    c = sv.connect()
    c.put("t", pa.table(ROWS))
    return c


def test_reference_plan_runs_on_duckdb_and_polars(con) -> None:
    """Integer SUM and AVG, a float aggregate within a tolerance, and a sort
    with its NULLs placed: verified once under the reference, run on both
    engines by the reference's translation, and equal up to the observation."""
    t = con.table("t")
    expr = (
        t.group_by("k")
        .aggregate(total=t.i.sum(), mean_i=t.i.mean(), mean_x=t.x.mean())
        .order_by(ibis.asc("k", nulls_first=True))
    )
    q = sv.equivalent(rows="sequence", floats=sv.within(rel=1e-12))
    report = sv.verify(
        expr,
        requires={"t": [_.i.between(-1000, 1000), _.x.between(-1e6, 1e6), sv.max_rows(1_000_000)]},
        ensures=[q, sv.unique("k"), sv.approx(_.mean_x <= 1e6)],
    )
    assert report.proved, str(report)
    assert report.observation == q

    results = {}
    for engine in ("duckdb", "polars"):
        results[engine] = report.run(con, engine, route="auto")
        route = report.routes[engine]
        assert route.kind == "reference", route
        assert route.profile == "reference"
        assert route.deterministic
    assert q.difference(results["duckdb"], results["polars"]) is None

    expected = pa.table(
        {
            "k": [None, 1, 2],
            "total": [11, -1, 2],
            "mean_i": [5.5, -1 / 3, 1.0],
            "mean_x": [0.0, 0.6 / 3, (1e-3 + 1e3) / 2],
        }
    )
    for engine, out in results.items():
        assert q.difference(out, expected) is None, engine
    assert "route on duckdb: reference" in str(report)


@pytest.mark.xfail(
    routes.choices("duckdb") is None or routes.choices("polars") is None,
    reason="Profile.duckdb and Profile.polars choice tables (#444 3a, 3c) not in the checker",
    strict=True,
)
def test_duckdb_plan_transfers_to_polars_or_is_refused(con) -> None:
    """A plan whose meaning is DuckDB's (`semantics="duckdb"`): `sqrt` of a
    negative is NaN there (`on_domain_error: NAN`), which the reference
    raises on, and `%` truncates, where Polars floors (polars-int-modulus).
    It runs natively on DuckDB; on Polars, only if the transfer check
    passes for every option its proof depends on."""
    t = con.table("t")
    report = sv.verify(
        "SELECT k, i % 3 AS m, sqrt(x) AS r FROM t",
        tables={"t": t},
        requires={"t": [_.i.between(-1000, 1000)]},
        semantics="duckdb",
    )
    assert report.proved, str(report)
    assert routes.choose(report, "duckdb").kind == "native"
    under_reference = sv.verify(
        "SELECT k, i % 3 AS m, sqrt(x) AS r FROM t",
        tables={"t": t},
        requires={"t": [_.i.between(-1000, 1000)]},
    )
    assert not under_reference.proved, "the plan must rely on a DuckDB value choice"

    route = routes.choose(report, "polars")
    if route.refused:
        assert route.failures, route.reason
        assert "transfer check fails on" in route.reason
        assert any(f["option"] == "division_type" for f in route.failures), route.failures
        with pytest.raises(routes.RouteError, match="refused on polars"):
            report.run(con, "polars", route="auto")
    else:
        assert route.kind in ("transfer", "recheck"), route
        q = sv.equivalent(zeros="canon")
        duck = report.run(con, "duckdb", route="auto")
        polars = report.run(con, "polars", route="auto")
        assert q.difference(duck, polars) is None
