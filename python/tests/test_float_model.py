"""One model for doubles (#689) and a class for every verified route (#696).

Stating no observation, `sv.equivalent(floats="plan")` and the plan's own
bound are one observation, printed with the bound. A stated tolerance, of any
kind, and `floats="exact"` are checked against that bound at `verify`, on
each engine, with the reason in the report.
"""

from __future__ import annotations

import datetime as dt

import ibis
import pyarrow as pa
import pytest
from ibis import _

import sverify as sv
from sverify import routes
from sverify.errors import ExportError, RouteError
from sverify.observation import Observation, Within

pytest.importorskip("polars")

REQ = {"readings": [_.x.between(-1000, 1000), sv.max_rows(1000)]}


@pytest.fixture(scope="module")
def con():
    c = sv.connect()
    c.put("readings", pa.table({"k": [1, 2, 2], "x": [0.1, 0.2, 0.3]}))
    return c


def mean_x(con):
    r = con.table("readings")
    return r.group_by("k").aggregate(mean_x=r.x.mean())


def verify(con, ensures):
    return sv.verify(mean_x(con), requires=REQ, ensures=ensures, counterexamples=0)


# -- the three spellings of the default ---------------------------------------


def test_absent_plan_and_the_bound_are_one_observation(con) -> None:
    absent = verify(con, [])
    plan = verify(con, [sv.equivalent(floats="plan")])
    bound = routes.plan_bound(absent.epsilon)
    assert isinstance(bound, Within) and bound.abs and bound.abs > 0
    stated = verify(con, [sv.equivalent(floats=sv.within(abs=bound.abs))])

    assert absent.observation == plan.observation == sv.equivalent(floats="plan")
    assert absent.observation.bound == plan.observation.bound == bound
    assert str(absent.observation) == f"equivalent(floats=plan, ≤ {bound.abs:.1e})"
    assert f"observes: equivalent(floats=plan, ≤ {bound.abs:.1e})" in str(absent)
    assert absent.proved and plan.proved and stated.proved
    assert absent.floats_on == plan.floats_on == {}
    assert all(not ps for ps in stated.floats_on.values())
    assert f"the plan's bound on its doubles is {bound.abs:.1e}" in str(stated)

    runs = []
    for report in (absent, plan, stated):
        a, b = report.run(con, "duckdb"), report.run(con, "polars")
        assert report.observation.equal(a, b)
        runs.append({e: (r.cls, r.observation) for e, r in report.routes.items()})
    assert runs[0] == runs[1] == runs[2]
    assert {cls for cls, _ in runs[0].values()} == {"observed"}


def test_a_postcondition_on_a_double_is_held_under_a_stated_plan_bound(con) -> None:
    """`floats="plan"` stated holds a read column exact at run time, as the
    absent observation does, so the postcondition does not depend on what
    the observation ignores."""
    for ensures in ([_.mean_x <= 1000], [sv.equivalent(floats="plan"), _.mean_x <= 1000]):
        report = verify(con, ensures)
        assert [c.ignores for c in report.ensures if c.label.startswith("(")] == [()]


def test_plan_bound_equality_uses_the_bound() -> None:
    a = pa.table({"m": [1.0]})
    b = pa.table({"m": [1.0 + 1e-9]})
    assert not Observation(floats="plan").equal(a, b)
    assert Observation(floats="plan", bound=Within(abs=1e-8)).equal(a, b)
    assert Observation(floats="plan", bound=Within(abs=1e-8)) == Observation(floats="plan")


# -- tolerances and exact doubles at verify -----------------------------------


@pytest.mark.parametrize(
    "tol", [sv.within(abs=1e-12), sv.within(rel=1e-12), sv.within(ulps=4)], ids=str
)
def test_a_tolerance_below_the_bound_is_refused_at_verify(con, tol) -> None:
    report = verify(con, [sv.equivalent(floats=tol)])
    assert not report.proved
    assert report.floats_on and all(report.floats_on.values())
    text = str(report)
    assert f"observes: equivalent(floats={tol}); the plan's bound on its doubles is " in text
    assert "NOT met: no engine meets the tolerance" in text
    assert "or looser in ensures" in text
    with pytest.raises(RouteError, match="no engine meets the observation's tolerance"):
        report.run(con, "duckdb")
    with pytest.raises(ExportError, match="no engine meets"):
        report.to_substrait()


def test_exact_doubles_say_which_engines_give_them(con) -> None:
    mean = verify(con, [sv.equivalent(floats="exact")])
    assert not mean.proved
    assert "NOT met: no engine meets exact doubles" in str(mean)

    r = con.table("readings")
    doubled = sv.verify(
        r.select("k", y=r.x * 2), requires=REQ, ensures=[sv.equivalent(floats="exact")]
    )
    assert doubled.proved
    assert doubled.floats_on == {"duckdb": [], "polars": []}
    assert "duckdb, polars meet exact doubles" in str(doubled)


# -- what routes and the manifest print ---------------------------------------


def test_routes_and_the_manifest_agree_on_the_class(con) -> None:
    report = verify(con, [sv.equivalent(floats=sv.within(abs=1e-6))])
    report.run(con, "duckdb")
    report.run(con, "polars")
    assert {r.cls for r in report.routes.values()} == {"observed"}
    assert report.substrait_contract()["manifest"]["class"] == "observed"


def test_an_unsorted_plan_is_observed_as_a_multiset(con) -> None:
    report = verify(con, [])
    report.run(con, "polars")
    route = report.routes["polars"]
    assert route.observation is not None and route.observation.rows == "multiset"
    assert "rows='sequence'" not in str(route)


def test_an_observation_reprs_as_its_call() -> None:
    q = sv.equivalent(rows="sequence", floats=sv.within(abs=1e-6))
    assert repr(q) == str(q) == "equivalent(rows='sequence', floats=within(abs=1e-06))"


# -- a class for every verified route (#696) ----------------------------------


def test_a_window_over_a_key_has_a_class() -> None:
    """`api-critique/tasks/t7_engines.py`: a LAG over a unique key runs on
    both engines with route `reference`; its class is one of the four."""
    c = sv.connect()
    c.put(
        "events",
        pa.table(
            {
                "id": pa.array([1, 2, 3, 4], pa.int64()),
                "user": ["Ada", "bob", "Cy", "bob"],
                "ms": pa.array([-7, 5, 12, 9], pa.int64()),
                "ts": [dt.datetime(2026, 1, 1, h) for h in (1, 2, 3, 4)],
            }
        ),
    )
    e = c.table("events")
    req = {"events": [sv.unique("id"), _.id.notnull(), _.ms.between(-1000, 1000), _.user.notnull()]}
    window = ibis.window(group_by=e.user, order_by=e.id)
    report = sv.verify(e.mutate(prev=e.ms.lag().over(window)), requires=req)
    assert report.proved
    for engine in ("duckdb", "polars"):
        assert report.run(c, engine).num_rows == 4
        route = report.routes[engine]
        assert route.kind == "reference"
        assert route.cls in routes.CLASSES
        assert route.cls == "exact" and route.evidence == "tested"
