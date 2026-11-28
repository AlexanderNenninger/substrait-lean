"""What a rerun must reproduce (`q_det`, #444 D20): the engine's run-to-run
variation (the `"rerun"` column of its choices) must refine the observation
the consumer requires, or the route is refused."""

from __future__ import annotations

import ibis
import pyarrow as pa
import pytest
from deltalake import DeltaTable
from ibis import _

import sverify as sv
from _pipelines import make_orders
from sverify import routes
from sverify.errors import RouteError
from sverify.io import DeltaSink
from sverify.observation import PLAN_BOUND


@pytest.fixture
def con() -> sv.engine.Connection:
    c = sv.connect()
    c.put("t", pa.table({"k": [1, 1, 2], "x": [0.1, 0.2, 0.3]}))
    return c


def _float_sum(con) -> sv.Report:
    """A double sum with a row cap: Polars's `sum_order` varies between runs
    within the plan's bound (`ObsRow.fsumOrder`), here abs=111.023 and
    rel=2.22045e-10, both proved."""
    t = con.table("t")
    return sv.verify(
        t.group_by("k").aggregate(total=t.x.sum()),
        requires={"t": [_.x.between(0, 1e6), sv.max_rows(1_000_000)]},
    )


def test_a_float_sum_on_polars_streaming(con) -> None:
    """Polars's streaming engine sums in an order that varies between runs:
    a consumer that accepts the plan's bound gets the run, one that needs
    exact values does not. The checker decides (`Realize.rerunCheck`); its
    cases with made-up rows are `#guard`s there."""
    report = _float_sum(con)
    ok = routes.choose(report, "polars", reproducible=sv.equivalent(floats=sv.within(abs=1e3)))
    # The other options' reruns rest on their facts' tests (#900).
    assert ok.taken == "translated" and ok.rerun_evidence == "tested"
    assert (
        routes.choose(
            report, "polars", reproducible=sv.equivalent(floats=sv.within(rel=1e-9))
        ).taken
        == "translated"
    )
    exact = routes.choose(report, "polars", reproducible=sv.equivalent())
    assert exact.refused
    assert "a rerun must give the same result" in exact.why
    # Two runs are within twice each run's absolute bound, and the relative bound as it is
    # (#2631).
    assert "two runs on polars are within abs=222.045, rel=2.22045e-10 of each other" in exact.why
    assert exact.reproducible == sv.equivalent()
    # Without a requirement, the route only reports.
    assert routes.choose(report, "polars").taken == "translated"
    with pytest.raises(RouteError, match="rerun must give the same result"):
        report.run(con, "polars", route="auto", reproducible=sv.equivalent())


def test_a_stated_tolerance_against_the_plans_bound(con) -> None:
    """Ruling 281: a stated `reproducible=` stricter than the plan's bound is
    refused, one looser is met, and the sinks' default asks nothing more."""
    report = _float_sum(con)
    strict = sv.equivalent(floats=sv.within(abs=1.0))
    problems, _ = routes.reproducibility(report, "polars", strict)
    assert len(problems) == 1 and "within abs=222.045" in problems[0]
    assert "pass reproducible=sv.equivalent(floats=sv.within(rel=3e-10)) or looser" in problems[0]
    loose = sv.equivalent(floats=sv.within(abs=1e3))
    assert routes.reproducibility(report, "polars", loose) == ([], "tested")
    assert routes.reproducibility(report, "polars", sv.equivalent(floats="plan")) == (
        [],
        "tested",
    )


def test_a_stated_lens_asks_the_checker_once(monkeypatch, con) -> None:
    """The default lenses' answer is the report's own; another lens asks the
    checker once per plan and lenses in a process."""
    from sverify import engine

    report = _float_sum(con)
    routes._rerun_request.cache_clear()
    calls: list[tuple[str, ...]] = []
    run = engine.run_checker

    def counted(flags, stdin):
        calls.append(flags)
        return run(flags, stdin)

    monkeypatch.setattr(engine, "run_checker", counted)
    routes.reproducibility(report, "polars", PLAN_BOUND)
    assert calls == [], "the sinks' default is answered at verify time"
    strict = sv.equivalent(floats=sv.within(abs=1.0))
    first = routes.reproducibility(report, "polars", strict)
    assert first == routes.reproducibility(report, "polars", strict)
    routes.reproducibility(report, "duckdb", strict)
    assert calls == [("--contract",)]
    assert routes._rerun_request.cache_info().hits == 2


def test_an_open_choice_fails_every_requirement(con) -> None:
    """A result not determined up to row order (a LIMIT without an ORDER
    BY, ties) is reproduced by no rerun, however coarse the requirement."""
    t = con.table("t")
    report = sv.verify(t.limit(2))
    assert not report.deterministic
    coarse = sv.equivalent(floats=sv.within(abs=1e9), zeros="canon", elements="multiset")
    for q in (sv.equivalent(), coarse):
        r = routes.choose(report, "duckdb", reproducible=q)
        assert r.refused and "not determined up to row order" in r.why


def test_a_limit_without_order_by_is_refused(con) -> None:
    """A rerun requirement names the LIMIT that leaves the rows open (D24)."""
    t = con.table("t")
    report = sv.verify(t.limit(2))
    assert not report.deterministic
    assert [p.op for p in report._tie_places] == ["fetch"]
    with pytest.raises(RouteError, match="the plan leaves open the fetch at relation 0"):
        report.run(con, "duckdb", route="auto", reproducible=sv.equivalent(rows="multiset"))


@sv.transform(requires={"orders": [_.amount >= 0, _.amount < 1_000]})
def mean_amount(orders):
    return orders.group_by("customer").aggregate(mean=orders.amount.cast("float64").mean())


@sv.transform(requires={"orders": [_.amount >= 0, _.amount < 1_000, sv.max_rows(1_000)]})
def capped_mean(orders):
    return orders.group_by("customer").aggregate(mean=orders.amount.cast("float64").mean())


def test_a_sink_states_what_a_rerun_must_reproduce(tmp_path) -> None:
    """A sink commits each epoch once: by default a rerun must reproduce
    doubles within the plan's bound, which a mean without a row cap meets
    only on a test; a sink that asks exact values or a tolerance says so,
    and a tolerance needs the bound a row cap gives."""
    orders = make_orders(tmp_path / "orders", [(1, "ada", 5), (2, "ada", 7)])
    unbounded = mean_amount(orders).write(DeltaSink(str(tmp_path / "unbounded")))
    out = unbounded.refresh(engine="polars", route="auto")
    assert out["unbounded"].route is not None
    assert out["unbounded"].route.rerun_evidence == "tested"
    exact = mean_amount(orders).write(
        DeltaSink(str(tmp_path / "exact"), reproducible=sv.equivalent())
    )
    with pytest.raises(
        RouteError, match=r"mean_amount \(stored as exact\): a rerun must give the same result"
    ):
        exact.refresh(engine="polars")
    with pytest.raises(Exception):  # noqa: B017 - nothing was written
        DeltaTable(str(tmp_path / "exact"))
    tolerance = sv.equivalent(floats=sv.within(rel=1e-9))
    uncapped = mean_amount(orders).write(
        DeltaSink(str(tmp_path / "uncapped"), reproducible=tolerance)
    )
    with pytest.raises(RouteError, match="mean has no bound on its distance to the reference"):
        uncapped.refresh(engine="polars")
    loose = capped_mean(orders).write(DeltaSink(str(tmp_path / "loose"), reproducible=tolerance))
    out = loose.refresh(engine="polars", route="auto")
    assert out["loose"].route is not None and out["loose"].route.reproducible is not None
    assert DeltaTable(str(tmp_path / "loose")).to_pyarrow_table().num_rows == 1
    # The refresh's own requirement replaces the sink's.
    again = capped_mean(orders).write(DeltaSink(str(tmp_path / "again")))
    again.refresh(engine="polars", reproducible=tolerance)


def test_a_float_sum_on_polars_against_the_checkers_tables(con) -> None:
    """Polars's float sum is approx within the plan's bound (#612's rows), so
    the postcondition states a tolerance (`q_post`) and the rerun's `q_det`
    decides the route."""
    t = con.table("t")
    report = sv.verify(
        t.group_by("k").aggregate(total=t.x.sum()),
        requires={"t": [_.x.between(0, 1e6), sv.max_rows(1_000_000)]},
        ensures=[sv.equivalent(floats=sv.within(abs=1e3, rel=1e-6))],
    )
    assert report._epsilon, "the plan's bound on the sum"
    loose = sv.equivalent(floats=sv.within(abs=1.0, rel=1e-6))
    assert routes.choose(report, "polars", reproducible=loose).taken == "translated"
    exact = routes.choose(report, "polars", reproducible=sv.equivalent())
    assert exact.refused and "sum_order" in exact.why


def test_ties_permuted_sits_between_sequence_and_multiset(con) -> None:
    """#612's rows level: two runs agree up to permutations of tied rows."""
    ties = sv.equivalent(rows="ties permuted")
    assert sv.equivalent(rows="sequence").refines(ties)
    assert ties.refines(sv.equivalent(rows="multiset"))
    assert not ties.refines(sv.equivalent(rows="sequence"))
    # Polars's `tie_order`: a list ordered by a key reruns up to tied rows.
    con.put("u", pa.table({"k": [1, 1, 2], "n": [1, 2, 3]}))
    u = con.table("u")
    report = sv.verify(
        u.group_by("k").aggregate(l=u.n.collect(order_by=u.n)),
        requires={"u": [sv.unique("n")]},
    )
    assert routes.choose(report, "polars", reproducible=sv.equivalent()).taken == "translated"
    r = routes.choose(report, "polars", reproducible=sv.equivalent(rows="sequence"))
    assert r.refused and "two runs on polars agree only up to" in r.why and "rows" in r.why


def test_deterministic_is_gone():
    t = ibis.table({"k": "int64"}, name="t")
    report = sv.verify(t.select("k"))
    con = sv.connect()
    con.put("t", pa.table({"k": [1, 2]}))
    with pytest.raises(TypeError):
        report.run(con, "duckdb", deterministic=True)  # type: ignore[call-arg]
    with pytest.raises(TypeError):
        routes.choose(report, "duckdb", deterministic=True)  # type: ignore[call-arg]
