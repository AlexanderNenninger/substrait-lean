"""What a rerun must reproduce (`q_det`, #444 D20): the engine's run-to-run
variation (the `"rerun"` column of its choices) must refine the observation
the consumer requires, or the route is refused."""

from __future__ import annotations

from dataclasses import replace

import pyarrow as pa
import pytest
from deltalake import DeltaTable
from ibis import _

import sverify as sv
from _pipelines import make_orders
from sverify import routes
from sverify.errors import RouteError
from sverify.io import DeltaSink


@pytest.fixture
def con() -> sv.engine.Connection:
    c = sv.connect()
    c.put("t", pa.table({"k": [1, 1, 2], "x": [0.1, 0.2, 0.3]}))
    return c


def _tables(
    monkeypatch: pytest.MonkeyPatch, rerun: dict | None, evidence: str | None = "proved"
) -> None:
    """Polars's `sum_order` row with run-to-run variation `rerun`."""
    row = {
        "group": None,
        "option": "sum_order",
        "choice": {"kind": "oneOf", "behaviours": ["ANY"]},
        "class": "refines",
        "evidence": "proved",
        "facts": ["polars-sum-float"],
    }
    if rerun is not None:
        row["rerun"] = rerun
        row["rerun_evidence"] = evidence
    tables = {"groups": {}, "choices": {"reference": [], "duckdb": [], "polars": [row]}}
    monkeypatch.setattr(routes, "_options_json", lambda: tables)


def _float_sum(con) -> sv.Report:
    t = con.table("t")
    report = sv.verify(
        t.group_by("k").aggregate(total=t.x.sum()),
        requires={"t": [_.x.between(0, 1e6), sv.max_rows(1_000_000)]},
    )
    report.depends = [{"group": None, "option": "sum_order"}]
    return report


def test_a_float_sum_on_polars_streaming(monkeypatch, con) -> None:
    """Polars's streaming engine sums in an order that varies between runs:
    a consumer that accepts the plan's bound gets the run, one that needs
    exact values does not."""
    _tables(monkeypatch, {"floats": {"bound": "plan"}})
    report = _float_sum(con)
    report.epsilon = {"total": {"abs": 1e-3, "rel": 1e-10, "proved": {"abs": True}}}
    ok = routes.choose(report, "polars", reproducible=sv.equivalent(floats=sv.within(abs=1e-2)))
    assert ok.kind == "reference" and ok.rerun_evidence == "proved"
    assert (
        routes.choose(
            report, "polars", reproducible=sv.equivalent(floats=sv.within(rel=1e-9))
        ).rerun_evidence
        == "tested"
    ), "the relative bound is not proved"
    exact = routes.choose(report, "polars", reproducible=sv.equivalent())
    assert exact.refused
    assert "a rerun must give the same result" in exact.reason
    assert "total is within abs=0.001, rel=1e-10 (tested) between runs" in exact.reason
    assert exact.reproducible == sv.equivalent()
    # `deterministic=True` asks for exact values too.
    assert routes.choose(report, "polars", deterministic=True).refused
    # Without a requirement, the route only reports.
    assert routes.choose(report, "polars").kind == "reference"
    with pytest.raises(RouteError, match="rerun must give the same result"):
        report.run(con, "polars", route="auto", reproducible=sv.equivalent())


def test_a_fixed_variation(monkeypatch, con) -> None:
    _tables(monkeypatch, {"rows": "multiset", "floats": {"rel": 1e-12}})
    report = _float_sum(con)
    assert (
        routes.choose(
            report, "polars", reproducible=sv.equivalent(floats=sv.within(rel=1e-9))
        ).rerun_evidence
        == "proved"
    )
    r = routes.choose(report, "polars", reproducible=sv.equivalent(rows="sequence"))
    assert r.refused and "must reproduce its rows, floats" in r.reason


def test_a_missing_variation_reads_as_exact_on_a_test(monkeypatch, con) -> None:
    _tables(monkeypatch, None)
    report = _float_sum(con)
    r = routes.choose(report, "polars", reproducible=sv.equivalent())
    assert r.kind == "reference" and r.rerun_evidence == "tested"


@pytest.mark.parametrize(
    ("evidence", "expected"), [("proved", "proved"), ("tested", "tested"), (None, "tested")]
)
def test_an_exact_variation_with_its_evidence(monkeypatch, con, evidence, expected) -> None:
    """`"rerun": {}` marks a row known exact; its evidence is the row's
    `"rerun_evidence"`, "tested" where it says nothing."""
    _tables(monkeypatch, {}, evidence)
    report = _float_sum(con)
    r = routes.choose(report, "polars", reproducible=sv.equivalent())
    assert r.kind == "reference" and r.rerun_evidence == expected


def test_an_open_choice_fails_every_requirement(con) -> None:
    """A result not determined up to row order (a LIMIT without an ORDER
    BY, ties) is reproduced by no rerun, however coarse the requirement."""
    t = con.table("t")
    report = replace(sv.verify(t.select("k")), deterministic=False)
    coarse = sv.equivalent(floats=sv.within(abs=1e9), zeros="canon", elements="multiset")
    for q in (sv.equivalent(), coarse):
        r = routes.choose(report, "duckdb", reproducible=q)
        assert r.refused and "not determined up to row order" in r.reason


def test_a_limit_without_order_by_is_refused(con) -> None:
    """The deterministic profile names the LIMIT that leaves the rows open (D24)."""
    t = con.table("t")
    report = sv.verify(t.limit(2))
    assert not report.deterministic
    assert [p.op for p in report.tie_places] == ["fetch"]
    with pytest.raises(RouteError, match="ties stay open at the fetch at relation 0"):
        report.run(con, "duckdb", route="auto", reproducible=sv.equivalent(rows="multiset"))


@sv.transform(requires={"orders": [_.amount >= 0, _.amount < 1_000]})
def mean_amount(orders):
    return orders.group_by("customer").aggregate(mean=orders.amount.cast("float64").mean())


def test_a_sink_states_what_a_rerun_must_reproduce(monkeypatch, tmp_path) -> None:
    """A sink commits each epoch once: by default a rerun must reproduce
    doubles within the plan's bound, which this plan has none of (no row
    cap); a sink that asks exact values or accepts a tolerance says so."""
    _tables(monkeypatch, {"floats": {"rel": 1e-12}})
    monkeypatch.setattr(
        routes, "plan_options", lambda plan: [{"group": None, "option": "sum_order"}]
    )
    orders = make_orders(tmp_path / "orders", [(1, "ada", 5), (2, "ada", 7)])
    unbounded = mean_amount(orders).write(DeltaSink(str(tmp_path / "unbounded")))
    with pytest.raises(RouteError, match="no bound on the plan's doubles"):
        unbounded.refresh(engine="polars")
    exact = mean_amount(orders).write(
        DeltaSink(str(tmp_path / "exact"), reproducible=sv.equivalent())
    )
    with pytest.raises(
        RouteError, match=r"mean_amount \(stored as exact\): a rerun must give the same result"
    ):
        exact.refresh(engine="polars")
    with pytest.raises(Exception):  # noqa: B017 - nothing was written
        DeltaTable(str(tmp_path / "exact"))
    loose = mean_amount(orders).write(
        DeltaSink(str(tmp_path / "loose"), reproducible=sv.equivalent(floats=sv.within(rel=1e-9)))
    )
    out = loose.refresh(engine="polars", route="auto")
    assert out["loose"].route is not None and out["loose"].route.reproducible is not None
    assert DeltaTable(str(tmp_path / "loose")).to_pyarrow_table().num_rows == 1
    # The refresh's own requirement replaces the sink's.
    again = mean_amount(orders).write(DeltaSink(str(tmp_path / "again")))
    again.refresh(engine="polars", reproducible=sv.equivalent(floats=sv.within(rel=1e-9)))


def _has_rerun() -> bool:
    rows = (routes._options_json().get("choices") or {}).get("polars") or []
    return any("rerun" in r for r in rows)


@pytest.mark.xfail(
    not _has_rerun(),
    reason="the rerun column of Profile.polars's choices (#444 D20) not in the checker yet",
    strict=True,
)
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
    assert report.epsilon, "the plan's bound on the sum"
    loose = sv.equivalent(floats=sv.within(abs=1.0, rel=1e-6))
    assert routes.choose(report, "polars", reproducible=loose).kind == "reference"
    exact = routes.choose(report, "polars", reproducible=sv.equivalent())
    assert exact.refused and "sum_order" in exact.reason


def test_ties_permuted_sits_between_sequence_and_multiset(monkeypatch, con) -> None:
    """#612's rows level: two runs agree up to permutations of tied rows."""
    ties = sv.equivalent(rows="ties permuted")
    assert sv.equivalent(rows="sequence").refines(ties)
    assert ties.refines(sv.equivalent(rows="multiset"))
    assert not ties.refines(sv.equivalent(rows="sequence"))
    _tables(monkeypatch, {"rows": "ties permuted"})
    report = _float_sum(con)
    assert routes.choose(report, "polars", reproducible=sv.equivalent()).kind == "reference"
    r = routes.choose(report, "polars", reproducible=sv.equivalent(rows="sequence"))
    assert r.refused and "rows" in r.reason
