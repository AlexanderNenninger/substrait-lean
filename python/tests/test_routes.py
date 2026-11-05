"""Routes from a verified plan to an engine, and engine versions (#444 D10, D13, D14)."""

from __future__ import annotations

import ibis
import pyarrow as pa
import pytest
from ibis import _

import sverify as sv
from sverify import routes
from sverify.errors import PreconditionError


@pytest.fixture
def con() -> sv.engine.Connection:
    c = sv.connect()
    c.put("t", pa.table({"k": [1, 1, None], "i": [-7, 2, 3]}))
    return c


def _tables(monkeypatch: pytest.MonkeyPatch, choices: dict) -> None:
    def rows(table: dict) -> list[dict]:
        return [
            {
                "group": g,
                "option": o,
                "choice": {"kind": "oneOf", "behaviours": bs},
                "facts": [f"{o}-fact"],
            }
            for (g, o), bs in table.items()
        ]

    tables = {
        "groups": {"int.mod": ["division_type"]},
        "choices": {p: rows(t) for p, t in choices.items()},
    }
    monkeypatch.setattr(routes, "_options_json", lambda: tables)


def test_native_and_reference(con) -> None:
    t = con.table("t")
    report = sv.verify(t.select("k", j=t.i + 1), requires={"t": [_.i.between(-100, 100)]})
    assert report.proved
    for engine in ("duckdb", "polars"):
        out = report.run(con, engine, route="auto")
        r = report.routes[engine]
        assert r.kind == "reference" and r.profile == "reference", r
        assert sorted(out.column("j").to_pylist()) == [-6, 3, 4]
    assert "route on polars: exact" in str(report)
    duck = sv.verify("SELECT k, i % 3 AS m FROM t", tables={"t": t}, semantics="duckdb")
    assert routes.choose(duck, "duckdb").kind == "native"


def test_explicit_route_is_taken_or_refused(con) -> None:
    t = con.table("t")
    report = sv.verify(t.select("k", j=t.i + 1), requires={"t": [_.i.between(-100, 100)]})
    assert routes.choose(report, "duckdb", "reference").kind == "reference"
    r = routes.choose(report, "duckdb", "native")
    assert r.refused and "not verified under Profile.duckdb" in r.reason
    with pytest.raises(routes.RouteError, match="refused on duckdb"):
        report.run(con, "duckdb", route="native")
    with pytest.raises(ValueError, match="route must be"):
        routes.choose(report, "duckdb", "sideways")  # type: ignore[arg-type]


def test_run_chooses_a_route_by_default(con) -> None:
    duck = sv.verify(
        "SELECT k, i % 3 AS m FROM t", tables={"t": con.table("t")}, semantics="duckdb"
    )
    duck.run(con, "duckdb")
    assert duck.routes["duckdb"].kind == "native"


def test_transfer_check(monkeypatch: pytest.MonkeyPatch, con) -> None:
    duck = sv.verify(
        "SELECT k, i % 3 AS m FROM t", tables={"t": con.table("t")}, semantics="duckdb"
    )
    _tables(
        monkeypatch,
        {
            "duckdb": {("int.mod", "division_type"): ["TRUNCATE"]},
            "polars": {("int.mod", "division_type"): ["FLOOR"]},
            "datafusion": {("int.mod", "division_type"): ["TRUNCATE"]},
        },
    )
    monkeypatch.setattr(routes, "_groups_of", lambda name: {"int.mod"})
    r = routes.choose(duck, "polars", "transfer")
    assert r.refused
    assert r.failures == (
        {
            "group": "int.mod",
            "option": "division_type",
            "from": ["TRUNCATE"],
            "to": ["FLOOR"],
            "facts": ["division_type-fact"],
        },
    )
    assert "int.mod's division_type: duckdb gives TRUNCATE, polars gives FLOOR" in r.reason
    # #655: under "auto", the refusal leads with what to do. The re-check
    # under `Profile.polars` proves this plan, so it is made to fail here.
    assert routes.choose(duck, "polars").kind == "recheck"
    monkeypatch.setattr(routes, "recheck", lambda report, e: (False, "not proved"))
    auto = routes.choose(duck, "polars")
    assert auto.reason.startswith("verify with semantics='reference' to run on polars")
    assert routes.choose(duck, "datafusion", "transfer").kind == "transfer"
    # The checker's own dependency report narrows the check.
    duck.depends = []
    assert routes.choose(duck, "polars", "transfer").kind == "transfer"


def test_transfer_without_tables_is_refused_with_the_reason(monkeypatch, con) -> None:
    monkeypatch.setattr(routes, "_options_json", lambda: {})
    duck = sv.verify(
        "SELECT k, i % 3 AS m FROM t", tables={"t": con.table("t")}, semantics="duckdb"
    )
    r = routes.choose(duck, "polars", "transfer")
    assert r.refused
    assert "no choices table" in r.reason
    # `auto` goes on to the re-check, which the checker proves under
    # `Profile.polars` (the plan states its options, `PolarsProfile.lean`).
    auto = routes.choose(duck, "polars")
    assert (auto.kind, auto.profile) == ("recheck", "polars"), auto


def test_unproved_plan_is_refused(con) -> None:
    t = con.table("t")
    report = sv.verify(t.select("k", j=t.i * t.i), infer=False)
    assert not report.proved
    reason = routes.choose(report, "duckdb").reason
    assert reason.startswith("not verified: may fail: overflow: i * i (see report.errors)")
    assert "unverified=True" in reason


def test_run_refuses_an_unproved_plan_unless_asked(con) -> None:
    """#655: an unproved plan does not run silently; `unverified=True` runs
    it, and the result, the routes and a warning say so."""
    t = con.table("t")
    report = sv.verify(t.select("k", j=t.i * t.i), infer=False)
    with pytest.raises(routes.RouteError, match=r"refused on duckdb: not verified: may fail"):
        report.run(con)
    with pytest.warns(routes.UnverifiedRunWarning, match="running on duckdb unverified"):
        out = report.run(con, unverified=True)
    assert out.schema.metadata[b"sverify.verified"] == b"false"
    assert report.routes["duckdb"].kind == "unverified"
    assert "route on duckdb: unverified: not verified" in str(report)


def test_determinism_is_reported_and_required_on_request() -> None:
    t = ibis.table({"k": "int64", "o": "int64", "v": "int64"}, name="t")
    expr = t.group_by("k").aggregate(f=t.v.first(order_by=t.o))
    report = sv.verify(expr)
    assert report.proved and not report.deterministic
    r = routes.choose(report, "duckdb")
    assert r.kind == "reference" and not r.deterministic
    assert any("ties stay open" in w for w in r.warnings)
    strict = routes.choose(report, "duckdb", deterministic=True)
    assert strict.refused and "rerun must give the same result" in strict.reason


def test_sequence_needs_a_sorted_result(con) -> None:
    t = con.table("t")
    req = {"t": [_.i.between(-100, 100)]}
    seq = sv.equivalent(rows="sequence")
    unsorted = sv.verify(t.select("k", "i"), requires=req, ensures=[seq])
    assert "not sorted" in routes.choose(unsorted, "duckdb").reason
    ordered = sv.verify(
        t.select("k", "i").order_by([ibis.asc("k", nulls_first=True), "i"]),
        requires=req,
        ensures=[seq],
    )
    assert routes.choose(ordered, "duckdb").kind == "reference"


def test_engine_versions(monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setattr(routes, "_options_json", lambda: {})
    assert routes.check_version("duckdb", "2.0.0") is None
    assert routes.check_version("datafusion", "1.0.0") is None
    with pytest.warns(routes.EngineVersionWarning, match="polars 2.2.0"):
        assert routes.check_version("polars", "2.2.0")
    with pytest.raises(routes.EngineVersionError, match="needs its facts probed again"):
        routes.check_version("duckdb", "3.0.0")
    # The checker's profiles take precedence.
    monkeypatch.setattr(
        routes,
        "_options_json",
        lambda: {"profiles": {"duckdb": {"engine": "duckdb", "versions": ["3.0.0"]}}},
    )
    assert routes.check_version("duckdb", "3.0.0") is None


def test_installed_versions_are_the_probed_ones() -> None:
    """The pinned engines match their profiles' facts; bump the facts with the pins."""
    for engine, prof in routes.PROFILES.items():
        assert routes.installed_version(engine) in prof.versions, engine


def _classed_tables(monkeypatch: pytest.MonkeyPatch, polars_rows: list[dict]) -> None:
    tables = {
        "groups": {},
        "choices": {"reference": [], "duckdb": [], "polars": polars_rows},
    }
    monkeypatch.setattr(routes, "_options_json", lambda: tables)


def _row(option: str, cls: str, q: dict | None = None, shim: str | None = None, ev: str = "proved"):
    return {
        "group": None,
        "option": option,
        "choice": {"kind": "oneOf", "behaviours": ["X"]},
        "class": cls,
        "q": q,
        "shim": shim,
        "evidence": ev,
        "facts": [f"polars-{option}"],
    }


def test_the_class_is_the_worst_over_the_options(monkeypatch, con) -> None:
    t = con.table("t")
    report = sv.verify(t.select("k"))
    report.depends = [{"group": None, "option": "a"}, {"group": None, "option": "b"}]
    _classed_tables(
        monkeypatch, [_row("a", "refines"), _row("b", "shim", shim="CASE", ev="tested")]
    )
    r = routes.choose(report, "polars")
    assert (r.kind, r.cls, r.evidence, r.shims) == ("reference", "shim", "tested", ("b: CASE",))
    assert str(r).startswith("shim (") and str(r).endswith("; evidence tested")
    _classed_tables(monkeypatch, [_row("a", "refines"), _row("b", "refused")])
    r = routes.choose(report, "polars")
    assert r.refused and r.cls == "refused" and "b is refused on polars (polars-b)" in r.reason


def test_q_refinement_against_the_postcondition(monkeypatch, con) -> None:
    """D18's check: an engine equal to the reference up to `canon` meets a
    postcondition that observes zeros only if it says `zeros="canon"`, or
    through the row's shim."""
    t = con.table("t")
    exact = sv.verify(t.select("k"))
    canon = sv.verify(t.select("k"), ensures=[sv.equivalent(zeros="canon")])
    for report in (exact, canon):
        report.depends = [{"group": None, "option": "zero_sign"}]
    _classed_tables(monkeypatch, [_row("zero_sign", "refines_up_to", q={"zeros": "canon"})])
    r = routes.choose(exact, "polars")
    assert r.refused and "observes its zeros" in r.reason and "sv.equivalent" in r.reason
    assert routes.choose(canon, "polars").cls == "observed"
    _classed_tables(
        monkeypatch, [_row("zero_sign", "refines_up_to", q={"zeros": "canon"}, shim="canon")]
    )
    assert routes.choose(exact, "polars").cls == "shim"
    # A tolerance: the engine's ε must be within the stated one.
    _classed_tables(
        monkeypatch, [_row("sum_order", "approx", q={"rows": "multiset", "floats": {"rel": 1e-12}})]
    )
    for report, ok in (
        (sv.verify(t.select("k"), ensures=[sv.equivalent(floats=sv.within(rel=1e-9))]), True),
        (sv.verify(t.select("k"), ensures=[sv.equivalent(floats=sv.within(rel=1e-15))]), False),
        (exact, False),
    ):
        report.depends = [{"group": None, "option": "sum_order"}]
        r = routes.choose(report, "polars")
        assert (r.cls == "observed") is ok, r


def test_unsupported_functions_are_refused(con) -> None:
    t = con.table("t")
    report = sv.verify(t.select(h=t.k.cast("string").hexdigest("md5")))
    r = routes.choose(report, "polars")
    assert r.refused and r.cls == "refused" and "see #271" in r.reason


def test_inputs_are_checked_before_the_run(con) -> None:
    t = con.table("t")
    report = sv.verify(t.select("k", j=t.i + 1), requires={"t": [_.i <= 2]})
    with pytest.raises(PreconditionError, match=r"violate \(_.i <= 2\): refused before"):
        report.run(con, "polars", route="auto")
    # Without a route too (#604), unless the caller opts out.
    with pytest.raises(PreconditionError, match=r"violate \(_.i <= 2\): refused before"):
        report.run(con, "polars")
    report.run(con, "polars", check_inputs=False)


def test_a_plan_dependent_float_bound(monkeypatch, con) -> None:
    """Polars's `sum_order`: `q` bounds the doubles per plan. The contract's
    `ε` gives bounds that each hold on their own; a stated tolerance is met
    by one no larger than its bound of the same kind (B1)."""
    t = con.table("t")
    _classed_tables(monkeypatch, [_row("sum_order", "approx", q={"floats": {"bound": "plan"}})])

    def route(tolerance, epsilon):
        report = sv.verify(t.select("k"), ensures=[sv.equivalent(floats=tolerance)])
        report.depends = [{"group": None, "option": "sum_order"}]
        report.epsilon = epsilon
        return routes.choose(report, "polars")

    both = {"total": {"abs": 222.0, "rel": 1e-10}, "k": {}}
    assert route(sv.within(rel=1e-9), both).cls == "observed"
    assert route(sv.within(abs=1e3), both).cls == "observed"
    r = route(sv.within(rel=1e-15, abs=1.0), both)
    assert r.refused and "total is within abs=222 (tested), rel=1e-10 (tested)" in r.reason
    assert "no per-plan bound" in route(sv.within(rel=1e-9), None).reason
    # A bound is proved only where Lean says so; otherwise the route rests
    # on a test.
    assert route(sv.within(rel=1e-9), both).evidence == "tested"
    marked = {"total": {"abs": 222.0, "rel": 1e-10, "proved": {"abs": True, "rel": False}}}
    assert route(sv.within(rel=1e-9), marked).evidence == "tested"
    assert route(sv.within(abs=1e3), marked).evidence == "proved"
    assert route(sv.within(abs=1e3), {"total": {"abs": 222.0, "proved": True}}).evidence == "proved"
    nested = {"total": {"rel": {"value": 1e-10, "proved": True}}}
    assert route(sv.within(rel=1e-9), nested).evidence == "proved"


def test_rows_that_may_flip_under_the_bound_are_refused(monkeypatch, con) -> None:
    """#568's threshold rule: where a filter, key or sort on a double may
    keep other rows on the engine than on the reference (`rows_exact`), a
    per-plan float bound does not carry over, and the route is refused."""
    t = con.table("t")
    _classed_tables(monkeypatch, [_row("sum_order", "approx", q={"floats": {"bound": "plan"}})])

    def route(rows_exact):
        report = sv.verify(t.select("k"), ensures=[sv.equivalent(floats=sv.within(abs=1e3))])
        report.depends = [{"group": None, "option": "sum_order"}]
        report.epsilon = {"total": {"abs": 222.0, "proved": True}}
        report.rows_exact = rows_exact
        return routes.choose(report, "polars")

    assert route({"polars": True}).cls == "observed"
    assert route(None).cls == "observed"
    r = route({"polars": False})
    assert r.refused and "may keep other rows on polars" in r.reason
