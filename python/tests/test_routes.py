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


def test_native_and_reference(con) -> None:
    t = con.table("t")
    report = sv.verify(t.select("k", j=t.i + 1), requires={"t": [_.i.between(-100, 100)]})
    assert report.proved
    for engine in ("duckdb", "polars"):
        out = report.run(con, engine, route="auto")
        r = report.routes[engine]
        assert r.kind == "translated" and r.profile == "reference", r
        assert sorted(out.column("j").to_pylist()) == [-6, 3, 4]
    assert "route on polars: exact" in str(report)
    duck = sv.verify("SELECT k, i % 3 AS m FROM t", tables={"t": t}, semantics="duckdb")
    assert routes.choose(duck, "duckdb").kind == "native"


def test_explicit_route_is_taken_or_refused(con) -> None:
    t = con.table("t")
    report = sv.verify(t.select("k", j=t.i + 1), requires={"t": [_.i.between(-100, 100)]})
    assert routes.choose(report, "duckdb", "translated").kind == "translated"
    r = routes.choose(report, "duckdb", "native")
    assert r.refused and 'not verified under semantics="duckdb"' in r.reason
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
    """The transfer route takes the checker's check (`transferB`, proved
    sound by `Rel.transfer_of_transferB`) over every option the plan reads."""
    duck = sv.verify(
        "SELECT k, i % 3 AS m FROM t", tables={"t": con.table("t")}, semantics="duckdb"
    )
    r = routes.choose(duck, "polars", "transfer")
    assert r.refused
    assert {
        "group": "int.mod",
        "option": "division_type",
        "preferences": [],
        "from": ["TRUNCATE"],
        "to": ["FLOOR"],
        "facts": ["polars-int-modulus"],
    } in r.failures
    assert (
        "int.mod's division_type: duckdb gives TRUNCATE, polars gives FLOOR (polars-int-modulus)"
        in r.reason
    )
    # #655: under "auto", the refusal leads with what to do. The re-check
    # under `Profile.polars` proves this plan, so it is made to fail here.
    assert routes.choose(duck, "polars").kind == "recheck"
    monkeypatch.setattr(routes, "recheck", lambda report, e: (False, "not proved"))
    auto = routes.choose(duck, "polars")
    assert auto.reason.startswith("verify with semantics='reference' to run on polars")
    # Where the check passes, the route is taken.
    assert duck._engines is not None
    duck._engines["polars"]["transfer"]["duckdb"] = {"ok": True, "failures": []}
    assert routes.choose(duck, "polars", "transfer").kind == "transfer"


def test_transfer_without_a_verdict_is_refused_with_the_reason(con) -> None:
    duck = sv.verify(
        "SELECT k, i % 3 AS m FROM t", tables={"t": con.table("t")}, semantics="duckdb"
    )
    duck._engines = None
    r = routes.choose(duck, "polars", "transfer")
    assert r.refused and "gave no transfer check" in r.reason
    # `auto` goes on to the re-check, which the checker proves under
    # `Profile.polars` (the plan states its options, `PolarsProfile.lean`).
    auto = routes.choose(duck, "polars")
    assert (auto.kind, auto.profile) == ("recheck", "polars"), auto


def test_unproved_plan_is_refused(con) -> None:
    t = con.table("t")
    report = sv.verify(t.select("k", j=t.i * t.i), on_inferred="off")
    assert not report.proved
    reason = routes.choose(report, "duckdb").reason
    assert reason.startswith("not verified: may fail: overflow: i * i (see report.errors)")
    assert "unverified=True" in reason


def test_run_refuses_an_unproved_plan_unless_asked(con) -> None:
    """#655: an unproved plan does not run silently; `unverified=True` runs
    it, and the result, the routes and a warning say so."""
    t = con.table("t")
    report = sv.verify(t.select("k", j=t.i * t.i), on_inferred="off")
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
    assert r.kind == "translated" and not r.deterministic
    assert any("ties stay open" in w for w in r.warnings)
    strict = routes.choose(report, "duckdb", reproducible=sv.equivalent())
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
    assert routes.choose(ordered, "duckdb").kind == "translated"


def test_engine_versions(monkeypatch: pytest.MonkeyPatch) -> None:
    versions = {"duckdb": "2.0.0", "polars": "2.1.0", "spark": "4.3.0"}
    monkeypatch.setattr(
        routes,
        "_options_json",
        lambda: {"profiles": {e: {"engine": e, "versions": [v]} for e, v in versions.items()}},
    )
    assert routes.check_version("duckdb", "2.0.0") is None
    assert routes.check_version("datafusion", "1.0.0") is None
    with pytest.warns(routes.EngineVersionWarning, match="polars 2.2.0"):
        assert routes.check_version("polars", "2.2.0")
    with pytest.raises(routes.EngineVersionError, match="needs its facts probed again"):
        routes.check_version("duckdb", "3.0.0")
    # The checker's profiles are the only source of the versions.
    monkeypatch.setattr(
        routes,
        "_options_json",
        lambda: {"profiles": {"duckdb": {"engine": "duckdb", "versions": ["3.0.0"]}}},
    )
    assert routes.check_version("duckdb", "3.0.0") is None


def test_installed_versions_are_the_probed_ones() -> None:
    """The pinned engines match their profiles' facts; bump the facts with the pins."""
    found = {e: p for e, p in routes.profiles().items() if e in ("duckdb", "polars", "spark")}
    assert set(found) == {"duckdb", "polars", "spark"}
    for engine, prof in found.items():
        assert routes.installed_version(engine) in prof.versions, engine


def _verdict(cls="exact", evidence="proved", observed=(), shims=(), problems=(), **kw) -> dict:
    """A checker verdict on Polars (`"engines"`, `SubstraitLean/Realize.lean`)."""
    return {
        "class": cls,
        "evidence": evidence,
        "observed": list(observed),
        "shims": list(shims),
        "problems": list(problems),
        "theorems": [],
        "facts": [],
        "issues": [],
        "proved_facts": [],
        "version": "",
        "transfer": {},
        **kw,
    }


def _observed(option: str, observation: dict, shim: str | None = None) -> dict:
    return {
        "group": "",
        "option": option,
        "observation": observation,
        "shim": shim,
        "facts": [f"polars-{option}"],
    }


def _on_polars(report, **kw) -> routes.Route:
    report._engines = {"polars": _verdict(**kw)}
    return routes.choose(report, "polars")


def test_the_route_carries_the_checker_s_evidence(con) -> None:
    """The class, the evidence and what it cites are the checker's (#1166):
    a route takes them as they are, and names them."""
    t = con.table("t")
    report = sv.verify(t.select("k"))
    assert _on_polars(report, evidence="tested").evidence == "tested"
    r = _on_polars(report, theorems=["Polars.a", "Polars.b"], facts=["polars-a"])
    assert (r.evidence, r.theorems, r.facts) == ("proved", ("Polars.a", "Polars.b"), ("polars-a",))
    assert "evidence: polars exact, proved by Polars.a, Polars.b" in str(report)
    from sverify import report_json

    assert report_json.route(report_json.route_json(r)) == r
    # A tested row names its engine version and its tracking issue (#1170).
    r = _on_polars(
        report, evidence="tested", facts=["polars-a", "polars-b"], version="2.1.1", issues=[1166]
    )
    assert (r.version, r.issues) == ("2.1.1", (1166,))
    assert str(r).endswith("; evidence tested at 2.1.1 (facts polars-a, polars-b; #1166)")
    assert report_json.route(report_json.route_json(r)) == r


def test_a_proof_of_the_engine_s_model_names_its_facts(con) -> None:
    """A theorem about the engine's model reaches the engine only through the
    facts that say the engine is that model (#900): the evidence names them.
    A theorem without such facts is plainly proved."""
    t = con.table("t")
    report = sv.verify(t.select("k"))
    r = _on_polars(report, theorems=["Rel.polars_sound"], proved_facts=["polars-int-arith"])
    assert str(r).endswith(
        "; evidence proved by Rel.polars_sound on polars's model (facts polars-int-arith)"
    )
    assert "evidence: polars exact, proved by Rel.polars_sound on polars's model" in str(report)
    from sverify import report_json

    assert report_json.route(report_json.route_json(r)) == r
    r = _on_polars(report, theorems=["Lowering.lower_correct"])
    assert str(r).endswith("; evidence proved by Lowering.lower_correct")


def test_the_class_and_the_refusals_are_the_checker_s(con) -> None:
    t = con.table("t")
    report = sv.verify(t.select("k"))
    shim = {"group": "", "option": "b", "shim": "CASE"}
    r = _on_polars(report, cls="shim", evidence="tested", shims=[shim], facts=["polars-b"])
    assert (r.kind, r.cls, r.evidence, r.shims) == ("translated", "shim", "tested", ("b: CASE",))
    assert str(r).startswith("shim (") and str(r).endswith(
        "; evidence tested at 2.1.0 (facts polars-b)"
    )
    refused = {"code": "option_refused", "group": "", "option": "b", "facts": ["polars-b"]}
    r = _on_polars(report, cls="refused", problems=[refused])
    assert r.refused and r.cls == "refused" and "b is refused on polars (polars-b)" in r.reason
    report._engines = None
    r = routes.choose(report, "polars")
    assert r.refused and "gave no verdict on polars" in r.reason


def test_q_refinement_against_the_postcondition(con) -> None:
    """D18's check: an engine equal to the reference up to `canon` meets a
    postcondition that observes zeros only if it says `zeros="canon"`, or
    through the row's shim."""
    t = con.table("t")
    exact = sv.verify(t.select("k"))
    canon = sv.verify(t.select("k"), ensures=[sv.equivalent(zeros="canon")])
    zeros = [_observed("zero_sign", {"zeros": "canon"})]
    r = _on_polars(exact, cls="observed", observed=zeros)
    assert r.refused and "observes its zeros" in r.reason and "sv.equivalent" in r.reason
    assert _on_polars(canon, cls="observed", observed=zeros).cls == "observed"
    shimmed = [_observed("zero_sign", {"zeros": "canon"}, shim="canon")]
    assert _on_polars(exact, cls="observed", observed=shimmed).cls == "shim"
    # A tolerance: the engine's ε must be within the stated one.
    tol = [_observed("sum_order", {"rows": "multiset", "floats": {"rel": 1e-12}})]
    for report, ok in (
        (sv.verify(t.select("k"), ensures=[sv.equivalent(floats=sv.within(rel=1e-9))]), True),
        (sv.verify(t.select("k"), ensures=[sv.equivalent(floats=sv.within(rel=1e-15))]), False),
        (exact, False),
    ):
        r = _on_polars(report, cls="observed", observed=tol)
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
    report.run(con, "polars", check_requires=False)


def test_a_plan_dependent_float_bound(con) -> None:
    """Polars's `sum_order`: `q` bounds the doubles per plan. The contract's
    `ε` gives bounds that each hold on their own; a stated tolerance is met
    by one no larger than its bound of the same kind (B1)."""
    t = con.table("t")

    def route(tolerance, epsilon):
        report = sv.verify(t.select("k"), ensures=[sv.equivalent(floats=tolerance)])
        report._epsilon = epsilon
        plan = [_observed("sum_order", {"floats": {"bound": "plan"}})]
        return _on_polars(report, cls="observed", observed=plan)

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


def test_rows_that_may_flip_under_the_bound_are_refused(con) -> None:
    """#568's threshold rule, as the checker applies it: where a filter, key
    or sort on a double may keep other rows on the engine than on the
    reference, the route is refused."""
    t = con.table("t")
    report = sv.verify(t.select("k"), ensures=[sv.equivalent(floats=sv.within(abs=1e3))])
    report._epsilon = {"total": {"abs": 222.0, "proved": True}}
    plan = [_observed("sum_order", {"floats": {"bound": "plan"}})]
    assert _on_polars(report, cls="observed", observed=plan).cls == "observed"
    r = _on_polars(report, cls="refused", observed=plan, problems=[{"code": "threshold"}])
    assert r.refused and "may keep other rows on polars" in r.reason
