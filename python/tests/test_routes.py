"""Routes from a verified plan to an engine, and engine versions (#444 D10, D13, D14)."""

from __future__ import annotations

import ibis
import pyarrow as pa
import pytest
from ibis import _

import sverify as sv
from _repo import ROOT, needs_repo
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
    assert report.verdict == sv.Verdict.PROVED
    for engine in ("duckdb", "polars"):
        out = report.run(con, engine, route="auto")
        r = report.routes[engine]
        assert r.taken == "translated" and r.profile == "portable", r
        assert sorted(out.column("j").to_pylist()) == [-6, 3, 4]
    assert "route on polars: exact" in report.details()
    duck = sv.verify("SELECT k, i % 3 AS m FROM t", tables={"t": t}, semantics="duckdb")
    assert routes.choose(duck, "duckdb").taken == "native"


def test_explicit_route_is_taken_or_refused(con) -> None:
    t = con.table("t")
    report = sv.verify(t.select("k", j=t.i + 1), requires={"t": [_.i.between(-100, 100)]})
    assert routes.choose(report, "duckdb", "translated").taken == "translated"
    r = routes.choose(report, "duckdb", "native")
    assert r.refused and 'not verified under semantics="duckdb"' in r.why
    with pytest.raises(routes.RouteError, match="refused on duckdb"):
        report.run(con, "duckdb", route="native")
    with pytest.raises(ValueError, match="route must be"):
        routes.choose(report, "duckdb", "sideways")  # type: ignore[arg-type]


def test_explicit_route_refusal_names_its_exit(con) -> None:
    """A refused explicit route says how to reach the engine (#1046)."""
    duck = sv.verify(
        "SELECT k, i % 3 AS m FROM t", tables={"t": con.table("t")}, semantics="duckdb"
    )
    r = routes.choose(duck, "polars", "translated")
    assert r.refused and "verify with semantics='portable' to run on polars" in r.why
    ref = sv.verify("SELECT k, i % 3 AS m FROM t", tables={"t": con.table("t")})
    r = routes.choose(ref, "duckdb", "native")
    assert r.refused and 'route="auto" tries every route' in r.why


def test_run_chooses_a_route_by_default(con) -> None:
    duck = sv.verify(
        "SELECT k, i % 3 AS m FROM t", tables={"t": con.table("t")}, semantics="duckdb"
    )
    duck.run(con, "duckdb")
    assert duck.routes["duckdb"].taken == "native"


def test_transfer_check(con) -> None:
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
        in r.why
    )
    # #655: under "auto", the refusal leads with what to do. The checker
    # cannot prove under `Profile.polars` yet (#271), so there is no re-check.
    auto = routes.choose(duck, "polars")
    assert auto.why.startswith("verify with semantics='portable' to run on polars")
    # Where the check passes, the route is taken.
    assert duck._engines is not None
    duck._engines["polars"]["transfer"]["duckdb"] = {"ok": True, "failures": []}
    assert routes.choose(duck, "polars", "transfer").taken == "transfer"


def test_transfer_without_a_verdict_is_refused_with_the_reason(con) -> None:
    duck = sv.verify(
        "SELECT k, i % 3 AS m FROM t", tables={"t": con.table("t")}, semantics="duckdb"
    )
    duck._engines = None
    r = routes.choose(duck, "polars", "transfer")
    assert r.refused and "gave no transfer check" in r.why
    # `auto` has no re-check to go on to: the checker reports `polars` as
    # pending (#271), so it names the reference as the way.
    auto = routes.choose(duck, "polars")
    assert auto.refused and auto.why.startswith("verify with semantics='portable'"), auto


def test_unproved_plan_is_refused(con) -> None:
    t = con.table("t")
    report = sv.verify(t.select("k", j=t.i * t.i), on_inferred="off")
    assert report.verdict == sv.Verdict.UNPROVED
    reason = routes.choose(report, "duckdb").why
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
    assert report.routes["duckdb"].taken == "unverified"
    assert "route on duckdb: unverified: not verified" in report.details()


def test_determinism_is_reported_and_required_on_request() -> None:
    t = ibis.table({"k": "int64", "o": "int64", "v": "int64"}, name="t")
    expr = t.group_by("k").aggregate(f=t.v.first(order_by=t.o))
    report = sv.verify(expr)
    assert report.verdict == sv.Verdict.PROVED and not report.deterministic
    r = routes.choose(report, "duckdb")
    assert r.taken == "translated" and not r.deterministic
    assert any("ties stay open" in w for w in r.warnings)
    strict = routes.choose(report, "duckdb", reproducible=sv.equivalent())
    assert strict.refused and "rerun must give the same result" in strict.why


def test_sequence_needs_a_total_sort(con) -> None:
    """`rows="sequence"` needs a result the plan orders without ties: sorted
    on columns that contain a key of its input (`check_sequence_determined_sound`).
    A result sorted on a non-key keeps its ties open."""
    t = con.table("t")
    req = {"t": [_.i.between(-100, 100)]}
    seq = sv.equivalent(rows="sequence")
    unsorted = sv.verify(t.select("k", "i"), requires=req, ensures=[seq])
    assert "not sorted" in routes.choose(unsorted, "duckdb").why
    order = [ibis.asc("k", nulls_first=True), "i"]
    tied = sv.verify(t.select("k", "i").order_by(order), requires=req, ensures=[seq])
    assert not tied._sequence_determined
    assert "not sorted on a key" in routes.choose(tied, "duckdb").why
    keyed = {"t": [*req["t"], sv.unique("k", "i")]}
    total = sv.verify(t.select("k", "i").order_by(order), requires=keyed, ensures=[seq])
    assert total._sequence_determined
    assert routes.choose(total, "duckdb").taken == "translated"


def test_engine_versions(monkeypatch: pytest.MonkeyPatch) -> None:
    """D70: a probed version claims in full, an unprobed patch warns, an
    unprobed minor or major is refused."""
    versions = {"duckdb": "2.0.0", "polars": "2.1.0", "spark": "4.3.0"}
    monkeypatch.setattr(
        routes,
        "_options_json",
        lambda: {"profiles": {e: {"engine": e, "versions": [v]} for e, v in versions.items()}},
    )
    assert routes.check_version("duckdb", "2.0.0") is None
    assert routes.check_version("outside", "1.0.0") is None
    with pytest.warns(
        routes.EngineVersionWarning,
        match="2.1.0 does, and an unproved run relies on 2.1.3's own errors",
    ):
        assert routes.check_version("polars", "2.1.3")
    for v in ("2.2.0", "2.0.9", "3.0.0", "nightly"):
        with pytest.raises(
            routes.EngineVersionError, match=r"install a version of polars in >=2\.1\.0,<2\.2"
        ):
            routes.check_version("polars", v)
    with pytest.raises(routes.EngineVersionError, match="unverified=True"):
        routes.check_version("duckdb", "2.1.0")
    # The checker's profiles are the only source of the versions.
    monkeypatch.setattr(
        routes,
        "_options_json",
        lambda: {"profiles": {"duckdb": {"engine": "duckdb", "versions": ["3.0.0"]}}},
    )
    assert routes.check_version("duckdb", "3.0.0") is None


#: Installed versions that are not yet probed versions, with the issue that closes each.
UNPROBED = {"duckdb": "2.0.1"}


def test_the_range_is_the_probed_minors() -> None:
    assert routes._version_range(("2.0.0",)) == ("2.0.0", "2.1")
    assert routes._version_range(("2.0.2", "2.0.1", "2.1.0")) == ("2.0.1", "2.2")
    assert routes._version_range(("py-1.2.3",)) == ("1.2.3", "1.3")
    assert routes._version_range(()) is None
    probed = ("2.0.1", "2.1.0")
    assert [routes._in_range(v, probed) for v in ("2.0.0", "2.0.1", "2.0.7", "2.1.4", "2.2.0")] == [
        False,
        True,
        True,
        True,
        False,
    ]


#: Each engine package's own dependency on its engine (D70, V1), and
#: sverify-dbt's on DuckDB.
_BOUNDS = {
    "duckdb": ("engines/duckdb/pyproject.toml", "duckdb"),
    "polars": ("engines/polars/pyproject.toml", "polars"),
    "spark": ("engines/spark/pyproject.toml", "pyspark"),
    "dbt": ("dbt/pyproject.toml", "duckdb"),
}


@needs_repo
@pytest.mark.parametrize("package", sorted(_BOUNDS))
def test_the_package_bound_is_the_profiles_range(package: str) -> None:
    """The bound is the profile's range, written in the profile once: a bump
    of the probed versions moves the bound with it, and no released package
    allows an install its guard refuses (V7)."""
    import tomllib

    from packaging.requirements import Requirement

    path, dist = _BOUNDS[package]
    meta = tomllib.loads((ROOT / path).read_text())
    reqs = [
        *meta["project"].get("dependencies", ()),
        *(r for rs in meta["project"].get("optional-dependencies", {}).values() for r in rs),
    ]
    found = {str(Requirement(r).specifier) for r in reqs if Requirement(r).name == dist}
    engine = "duckdb" if package == "dbt" else package
    versions = routes.profiles()[engine].versions
    # One probed minor (D70 at 1.0): only then is the range one bound.
    assert len({r[:2] for v in versions if (r := routes._release(v))}) == 1
    floor, ceiling = routes._version_range(versions) or ("", "")
    assert found == {f"<{ceiling},>={floor}"}, path


def test_installed_versions_are_the_probed_ones() -> None:
    """The pinned engines match their profiles' facts; bump the facts with the pins."""
    found = {e: p for e, p in routes.profiles().items() if e in ("duckdb", "polars", "spark")}
    assert set(found) == {"duckdb", "polars", "spark"}
    for engine, prof in found.items():
        installed = routes.installed_version(engine)
        # DuckDB 2.0.1 is locked, with facts probed; its `alsoProbed` follows C2′ (#2045).
        assert installed in prof.versions or installed == UNPROBED.get(engine), engine


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
    assert (r.evidence, r.theorems, r.engine_facts) == (
        "proved",
        ("Polars.a", "Polars.b"),
        ("polars-a",),
    )
    assert "evidence: polars exact, proved by Polars.a, Polars.b" in report.details()
    from sverify import report_json

    assert report_json.route(report_json.route_json(r)) == r
    # A tested row names its engine version and its tracking issue (#1170).
    r = _on_polars(
        report, evidence="tested", facts=["polars-a", "polars-b"], version="2.1.1", issues=[1166]
    )
    assert (r.probed_version, r.issues) == ("2.1.1", (1166,))
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
    assert (
        "evidence: polars exact, proved by Rel.polars_sound on polars's model" in report.details()
    )
    from sverify import report_json

    assert report_json.route(report_json.route_json(r)) == r
    r = _on_polars(report, theorems=["Lowering.lower_correct"])
    assert str(r).endswith("; evidence proved by Lowering.lower_correct")


def test_the_class_and_the_refusals_are_the_checker_s(con) -> None:
    t = con.table("t")
    report = sv.verify(t.select("k"))
    shim = {"group": "", "option": "b", "shim": "CASE"}
    r = _on_polars(report, cls="shim", evidence="tested", shims=[shim], facts=["polars-b"])
    assert (r.taken, r.cls, r.evidence, r.shims) == ("translated", "shim", "tested", ("b: CASE",))
    assert str(r).startswith("shim (") and str(r).endswith(
        "; evidence tested at 2.1.0 (facts polars-b)"
    )
    refused = {"code": "option_refused", "group": "", "option": "b", "facts": ["polars-b"]}
    r = _on_polars(report, cls="refused", problems=[refused])
    assert r.refused and r.cls == "refused" and "b is refused on polars (polars-b)" in r.why
    report._engines = None
    r = routes.choose(report, "polars")
    assert r.refused and "gave no verdict on polars" in r.why


def test_q_refinement_against_the_postcondition(con) -> None:
    """D18's check: an engine equal to the reference up to `canon` meets a
    postcondition that observes zeros only if it says `zeros="canon"`, or
    through the row's shim."""
    t = con.table("t")
    exact = sv.verify(t.select("k"), ensures=[sv.equivalent(floats="plan")])
    canon = sv.verify(t.select("k"), ensures=[sv.equivalent(zeros="canon")])
    zeros = [_observed("zero_sign", {"zeros": "canon"})]
    r = _on_polars(exact, cls="observed", observed=zeros)
    assert r.refused and "observes its zeros" in r.why and "sv.equivalent" in r.why
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
    assert r.refused and r.cls == "refused" and "see #2540" in r.why


def test_inputs_are_checked_before_the_run(con) -> None:
    t = con.table("t")
    report = sv.verify(t.select("k", j=t.i + 1), requires={"t": [_.i <= 2]})
    with pytest.raises(PreconditionError, match=r"violate \(_.i <= 2\): refused before"):
        report.run(con, "polars", route="auto")
    # Without a route too (#604), unless the caller opts out.
    with pytest.raises(PreconditionError, match=r"violate \(_.i <= 2\): refused before"):
        report.run(con, "polars")
    report.run(con, "polars", check_requires=False)


def _eps(why: str | None = None, **kinds: tuple[float, bool]) -> dict:
    """A column's `ε` as the checker normalises it (`Realize.epsBounds`):
    each kind's value and whether it is proved."""
    bounds = {k: {"value": v, "proved": p} for k, (v, p) in kinds.items()}
    return {"bounds": bounds, "unbounded": False, "why": why}


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

    no_bound = {"bounds": {}, "unbounded": False, "why": None}
    both = {"total": _eps(abs=(222.0, False), rel=(1e-10, False)), "k": no_bound}
    assert route(sv.within(rel=1e-9), both).cls == "observed"
    assert route(sv.within(abs=1e3), both).cls == "observed"
    r = route(sv.within(rel=1e-15, abs=1.0), both)
    assert r.refused and "total is within abs=222 (tested), rel=1e-10 (tested)" in r.why
    assert "no per-plan bound" in route(sv.within(rel=1e-9), None).why
    # A bound is proved only where Lean says so; otherwise the route rests
    # on a test.
    assert route(sv.within(rel=1e-9), both).evidence == "tested"
    marked = {"total": _eps(abs=(222.0, True), rel=(1e-10, False))}
    assert route(sv.within(rel=1e-9), marked).evidence == "tested"
    assert route(sv.within(abs=1e3), marked).evidence == "proved"
    assert route(sv.within(rel=1e-9), {"total": _eps(rel=(1e-10, True))}).evidence == "proved"


def test_a_shim_does_not_lift_the_plans_bound(con) -> None:
    """A row with a shim and a per-plan bound (DuckDB's VAR row, whose
    `nan_through` handles NaN only) still refuses a tolerance its bound does
    not meet: the census's `var-within-rel-cap`, `within(rel=1e-9)` against
    abs = 1.78e-7."""
    t = con.table("t")

    def route(tolerance):
        report = sv.verify(t.select("k"), ensures=[sv.equivalent(floats=tolerance)])
        report._epsilon = {"v": _eps(abs=(1.77815e-07, True))}
        plan = [_observed("stat_algo", {"floats": {"bound": "plan"}}, shim="nan_through")]
        return _on_polars(report, cls="observed", observed=plan)

    r = route(sv.within(rel=1e-9))
    assert r.refused and "v is within abs=1.77815e-07" in r.why
    assert route(sv.within(abs=1e-6)).cls == "observed"


def test_rows_that_may_flip_under_the_bound_are_refused(con) -> None:
    """#568's threshold rule, as the checker applies it: where a filter, key
    or sort on a double may keep other rows on the engine than on the
    reference, the route is refused."""
    t = con.table("t")
    report = sv.verify(t.select("k"), ensures=[sv.equivalent(floats=sv.within(abs=1e3))])
    report._epsilon = {"total": _eps(abs=(222.0, True))}
    plan = [_observed("sum_order", {"floats": {"bound": "plan"}})]
    assert _on_polars(report, cls="observed", observed=plan).cls == "observed"
    r = _on_polars(report, cls="refused", observed=plan, problems=[{"code": "threshold"}])
    assert r.refused and "may keep other rows or give other values on polars" in r.why


def test_a_threshold_computed_from_the_data_names_exact_columns() -> None:
    """The refusal's two exits (#1608): a constant threshold takes a
    precondition, a mean or sum takes exact columns."""
    from sverify import routes

    text = routes._THRESHOLD.format(engine="duckdb")
    assert "for a constant threshold, state a precondition" in text
    assert "`x * COUNT(y) > SUM(y)`" in text
    assert "compares the exact mean, not the rounded one" in text
    assert "its product must fit BIGINT" in text


def test_a_failed_transfer_check_is_not_kept(monkeypatch) -> None:
    """The checker's transfer answer is kept per process, a failure is not:
    a timeout once does not stick (#862)."""
    import subprocess

    from sverify import routes

    calls = []

    def run(*args, **kwargs):
        calls.append(1)
        if len(calls) == 1:
            raise subprocess.TimeoutExpired("substrait-check", 60)
        return subprocess.CompletedProcess(args, 0, stdout='{"ok": true}')

    routes._answer.cache_clear()
    monkeypatch.setattr(subprocess, "run", run)
    assert routes._transfer("checker", "{}") is None
    assert routes._transfer("checker", "{}") == '{"ok": true}'
    assert routes._transfer("checker", "{}") == '{"ok": true}'
    assert len(calls) == 2
    routes._answer.cache_clear()


# -- the engine version a report's profile describes (#710) ---------------------------


def test_engine_version_is_the_profiles():
    sql, tables = "select k from t", {"t": {"k": "BIGINT"}}
    r = sv.verify(sql, tables=tables, semantics="duckdb")
    assert r.engine_version == routes.probed_version("duckdb") is not None
    assert sv.Report.from_json(r.to_json()).engine_version == r.engine_version
    assert sv.verify(sql, tables=tables).engine_version is None


def test_a_sessions_own_version_decides() -> None:
    """V6: a session of the caller's (a Spark session) reports its version."""

    class Session:
        version = "4.3.1"

    assert routes.session_version(Session()) == "4.3.1"
    assert routes.session_version("spark") is None


def _unbounded_means():
    """A mean of values in [0, 100] with no row cap (so no bound on its
    distance to the reference) and the same with a cap."""
    import ibis

    t = ibis.table({"k": "int64", "x": "float64"}, name="t")
    s = t.group_by("k").aggregate(avg=t.x.mean()).select("k", "avg")
    base = [_.x >= 0, _.x <= 100, _.x.notnull(), _.k.notnull()]
    return s, {"t": base}, {"t": [*base, sv.max_rows(1000)]}


def test_a_postcondition_that_reads_an_unbounded_double_is_refused_as_for_a_bounded_one() -> None:
    """#1045: `avg <= 100` is proved of the reference's exact mean, which an
    engine's is only near. With a row cap the route refused it; without one,
    where the checker has no bound at all, it ran. Both refuse now, naming
    `sv.approx` as the exit, and the uncapped one also names the cap."""
    s, uncapped, capped = _unbounded_means()
    for requires, what in ((capped, "is within"), (uncapped, "has no bound on its distance")):
        report = sv.verify(s, requires=requires, ensures=[_.avg <= 100], on_inferred="warn")
        r = routes.choose(report, "duckdb")
        assert r.refused and "reads avg" in r.why and what in r.why, r.why
        assert "sv.approx((_.avg <= 100))" in r.why
    assert (
        "sv.max_rows(n)"
        in routes.choose(
            sv.verify(s, requires=uncapped, ensures=[_.avg <= 100], on_inferred="warn"), "duckdb"
        ).why
    )


def test_what_the_engine_keeps_of_an_unbounded_double_still_runs() -> None:
    """The sign of a sum of values of one sign holds of every engine's value
    (`TreeSum.sign`): a postcondition that reads only that is not held, and
    `sv.approx` states the claim that is."""
    import ibis

    t = ibis.table({"k": "int64", "x": "float64"}, name="t")
    s = t.group_by("k").aggregate(total=t.x.sum()).select("k", "total")
    requires = {"t": [_.x >= 0, _.x.notnull(), _.k.notnull()]}
    sign = sv.verify(s, requires=requires, ensures=[_.total >= 0], on_inferred="warn")
    assert not routes.choose(sign, "duckdb").refused
    s2, uncapped, _capped = _unbounded_means()
    stated = sv.verify(s2, requires=uncapped, ensures=[sv.approx(_.avg <= 100)], on_inferred="warn")
    assert not routes.choose(stated, "duckdb").refused
