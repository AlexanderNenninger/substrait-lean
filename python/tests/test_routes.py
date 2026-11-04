"""Routes from a verified plan to an engine, and engine versions (#444 D10, D13, D14)."""

from __future__ import annotations

import ibis
import pyarrow as pa
import pytest
from ibis import _

import sverify as sv
from sverify import routes


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
    assert "route on polars: reference" in str(report)
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


def test_without_route_run_is_unchanged(con) -> None:
    duck = sv.verify(
        "SELECT k, i % 3 AS m FROM t", tables={"t": con.table("t")}, semantics="duckdb"
    )
    duck.run(con, "duckdb")
    assert duck.routes == {}


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
    assert "int.mod's division_type: Profile.duckdb gives TRUNCATE, polars gives FLOOR" in r.reason
    assert routes.choose(duck, "datafusion", "transfer").kind == "transfer"
    # The checker's own dependency report narrows the check.
    duck.depends = []
    assert routes.choose(duck, "polars", "transfer").kind == "transfer"


def test_transfer_without_tables_is_refused_with_the_reason(monkeypatch, con) -> None:
    monkeypatch.setattr(routes, "_options_json", lambda: {})
    duck = sv.verify(
        "SELECT k, i % 3 AS m FROM t", tables={"t": con.table("t")}, semantics="duckdb"
    )
    r = routes.choose(duck, "polars")
    assert r.refused
    assert "no choices table" in r.reason
    assert "not verified under the reference" in r.reason


def test_unproved_plan_is_refused(con) -> None:
    t = con.table("t")
    report = sv.verify(t.select("k", j=t.i * t.i), infer=False)
    assert not report.proved
    assert routes.choose(report, "duckdb").reason.startswith("the plan is not verified")


def test_determinism_is_reported_and_required_on_request() -> None:
    t = ibis.table({"k": "int64", "o": "int64", "v": "int64"}, name="t")
    expr = t.group_by("k").aggregate(f=t.v.first(order_by=t.o))
    report = sv.verify(expr)
    assert report.proved and not report.deterministic
    r = routes.choose(report, "duckdb")
    assert r.kind == "reference" and not r.deterministic
    assert any("open choice" in w for w in r.warnings)
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
    with pytest.raises(routes.EngineVersionError, match="re-run the probes"):
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
