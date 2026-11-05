"""Engine settings against the profile's (#444, beside D14's version check):
a routed run reads the settings it will run under and refuses, or warns,
where they differ from those the profile's facts were probed under."""

from __future__ import annotations

import os
from collections.abc import Iterator

import pyarrow as pa
import pytest
from ibis import _

import sverify as sv
from sverify import _duckdb, _engine_settings, routes
from sverify.errors import EngineSettingsError, EngineSettingsWarning


@pytest.fixture
def con() -> sv.engine.Connection:
    c = sv.connect()
    c.put("t", pa.table({"k": [2, None, 1], "i": [3, 4, 5]}))
    return c


@pytest.fixture
def duckdb_global() -> Iterator:
    """`SET GLOBAL` on another cursor of the process's database, reset after."""
    other = _duckdb.cursor()
    changed: list[str] = []

    def set_global(name: str, value: str) -> None:
        other.execute(f"SET GLOBAL {name} = {value}").fetchall()
        changed.append(name)

    yield set_global
    for name in changed:
        other.execute(f"RESET GLOBAL {name}").fetchall()


@pytest.fixture
def affinity() -> Iterator:
    """Polars's engine affinity, restored after."""
    import polars as pl

    before = os.environ.get("POLARS_ENGINE_AFFINITY")
    yield pl.Config.set_engine_affinity
    if before is None:
        os.environ.pop("POLARS_ENGINE_AFFINITY", None)
    else:
        os.environ["POLARS_ENGINE_AFFINITY"] = before


def test_the_defaults_are_the_profiles() -> None:
    for engine in ("duckdb", "polars"):
        assert _engine_settings.differences(engine) == [], engine
        assert routes.check_settings(engine) == []


@pytest.mark.parametrize(
    ("name", "value", "named"),
    [
        ("integer_division", "true", "integer_division is True"),
        ("error_on_division_by_zero", "false", "error_on_division_by_zero is False"),
        ("default_collation", "'nocase'", "default_collation is 'nocase'"),
        (
            "scalar_subquery_error_on_multiple_rows",
            "false",
            "scalar_subquery_error_on_multiple_rows is False",
        ),
        ("enable_optimizer", "false", "enable_optimizer is False"),
        ("disabled_optimizers", "'filter_pushdown'", "disabled_optimizers is 'filter_pushdown'"),
    ],
)
def test_a_duckdb_setting_a_choice_depends_on_refuses(
    con, duckdb_global, name: str, value: str, named: str
) -> None:
    t = con.table("t")
    report = sv.verify(t.select("k", j=t.i // 2), requires={"t": [_.i.between(-100, 100)]})
    duckdb_global(name, value)
    with pytest.raises(EngineSettingsError, match=f"{named}.*which this plan relies on"):
        report.run(con, "duckdb", route="auto")
    # #655: the message says how to restore it.
    with pytest.raises(EngineSettingsError, match=f"restore it with `SET GLOBAL {name} = "):
        report.run(con, "duckdb")


@pytest.mark.parametrize(
    ("name", "value", "named"),
    [
        ("default_null_order", "'nulls_first'", "default_null_order is 'NULLS_FIRST'"),
        ("default_order", "'desc'", "default_order is 'DESC'"),
        ("integer_division", "true", "integer_division is True"),
    ],
)
def test_a_setting_the_plan_does_not_rely_on_warns(
    con, duckdb_global, name: str, value: str, named: str
) -> None:
    """#655: a sort states its NULLS LAST, and the written SQL spells it out,
    so the session's default null order changes nothing the plan relies on."""
    t = con.table("t")
    report = sv.verify(
        t.order_by(t.i).select("k", j=t.i + 1), requires={"t": [_.i.between(-100, 100)]}
    )
    duckdb_global(name, value)
    with pytest.warns(EngineSettingsWarning, match=f"{named}.*this plan does not rely on it"):
        report.run(con, "duckdb")
    assert report.routes["duckdb"].kind == "translated"


def test_a_session_set_on_another_cursor_is_not_seen(con) -> None:
    """sverify runs on a cursor of its own: a session-scoped `SET` on
    another cursor leaves it at the profile's settings. (Some settings,
    such as `default_null_order`, are global in DuckDB 2.0, and a plain
    `SET` reaches every cursor; the check sees those.)"""
    other = _duckdb.cursor()
    other.execute("SET integer_division = true").fetchall()
    try:
        t = con.table("t")
        report = sv.verify(t.select("k"))
        report.run(con, "duckdb", route="auto")
        assert report.routes["duckdb"].kind == "translated"
    finally:
        other.execute("RESET integer_division").fetchall()


def test_a_global_only_setting_is_seen_from_any_cursor(con) -> None:
    other = _duckdb.cursor()
    other.execute("SET default_null_order = 'nulls_first'").fetchall()
    try:
        t = con.table("t")
        with pytest.warns(EngineSettingsWarning, match="default_null_order"):
            sv.verify(t.select("k")).run(con, "duckdb", route="auto")
    finally:
        other.execute("RESET GLOBAL default_null_order").fetchall()


def test_the_time_zone_is_not_checked(con, duckdb_global) -> None:
    """No choice depends on the session's zone: the written SQL never reads
    it (duckdb-time-zones)."""
    t = con.table("t")
    report = sv.verify(t.select("k"))
    duckdb_global("TimeZone", "'America/New_York'")
    report.run(con, "duckdb", route="auto")
    assert report.routes["duckdb"].warnings == ()


def test_the_calendar_is_not_checked_and_insertion_order_warns(con, duckdb_global) -> None:
    t = con.table("t")
    report = sv.verify(t.select("k"))
    duckdb_global("Calendar", "'japanese'")
    report.run(con, "duckdb", route="auto")
    assert report.routes["duckdb"].warnings == ()
    duckdb_global("preserve_insertion_order", "false")
    with pytest.warns(EngineSettingsWarning, match="preserve_insertion_order is False"):
        report.run(con, "duckdb", route="auto")


@pytest.mark.parametrize("value", ["in-memory", "gpu"])
def test_polars_refuses_an_engine_other_than_streaming(con, monkeypatch, value: str) -> None:
    t = con.table("t")
    report = sv.verify(t.select("k"))
    monkeypatch.setenv("POLARS_ENGINE_AFFINITY", value)
    with pytest.raises(EngineSettingsError, match=f"engine_affinity is '{value}'"):
        report.run(con, "polars", route="auto")


def test_polars_streaming_variables_are_not_refused(con, monkeypatch) -> None:
    """Streaming is the engine sverify runs (#605)."""
    t = con.table("t")
    report = sv.verify(t.select("k"))
    monkeypatch.setenv("POLARS_FORCE_STREAMING", "1")
    monkeypatch.setenv("POLARS_AUTO_STREAMING", "1")
    report.run(con, "polars", route="auto")
    assert report.routes["polars"].kind == "translated"


def test_a_setting_nothing_relies_on_warns(monkeypatch) -> None:
    extra = _engine_settings.Setting("threads", (4,), "warn", (), "nothing sverify relies on")
    monkeypatch.setitem(_engine_settings.SETTINGS, "duckdb", (extra,))
    with pytest.warns(EngineSettingsWarning, match="threads is 8"):
        assert routes.check_settings("duckdb", {"threads": 8})
    assert routes.check_settings("duckdb", {"threads": 4}) == []


def test_polars_engine_affinity(con, affinity) -> None:
    t = con.table("t")
    report = sv.verify(t.select("k", j=t.i + 1), requires={"t": [_.i.between(-100, 100)]})
    affinity("streaming")
    report.run(con, "polars", route="auto")
    affinity("in-memory")
    with pytest.raises(
        EngineSettingsError, match="engine_affinity is 'in-memory'.*polars-sum-float"
    ):
        report.run(con, "polars", route="auto")
    # DuckDB does not read Polars's settings.
    report.run(con, "duckdb", route="auto")


def test_values_are_compared_normalised() -> None:
    assert (
        _engine_settings.differences(
            "duckdb",
            {
                "default_null_order": "NULLS_LAST",
                "default_order": "ASCENDING",
                "integer_division": "false",
                "error_on_division_by_zero": True,
                "ieee_floating_point_ops": "True",
                "default_collation": "",
                "scalar_subquery_error_on_multiple_rows": "true",
                "enable_optimizer": True,
                "disabled_optimizers": "",
                "preserve_insertion_order": True,
            },
        )
        == []
    )
