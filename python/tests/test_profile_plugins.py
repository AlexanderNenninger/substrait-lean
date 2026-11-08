"""Engine profiles from outside sverify (`sverify.profiles`): a package
registers a `ProfilePlugin` under the entry-point group `sverify.profiles`,
beside sverify's own engines, and the routes, the settings check, the version
check and `semantics=` take it in. The Lean side, a checker over `builtinEngines ++ [a profile]`, is
`SubstraitCheckExamples/DummyEngine.lean`.
"""

from __future__ import annotations

from collections.abc import Iterator
from importlib.metadata import entry_points
from pathlib import Path

import pyarrow as pa
import pytest
from ibis import _

import sverify as sv
from sverify import _checker, _engine_settings, profiles, routes
from sverify.engines import SNOWFLAKE, to_sql, written_plan
from sverify.profiles import ProfilePlugin, Setting
from sverify.routes import EngineSettingsError, EngineVersionError

DUMMY = ProfilePlugin(
    engine="dummy",
    versions=("1.2.0",),
    translation="the dummy writer, proved (DummyEngine.dummy_sound)",
    settings=(Setting("dummy_mode", ("strict",), "refuse", ("dummy-mode",), "every value"),),
    shim_text={"dummy_shim": "a dummy rewrite"},
    installed_version=lambda: "1.2.3",
    restore=lambda s: f"dummy.set({s.name!r}, {s.expected[0]!r})",
)


class _EntryPoint:
    def __init__(self, name: str, value: object) -> None:
        self.name = name
        self._value = value

    def load(self) -> object:
        if isinstance(self._value, Exception):
            raise self._value
        return self._value


@pytest.fixture
def installed(monkeypatch: pytest.MonkeyPatch) -> Iterator[None]:
    """The dummy profile installed, beside a broken entry point and one that
    loads something else."""
    found = [
        *entry_points(group=profiles.GROUP),
        _EntryPoint("dummy", DUMMY),
        _EntryPoint("broken", ImportError("no module named dummy_broken")),
        _EntryPoint("other", object()),
    ]
    monkeypatch.setattr(profiles, "entry_points", lambda group: found)
    profiles.plugins.cache_clear()
    yield
    profiles.plugins.cache_clear()


def test_no_profile_from_outside_by_default() -> None:
    assert "dummy" not in profiles.plugins()


def test_a_profile_from_outside_is_loaded(installed: None) -> None:
    with pytest.warns(profiles.ProfilePluginWarning) as warned:
        found = profiles.plugins.__wrapped__()
    assert set(found) == {"dummy", "duckdb", "polars", "spark", "datafusion", "snowflake"}
    assert {str(w.message).split("'")[1] for w in warned} == {"broken", "other"}


@pytest.mark.filterwarnings("ignore::sverify.profiles.ProfilePluginWarning")
def test_the_routes_take_it_in(installed: None) -> None:
    assert routes.profiles()["dummy"].versions == ("1.2.0",)
    assert routes.translations()["dummy"] == DUMMY.translation
    assert routes.shim_text("dummy_shim") == "a dummy rewrite"
    assert routes.installed_version("dummy") == "1.2.3"
    assert routes.check_version("dummy", "1.2.0") is None
    with pytest.raises(EngineVersionError, match="probed at 1.2.0"):
        routes.check_version("dummy", "2.0.0")


@pytest.mark.filterwarnings("ignore::sverify.profiles.ProfilePluginWarning")
def test_its_settings_are_checked(installed: None) -> None:
    assert _engine_settings.differences("dummy", {"dummy_mode": "strict"}) == []
    with pytest.raises(EngineSettingsError, match=r"dummy_mode.*dummy\.set\('dummy_mode'"):
        routes.check_settings("dummy", {"dummy_mode": "loose"})


@pytest.mark.filterwarnings("ignore::sverify.profiles.ProfilePluginWarning")
def test_semantics_needs_a_checker_with_the_profile(installed: None) -> None:
    con = sv.connect()
    con.put("t", pa.table({"i": [1, 2]}))
    t = con.table("t")
    # The checker in use is sverify's own, which has no profile "dummy".
    with pytest.raises(ValueError, match='no profile "dummy".*SVERIFY_CHECKER'):
        sv.verify(t.filter(t.i > 0), semantics="dummy")  # type: ignore[arg-type]


def test_the_checker_precedence(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    mine = tmp_path / "substrait-check-dummy"
    mine.touch()
    monkeypatch.delenv("SVERIFY_CHECKER", raising=False)
    monkeypatch.delenv("SVERIFY_CHECK", raising=False)
    monkeypatch.setattr(
        profiles, "plugins", lambda: {"dummy": ProfilePlugin("dummy", ("1.2.0",), "", checker=mine)}
    )
    assert _checker._checker_file() == mine
    monkeypatch.setenv("SVERIFY_CHECKER", str(tmp_path / "env-checker"))
    assert _checker._checker_file() == tmp_path / "env-checker"
    monkeypatch.delenv("SVERIFY_CHECKER")
    monkeypatch.setattr(
        profiles,
        "plugins",
        lambda: {
            "a": ProfilePlugin("a", (), "", checker=mine),
            "b": ProfilePlugin("b", (), "", checker=tmp_path / "other"),
        },
    )
    with pytest.raises(ValueError, match="a, b each name a checker"):
        _checker._checker_file()


def test_snowflake_sql_without_a_profile_is_the_reference_translation() -> None:
    """Without an installed Snowflake profile, a plan verified under the
    reference exports to Snowflake as before: the reference's translation, no
    class claimed, nothing refused."""
    con = sv.connect()
    con.put("orders", pa.table({"id": [1, 2], "amount": [30, 5]}))
    report = sv.verify(
        con.table("orders").filter(_.amount > 10).group_by("id").aggregate(s=_.amount.sum())
    )
    assert "snowflake" not in routes.translations()
    assert report.internal_plan is not None
    assert report.to_sql("snowflake") == to_sql(
        written_plan(report.internal_plan),
        SNOWFLAKE,
        deterministic=report.deterministic,
        finite=True,
    )
