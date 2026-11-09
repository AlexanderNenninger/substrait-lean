"""The engines sverify names come from the installed plugins (`sverify.profiles`,
#1189): sverify's own engines register theirs as a package from outside does,
and nothing else names an engine. The types that name the profiles agree
with the checker's (`--options`, `"profiles"`, #1166)."""

from __future__ import annotations

import ast
import subprocess
import sys
import textwrap
from collections.abc import Iterator
from dataclasses import replace
from importlib.metadata import entry_points
from pathlib import Path

import pytest

from _repo import needs_repo
from sverify import _engines, engines, profiles, routes
from sverify.contracts import semantics_names
from sverify.engine import _LOCAL_ENGINES
from sverify.profiles import ProfilePlugin
from sverify.routes import _options_json
from sverify.sql import DIALECTS

BUILTIN = {"duckdb", "polars", "spark", "datafusion", "snowflake", "substrait"}
#: The built-in engines that are packages of their own (`engines/<engine>/`).
PACKAGES = {"polars", "spark"}


def _checker_profiles() -> dict[str, dict]:
    return _options_json()["profiles"]


def _engine_profiles() -> set[str]:
    """The checker's profiles of an engine."""
    return {e for e, p in _checker_profiles().items() if p.get("engine")}


def test_semantics_are_the_checker_s_profiles() -> None:
    """A plan is verified under any profile of the checker but the core: the
    reference, DuckDB's through its lift, and each plugin's that has one
    (`ProfilePlugin.profile`, #1189)."""
    assert set(semantics_names()) == set(_checker_profiles()) - {"core"}
    with_profile = {e for e, p in profiles.plugins().items() if p.verifiable}
    assert with_profile == set(_checker_profiles()) - {"core", "reference", "duckdb"}


def test_every_engine_has_a_plugin() -> None:
    assert _engine_profiles() <= _engines.NAMED
    assert set(engines.ENGINES) <= _engine_profiles()
    assert set(_LOCAL_ENGINES) == {*engines.ENGINES, "datafusion"}
    assert set(DIALECTS) <= _engines.NAMED
    # The engines within the 1.x promise, and their names in prose.
    assert set(_engines.SUPPORTED) == {*engines.ENGINES, "spark", "snowflake"}
    assert [_engines.title(e) for e in _engines.SUPPORTED] == [
        "DuckDB",
        "Polars",
        "Snowflake",
        "Spark",
    ]


def test_every_engine_a_plan_runs_on_has_a_translation() -> None:
    assert {*_engine_profiles(), *_LOCAL_ENGINES} <= set(_engines.translations())


def test_sverify_registers_its_engines_in_its_metadata() -> None:
    """The built-in engines are entry points of sverify's own distribution:
    an installed wheel without them names no engine."""
    eps = entry_points(group=profiles.GROUP)
    ours = {ep.name for ep in eps if ep.value.startswith("sverify.")}
    assert ours == BUILTIN - PACKAGES
    # An engine package registers from its own distribution (#1189).
    for e in PACKAGES:
        [ep] = [ep for ep in eps if ep.name == e]
        assert ep.dist is not None and ep.dist.name == f"sverify-{e}", ep


def test_without_the_entry_points_sverify_names_no_engine() -> None:
    """With no entry points, no engine is left: no path but the plugins'
    reaches one. sverify says so, naming the fix, since an editable install
    from before the entry points existed lands here."""
    code = textwrap.dedent(
        """
        import importlib.metadata as m
        import warnings

        m.entry_points = lambda **kw: []
        import sverify as sv
        from sverify import profiles

        with warnings.catch_warnings(record=True) as seen:
            warnings.simplefilter("always")
            profiles.plugins()
        assert [str(w.message) for w in seen] == [profiles.MISSING_BUILTINS], seen
        assert "run `uv sync` in python/" in profiles.MISSING_BUILTINS
        from sverify import routes
        from sverify.engines import ENGINES
        from sverify.sql import dialect_of

        assert ENGINES == (), ENGINES
        for name in ("duckdb", "polars", "datafusion"):
            try:
                sv.connect(name)
            except ValueError:
                pass
            else:
                raise AssertionError(name)
        for name in ("duckdb", "spark", "snowflake"):
            try:
                dialect_of(name)
            except ValueError as err:
                assert "unknown dialect" in str(err), err
            else:
                raise AssertionError(name)
        assert routes.installed_version("duckdb") is None
        assert routes.translations() == {}
        """
    )
    done = subprocess.run([sys.executable, "-c", code], capture_output=True, text=True)
    assert done.returncode == 0, done.stderr


class _EntryPoint:
    def __init__(self, name: str, value: object) -> None:
        self.name = name
        self.value = "test:TWIN"
        self._value = value

    def load(self) -> object:
        return self._value


@pytest.fixture
def twin(monkeypatch: pytest.MonkeyPatch) -> Iterator[ProfilePlugin]:
    """An engine from outside, `twin`, beside sverify's own: DuckDB's runner
    and dialect under another name, with a setting of its own."""
    duckdb = profiles.plugins()["duckdb"]
    plugin = replace(
        duckdb,
        engine="twin",
        installed_version=lambda: "0.1.0",
        read_settings=lambda names, session: {"twin_mode": "loose"},
        settings=(profiles.Setting("twin_mode", ("strict",), "refuse", (), "every value"),),
        restore=lambda s: f"twin.set({s.name!r})",
    )
    found = [*entry_points(group=profiles.GROUP), _EntryPoint("twin", plugin)]
    monkeypatch.setattr(profiles, "entry_points", lambda group: found)
    profiles.plugins.cache_clear()
    yield plugin
    profiles.plugins.cache_clear()


def test_an_engine_from_outside_runs_as_the_built_ins_do(twin: ProfilePlugin) -> None:
    """A plugin gets what sverify's own engines get, by the same path:
    `connect`, `run`, `to_sql`, its version and its settings check."""
    import pyarrow as pa

    import sverify as sv
    from sverify.engines import run, to_sql, written_plan
    from sverify.sql import dialect_of

    con = sv.connect("twin")  # type: ignore[arg-type]
    assert con.engine == "twin"
    con.put("t", pa.table({"i": [1, 2, 3]}))
    t = con.table("t")
    report = sv.verify(t.filter(t.i > 1))
    assert report.internal_plan is not None
    plan = written_plan(report.internal_plan)
    assert run(con, plan, "twin").to_pylist() == [{"i": 2}, {"i": 3}]
    assert to_sql(plan, dialect_of("twin")) == to_sql(plan, dialect_of("duckdb"))
    assert routes.installed_version("twin") == "0.1.0"
    with pytest.raises(routes.EngineSettingsError, match=r"twin_mode.*twin\.set\('twin_mode'\)"):
        routes.check_settings("twin")


def test_entries_of_one_engine_merge() -> None:
    """A dialect from one package and a profile from another make one engine
    (Snowflake's: its dialect is sverify's, its profile private)."""
    ours = profiles.plugins()["snowflake"]
    private = ProfilePlugin("snowflake", ("9.1.0",), "the private writer", checker="/x/check")
    merged = profiles._merged([ours, private])
    assert merged.dialect is ours.dialect
    assert (merged.versions, merged.translation, merged.checker) == (
        ("9.1.0",),
        "the private writer",
        "/x/check",
    )
    with pytest.warns(profiles.ProfilePluginWarning, match="snowflake's translation"):
        assert profiles._merged([merged, replace(private, translation="another")]) == merged


#: Shared modules, with the comparisons of a value with an engine's name
#: they still make (`engine == "polars"`, `x in ("duckdb", "spark")`). An
#: engine's behaviour belongs in its plugin; this count only goes down.
_NAME_TESTS = {
    "contracts.py": 2,  # semantics="polars" and "substrait" (#1166)
    "engine.py": 0,
    "_engine_settings.py": 0,
    "_engines.py": 0,
    "nodes.py": 0,
    "profiles.py": 0,
    "report.py": 1,  # Polars's streaming check (#1166)
    "routes.py": 0,
    "sql/__init__.py": 0,
    "testing.py": 0,
}


def _name_tests(path: Path) -> int:
    n = 0
    for node in ast.walk(ast.parse(path.read_text())):
        if isinstance(node, ast.Compare):
            for side in [node.left, *node.comparators]:
                consts = side.elts if isinstance(side, (ast.Tuple, ast.Set, ast.List)) else [side]
                if any(isinstance(c, ast.Constant) and c.value in BUILTIN for c in consts):
                    n += 1
                    break
    return n


@pytest.mark.parametrize("module", sorted(_NAME_TESTS))
def test_shared_code_names_no_engine(module: str) -> None:
    import sverify

    found = _name_tests(Path(sverify.__file__).parent / module)
    assert found <= _NAME_TESTS[module], f"{module}: {found} comparisons with an engine's name"


#: Literals that list two or more engines by name (a tuple, list, set or
#: dict's keys), per file of `sverify` and `sverify_dev`. A list of the
#: engines comes from `sverify._engines`; what is left is per-function data
#: (`_support`, the coverage cases; #1166's PR D) and the catalogue's own
#: columns. This count only goes down.
_NAME_LISTS = {
    "sverify/_functions.py": 6,
    "sverify/_support.py": 2,
    "sverify/engine.py": 1,
    "sverify/report.py": 1,
    "sverify_dev/bugs.py": 2,
    "sverify_dev/catalogue.py": 3,
    "sverify_dev/coverage.py": 1,
    "sverify_dev/coverage_cases/_common.py": 3,
    "sverify_dev/coverage_cases/joins.py": 1,
    "sverify_dev/coverage_cases/numeric.py": 1,
    "sverify_dev/coverage_cases/strings.py": 1,
    "sverify_dev/coverage_cases/temporal.py": 3,
    "sverify_dev/probe_float_arith.py": 2,
    "sverify_dev/probe_statistics.py": 1,
    "sverify_dev/probe_window_sums.py": 1,
}


def _name_lists(path: Path) -> int:
    n = 0
    for node in ast.walk(ast.parse(path.read_text())):
        if isinstance(node, (ast.Tuple, ast.List, ast.Set)):
            elts: list = node.elts
        elif isinstance(node, ast.Dict):
            elts = list(node.keys)
        else:
            continue
        if sum(isinstance(c, ast.Constant) and c.value in BUILTIN for c in elts) >= 2:
            n += 1
    return n


@needs_repo
def test_engine_lists_come_from_the_plugins() -> None:
    import sverify

    src = Path(sverify.__file__).parent.parent
    tools = src.parent / "tools"
    found = {}
    for root in (src / "sverify", tools / "sverify_dev"):
        for f in root.rglob("*.py"):
            if n := _name_lists(f):
                found[f.relative_to(root.parent).as_posix()] = n
    over = {f: n for f, n in found.items() if n > _NAME_LISTS.get(f, 0)}
    assert not over, f"lists of engines by name: {over}; take them from sverify._engines"
