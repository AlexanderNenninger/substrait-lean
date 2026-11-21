"""The engines sverify names, from the installed plugins (#1166, #1189).

Internal: not part of sverify's public API. Every engine, sverify's own
among them, is a `ProfilePlugin` registered under `sverify.profiles`
(`sverify._builtin`); the sets the rest of sverify reads are derived from
them here, once, when sverify is imported. Which engines have a profile of
their own is the checker's (`substrait-check --options`, `"profiles"`);
`tests/test_engines_table.py` checks the types that name them (`Engine`,
`Semantics`) against it.
"""

from __future__ import annotations

from collections.abc import Callable, Mapping
from typing import Any

from sverify.profiles import plugins

_FOUND = plugins()

#: The engines a `Connection` runs plans on (`sverify.engines.ENGINES`).
LOCAL: tuple[str, ...] = tuple(e for e, p in _FOUND.items() if p.local)
#: The engines sverify supports, local or not: every plugin that runs plans
#: or writes their SQL (a profile alone, Substrait's, is no engine).
SUPPORTED: tuple[str, ...] = tuple(e for e, p in _FOUND.items() if p.local or p.runner or p.dialect)
#: The dialects `to_sql` writes.
DIALECTS: tuple[str, ...] = tuple(e for e, p in _FOUND.items() if p.dialect)
#: Every engine sverify names: each plugin's.
NAMED: frozenset[str] = frozenset(_FOUND)
#: The modules each engine needs.
MODULES: Mapping[str, tuple[str, ...]] = {e: p.modules for e, p in _FOUND.items()}


def _engine_extras() -> dict[str, str]:
    """The extras of sverify named for the engine package they install, with
    that package's module (`polars`: `sverify-polars`, so `sverify_polars`),
    read from sverify's own metadata."""
    import re
    from importlib.metadata import PackageNotFoundError, requires

    try:
        reqs = requires("sverify") or []
    except PackageNotFoundError:
        return {}
    found = (re.match(r"sverify-([\w-]+).*extra *== *['\"]([\w-]+)['\"]", r) for r in reqs)
    return {m.group(2): f"sverify_{m.group(1)}" for m in found if m and m.group(1) == m.group(2)}


def not_installed(name: object) -> ImportError | None:
    """The error for a name of an engine sverify installs as an extra, where
    the engine's package or a module it runs on is missing: it names the
    extra. None for any other name."""
    from importlib.util import find_spec

    if not isinstance(name, str) or (module := _engine_extras().get(name.lower())) is None:
        return None
    p = plugins().get(name.lower())
    # A package that is installed but registers no plugin is a broken
    # install (`profiles.MISSING_BUILTINS`), which no extra fixes.
    modules = (*(p.modules or (p.engine,)), module) if p is not None else (module,)
    if all(find_spec(m) is not None for m in modules):
        return None
    return ImportError(f"engine {name!r} is not installed: pip install 'sverify[{name.lower()}]'")


def default() -> str:
    """The engine that runs plans where none is named: the installed one that
    says so (`ProfilePlugin.default`), or else the first local one. `verify`
    needs none; running a plan does.

    Raises:
        ValueError: No engine that runs plans is installed.
    """
    from sverify import profiles

    found = profiles.plugins()
    local = [e for e, p in found.items() if p.local]
    named = [e for e in local if found[e].default]
    if not (named or local):
        raise ValueError(
            "no engine that runs plans is installed: install one, e.g. "
            "pip install 'sverify[duckdb]' or 'sverify[polars]'"
        )
    return (named or local)[0]


def sql_dialect() -> Callable[[], Any]:
    """The SQL dialect of the engine that runs plans, or where it has none (or
    none is installed: `verify` needs no engine), DuckDB's, which every
    install writes."""
    from sverify import profiles

    found = profiles.plugins()
    try:
        dialect = found[default()].dialect
    except ValueError:
        dialect = None
    dialect = dialect or found["duckdb"].dialect
    assert dialect is not None
    return dialect


def translations() -> dict[str, str]:
    """The translation from the reference to each engine that has one of its
    own, with what makes it sound: every engine a route may reach."""
    return {e: p.translation for e, p in plugins().items() if p.translation}


def title(engine: str) -> str:
    """`engine`'s name as prose writes it (`"DuckDB"`)."""
    p = plugins().get(engine)
    return p.title if p is not None and p.title else engine
