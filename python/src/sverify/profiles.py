"""Engines, built in or from outside sverify: a package registers one under
the entry-point group `sverify.profiles`, and sverify finds engines there and
nowhere else (#1189).

An engine is one `ProfilePlugin`. sverify's own engines register theirs in
sverify's metadata (`sverify._builtin`), the same way a package from outside
does:

```toml
[project.entry-points."sverify.profiles"]
myengine = "my_package:PROFILE"
```

Every field but `engine` is optional, and each says one thing the engine
brings:

- a profile: `versions`, `translation`, `settings`, `shim_text`,
  `installed_version`, `restore`, `checker`. A profile from outside has a
  Lean package that requires substrait-lean, states its `EngineProfile`,
  checks it with `#check_engine_profiles` and builds a checker over
  `builtinEngines ++ [its profile]` (`SubstraitCheckExamples/DummyEngine.lean`);
  its plugin names that checker. With it installed, `verify(semantics=...)`
  checks under the profile and `sverify.routes.choose` routes plans to the
  engine with their class. `$SVERIFY_CHECKER` still takes precedence over a
  plugin's checker.
- a runner: `runner`, `local`, `optional`, `session`, `modules`,
  `read_settings`. `sverify.engines.run` runs plans with it, and a
  `Connection` takes the engine when it is `local`.
- runs over Arrow tables: `run_tables`, for `sverify.partition.run_sharded`
  and, with `guard_free_theorem`, for plans whose checks a contract report
  discharged; `fallbacks`, the plan's nodes the engine runs outside its
  chosen executor, which a route records.
- a SQL dialect: `dialect`, for `to_sql`.
- its name in prose: `title`.

Several entry points may describe one engine; they are merged field by
field, so a package can add a profile to an engine whose dialect another
ships. Two that set one field differently warn, and the first one wins.
"""

from __future__ import annotations

import functools
import warnings
from collections.abc import Callable, Mapping, Sequence
from dataclasses import MISSING, dataclass, field, fields, replace
from importlib.metadata import entry_points
from pathlib import Path
from typing import Any, Literal

from sverify._unsupported import SverifyWarning

__all__ = ["ProfilePlugin", "Setting", "plugins"]

#: A plan runner: `runner(con, plan_json, session, keep=, finite=, tie_free=)`.
Runner = Callable[..., Any]
#: A run over Arrow tables: `run_tables(plan_json, tables, guard_free=, finite=)`.
TablesRunner = Callable[..., Any]

Action = Literal["refuse", "warn"]


@dataclass(frozen=True)
class Setting:
    """A setting a profile assumes."""

    name: str
    expected: tuple[Any, ...]
    """The values the profile's facts hold under (normalised: lower-case
    strings, bools)."""
    action: Action
    """`"refuse"` where a choice-table row depends on the setting, `"warn"`
    where only behaviour sverify does not rely on changes."""
    facts: tuple[str, ...] = ()
    """The facts probed under it."""
    affects: str = ""
    """What it changes, for the message."""
    options: tuple[str, ...] = ()
    """The choice-table options it changes. A plan that depends on none of
    them, or states the behaviour at each (`"stated"` in its dependency
    report, as a sort's NULLS LAST), does not rely on the setting, and the
    run only warns. Empty: every plan relies on it."""


#: The entry-point group a package registers its profile under.
GROUP = "sverify.profiles"

#: The warning when sverify's own engines are not in its metadata: an
#: editable install from before they were plugins, or a borrowed venv.
MISSING_BUILTINS = (
    "sverify's engine entry points are not installed, so it names no engine; "
    "run `uv sync` in python/ (or reinstall sverify)"
)


@dataclass(frozen=True)
class ProfilePlugin:
    """An engine, as sverify needs it: its profile, its runner and its SQL
    dialect, each optional. This is the plugin interface; sverify's own
    engines use it as a package from outside does."""

    engine: str
    """The engine's name, the profile's in the checker's tables."""
    versions: tuple[str, ...] = ()
    """The engine versions its facts were probed at (D14). Empty for a
    profile the checker carries the versions of (sverify's own) or an
    engine without one."""
    translation: str = ""
    """The translation from the reference to the engine, with what makes it
    sound, as a route line names it. Empty: no translation of its own, so a
    route takes the reference's."""
    checker: str | Path | None = None
    """A `substrait-check` built over the built-in profiles and this one;
    None to use sverify's own."""
    settings: tuple[Setting, ...] = ()
    """The engine settings the profile assumes, checked before a routed run."""
    shim_text: Mapping[str, str] = field(default_factory=dict)
    """What each of its shims does, as a route line says it."""
    installed_version: Callable[[], str | None] | None = None
    """The engine version this process runs, where it can tell."""
    restore: Callable[[Setting], str] | None = None
    """How the user puts a setting back."""
    runner: Runner | None = None
    """Runs a plan in Lean's written form over a `Connection`'s tables:
    `runner(con, plan_json, session, *, keep, finite, tie_free)`, with
    `session` the object `session` recognised (None: the engine's own).
    None: `sverify.engines.run` does not run on the engine."""
    local: bool = False
    """A `Connection` takes the engine as the one it runs plans on."""
    optional: bool = False
    """Outside the 1.x promise: `sverify.engines.ENGINES` leaves it out
    (`docs/stability.md`)."""
    session: Callable[[Any], bool] | None = None
    """Recognises a session of the engine passed as `engine=` in place of
    its name (a Spark session)."""
    modules: tuple[str, ...] = ()
    """The modules a run on it needs (`sverify.testing.installed_engines`)."""
    read_settings: Callable[[Sequence[str], Any], Mapping[str, Any]] | None = None
    """The values of the named settings in `session` (None: the session the
    next run uses); empty where it cannot tell yet. None: the settings are
    read where the engine runs."""
    dialect: Callable[[], Any] | None = None
    """The `sverify.sql.Dialect` that `to_sql` writes for it."""
    title: str = ""
    """The engine's name as prose writes it (`"DuckDB"`); empty: `engine`."""
    functions: frozenset[str] = frozenset()
    """The functions it runs that not every engine runs, by plan name
    (`sverify._support`): a function some engine lists here runs only on the
    engines that list it; any other runs everywhere."""
    window_functions: frozenset[str] = frozenset()
    """The same over a window, where fewer engines run a function than as an
    aggregate."""
    refuses: Mapping[str, tuple[str, str]] = field(default_factory=dict)
    """The functions it refuses with a reason of their own: by plan name, the
    reason and what tracks it (an issue or an upstream bug)."""
    guards: tuple[str, ...] = ()
    """The guards that raise (`sverify_raise`) its dialect writes, by the start
    of their message, beside the ones it runs as functions."""
    run_tables: TablesRunner | None = None
    """Runs a plan in Lean's written form over Arrow tables by name:
    `run_tables(plan_json, tables, *, guard_free=False, finite=True)`.
    `guard_free=True` leaves out the per-row checks a `guard_free` contract
    report discharged, keeping the assumed issues' checks; `finite=False`
    leaves out the check of an overflow to ±∞ (#575). None: no run over
    tables (`sverify.partition.run_sharded`, guard-free runs)."""
    guard_free_theorem: str = ""
    """The theorem that covers `run_tables(..., guard_free=True)`, as the
    checker names it (`"guard_free_theorem"`); empty: no guard-free run."""
    profile: bool | None = None
    """The checker has the engine's profile, and a plan may be verified under
    it (`verify(semantics=engine)`): a `--contract` request names it
    (`"profile"`). Unset, it is whether the plugin brings a checker of its
    own (`checker`), which holds its profile: a profile from outside sverify
    needs nothing more (`verifiable`). sverify's own engines say it, since
    they use sverify's checker. False for an engine that only runs plans or
    writes SQL."""
    fallbacks: Callable[[Mapping[str, Any], Mapping[str, Any]], Sequence[str]] | None = None
    """The nodes of a plan (Lean's written form, parsed) the engine would run
    outside its chosen executor over these tables (Polars's in-memory nodes
    of a streaming plan). A route records them; `streaming="require"`
    refuses a plan with any. None: the engine has one executor."""
    floor_division: bool = False
    """The engine's integer `//` and `%` floor (the remainder takes the
    divisor's sign): under its profile, the Ibis producer writes them as the
    engine computes them (`division_type: FLOOR`), and no division hint is
    given."""
    default: bool = False
    """The engine that runs plans where none is named (`sv.connect()`,
    `Node.refresh()`, `sverify refresh`): `sverify._engines.default`."""

    @property
    def verifiable(self) -> bool:
        """Whether a plan may be verified under the engine's profile:
        `profile`, or, unset, whether the plugin brings a checker. Read
        here, not stored, so two entry points of one engine merge `profile`
        as unset (`plugins`)."""
        return self.profile if self.profile is not None else self.checker is not None


def _merged(found: list[ProfilePlugin]) -> ProfilePlugin:
    """One engine's entries, merged field by field: a field takes the first
    value an entry sets; a second, different one warns."""
    out = found[0]
    for other in found[1:]:
        changes = {}
        for f in fields(ProfilePlugin)[1:]:  # `engine` is theirs in common
            mine, theirs = getattr(out, f.name), getattr(other, f.name)
            default = f.default if f.default is not MISSING else f.default_factory()  # type: ignore[misc]
            if theirs in (default, mine):
                continue
            if mine == default:
                changes[f.name] = theirs
            else:
                warnings.warn(
                    f"two {GROUP} entry points set {out.engine}'s {f.name}; "
                    "the first one's is kept",
                    ProfilePluginWarning,
                    stacklevel=3,
                )
        out = replace(out, **changes)
    return out


class ProfilePluginWarning(SverifyWarning):
    """An entry point of `sverify.profiles` did not load."""


@functools.cache
def plugins() -> dict[str, ProfilePlugin]:
    """The installed engines, by name, sverify's own among them. An entry
    point that fails to load, or loads no `ProfilePlugin`, warns and is
    skipped; entries of one engine are merged."""
    found: dict[str, list[ProfilePlugin]] = {}
    eps = list(entry_points(group=GROUP))
    if not any(getattr(ep, "value", "").startswith("sverify._builtin.") for ep in eps):
        warnings.warn(MISSING_BUILTINS, ProfilePluginWarning, stacklevel=2)
    for ep in eps:
        try:
            plugin = ep.load()
        except Exception as err:  # a broken plugin must not break sverify
            warnings.warn(
                f"{GROUP} entry point {ep.name!r} did not load: {err}",
                ProfilePluginWarning,
                stacklevel=2,
            )
            continue
        if not isinstance(plugin, ProfilePlugin):
            warnings.warn(
                f"{GROUP} entry point {ep.name!r} is no ProfilePlugin",
                ProfilePluginWarning,
                stacklevel=2,
            )
            continue
        found.setdefault(plugin.engine, []).append(plugin)
    return {e: _merged(ps) for e, ps in sorted(found.items())}


def find(engine: Any) -> ProfilePlugin | None:
    """The installed engine `engine` names: by name (any case), or a session
    an engine recognises (`ProfilePlugin.session`)."""
    if isinstance(engine, str):
        return plugins().get(engine.lower())
    return next((p for p in plugins().values() if p.session and p.session(engine)), None)


def checker() -> Path | None:
    """The checker the installed profiles name, None where none names one.

    Raises:
        ValueError: Two profiles name different checkers: neither is a
            superset of the other, so set `SVERIFY_CHECKER`.
    """
    named = {e: Path(p.checker) for e, p in plugins().items() if p.checker is not None}
    paths = set(named.values())
    if len(paths) > 1:
        raise ValueError(
            "the engine profiles "
            + ", ".join(sorted(named))
            + " each name a checker of their own; set SVERIFY_CHECKER to one built over all of them"
        )
    return next(iter(paths), None)
