"""Engine profiles from outside sverify: a package registers one under the
entry-point group `sverify.profiles`.

A profile from outside comes in two parts. Its Lean package requires
substrait-lean, states its `EngineProfile` (choices, observation rows, the
theorem its translation rests on), checks it with `#check_engine_profiles`,
and builds a checker over `builtinEngines ++ [its profile]`
(`SubstraitCheckExamples/DummyEngine.lean` shows how). Its Python package
names that checker and what the routes need, as a `ProfilePlugin`:

```toml
[project.entry-points."sverify.profiles"]
myengine = "my_package:PROFILE"
```

With the package installed, `verify(semantics="myengine")` checks under the
profile, and `sverify.routes.choose` routes plans to the engine with their
class, as for the engines sverify ships with. `$SVERIFY_CHECKER` still takes
precedence over a plugin's checker.
"""

from __future__ import annotations

import functools
import warnings
from collections.abc import Callable, Mapping
from dataclasses import dataclass, field
from importlib.metadata import entry_points
from pathlib import Path

from sverify._engine_settings import Setting
from sverify._unsupported import SverifyWarning

__all__ = ["ProfilePlugin", "Setting", "plugins"]

#: The entry-point group a package registers its profile under.
GROUP = "sverify.profiles"


@dataclass(frozen=True)
class ProfilePlugin:
    """An engine profile from outside sverify, as the routes need it."""

    engine: str
    """The engine's name, the profile's in the checker's tables."""
    versions: tuple[str, ...]
    """The engine versions its facts were probed at (D14)."""
    translation: str
    """The translation from the reference to the engine, with what makes it
    sound, as a route line names it."""
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


class ProfilePluginWarning(SverifyWarning):
    """An entry point of `sverify.profiles` did not load."""


@functools.cache
def plugins() -> dict[str, ProfilePlugin]:
    """The installed profiles from outside sverify, by engine. An entry point
    that fails to load, or loads no `ProfilePlugin`, warns and is skipped."""
    out: dict[str, ProfilePlugin] = {}
    for ep in entry_points(group=GROUP):
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
        out[plugin.engine] = plugin
    return out


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
