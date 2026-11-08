"""The engine settings each profile assumes, checked before a routed run
(#444, alongside D14's version check in `sverify.routes`).

Internal: not part of sverify's public API.

A profile's facts were probed under the engine's default settings
(`characterization/<engine>/facts/`, each fact's `settings`). A session
that changes one of them changes what the engine computes, so a routed run
reads the settings the plan will run under and compares them with the
profile's: a setting a choice-table row depends on refuses the run, one
that only changes behaviour sverify does not rely on warns.

Each engine's plugin (`sverify.profiles`) states its settings, reads them
and says how to put one back; `sverify._builtin` has sverify's own, with
what each engine's check covers.
"""

from __future__ import annotations

from collections.abc import Mapping
from typing import Any

from sverify import profiles
from sverify.profiles import Setting


def settings_of(engine: str) -> tuple[Setting, ...]:
    """The settings `engine`'s profile assumes (its plugin's)."""
    p = profiles.find(engine)
    return () if p is None else p.settings


def _norm(v: Any) -> Any:
    if isinstance(v, str):
        low = v.strip().lower()
        if low in ("true", "false"):
            return low == "true"
        return low
    return v


def current(engine: str, session: Any = None) -> dict[str, Any]:
    """The settings of `engine` that its profile assumes, as a run will see
    them (in `session`, an engine session the caller passes; None: the one
    the next run uses); empty for an engine without a profile, one whose
    plugin reads its settings where it runs, and Spark before sverify's
    session starts (it starts with `SPARK_CONF`)."""
    p = profiles.find(engine)
    settings = settings_of(engine)
    if p is None or not settings or p.read_settings is None:
        return {}
    return dict(p.read_settings([s.name for s in settings], session))


def differences(engine: str, values: Mapping[str, Any] | None = None) -> list[tuple[Setting, Any]]:
    """The settings of `engine` (read now, or `values`) that differ from its
    profile's, with the value found."""
    found = current(engine) if values is None else values
    return [
        (s, found[s.name])
        for s in settings_of(engine)
        if s.name in found and _norm(found[s.name]) not in s.expected
    ]


def relies(setting: Setting, depends: list[dict] | None) -> bool:
    """Whether a plan that depends on `depends` (None: unknown) relies on
    `setting`."""
    if not setting.options or depends is None:
        return True
    return any(d["option"] in setting.options and not d.get("stated") for d in depends)


def restore(engine: str, setting: Setting) -> str:
    """How the user puts a setting back."""
    p = profiles.find(engine)
    if p is not None and p.restore is not None:
        return p.restore(setting)
    return f"set {setting.name} back to {setting.expected[0]!r}"


def describe(engine: str, setting: Setting, value: Any) -> str:
    """How a check names a setting that differs."""
    want = " or ".join(repr(v) for v in setting.expected)
    facts = (
        f" ({', '.join(setting.facts[:3])}{', …' if len(setting.facts) > 3 else ''})"
        if setting.facts
        else ""
    )
    return (
        f"{engine}'s {setting.name} is {value!r}, and the facts of "
        f'semantics="{engine}" hold under '
        f"{want}{facts}: it changes {setting.affects}"
    )
