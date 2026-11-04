"""The engine settings each profile assumes, checked before a routed run
(#444, alongside D14's version check in `sverify.routes`).

Internal: not part of sverify's public API.

A profile's facts were probed under the engine's default settings
(`characterization/<engine>/facts/`, each fact's `settings`). A session
that changes one of them changes what the engine computes, so a routed run
reads the settings the plan will run under and compares them with the
profile's: a setting a choice-table row depends on refuses the run, one
that only changes behaviour sverify does not rely on warns.

DuckDB: sverify runs each plan on a cursor of its own on the process's
database (`sverify.duckdb_engine`), so a session's `SET` on another cursor
leaves it alone; `SET GLOBAL` reaches it, and that is what the check sees.

Not checked, since no choice depends on them: display settings
(`set_fmt_float`, …), which change no value; threads, which change the
order of a double `SUM`, an open option every route already allows within
the plan's bound (`sum_order`); and DuckDB's `TimeZone` and `Calendar`,
which the written SQL never reads, since plans with time-zone-aware
timestamps are refused (duckdb-time-zones). DuckDB's
`dialect_compatibility_mode` and `regex_match_operator_semantics` wait on a
check of DuckDB's source.

Polars: the engine a lazy query runs on, from `pl.Config.set_engine_affinity`
(`POLARS_ENGINE_AFFINITY`), `POLARS_FORCE_STREAMING` and
`POLARS_AUTO_STREAMING`. The Polars engine pins `collect(engine="in-memory")`,
so this check is defence in depth.
"""

from __future__ import annotations

import os
from collections.abc import Callable, Mapping
from dataclasses import dataclass
from typing import Any, Literal

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


_R15 = tuple(
    f"duckdb-R15-{n}"
    for n in (
        "atan2",
        "digests",
        "double-arith",
        "double-modulus",
        "elementary",
        "int-arith",
        "int-divide",
        "int-modulus",
        "math-domain",
        "regexp",
        "round-digits",
        "round",
        "shift-left",
        "shift-right",
    )
)

#: The settings each engine profile assumes.
SETTINGS: Mapping[str, tuple[Setting, ...]] = {
    "duckdb": (
        Setting(
            "default_null_order",
            ("nulls_last",),
            "refuse",
            ("duckdb-F2",),
            "where NULLs sort in a key without a placement (null_order)",
        ),
        Setting(
            "default_order",
            ("ascending", "asc"),
            "refuse",
            (),
            "the direction of a sort key without one",
        ),
        Setting(
            "integer_division",
            (False,),
            "refuse",
            ("duckdb-F1",),
            "whether `/` of integers divides as integers (division_type)",
        ),
        Setting(
            "error_on_division_by_zero",
            (True,),
            "refuse",
            ("duckdb-R2", "duckdb-R3", "duckdb-R4", *_R15),
            "what a division by zero gives (on_division_by_zero)",
        ),
        Setting(
            "ieee_floating_point_ops",
            (True,),
            "refuse",
            ("duckdb-R4", "duckdb-R5", *_R15),
            "NaN and ±inf from double operations (nan_creation)",
        ),
        Setting(
            "default_collation",
            ("",),
            "refuse",
            ("characterization/duckdb/collate.json",),
            "how strings compare; NOCASE may change starts_with, strpos and replace",
        ),
        Setting(
            "scalar_subquery_error_on_multiple_rows",
            (True,),
            "refuse",
            ("characterization/duckdb/subquery.json",),
            "whether a scalar subquery with several rows raises or takes one",
        ),
        Setting(
            "enable_optimizer",
            (True,),
            "refuse",
            ("characterization/duckdb/settings.json",),
            "which rows a raising expression sees",
        ),
        Setting(
            "disabled_optimizers",
            ("",),
            "refuse",
            ("characterization/duckdb/settings.json",),
            "which rows a raising expression sees",
        ),
        Setting(
            "preserve_insertion_order",
            (True,),
            "warn",
            ("characterization/duckdb/order.json",),
            "the order of rows without an ORDER BY, which no route relies on",
        ),
    ),
    "polars": (
        Setting(
            "engine_affinity",
            ("auto", "in-memory"),
            "refuse",
            (
                "polars-sum-float",
                "polars-var-std",
                "polars-cov",
                "polars-mean-float",
            ),
            "the algorithms of float aggregates (sum_order, stat_algo), probed in memory",
        ),
        Setting(
            "force_streaming",
            (False,),
            "refuse",
            ("polars-sum-float", "polars-var-std", "polars-cov"),
            "the engine a query runs on (POLARS_FORCE_STREAMING), probed in memory",
        ),
        Setting(
            "auto_streaming",
            (False,),
            "refuse",
            ("polars-sum-float", "polars-var-std", "polars-cov"),
            "the engine a query runs on (POLARS_AUTO_STREAMING), probed in memory",
        ),
    ),
}


def _norm(v: Any) -> Any:
    if isinstance(v, str):
        low = v.strip().lower()
        if low in ("true", "false"):
            return low == "true"
        return low
    return v


def _duckdb_reader() -> Callable[[str], Any]:
    from sverify import duckdb_engine

    return duckdb_engine.setting


#: Polars's environment variables for its settings (`pl.Config` writes
#: `POLARS_ENGINE_AFFINITY` too).
_POLARS_ENV = {
    "engine_affinity": ("POLARS_ENGINE_AFFINITY", "auto"),
    "force_streaming": ("POLARS_FORCE_STREAMING", "0"),
    "auto_streaming": ("POLARS_AUTO_STREAMING", "0"),
}


def _polars_reader() -> Callable[[str], Any]:
    def read(name: str) -> Any:
        var, default = _POLARS_ENV[name]
        value = os.environ.get(var, default)
        if name == "engine_affinity":
            return value
        return value.strip().lower() not in ("", "0", "false", "no", "off")

    return read


_READERS: Mapping[str, Callable[[], Callable[[str], Any]]] = {
    "duckdb": _duckdb_reader,
    "polars": _polars_reader,
}


def current(engine: str) -> dict[str, Any]:
    """The settings of `engine` that its profile assumes, as the next run
    will see them; empty for an engine without a profile."""
    settings = SETTINGS.get(engine, ())
    if not settings:
        return {}
    read = _READERS[engine]()
    return {s.name: read(s.name) for s in settings}


def differences(engine: str, values: Mapping[str, Any] | None = None) -> list[tuple[Setting, Any]]:
    """The settings of `engine` (read now, or `values`) that differ from its
    profile's, with the value found."""
    found = current(engine) if values is None else values
    return [
        (s, found[s.name])
        for s in SETTINGS.get(engine, ())
        if s.name in found and _norm(found[s.name]) not in s.expected
    ]


def describe(engine: str, setting: Setting, value: Any) -> str:
    """How a check names a setting that differs."""
    want = " or ".join(repr(v) for v in setting.expected)
    facts = (
        f" ({', '.join(setting.facts[:3])}{', …' if len(setting.facts) > 3 else ''})"
        if setting.facts
        else ""
    )
    return (
        f"{engine}'s {setting.name} is {value!r}, and Profile.{engine}'s facts hold under "
        f"{want}{facts}: it changes {setting.affects}"
    )
