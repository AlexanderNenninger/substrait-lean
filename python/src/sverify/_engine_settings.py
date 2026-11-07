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

Spark: a run reads the session's `spark.conf`: sverify's local session
(`sverify.spark_engine.session`, which starts with `SPARK_CONF`) or the
session passed as the engine. The facts were probed under ANSI mode, with
`TIMESTAMP` as `TIMESTAMP_NTZ` and the session time zone UTC
(spark-exec-settings); the writer's SQL relies on those and on
`caseSensitive` and `escapedStringLiterals`, so a session that changes them
refuses every run. The legacy statistics, decimal-precision and
`percentile_disc` settings refuse only plans whose options they change.

Polars: sverify runs the streaming engine (`collect(engine="streaming")`,
#605); the in-memory engine is legacy. The check refuses an engine affinity
that forces another engine (`pl.Config.set_engine_affinity("in-memory")`,
which writes `POLARS_ENGINE_AFFINITY`). With the engine pinned, it is
defence in depth.
"""

from __future__ import annotations

import os
from collections.abc import Callable, Mapping, Sequence
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
    options: tuple[str, ...] = ()
    """The choice-table options it changes. A plan that depends on none of
    them, or states the behaviour at each (`"stated"` in its dependency
    report, as a sort's NULLS LAST), does not rely on the setting, and the
    run only warns. Empty: every plan relies on it."""


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
            "where NULLs sort in a key without a placement (null_order), and in "
            "FIRST/LAST(... ORDER BY) and list_sort",
            ("null_order", "list_null_order"),
        ),
        Setting(
            "default_order",
            ("ascending", "asc"),
            "refuse",
            (),
            "the direction of a sort key without one",
            ("null_order", "list_null_order"),
        ),
        Setting(
            "integer_division",
            (False,),
            "refuse",
            ("duckdb-F1",),
            "whether `/` of integers divides as integers (division_type)",
            ("division_type",),
        ),
        Setting(
            "error_on_division_by_zero",
            (True,),
            "refuse",
            ("duckdb-R2", "duckdb-R3", "duckdb-R4", *_R15),
            "what a division by zero gives (on_division_by_zero): `//` and `%` give NULL "
            "instead of raising; deprecated in DuckDB 2.0.0, still read and still in "
            "effect there",
            ("on_division_by_zero",),
        ),
        Setting(
            "ieee_floating_point_ops",
            (True,),
            "refuse",
            ("duckdb-R4", "duckdb-R5", *_R15),
            "NaN and ±inf from double operations (nan_creation)",
            ("nan_creation", "float_overflow"),
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
    "spark": (
        Setting(
            "spark.sql.ansi.enabled",
            (True,),
            "refuse",
            ("spark-exec-settings", "spark-int-arith", "spark-int-divide", "spark-double-divide"),
            "whether integer overflow, a zero divisor and a bad cast raise or give NULL or a "
            "wrapped value (overflow, on_division_by_zero, cast_failure)",
        ),
        Setting(
            "spark.sql.timestampType",
            ("timestamp_ntz",),
            "refuse",
            ("spark-time-zones", "spark-type-names"),
            "what TIMESTAMP means: an instant in the session time zone or a wall-clock time",
        ),
        Setting(
            "spark.sql.session.timeZone",
            ("utc", "etc/utc"),
            "refuse",
            ("spark-time-zones",),
            "the wall clock the written SQL reads microseconds as (`unix_micros`, "
            "`timestamp_micros`)",
        ),
        Setting(
            "spark.sql.caseSensitive",
            (True,),
            "refuse",
            ("spark-exec-settings",),
            "whether columns `a` and `A` are one column",
        ),
        Setting(
            "spark.sql.parser.escapedStringLiterals",
            (False,),
            "refuse",
            ("spark-exec-settings",),
            "how a backslash in a string literal reads",
        ),
        Setting(
            "spark.sql.legacy.statisticalAggregate",
            (False,),
            "refuse",
            ("spark-var-stddev", "spark-covar", "spark-corr"),
            "whether a sample variance, covariance or correlation of one value is NULL or NaN "
            "(stat_degenerate)",
            ("stat_degenerate", "stat_algo"),
        ),
        Setting(
            "spark.sql.decimalOperations.allowPrecisionLoss",
            (True,),
            "refuse",
            ("spark-decimal-arith",),
            "the scale of a decimal result past 38 digits (decimal_rescale)",
            ("decimal_rescale",),
        ),
        Setting(
            "spark.sql.legacy.percentileDiscCalculation",
            (False,),
            "refuse",
            ("spark-quantile",),
            "which value percentile_disc takes (quantile_interp)",
            ("quantile_interp",),
        ),
    ),
    "polars": (
        Setting(
            "engine_affinity",
            ("auto", "streaming"),
            "refuse",
            (
                "polars-sum-float",
                "polars-var-std",
                "polars-cov",
                "polars-mean-float",
            ),
            "the engine a query runs on, and with it the algorithms of float aggregates "
            "(sum_order, stat_algo); sverify runs Polars's streaming engine (#605)",
        ),
    ),
}


def settings_of(engine: str) -> tuple[Setting, ...]:
    """The settings `engine`'s profile assumes: `SETTINGS`, or those of an
    installed profile from outside sverify (`sverify.profiles`)."""
    if engine in SETTINGS:
        return SETTINGS[engine]
    from sverify import profiles

    p = profiles.plugins().get(engine)
    return () if p is None else p.settings


def _norm(v: Any) -> Any:
    if isinstance(v, str):
        low = v.strip().lower()
        if low in ("true", "false"):
            return low == "true"
        return low
    return v


def _duckdb_reader() -> Callable[[Sequence[str]], dict[str, Any]]:
    from sverify import duckdb_engine

    return duckdb_engine.settings


#: Polars's environment variables for its settings (`pl.Config` writes them).
_POLARS_ENV = {
    "engine_affinity": ("POLARS_ENGINE_AFFINITY", "auto"),
}


def _polars_reader() -> Callable[[Sequence[str]], dict[str, Any]]:
    def read(names: Sequence[str]) -> dict[str, Any]:
        return {n: os.environ.get(*_POLARS_ENV[n]) for n in names}

    return read


def spark_values(spark: Any) -> dict[str, Any]:
    """The settings of `SETTINGS["spark"]` in the session `spark`, with
    Spark's defaults for those it does not set."""
    return {s.name: spark.conf.get(s.name, _SPARK_DEFAULTS.get(s.name)) for s in SETTINGS["spark"]}


#: Spark 4.3.0's defaults for the settings `SETTINGS["spark"]` reads (spark-exec-settings).
_SPARK_DEFAULTS: Mapping[str, str] = {
    "spark.sql.ansi.enabled": "true",
    "spark.sql.timestampType": "TIMESTAMP_LTZ",
    "spark.sql.caseSensitive": "false",
    "spark.sql.parser.escapedStringLiterals": "false",
    "spark.sql.legacy.statisticalAggregate": "false",
    "spark.sql.decimalOperations.allowPrecisionLoss": "true",
    "spark.sql.legacy.percentileDiscCalculation": "false",
}


def _spark_session() -> Any:
    """The session a run on `"spark"` uses: sverify's local one, if it has
    started (`sverify.spark_engine.session`); None before, when the run
    starts it with `SPARK_CONF`."""
    import sys

    engine = sys.modules.get("sverify.spark_engine")
    if engine is None or engine.session.cache_info().currsize == 0:
        return None
    return engine.session()


#: Each engine's reader of its settings, all in one call.
_READERS: Mapping[str, Callable[[], Callable[[Sequence[str]], dict[str, Any]]]] = {
    "duckdb": _duckdb_reader,
    "polars": _polars_reader,
}


def current(engine: str) -> dict[str, Any]:
    """The settings of `engine` that its profile assumes, as the next run
    will see them; empty for an engine without a profile, and for Spark
    before sverify's session starts (it starts with `SPARK_CONF`)."""
    settings = settings_of(engine)
    if not settings or engine not in _READERS and engine != "spark":
        # A profile from outside: its settings are read where it runs.
        return {}
    if engine == "spark":
        spark = _spark_session()
        return {} if spark is None else spark_values(spark)
    return _READERS[engine]()([s.name for s in settings])


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
    if engine == "duckdb":
        v = setting.expected[0]
        value = f"'{v}'" if isinstance(v, str) else str(v).lower()
        return f"SET GLOBAL {setting.name} = {value}"
    if engine == "polars" and setting.name == "engine_affinity":
        return 'pl.Config.set_engine_affinity("streaming")'
    if engine == "spark":
        from sverify.sql.spark import SPARK_CONF

        v = SPARK_CONF.get(setting.name, _SPARK_DEFAULTS.get(setting.name, setting.expected[0]))
        return f'spark.conf.set("{setting.name}", "{v}")'
    from sverify import profiles

    p = profiles.plugins().get(engine)
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
