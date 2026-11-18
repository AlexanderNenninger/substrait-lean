"""sverify's Spark engine (#1189): the Spark SQL dialect
(`sverify_spark.dialect`: `SPARK`, `SPARK_CONF`), with shims where Spark
differs from the reference, proved against Spark's facts (`Rel.spark_sound`),
and the runner on a Spark session (`sverify_spark.engine`), registered as the
`ProfilePlugin` `PLUGIN` under the entry-point group `sverify.profiles`.

Spark's settings: a run reads the session's `spark.conf`: sverify's local
session (`sverify_spark.engine.session`, which starts with `SPARK_CONF`) or
the session passed as the engine. The facts were probed under ANSI mode,
with `TIMESTAMP` as `TIMESTAMP_NTZ` and the session time zone UTC
(spark-exec-settings); the writer's SQL relies on those and on
`caseSensitive` and `escapedStringLiterals`, so a session that changes them
refuses every run. The legacy statistics, decimal-precision and
`percentile_disc` settings refuse only plans whose options they change.
"""

from __future__ import annotations

import json
import sys
from collections.abc import Mapping, Sequence
from typing import Any

from sverify._unsupported import ISSUE_271, RANGE_GUARD
from sverify.profiles import ProfilePlugin, Setting
from sverify_spark.store import ArrowStore

#: The settings Spark's profile assumes.
SETTINGS: tuple[Setting, ...] = (
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
        "the wall clock the written SQL reads microseconds as (`unix_micros`, `timestamp_micros`)",
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
)

#: Spark 4.3.0's defaults for the settings `SETTINGS` reads (spark-exec-settings).
DEFAULTS: Mapping[str, str] = {
    "spark.sql.ansi.enabled": "true",
    "spark.sql.timestampType": "TIMESTAMP_LTZ",
    "spark.sql.caseSensitive": "false",
    "spark.sql.parser.escapedStringLiterals": "false",
    "spark.sql.legacy.statisticalAggregate": "false",
    "spark.sql.decimalOperations.allowPrecisionLoss": "true",
    "spark.sql.legacy.percentileDiscCalculation": "false",
}


def _run(
    con: Any, plan_json: str, session: Any, *, keep: bool, finite: bool, tie_free: bool
) -> Any:
    from sverify.engine import _rename_tables, read_tables
    from sverify_spark import engine as spark_engine

    plan = json.loads(plan_json)
    # Spark's temporary views take plain names, not the delta plans' `t$delta`.
    names = {t: f"__sverify_{i}" for i, t in enumerate(read_tables(plan))}
    _rename_tables(plan, names)
    spark = session if session is not None else spark_engine.session()
    tables = {alias: _table(con, t, spark) for t, alias in names.items()}
    return spark_engine.run(plan, tables, session, deterministic=tie_free, finite=finite)


def _table(con: Any, name: str, spark: Any) -> Any:
    """Table `name` of the connection for Spark: a `Scan` of local files as it is
    (the session reads it, `sverify_spark.scan`) where this route covers it, any
    other table as Arrow. A scan it does not cover (a `where`, which is
    DuckDB SQL, partition constants, a column mapping, or files that are not
    local) reads through Arrow on a session that shares the driver's filesystem, and is refused on a Spark
    Connect or non-local-master session: the server-side read is N12 of #173."""
    from sverify._scan import Scan
    from sverify._unsupported import Unsupported
    from sverify_spark.scan import shares_filesystem

    table = con.get(name)
    if not isinstance(table, Scan) or not table.readable():
        return con._arrow[name]
    from sverify._scan import local_path

    files = [*table.files, *(e.file for e in table.equality)]
    covered = (
        table.where is None
        and not getattr(table, "partitions", None)
        and not getattr(table, "physical", None)
        and all(local_path(f) is not None for f in files)
    )
    if covered:
        return table
    if shares_filesystem(spark):
        return con._arrow[name]
    raise Unsupported(
        f"{name}: a table with a `where`, partition values or column mapping is read through "
        "Arrow on a local Spark session only; reading it on a Spark Connect or cluster session "
        "is N12 of #173"
    )


def _is_session(obj: Any) -> bool:
    """A Spark session (any object that is not an engine's name was one,
    before engines were plugins; a session's class is pyspark's)."""
    return type(obj).__module__.startswith("pyspark.")


def _version() -> str | None:
    import pyspark

    return pyspark.__version__


def _local_session() -> Any:
    """The session a run on `"spark"` uses: sverify's local one, if it has
    started (`sverify_spark.engine.session`); None before, when the run
    starts it with `SPARK_CONF`."""
    engine = sys.modules.get("sverify_spark.engine")
    if engine is None or engine.session.cache_info().currsize == 0:
        return None
    return engine.session()


def _read_settings(names: Sequence[str], session: Any) -> dict[str, Any]:
    spark = session if session is not None else _local_session()
    if spark is None:
        return {}
    return {n: spark.conf.get(n, DEFAULTS.get(n)) for n in names}


def _restore(setting: Setting) -> str:
    from sverify_spark.dialect import SPARK_CONF

    v = SPARK_CONF.get(setting.name, DEFAULTS.get(setting.name, setting.expected[0]))
    return f'spark.conf.set("{setting.name}", "{v}")'


def _dialect() -> Any:
    from sverify_spark.dialect import SPARK

    return SPARK


PLUGIN = ProfilePlugin(
    "spark",
    store=ArrowStore,
    title="Spark",
    profile=True,
    translation="sverify's Spark SQL writer, with shims where Spark differs from the "
    "reference, proved against Spark's facts (Rel.spark_sound) and tested against "
    "the reference",
    settings=SETTINGS,
    installed_version=_version,
    restore=_restore,
    runner=_run,
    session=_is_session,
    modules=("pyspark",),
    read_settings=_read_settings,
    dialect=_dialect,
    refuses={
        "sverify_raise": (
            "Spark's SQL of the date guards exhausts its JVM's heap (a date from columns "
            "is 38 KB of nested CASEs)",
            ISSUE_271,
        )
    },
    guards=(RANGE_GUARD,),
    shim_text={"null_order": "NULLs sorted as the reference sorts them"},
)
