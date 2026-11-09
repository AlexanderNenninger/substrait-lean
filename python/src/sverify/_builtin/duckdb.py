"""DuckDB (`sverify.duckdb_engine`): sverify's default engine, its lowering
proved for every plan.

DuckDB's settings: sverify runs each plan on a cursor of its own on the
process's database (`sverify.duckdb_engine`), so a session's `SET` on another
cursor leaves it alone; `SET GLOBAL` reaches it, and that is what the check
sees. Not checked, since no choice depends on them: display settings, threads
(the order of a double `SUM`, `sum_order`, which every route allows within
the plan's bound), and `TimeZone` and `Calendar`, which the written SQL never
reads (plans with time-zone-aware timestamps are refused, duckdb-time-zones).
`dialect_compatibility_mode` and `regex_match_operator_semantics` wait on a
check of DuckDB's source.
"""

from __future__ import annotations

import json
from collections.abc import Sequence
from typing import Any

from sverify.profiles import ProfilePlugin, Setting

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

#: The settings DuckDB's profile assumes.
SETTINGS: tuple[Setting, ...] = (
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
)


def _run(
    con: Any, plan_json: str, session: Any, *, keep: bool, finite: bool, tie_free: bool
) -> Any:
    from sverify import duckdb_engine
    from sverify.engine import read_tables

    # DuckDB reads `Scan` and `Resident` tables where they are.
    tables = {t: con.get(t) for t in read_tables(json.loads(plan_json))}
    if keep:
        return duckdb_engine.run(plan_json, tables, keep=True, finite=finite)
    return duckdb_engine.run(plan_json, tables, finite=finite)


def _version() -> str | None:
    import duckdb

    return duckdb.__version__


def _read_settings(names: Sequence[str], session: Any) -> dict[str, Any]:
    from sverify import duckdb_engine

    return duckdb_engine.settings(names)


def _restore(setting: Setting) -> str:
    v = setting.expected[0]
    value = f"'{v}'" if isinstance(v, str) else str(v).lower()
    return f"SET GLOBAL {setting.name} = {value}"


def _dialect() -> Any:
    from sverify.sql.duckdb import DUCKDB

    return DUCKDB


PLUGIN = ProfilePlugin(
    "duckdb",
    title="DuckDB",
    default=True,
    translation="sverify's DuckDB lowering, proved for every plan, and its SQL writer",
    settings=SETTINGS,
    installed_version=_version,
    restore=_restore,
    runner=_run,
    local=True,
    read_settings=_read_settings,
    dialect=_dialect,
)
