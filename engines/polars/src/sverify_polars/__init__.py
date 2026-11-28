"""sverify's Polars engine (#1189): plans translated to lazy frames
(`sverify_polars.engine`), with shims where Polars differs from the reference
(`sverify_polars.shims`), registered as the `ProfilePlugin` `PLUGIN` under the
entry-point group `sverify.profiles`.

Polars's settings: sverify runs the streaming engine (`collect(engine=
"streaming")`, #605); the in-memory engine is legacy. The check refuses an
engine affinity that forces another engine (`pl.Config.set_engine_affinity(
"in-memory")`, which writes `POLARS_ENGINE_AFFINITY`). With the engine
pinned, it is defence in depth.
"""

from __future__ import annotations

import json
import os
from collections.abc import Mapping, Sequence

# An engine built from main beside PyPI's sverify of the same version number
# fails deep inside sverify with a TypeError (#1585): check the interface first.
from importlib.metadata import version as _version
from typing import Any, Literal

from sverify import _meta

if getattr(_meta, "PLUGIN_API", None) != 5:
    raise ImportError(
        f"{__name__.replace('_', '-')} {_version(__name__.replace('_', '-'))} "
        f"needs a sverify of its own build, found sverify {_meta.VERSION}: "
        "install both from the same release (`pip install -U sverify sverify-polars`)"
    )

from sverify._unsupported import ISSUE_2540, MIN_MOD_GUARD
from sverify.profiles import Finite, ProfilePlugin, Setting
from sverify_polars.store import PolarsStore

#: The settings Polars's profile assumes.
SETTINGS: tuple[Setting, ...] = (
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
        "(sum_order, stat_algo); sverify runs Polars's streaming engine",
    ),
)

#: Polars's environment variables for its settings (`pl.Config` writes them).
_ENV = {"engine_affinity": ("POLARS_ENGINE_AFFINITY", "auto")}


def _run(
    con: Any,
    plan_json: str,
    session: Any,
    *,
    keep: bool,
    finite: Finite,
    tie_free: bool,
    rows: Literal["sequence", "multiset"] = "sequence",
) -> Any:
    from sverify.engine import read_tables

    # `rows="multiset"`: `Report.run` passes it where the result needs no
    # ordinal (`Report._ordinal_free`), and the groups come in any order.
    tables = {t: _table(con, t) for t in read_tables(json.loads(plan_json))}
    if keep:
        return _kept(plan_json, tables, finite=finite, rows=rows)
    return _run_tables(plan_json, tables, finite=finite, rows=rows)


def _checks(checks: frozenset[str], finite: Finite) -> frozenset[str]:
    """`checks` without the overflow-to-infinity ones `finite` leaves out: all
    for False, the operations' own for "aggregates"."""
    from sverify_polars import engine

    if finite is True:
        return checks
    gone = {engine.InfiniteResult.issue}
    if not finite:
        gone.add(engine.InfiniteAggregate.issue)
    return checks - gone


def _kept(
    plan_json: str,
    tables: Mapping[str, Any],
    *,
    finite: Finite,
    rows: Literal["sequence", "multiset"] = "sequence",
) -> Any:
    """The plan's result as a lazy weighted-table handle
    (`sverify._parts.Lazy`): the merge that adds it to the state
    streams it into a file, so it is never collected."""
    from sverify_polars import engine
    from sverify_polars.store import lazy_plan

    guards = _checks(engine.ALL_GUARDS, finite)
    return lazy_plan(engine.to_lazy(plan_json, tables, guards=guards, rows=rows))


def _table(con: Any, name: str) -> Any:
    """Table `name` of the connection for Polars: a `Scan` of local files without a
    `where` as a lazy scan (`sverify_polars.scan`), any other table as Arrow."""
    from sverify._scan import Scan

    table = con.get(name)
    if isinstance(table, Scan) and table.readable() and table.where is None:
        from sverify_polars.scan import lazy_scan

        return lazy_scan(table)
    return con._arrow[name]


def _run_tables(
    plan_json: str,
    tables: Mapping[str, Any],
    *,
    guard_free: bool = False,
    finite: Finite = True,
    rows: Literal["sequence", "multiset"] = "sequence",
) -> Any:
    from sverify_polars import engine

    checks = engine.NO_GUARDS if guard_free else engine.ALL_GUARDS
    return engine.run(plan_json, tables, guards=_checks(checks, finite), rows=rows)


def _fallbacks(plan: Mapping[str, Any], tables: Mapping[str, Any]) -> Sequence[str]:
    from sverify_polars import engine

    return tuple(engine.plan_fallbacks(dict(plan), tables))


def _version() -> str | None:
    import polars

    return polars.__version__


def _read_settings(names: Sequence[str], session: Any) -> dict[str, Any]:
    return {n: os.environ.get(*_ENV[n]) for n in names}


def _restore(setting: Setting) -> str:
    if setting.name == "engine_affinity":
        return 'pl.Config.set_engine_affinity("streaming")'
    return f"set {setting.name} back to {setting.expected[0]!r}"


PLUGIN = ProfilePlugin(
    "polars",
    store=PolarsStore,
    title="Polars",
    floor_division=True,
    profile=True,
    translation="sverify's Polars translation, with shims where Polars differs from the "
    "reference, tested against the reference",
    settings=SETTINGS,
    installed_version=_version,
    restore=_restore,
    runner=_run,
    local=True,
    modules=("polars", "numpy"),
    read_settings=_read_settings,
    run_tables=_run_tables,
    guard_free_theorem="Rel.polars_sound",
    fallbacks=_fallbacks,
    functions=frozenset({"array_agg", "regexp_extract", "regexp_replace"}),
    # Polars has no digests, and engine paths compute nothing in Python.
    refuses={
        fn: (f"Polars has no {fn} (polars-string-functions-missing)", ISSUE_2540)
        for fn in ("md5", "sha256")
    },
    # Only the integer `%` guard (#2058); the date and RANGE guards stay refused.
    guards=(MIN_MOD_GUARD,),
    shim_text={
        "int_div_trunc": "integer division rewritten to truncate",
        "int_mod_trunc": "integer remainder rewritten to truncate",
        "one_zero": "-0.0 written as 0.0",
        "round: 0.0 for a negative value that rounds to zero": "rounding to zero written as 0.0",
        "avg_int_declared": "the mean of integers cast to its declared type",
        "round_half_away": "rounding rewritten to round half away from zero",
        "decimal_round_half_away": "decimal rounding rewritten to round half away from zero",
        "decimal_div_half_away": "decimal division rewritten to round half away from zero",
        "null_order": "NULLs sorted as the reference sorts them",
        "strpos_chars": "string positions counted in characters",
        "substring_wrap": "substring positions rewritten as the reference reads them",
        "sum_empty_null": "a SUM of no rows written as NULL",
    },
)
