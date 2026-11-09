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
from typing import Any

from sverify.profiles import ProfilePlugin, Setting

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
        "(sum_order, stat_algo); sverify runs Polars's streaming engine (#605)",
    ),
)

#: Polars's environment variables for its settings (`pl.Config` writes them).
_ENV = {"engine_affinity": ("POLARS_ENGINE_AFFINITY", "auto")}


def _run(
    con: Any, plan_json: str, session: Any, *, keep: bool, finite: bool, tie_free: bool
) -> Any:
    from sverify.engine import read_tables

    tables = {t: con._arrow[t] for t in read_tables(json.loads(plan_json))}
    return _run_tables(plan_json, tables, finite=finite)


def _run_tables(
    plan_json: str, tables: Mapping[str, Any], *, guard_free: bool = False, finite: bool = True
) -> Any:
    from sverify_polars import engine

    checks = engine.NO_GUARDS if guard_free else engine.ALL_GUARDS
    if not finite:
        checks -= {engine.InfiniteResult.issue}
    return engine.run(plan_json, tables, guards=checks)


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
    title="Polars",
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
)
