"""Polars (`sverify.polars_engine`): plans translated to lazy frames, with
shims where Polars differs from the reference.

Polars's settings: sverify runs the streaming engine (`collect(engine=
"streaming")`, #605); the in-memory engine is legacy. The check refuses an
engine affinity that forces another engine (`pl.Config.set_engine_affinity(
"in-memory")`, which writes `POLARS_ENGINE_AFFINITY`). With the engine
pinned, it is defence in depth.
"""

from __future__ import annotations

import json
import os
from collections.abc import Sequence
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
    from sverify import polars_engine
    from sverify.engine import read_tables

    tables = {t: con._arrow[t] for t in read_tables(json.loads(plan_json))}
    guards = polars_engine.ALL_GUARDS - (
        frozenset() if finite else {polars_engine.InfiniteResult.issue}
    )
    return polars_engine.run(plan_json, tables, guards=guards)


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
    translation="sverify's Polars translation, with shims where Polars differs from the "
    "reference, tested against the reference",
    settings=SETTINGS,
    installed_version=_version,
    restore=_restore,
    runner=_run,
    local=True,
    modules=("polars", "numpy"),
    read_settings=_read_settings,
)
