"""DataFusion (`sverify.datafusion_engine`): an optional engine, outside the
1.x promise (`docs/stability.md`), never a reference.
"""

from __future__ import annotations

from typing import Any

from sverify.profiles import ProfilePlugin


def _run(
    con: Any, plan_json: str, session: Any, *, keep: bool, finite: bool, tie_free: bool
) -> Any:
    from sverify.datafusion_engine import datafusion_plan
    from sverify.engine import run_substrait_json

    return run_substrait_json(con, datafusion_plan(plan_json))


def _version() -> str | None:
    import datafusion

    return datafusion.__version__


PLUGIN = ProfilePlugin(
    "datafusion",
    title="DataFusion",
    translation="sverify's SQL writer, with shims where DataFusion differs from the "
    "reference, tested against the reference",
    runner=_run,
    local=True,
    optional=True,
    modules=("datafusion",),
)
