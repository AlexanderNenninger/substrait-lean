"""Which engines run each function: one row per function that not every
engine runs (#271), checked in one walk over the functions a plan calls,
before `to_sql` and `run_plan` dispatch.

Internal: not part of sverify's public API. Refusals that depend on more
than the function's name stay with the engine: an `avg` with an integer
result, a `substring` whose start may be negative, `round(x, d)`, `TRY_CAST`,
times of day, lists.
"""

from __future__ import annotations

from typing import Any

from sverify import _plan_read, black_box

ENGINES = frozenset({"duckdb", "spark", "snowflake", "datafusion", "polars"})
_DUCKDB = frozenset({"duckdb"})

#: The functions by their plan names, each with the engines that run it.
#: Every function not listed runs on every engine.
SUPPORT: dict[str, frozenset[str]] = {
    # Strings (#50).
    "regexp_extract": _DUCKDB,
    "regexp_replace": _DUCKDB,
    "md5": _DUCKDB,
    "sha256": _DUCKDB,
    # Aggregates (#53, #54, #55, #94).
    "first": _DUCKDB,
    "last": _DUCKDB,
    "string_agg": _DUCKDB,
    "array_agg": frozenset({"duckdb", "datafusion", "polars"}),
    "median": _DUCKDB,
    "quantile_cont": _DUCKDB,
    "quantile_disc": _DUCKDB,
    "mode": _DUCKDB,
    "arg_min": _DUCKDB,
    "arg_max": _DUCKDB,
    "covar_samp": _DUCKDB,
    "covar_pop": _DUCKDB,
    "corr": _DUCKDB,
    # The pairs `covar_*` and `corr` read.
    "sverify_pair": _DUCKDB,
    # Windows: DataFusion spreads the larger buckets out (upstream/bugs/DF-11.json).
    "ntile": ENGINES - {"datafusion"},
    # Black boxes (#325).
    **{name: _DUCKDB for name in sorted(black_box.NAMES)},
}

#: Why an engine refuses a function, where the reason is not #271.
_REASONS = {
    ("ntile", "datafusion"): "DataFusion's NTILE does not deal out buckets as SQL does",
}
#: What a refusal calls a function, where its name is not what users wrote.
_LABELS = {"sverify_pair": "covariance and correlation"}


def supported(name: str, engine: str) -> bool:
    """Does `engine` run the function `name` (a plan name, its signature aside)?"""
    engines = SUPPORT.get(_plan_read.base_name(name))
    return engines is None or engine.lower() in engines


def refusal(name: str, engine: str) -> str:
    """Why `engine` refuses the function `name`."""
    if name in black_box.NAMES:
        return black_box.refusal(name, engine)
    if reason := _REASONS.get((name, engine.lower())):
        return reason
    label = _LABELS.get(name, name)
    verb = "are" if " and " in label else "is"
    return f"{label} {verb} not yet supported on {engine}; see #271"


def floors(call: Any) -> bool:
    """Does the call state `division_type` = `FLOOR`: Polars's `//` and `%`
    of integers, which only a plan verified under `Profile.polars` states?"""
    return any(
        isinstance(o, dict)
        and o.get("name") == "division_type"
        and (o.get("preference") or [None])[0] == "FLOOR"
        for o in call.get("options", [])
    )


def floor_refusal(engine: str) -> str:
    """Why `engine` refuses a call that states `division_type` = `FLOOR`."""
    return (
        f"integer // and % with division_type FLOOR (Polars's, semantics='polars') run on "
        f"polars only; {engine} truncates: verify with semantics='reference' to run on {engine}"
    )


#: The nodes that call a function by its anchor.
_CALLS = ("scalarFunction", "measure", "windowFunction")


def check(plan: Any, engine: str, err: type[Exception] = ValueError) -> None:
    """Raise `err` for the first function the plan calls that `engine` does
    not run, in the plan's order (a node before its arguments)."""
    fns = _plan_read.function_names(plan, err)

    def walk(node: Any) -> None:
        if isinstance(node, dict):
            for key in _CALLS:
                call = node.get(key)
                if isinstance(call, dict):
                    # Protobuf JSON leaves out anchor 0.
                    name = fns.get(call.get("functionReference", 0))
                    if name is not None and not supported(name, engine):
                        raise err(refusal(_plan_read.base_name(name), engine))
                    if engine.lower() != "polars" and floors(call):
                        raise err(floor_refusal(engine))
            for v in node.values():
                walk(v)
        elif isinstance(node, list):
            for v in node:
                walk(v)

    walk(plan.get("relations", []) if isinstance(plan, dict) else plan)
