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
from sverify._unsupported import DUCKDB_ONLY, ISSUE_271  # noqa: F401  (re-exported)

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
    # Lists (#810, #812): DuckDB's list functions, `list(x)` keeping NULLs.
    "list_prepend": _DUCKDB,
    "list_concat": _DUCKDB,
    "list_contains": _DUCKDB,
    "list_position": _DUCKDB,
    "flatten": _DUCKDB,
    # The lift's guards (`UnFn.raise`): `make_date` of columns outside the
    # calendar (#809), on DuckDB only (`_REASONS`); a RANGE frame's bound that
    # leaves its integer key's type (#805) runs wherever the dialect raises
    # (`GUARDS`). Polars and DataFusion run plans without a way to raise.
    "sverify_raise": _DUCKDB,
    # Windows: DataFusion spreads the larger buckets out (upstream/bugs/DF-11.json).
    "ntile": ENGINES - {"datafusion"},
    # Black boxes (#325).
    **{name: _DUCKDB for name in sorted(black_box.NAMES)},
}

#: Functions that run on fewer engines over a window than as aggregates:
#: the variance over a frame is the reference's own two passes (`varOf`),
#: which only DuckDB's writer computes so far.
WINDOW_SUPPORT: dict[str, frozenset[str]] = {
    "variance": _DUCKDB,
    "std_dev": _DUCKDB,
}

#: Why an engine refuses a function, where the reason is not #271.
_REASONS = {
    ("ntile", "datafusion"): "DataFusion's NTILE does not deal out buckets as SQL does",
    ("sverify_raise", "spark"): (
        "Spark's SQL of the date guards exhausts its JVM's heap (a date from columns is "
        "38 KB of nested CASEs)"
    ),
    ("sverify_raise", "snowflake"): (
        "Snowflake's SQL of the date guards grows past what it runs: a date from columns "
        "writes 208 MB of nested CASEs"
    ),
}

#: Guards (`sverify_raise`) that run on more engines than the date guards,
#: by the start of their message: the engines whose dialect writes them
#: with `raise_` (#805).
GUARDS: dict[str, frozenset[str]] = {
    "Overflow in a RANGE frame bound": frozenset({"duckdb", "spark", "snowflake"}),
}


def _guard_engines(call: dict) -> frozenset[str] | None:
    """The engines that run the guard `call` (`sverify_raise`), by its
    message (`GUARDS`), or None for one `GUARDS` does not list."""
    for arg in call.get("arguments", [])[1:]:
        msg = (arg.get("value") or {}).get("literal", {}).get("string")
        if isinstance(msg, str):
            for start, engines in GUARDS.items():
                if msg.startswith(start):
                    return engines
    return None


#: What a refusal calls a function: the Ibis and SQL names users write,
#: where the plan's name differs (#655).
_LABELS = {
    "sverify_pair": "covariance and correlation (Ibis cov, corr)",
    "quantile_cont": "median() or quantile() (SQL median, quantile_cont)",
    "quantile_disc": "quantile() (SQL quantile_disc)",
    "sverify_raise": (
        "a guard that raises (a date from columns, Ibis ibis.date, SQL make_date; "
        "a RANGE frame with offsets over an integer)"
    ),
    "regexp_extract": "re_extract() (SQL regexp_extract)",
    "regexp_replace": "re_replace() (SQL regexp_replace)",
    "first": "first() (SQL first)",
    "last": "last() (SQL last)",
    "mode": "mode() (SQL mode)",
    "median": "median() (SQL median)",
    "string_agg": "group_concat() (SQL string_agg)",
    "array_agg": "collect() (SQL array_agg, list)",
    "arg_min": "argmin() (SQL arg_min)",
    "arg_max": "argmax() (SQL arg_max)",
    "covar_samp": "cov() (SQL covar_samp)",
    "covar_pop": "cov(how='pop') (SQL covar_pop)",
    "md5": "hexdigest('md5') (SQL md5)",
    "variance OVER": "var() over a window (SQL var_samp, var_pop OVER)",
    "std_dev OVER": "std() over a window (SQL stddev_samp, stddev_pop OVER)",
    "sha256": "hexdigest('sha256') (SQL sha256)",
    "list_prepend": "a list of computed values (SQL [a, b], list_prepend)",
    "flatten": "flatten() (SQL flatten, and list() keeping NULLs)",
}


def supported(name: str, engine: str) -> bool:
    """Does `engine` run the function `name` (a plan name, its signature aside)?"""
    engines = SUPPORT.get(_plan_read.base_name(name))
    return engines is None or engine.lower() in engines


def window_supported(name: str, engine: str) -> bool:
    """Does `engine` run the function `name` over a window?"""
    base = _plan_read.base_name(name)
    engines = WINDOW_SUPPORT.get(base)
    return supported(name, engine) and (engines is None or engine.lower() in engines)


def refusal(name: str, engine: str, window: bool = False) -> str:
    """Why `engine` refuses the function `name` (over a window, `window`)."""
    if name in black_box.NAMES:
        return black_box.refusal(name, engine)
    if reason := _REASONS.get((name, engine.lower())):
        return reason
    if window and name in WINDOW_SUPPORT and supported(name, engine):
        label = _LABELS.get(f"{name} OVER", name)
        runs = sorted(WINDOW_SUPPORT[name])
        where = " and ".join(runs)
        return (
            f"{label} runs on {where} only: run it with engine={runs[0]!r} "
            f"({engine} does not run it yet; {ISSUE_271})"
        )
    label = _LABELS.get(name, name)
    runs = sorted(SUPPORT.get(name, ENGINES))
    where = " and ".join(runs)
    return (
        f"{label} runs on {where} only: run it with engine={runs[0]!r} "
        f"({engine} does not run it yet; {ISSUE_271})"
    )


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
                    window = key == "windowFunction"
                    ok = window_supported if window else supported
                    base = _plan_read.base_name(name) if name is not None else None
                    guard = _guard_engines(call) if base == "sverify_raise" else None
                    if guard is not None:
                        if engine.lower() not in guard:
                            runs = " and ".join(sorted(guard))
                            raise err(
                                f"a RANGE frame with offsets over an integer runs on {runs} "
                                f"only: {engine} has no way to raise its guard ({ISSUE_271})"
                            )
                    elif name is not None and not ok(name, engine):
                        raise err(refusal(_plan_read.base_name(name), engine, window))
                    if engine.lower() != "polars" and floors(call):
                        raise err(floor_refusal(engine))
            for v in node.values():
                walk(v)
        elif isinstance(node, list):
            for v in node:
                walk(v)

    walk(plan.get("relations", []) if isinstance(plan, dict) else plan)
