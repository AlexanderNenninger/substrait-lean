"""Which engines run each function, as their plugins say
(`ProfilePlugin.functions`, `window_functions`, `refuses`, `guards`; #271,
#1189), checked in one walk over the functions a plan calls, before `to_sql`
and `run_plan` dispatch.

Internal: not part of sverify's public API. Refusals that depend on more
than the function's name stay with the engine: an `avg` with an integer
result, a `substring` whose start may be negative, `round(x, d)`, `TRY_CAST`,
times of day, lists.
"""

from __future__ import annotations

from typing import Any

from sverify import _plan_read, black_box
from sverify._unsupported import (  # noqa: F401  (re-exported)
    DECIMAL_38_38,
    DUCKDB_ONLY,
    ISSUE_271,
    MIN_MOD_GUARD,
)


def _engines() -> dict[str, Any]:
    """The installed engines' plugins: those that run plans or write their
    SQL (a profile alone is no engine)."""
    from sverify import profiles

    return {e: p for e, p in profiles.plugins().items() if p.local or p.runner or p.dialect}


def _restricted(field: str) -> frozenset[str]:
    """The functions some engine lists in `field`: those that run only on the
    engines that list them."""
    return frozenset().union(*(getattr(p, field) for p in _engines().values()))


def _runs(name: str, engine: str, field: str) -> bool:
    p = _engines().get(engine.lower())
    if p is None:
        return True
    if name in p.refuses:
        return False
    return name not in _restricted(field) or name in getattr(p, field)


def _guard_engines(call: dict) -> frozenset[str] | None:
    """The engines that run the guard `call` (`sverify_raise`), by its
    message (`ProfilePlugin.guards`), or None for one no engine lists."""
    for arg in call.get("arguments", [])[1:]:
        msg = (arg.get("value") or {}).get("literal", {}).get("string")
        if isinstance(msg, str):
            found = frozenset(
                e for e, p in _engines().items() if any(msg.startswith(g) for g in p.guards)
            )
            if found:
                return found
    return None


def _guard_text(call: dict) -> str:
    """What a refusal calls the guard `call`: the integer `%` under
    `semantics="duckdb"` (`MIN_MOD_GUARD`), else a RANGE frame."""
    for arg in call.get("arguments", [])[1:]:
        msg = (arg.get("value") or {}).get("literal", {}).get("string")
        if isinstance(msg, str) and msg.startswith(MIN_MOD_GUARD):
            return 'an integer % under semantics="duckdb" (it raises at MIN % -1)'
    return "a RANGE frame with offsets over an integer"


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


class _NoPlugin:
    refuses: dict[str, tuple[str, str]] = {}


_NO_PLUGIN = _NoPlugin()


def supported(name: str, engine: str) -> bool:
    """Does `engine` run the function `name` (a plan name, its signature
    aside)? Its plugin says so (`ProfilePlugin.functions`, `refuses`)."""
    return _runs(_plan_read.base_name(name), engine, "functions")


def window_supported(name: str, engine: str) -> bool:
    """Does `engine` run the function `name` over a window?"""
    base = _plan_read.base_name(name)
    return supported(name, engine) and _runs(base, engine, "window_functions")


def refusal(name: str, engine: str, window: bool = False) -> str:
    """Why `engine` refuses the function `name` (over a window, `window`)."""
    if name in black_box.NAMES:
        return black_box.refusal(name, engine)
    over = window and name in _restricted("window_functions") and supported(name, engine)
    label = _LABELS.get(f"{name} OVER" if over else name, name)
    field = "window_functions" if over else "functions"
    runs = sorted(e for e in _engines() if _runs(name, e, field))
    reason = (_engines().get(engine.lower()) or _NO_PLUGIN).refuses.get(name)
    if not runs:
        # No installed engine runs it. DuckDB is a base dependency, so it refuses too.
        why = f"{reason[0]}; " if reason else ""
        issue = reason[1] if reason else ISSUE_271
        return f"{label}: {why}no installed engine runs it; rewrite the step ({issue})"
    exit_ = f"run it with engine={runs[0]!r}"
    if reason:
        why, issue = reason
        return f"{label}: {why}; {exit_} ({issue})"
    where = " and ".join(runs)
    return f"{label} runs on {where} only: {exit_} ({engine} does not run it yet; {ISSUE_271})"


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
                                f"{_guard_text(call)} runs on {runs} only: {engine} has "
                                f"no way to raise its guard ({ISSUE_271})"
                            )
                    elif name is not None and not ok(name, engine):
                        raise err(refusal(_plan_read.base_name(name), engine, window))
            for v in node.values():
                walk(v)
        elif isinstance(node, list):
            for v in node:
                walk(v)

    walk(plan.get("relations", []) if isinstance(plan, dict) else plan)


def _decimal_text_38(node: Any) -> bool:
    """Does the core term `node` cast a `DECIMAL(38, 38)` to a string?"""
    from dataclasses import fields, is_dataclass

    from sverify.sql.core._base import Un

    if isinstance(node, Un) and node.op == "dtext" and node.digits == 38 and node.param == "38":
        return True
    if is_dataclass(node) and not isinstance(node, type):
        return any(_decimal_text_38(getattr(node, f.name)) for f in fields(node))
    if isinstance(node, (list, tuple)):
        return any(_decimal_text_38(x) for x in node)
    return False


def check_decimal_text(plan: Any, engine: str, err: type[Exception] = ValueError) -> None:
    """Raise `err` for a plan that casts a `DECIMAL(38, 38)` to a string on DuckDB: its writer
    has no wider decimal to print it from (D72, ruling 245, E6). The route check calls this, so
    `verify` reports it before anything runs."""
    from sverify.sql.core._base import WriterUnsupported, parse_plan

    if engine.lower() != "duckdb" or not isinstance(plan, dict):
        return
    try:
        root = parse_plan(plan).root
    except WriterUnsupported:
        return
    if _decimal_text_38(root):
        raise err(DECIMAL_38_38)
