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
from sverify._unsupported import DUCKDB_ONLY, ISSUE_271  # noqa: F401  (re-exported)


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
    exit_ = f"run it with engine={runs[0]!r}"
    reason = (_engines().get(engine.lower()) or _NO_PLUGIN).refuses.get(name)
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
                                f"a RANGE frame with offsets over an integer runs on {runs} "
                                f"only: {engine} has no way to raise its guard ({ISSUE_271})"
                            )
                    elif name is not None and not ok(name, engine):
                        raise err(refusal(_plan_read.base_name(name), engine, window))
            for v in node.values():
                walk(v)
        elif isinstance(node, list):
            for v in node:
                walk(v)

    walk(plan.get("relations", []) if isinstance(plan, dict) else plan)
