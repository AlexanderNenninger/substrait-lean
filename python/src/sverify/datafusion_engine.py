"""DataFusion as an engine: the plan its Substrait consumer runs.

Internal: not part of sverify's public API, which is `sverify`, `sverify.io`,
`sverify.engines` and `sverify.errors`; it may change in any release.

DataFusion is a tier-3 engine, optional and never a reference (#868). A plan
runs there when DataFusion computes what `Rel.eval` computes, and is refused
otherwise, naming DataFusion's bug (`upstream/bugs/DF-*.json`). Lean writes
the plan and refuses what it can see in the `Rel` (`substrait-check
--write-datafusion`, `SubstraitLean/DataFusion.lean`); this module renames the
functions DataFusion's consumer knows by other names and refuses what shows in
the written plan. `sverify.engine.run_plan` runs the result with
`run_substrait_json`.
"""

from __future__ import annotations

import json
from typing import Any

from sverify import _support
from sverify._checker import run_checker
from sverify._plan_read import base_name, function_names
from sverify._support import DUCKDB_ONLY
from sverify.sql import core as sql


def datafusion_plan(plan_json: str) -> str:
    """The plan for DataFusion to run (`substrait-check --write-datafusion`):
    Lean's written form, compensating for where DataFusion's semantics differ
    from `Rel.eval` (an integer `SUM` fails outside 64 bits instead of
    wrapping around)."""
    code, out, err = run_checker(("--write-datafusion",), plan_json)
    if code != 0:
        msg = (err or out).strip().splitlines()[-1:]
        raise ValueError(f"substrait-check --write-datafusion rejects the plan: {msg}")
    plan = json.loads(out)
    _check_datafusion_plan(plan)
    # sverify's own remainder of doubles (#256) is DataFusion's `%` of doubles,
    # C's `fmod` too: a name, not a workaround, so it has no expiry.
    for e in plan.get("extensions", []):
        f = e.get("extensionFunction", {})
        if f.get("name", "").split(":")[0] == "sverify_fmod":
            f["name"] = "modulus"
    _datafusion_variances(plan)
    return json.dumps(plan)


def _datafusion_variances(plan: dict) -> None:
    """Substrait's `variance` and `std_dev` say sample or population in an
    option; DataFusion has a function for each, and its consumer knows only
    those (#54, upstream/bugs/DF-21.json). Expires when DF-21 is fixed
    upstream (not filed yet)."""
    exts = plan.get("extensions", [])
    names: dict[Any, str] = {
        a: base_name(n) for a, n in function_names(plan, sql.Unsupported).items()
    }
    anchors: dict[str, int] = {}

    def anchor(name: str) -> int:
        if name not in anchors:
            a = max([*names, *anchors.values(), 0]) + 1
            anchors[name] = a
            exts.append({"extensionFunction": {"functionAnchor": a, "name": name}})
        return anchors[name]

    def walk(node: Any) -> None:
        if isinstance(node, dict):
            m = node.get("measure")
            if isinstance(m, dict) and names.get(m.get("functionReference")) in (
                "variance",
                "std_dev",
            ):
                pop = any(
                    o.get("name") == "distribution"
                    and o.get("preference", [])[:1] == ["POPULATION"]
                    for o in m.get("options", [])
                )
                base = "var" if names[m["functionReference"]] == "variance" else "stddev"
                m["functionReference"] = anchor(f"{base}_pop" if pop else f"{base}_samp")
                m.pop("options", None)
            for v in node.values():
                walk(v)
        elif isinstance(node, list):
            for v in node:
                walk(v)

    walk(plan)


def _check_datafusion_plan(plan: dict) -> None:
    """Refuse what DataFusion computes differently from the reference (#209):
    a `substring` whose start may be negative (DataFusion puts it left of the
    beginning, the reference counts it from the end, `Text.substrWrap`) unless
    the plan asks for `LEFT_OF_BEGINNING`; and an `avg` with an integer result
    (`AggFn.iavg`), which DataFusion computes as a double. These are
    DataFusion's documented choices (DF-23, DF-24, DF-25, "not a bug"), as is
    `round(x, d)`; each refusal expires with a shim from #271. `TRY_CAST`
    expires with #58's DataFusion support."""
    _support.check(plan, "DataFusion", sql.Unsupported)
    names: dict[Any, str] = {
        a: base_name(n) for a, n in function_names(plan, sql.Unsupported).items()
    }

    def walk(node: Any) -> None:
        if isinstance(node, dict):
            for key in ("measure", "windowFunction"):
                a = node.get(key)
                is_avg = isinstance(a, dict) and names.get(a.get("functionReference")) == "avg"
                ints = ("i8", "i16", "i32", "i64")
                if is_avg and any(k in a.get("outputType", {}) for k in ints):
                    raise sql.Unsupported(
                        "DataFusion's AVG has no integer result (upstream/bugs/DF-24.json)"
                    )
            c = node.get("cast")
            if isinstance(c, dict) and c.get("failureBehavior") == "FAILURE_BEHAVIOR_RETURN_NULL":
                raise sql.Unsupported("TRY_CAST is not yet supported on DataFusion; " + DUCKDB_ONLY)
            f = node.get("scalarFunction")
            fname = names.get(f.get("functionReference")) if isinstance(f, dict) else None
            if isinstance(f, dict) and fname == "round" and len(f.get("arguments", [])) == 2:
                # DataFusion's `round(x · 10ᵈ) / 10ᵈ` is not DuckDB's (#335).
                raise sql.Unsupported(
                    "round(x, d) is DuckDB's (#335, upstream/bugs/DF-25.json) and not yet "
                    "supported on DataFusion; " + DUCKDB_ONLY
                )
            if isinstance(f, dict) and fname == "substring":
                left = any(
                    o.get("name") == "negative_start"
                    and o.get("preference", [])[:1] == ["LEFT_OF_BEGINNING"]
                    for o in f.get("options", [])
                )
                args = f.get("arguments", [])
                lit = args[1].get("value", {}).get("literal", {}) if len(args) > 1 else {}
                start = next((v for k, v in lit.items() if k in ("i8", "i16", "i32", "i64")), None)
                if not left and (start is None or int(start) < 0):
                    raise sql.Unsupported(
                        "DataFusion's substring does not count a negative start from the end "
                        "(upstream/bugs/DF-23.json)"
                    )
            for v in node.values():
                walk(v)
        elif isinstance(node, list):
            for v in node:
                walk(v)

    walk(plan)
