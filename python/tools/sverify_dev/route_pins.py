"""Pins the route of every catalogue query and coverage case on every public engine (#1071).

`Report.route(engine)` takes a plan to an engine: its class, evidence, shims, the problems that
refuse it and, with `reproducible=`, what a rerun has to reproduce. Moving that decision from
`sverify.routes` into the checker (#1071 steps 2 and 3, ruling 257) must change none of it, so this
module records every route as `Report.route` gives it, and `tests/test_route_pins.py` compares a
fresh run with the record (`python/tests/route_pins.json`).

* A catalogue query with a contract is verified under it, as `catalogue.probe_contract` does; the
  others, and every coverage case the checker accepts, with no condition.
* Each engine's route is taken twice: by default, and with an exact rerun required
  (`reproducible=sv.equivalent(rows="sequence")`'s strictest form). Both are `report_json.route_json`'s
  fields, so a change to the class, the evidence, the shims, the reason, the lenses or the rerun
  evidence shows up as a changed line.
* An engine that cannot be reached (an engine package or session that is not installed) is left
  out of the record and of the comparison.

Regenerate with `python -m sverify_dev.route_pins --write` and review the diff.
"""

from __future__ import annotations

import json
import sys
import warnings
from pathlib import Path
from typing import Any

PINS = Path(__file__).resolve().parents[2] / "tests" / "route_pins.json"

#: The engines whose routes are public. Snowflake's profile is out of tree.
ENGINES = ("duckdb", "polars", "spark")


def _reports() -> list[tuple[str, Any]]:
    """`(id, report)` for every catalogue query and coverage case that verifies, or
    `(id, message)` where `verify` refuses it."""
    import sverify
    from sverify.ibis_substrait import Unsupported, to_substrait_json
    from sverify_dev import catalogue as cat
    from sverify_dev.coverage import CASES

    out: list[tuple[str, Any]] = []
    schemas = cat.load_schemas()
    for q in cat.load_queries():
        if q.not_expressible is not None:
            continue
        try:
            query = cat.build(q, schemas, "native")
            inputs = cat.tables(schemas, q.dataset, "native") if isinstance(query, str) else None
            if q.requires is not None:
                requires, ensures = cat.contract(q, schemas, "native")
            else:
                requires, ensures = None, None
            report = sverify.verify(
                query, requires=requires, ensures=ensures, tables=inputs, counterexamples=0
            )
        except Exception as e:  # noqa: BLE001 - what verify refuses is pinned too
            out.append((f"catalogue: {q.id}", f"{type(e).__name__}: {str(e).splitlines()[0]}"))
            continue
        out.append((f"catalogue: {q.id}", report))
    for c in CASES:
        if c.expected != "verified":
            continue
        try:
            expr = c.build()
            to_substrait_json(expr)
            report = sverify.verify(expr, counterexamples=0)
        except Unsupported as e:
            out.append((f"coverage: {c.area}: {c.label}", f"Unsupported: {str(e).splitlines()[0]}"))
            continue
        except Exception as e:  # noqa: BLE001
            out.append(
                (f"coverage: {c.area}: {c.label}", f"{type(e).__name__}: {str(e).splitlines()[0]}")
            )
            continue
        out.append((f"coverage: {c.area}: {c.label}", report))
    return out


def _routes(report: Any, engine: str) -> dict[str, Any] | None:
    import sverify
    from sverify import report_json

    try:
        default = report.route(engine)
        rerun = report.route(engine, reproducible=sverify.equivalent())
    except Exception as e:  # noqa: BLE001 - an engine that is not installed, a version outside range
        if type(e).__name__ in ("EngineVersionError", "EngineSettingsError", "KeyError"):
            return None
        return {"error": f"{type(e).__name__}: {str(e).splitlines()[0]}"}
    return {"auto": report_json.route_json(default), "rerun": report_json.route_json(rerun)}


def pins(engines: tuple[str, ...] = ENGINES) -> dict[str, dict[str, Any]]:
    """The record: id to `{"verify": message}` where verify refuses, else engine to its routes."""
    from sverify import _engines

    available = [e for e in engines if e in _engines.SUPPORTED]
    out: dict[str, dict[str, Any]] = {}
    with warnings.catch_warnings():
        warnings.simplefilter("ignore")
        for ident, report in _reports():
            if isinstance(report, str):
                out[ident] = {"verify": report}
                continue
            routes = {e: r for e in available if (r := _routes(report, e)) is not None}
            out[ident] = routes
    return out


def dump(record: dict[str, dict[str, Any]]) -> str:
    """One line per case and engine, so a diff names what changed."""
    lines = ["{"]
    items = list(record.items())
    for i, (ident, per) in enumerate(items):
        lines.append(f"{json.dumps(ident)}: {{")
        keys = list(per)
        for j, k in enumerate(keys):
            comma = "," if j < len(keys) - 1 else ""
            lines.append(f"  {json.dumps(k)}: {json.dumps(per[k], sort_keys=True)}{comma}")
        lines.append("}" + ("," if i < len(items) - 1 else ""))
    lines.append("}")
    return "\n".join(lines) + "\n"


def main() -> None:
    record = pins()
    text = dump(record)
    if "--write" in sys.argv:
        PINS.write_text(text)
        print(f"wrote {PINS} ({len(record)} cases)")
    else:
        sys.stdout.write(text)


if __name__ == "__main__":
    main()
