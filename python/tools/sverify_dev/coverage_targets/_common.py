"""What the coverage targets share: how a target is written and probed."""

from __future__ import annotations

import json
from dataclasses import dataclass
from typing import Literal

Decision = Literal["in", "skipped", "after"]
"""`in`: sverify 1.0 covers it. `skipped`: a hard blocker, listed with its
reason. `after`: wanted, but not a gate for 1.0."""

#: The tables the SQL probes read, as DuckDB SQL types.
SCHEMAS = {
    "t": {
        "id": "int64",
        "name": "string",
        "amount": "float64",
        "qty": "int64",
        "ts": "timestamp",
        "d": "date",
        "flag": "boolean",
        "price": "decimal(10, 2)",
        "xs": "array<int64>",
    },
    "u": {"name": "string", "region": "string", "lo": "date", "hi": "date"},
}


@dataclass(frozen=True)
class Target:
    """A construct real queries use, and what sverify 1.0 does with it."""

    area: str
    name: str
    decision: Decision
    uses: str
    """Who needs it: catalogue queries (`catalogue/features.toml`), dbt
    macros, the patterns of #749 and #765, the Eurostat pipeline of #771,
    refusals in DuckDB's sqllogictest replay (`characterization/duckdb`)."""
    covered: bool
    """What the probes give today; `tests/test_coverage_targets.py` pins it,
    so coverage changes by a deliberate edit here."""
    sql: str | None = None
    """A DuckDB SQL probe over `SCHEMAS`: covered when the lift reads it and
    the checker accepts the plan."""
    ibis: str | None = None
    """The label of a case of `sverify_dev.coverage_cases`: covered when it
    verifies."""
    issue: int | None = None
    why: str = ""
    """For `skipped` and `after`: the reason, or the workaround."""


def target(
    area: str,
    name: str,
    decision: Decision,
    uses: str,
    covered: bool,
    *,
    sql: str | None = None,
    ibis: str | None = None,
    issue: int | None = None,
    why: str = "",
) -> Target:
    return Target(area, name, decision, uses, covered, sql, ibis, issue, why)


def probe_sql(query: str) -> str | None:
    """Why the lift or the checker refuses `query`, or None if it verifies."""
    import ibis

    from sverify.engine import run_checker
    from sverify.sql_lift import lift

    schemas = {n: ibis.schema(s) for n, s in SCHEMAS.items()}
    try:
        lifted = lift(query, schemas, "duckdb")
    except Exception as e:  # noqa: BLE001 - a refusal, or a bug: reported
        return f"lift: {str(e).splitlines()[0]}"
    code, out, err = run_checker((), json.dumps(lifted.plan))
    if code == 0:
        return None
    return "checker: " + (((err or out).strip().splitlines() or ["?"])[-1])


def probe_ibis(label: str) -> str | None:
    """Why the checker refuses the Ibis case `label`, or None if it verifies."""
    from sverify_dev.coverage import CASES, check

    (case,) = [c for c in CASES if c.label == label]
    r = check(case)
    return None if r.status == "verified" else f"ibis: {r.status} {r.detail}"


def probe(t: Target) -> list[str]:
    """The refusals of `t`'s probes: empty when every probe verifies."""
    out = []
    if t.sql is not None and (why := probe_sql(t.sql)) is not None:
        out.append(why)
    if t.ibis is not None and (why := probe_ibis(t.ibis)) is not None:
        out.append(why)
    return out
