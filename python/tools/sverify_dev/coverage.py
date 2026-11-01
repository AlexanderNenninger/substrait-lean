"""Which parts of the Ibis API reach the Lean checker.

Maintainer tooling (`sverify_dev`): not in the wheel, and not part of sverify's
API.

Each case is an Ibis expression over two unbound tables. It is compiled the way
`sverify` compiles Ibis expressions (the vendored producer,
`sverify.ibis_substrait`) and handed to `substrait-check`:

* `verified`: parsed into the Lean model and well-formed, so contracts and
  (where `incremental`) incremental views apply;
* `rejected`: the producer or the checker refuses it (an operation outside
  the model);
* `upstream`: Ibis fails before a plan exists.

Every verified case also runs on each engine (`ENGINES`): Polars and the SQL
of DuckDB, Snowflake and Spark translate the plan Lean writes back out. `REFUSED`
lists the cases an engine refuses, and why; `tests/test_backends.py` runs the
rest on random tables and compares the engines.

The cases live in `sverify_dev.coverage_cases`, one module per area (the rows of
the README table), each with that area's entries of these tables, keyed by
case label:

* `REFUSED`: verified cases an engine refuses (`Unsupported`), with a pattern
  of the reason (`coverage_cases._common` explains the shared ones);
* `TIE_FREE`: of those, the cases Snowflake and Spark run when the caller
  promises no ties;
* `NO_DATAFUSION_SQL`: verified cases whose Ibis SQL DataFusion does not run,
  or runs wrongly; the tests check them against the other engines, Lean and
  Python instead;
* `DATAFUSION_SQL`: verified cases where DataFusion running Ibis's own SQL
  means something else than the plan (and SQL), or fails; the tests compare
  them with DuckDB running Ibis's DuckDB SQL instead;
* `UNORDERED_LISTS`: lists built from rows in an order the plan does not fix,
  compared as bags.

`tests/test_coverage.py` pins every case to its `expected` status and its
refusals, so a change in coverage is a deliberate edit there. The README
tables are regenerated with

    uv run python -m sverify_dev.coverage --write-readme

by the `Generated files` workflow on `main` after every merge; feature branches
leave them alone.
"""

from __future__ import annotations

import json
import re
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any

from sverify.engine import run_checker, written_plan
from sverify.ibis_substrait import Unsupported, to_substrait_json
from sverify_dev.coverage_cases import (
    CASES,
    DATAFUSION_SQL,
    NO_DATAFUSION_SQL,
    REFUSED,
    TIE_FREE,
    UNORDERED_LISTS,
)
from sverify_dev.coverage_cases._common import TABLES, Case, L, M, Status, T, U

__all__ = [
    "CASES",
    "DATAFUSION_SQL",
    "ENGINES",
    "MEMTABLES",
    "NO_DATAFUSION_SQL",
    "REFUSED",
    "TABLES",
    "TIE_FREE",
    "UNORDERED_LISTS",
    "Case",
    "L",
    "Result",
    "T",
    "U",
    "check",
    "refusal",
    "results",
    "table",
]

#: The engines besides DataFusion, which runs Ibis's own plans.
ENGINES = ("polars", "duckdb", "snowflake", "spark")

#: The memtables of the cases, by name: engines that run Ibis's SQL need them
#: as tables.
_M: Any = M.op()
MEMTABLES = {_M.name: _M.data.to_pyarrow(M.schema())}


def refusal(c: Case, engine: str, tie_free: bool = False) -> str | None:
    """Why `engine` refuses the plan of a verified case, or None if it runs it."""
    from sverify import polars_engine
    from sverify.sql import Unsupported as Untranslatable
    from sverify.sql import to_sql as plan_sql
    from sverify.sql.duckdb import DUCKDB
    from sverify.sql.snowflake import SNOWFLAKE
    from sverify.sql.spark import SPARK

    dialects = {"duckdb": DUCKDB, "snowflake": SNOWFLAKE, "spark": SPARK}
    plan = json.loads(written_plan(to_substrait_json(c.build())))
    try:
        if engine == "polars":
            tables = {t.get_name(): t.schema().to_pyarrow().empty_table() for t in TABLES}
            polars_engine.run(plan, tables)
        else:
            plan_sql(plan, dialects[engine], tie_free=tie_free)
    except (polars_engine.Unsupported, Untranslatable) as e:
        return str(e)
    return None


@dataclass(frozen=True)
class Result:
    case: Case
    status: Status
    incremental: bool
    detail: str
    refused: dict[str, str]
    """Engine → reason, for the engines that refuse a verified case."""


def check(c: Case) -> Result:
    try:
        expr = c.build()
    except Exception as e:  # noqa: BLE001 - any Ibis failure counts
        return Result(c, "upstream", False, str(e).splitlines()[0], {})
    try:
        plan = to_substrait_json(expr)
    except Unsupported as e:
        return Result(c, "rejected", False, str(e), {})
    code, stdout, stderr = run_checker((), plan)
    out = stdout + stderr
    if code == 0:
        refused = {e: why for e in ENGINES if (why := refusal(c, e)) is not None}
        return Result(c, "verified", "incremental: yes" in out, "", refused)
    lines = [ln for ln in out.splitlines() if ln.startswith(("error:", "well-formed: no"))]
    return Result(c, "rejected", False, (lines or [out.strip()])[-1], {})


def results() -> list[Result]:
    return [check(c) for c in CASES]


SYMBOL = {"verified": "✓", "rejected": "✗", "upstream": "–"}
START, END = "<!-- coverage:start -->", "<!-- coverage:end -->"
NAMES = {"polars": "Polars", "duckdb": "DuckDB", "snowflake": "Snowflake", "spark": "Spark"}


def table(rs: list[Result]) -> str:
    n = sum(r.status == "verified" for r in rs)
    lines = [
        f"{n} of {len(rs)} probed Ibis operations reach the checker "
        "(✓ verified, ✗ rejected by the checker, – fails in Ibis or DataFusion; "
        "*inc.* marks incremental maintenance).",
        "",
        "| Area | Operations |",
        "|---|---|",
    ]
    for area in dict.fromkeys(r.case.area for r in rs):
        ops = [
            f"{SYMBOL[r.status]} {r.case.label}" + (" *inc.*" if r.incremental else "")
            for r in rs
            if r.case.area == area
        ]
        lines.append(f"| {area} | {' · '.join(ops)} |")
    verified = [r for r in rs if r.status == "verified"]
    lines += [
        "",
        f"Every engine runs the plans of the {len(verified)} verified operations, except:",
        "",
        "| Engine | Runs | Refuses |",
        "|---|---|---|",
    ]
    for e in ENGINES:
        out = [r for r in verified if e in r.refused]
        refused = " · ".join(
            r.case.label + (" (with `tie_free=True` it runs)" if r.case.label in TIE_FREE else "")
            for r in out
        )
        lines.append(f"| {NAMES[e]} | {len(verified) - len(out)} | {refused or '—'} |")
    return "\n".join(lines)


def write_readme(rs: list[Result]) -> None:
    readme = Path(__file__).resolve().parents[3] / "README.md"
    text = readme.read_text()
    pattern = re.compile(re.escape(START) + ".*?" + re.escape(END), re.S)
    if not pattern.search(text):
        raise ValueError(f"{readme} has no {START} … {END} block")
    readme.write_text(pattern.sub(lambda _: f"{START}\n{table(rs)}\n{END}", text))


def main() -> None:
    rs = results()
    if "--write-readme" in sys.argv:
        write_readme(rs)
    else:
        print(table(rs))
    for r in rs:
        if r.status != r.case.expected:
            print(f"{r.case.label}: expected {r.case.expected}, got {r.status} {r.detail}")


if __name__ == "__main__":
    main()
