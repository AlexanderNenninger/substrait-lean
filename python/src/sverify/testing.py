"""Run a plan through Lean's own semantics, for differential tests against
DataFusion.

`inline_tables` replaces each named-table read by a Substrait virtual table
holding given rows (integers, finite doubles and NULLs); `lean_rows` evaluates
the plan with `Rel.eval` via `substrait-check` (doubles come back as codes).
"""

import subprocess
from collections.abc import Iterable, Mapping

from sverify.engine import checker_path


def literal(v: int | float | None) -> dict:
    if v is None:
        return {"literal": {"null": {"i64": {}}}}
    if isinstance(v, float):
        return {"literal": {"fp64": v}}
    return {"literal": {"i64": str(v)}}


def inline_tables(plan: dict, rows: Mapping[str, list[tuple]]) -> dict:
    """Replace the reads of the tables in `rows` by virtual tables (in place)."""

    def walk(node: object) -> None:
        if isinstance(node, dict):
            if "namedTable" in node:
                name = ".".join(node.pop("namedTable")["names"])
                exprs = [{"fields": [literal(v) for v in row]} for row in rows[name]]
                node["virtualTable"] = {"expressions": exprs}
            for v in node.values():
                walk(v)
        elif isinstance(node, list):
            for v in node:
                walk(v)

    walk(plan)
    return plan


def lean_rows(plan_json: str) -> list[tuple]:
    """The rows `Rel.eval` gives for a plan with only virtual tables."""
    out = subprocess.run(
        [str(checker_path()), "/dev/stdin"],
        input=plan_json,
        capture_output=True,
        text=True,
        check=True,
    ).stdout
    rows = out.split("rows (")[1].splitlines()[1:]
    return [
        tuple(None if x == "NULL" else int(x) for x in line.strip()[1:-1].split(", "))
        for line in rows
    ]


def canonical(rows: Iterable[tuple]) -> list[str]:
    """A bag of rows in a canonical order (NULLs and NaN compare as text)."""
    return sorted(map(repr, rows))
