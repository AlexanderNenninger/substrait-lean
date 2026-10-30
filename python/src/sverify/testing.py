"""Run a plan through Lean's own semantics, for differential tests against
DataFusion.

`inline_tables` replaces each named-table read by a Substrait virtual table
holding given rows (integers, finite doubles, strings and NULLs); `lean_rows`
evaluates the plan with `Rel.eval` via `substrait-check` (doubles come back as
codes), and `lean_values` also reads strings, booleans and printed doubles.
"""

import re
import subprocess
from collections.abc import Iterable, Mapping

from sverify.incremental import checker_path


def literal(v: int | float | str | None) -> dict:
    if v is None:
        return {"literal": {"null": {"i64": {}}}}
    if isinstance(v, str):
        return {"literal": {"string": v}}
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


def _evaluated_rows(plan_json: str) -> list[str]:
    out = subprocess.run(
        [str(checker_path()), "/dev/stdin"],
        input=plan_json,
        capture_output=True,
        text=True,
        check=True,
    ).stdout
    return [line.strip()[1:-1] for line in out.split("rows (")[1].splitlines()[1:]]


def lean_rows(plan_json: str) -> list[tuple]:
    """The rows `Rel.eval` gives for a plan with only virtual tables."""
    return [
        tuple(None if x == "NULL" else int(x) for x in line.split(", "))
        for line in _evaluated_rows(plan_json)
    ]


#: One rendered value: a string in Lean's quotes, or anything up to a comma.
_VALUE = re.compile(r'\s*("(?:[^"\\]|\\.)*"|[^,]+)')
_ESCAPE = re.compile(r"\\(x[0-9a-fA-F]{2}|u\{[0-9a-fA-F]+\}|.)")


def _unquote(s: str) -> str:
    def char(m: re.Match[str]) -> str:
        e = m.group(1)
        if e[0] == "x":
            return chr(int(e[1:], 16))
        if e[0] == "u":
            return chr(int(e[2:-1], 16))
        return {"n": "\n", "t": "\t", "r": "\r"}.get(e, e)

    return _ESCAPE.sub(char, s[1:-1])


def lean_values(plan_json: str) -> list[tuple]:
    """Like `lean_rows`, but also reads strings, booleans and doubles (which
    are printed with six decimals and a `d`)."""

    def value(x: str) -> object:
        if x == "NULL":
            return None
        if x in ("true", "false"):
            return x == "true"
        if x.startswith('"'):
            return _unquote(x)
        if x.endswith("d"):
            return float(x[:-1])
        return int(x)

    return [
        tuple(value(m.group(1).strip()) for m in _VALUE.finditer(line))
        for line in _evaluated_rows(plan_json)
    ]


def canonical(rows: Iterable[tuple]) -> list[str]:
    """A bag of rows in a canonical order (NULLs and NaN compare as text)."""
    return sorted(map(repr, rows))
