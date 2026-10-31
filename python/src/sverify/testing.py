"""Run a plan through Lean's own semantics, for differential tests against
DataFusion and DuckDB.

`inline_tables` replaces each named-table read by a Substrait virtual table
holding given rows (integers, strings, booleans, timestamps, doubles and
NULLs); `lean_rows` evaluates the plan with `Rel.eval` via `substrait-check`
(`lean_values` also reads printed doubles); `duckdb_rows` runs it as SQL on
DuckDB.
"""

import datetime as dt
import math
import re
import subprocess
from collections.abc import Iterable, Mapping

import pyarrow as pa

from sverify.engine import run_checker
from sverify.incremental import arrow_rows

EPOCH = dt.datetime(1970, 1, 1)


def literal(v: object) -> dict:
    if v is None:
        return {"literal": {"null": {"i64": {}}}}
    if isinstance(v, bool):
        return {"literal": {"boolean": v}}
    if isinstance(v, int):
        return {"literal": {"i64": str(v)}}
    if isinstance(v, str):
        return {"literal": {"string": v}}
    if isinstance(v, dt.datetime):
        micros = (v - EPOCH) // dt.timedelta(microseconds=1)
        return {"literal": {"precisionTimestamp": {"precision": 6, "value": str(micros)}}}
    if isinstance(v, float):
        if math.copysign(1.0, v) < 0 and (math.isnan(v) or v == 0):
            raise ValueError("Substrait JSON literals cannot hold -0.0 or -NaN")
        text = "NaN" if math.isnan(v) else "Infinity" if v == math.inf else "-Infinity"
        return {"literal": {"fp64": v if math.isfinite(v) else text}}
    raise TypeError(f"no literal for {v!r}")


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


def _checked(plan_json: str) -> str:
    code, out, err = run_checker((), plan_json)
    if code != 0:
        raise subprocess.CalledProcessError(code, "substrait-check", out, err)
    return out


def lean_rows(plan_json: str) -> list[tuple]:
    """The rows `Rel.eval` gives for a plan with only virtual tables, in
    Lean's order. Doubles, timestamps and dates come back as their integer
    codes (`SubstraitLean/Float.lean`); doubles are refused."""
    out = _checked(plan_json)
    return parse_rows(out)


def lean_values(plan_json: str) -> list[tuple]:
    """Like `lean_rows`, but reads doubles too, which Lean prints with six
    decimals and a `d` (so only approximately)."""
    out = _checked(plan_json)
    return parse_rows(out, doubles=True)


_VALUE = re.compile(r'\s*(NULL|true|false|"(?:[^"\\]|\\.)*"|[^,]+?)\s*(?:,|$)')
_ESCAPE = re.compile(r"\\(x[0-9a-fA-F]{2}|u\{[0-9a-fA-F]+\}|.)")


def _unquote(s: str) -> str:
    """A string in Lean's quotes (`String.quote`, which escapes with `\\x..`)."""

    def char(m: re.Match[str]) -> str:
        e = m.group(1)
        if e[0] == "x":
            return chr(int(e[1:], 16))
        if e[0] == "u":
            return chr(int(e[2:-1], 16))
        return {"n": "\n", "t": "\t", "r": "\r"}.get(e, e)

    return _ESCAPE.sub(char, s[1:-1])


def parse_rows(output: str, doubles: bool = False) -> list[tuple]:
    """The rows section of `substrait-check` output (`Row.render`)."""
    rows = []
    for line in output.split("rows (")[1].splitlines()[1:]:
        if not line.startswith("  ("):
            break
        values: list[object] = []
        for m in _VALUE.finditer(line.strip()[1:-1]):
            x = m.group(1)
            if x == "NULL":
                values.append(None)
            elif x in ("true", "false"):
                values.append(x == "true")
            elif x.startswith('"'):
                values.append(_unquote(x))
            elif re.fullmatch(r"-?\d+", x):
                values.append(int(x))
            elif doubles and x.endswith("d"):
                values.append(float(x[:-1]))
            else:
                raise ValueError(f"cannot read {x!r} (a double?) from Lean's output")
        rows.append(tuple(values))
    return rows


def duckdb_rows(plan_json: str, tables: Mapping[str, pa.Table] | None = None) -> list[tuple]:
    """Rows of the plan's SQL on a fresh DuckDB database holding `tables`."""
    from sverify import duckdb_engine

    return arrow_rows(duckdb_engine.run(plan_json, tables or {}))


def canonical(rows: Iterable[tuple]) -> list[str]:
    """A bag of rows in a canonical order (NULLs and NaN compare as text)."""
    return sorted(map(repr, rows))
