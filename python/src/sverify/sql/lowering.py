"""The generated lowering to DuckDB, as SQL (#241).

For each function DuckDB does not compute as the reference does, the Lean
build generates a template and proves it gives the reference's outcome under
DuckDB's profile (`SubstraitLean/LoweringDuckDB.lean`, `Lowering.duckdb_exact`).
`substrait-check --lowering-table` exports those templates, and this module
writes one as SQL: its fields are the arguments' SQL, its calls DuckDB's own
operators, its `CASE`s SQL's. The DuckDB printer (`sverify.sql.duckdb`) asks
it first (`Dialect.lowered`), so the guards in DuckDB's SQL are the proved
ones rather than hand-written.

The table is for DuckDB's default settings, `error_on_division_by_zero` and
`ieee_floating_point_ops` on, which sverify runs DuckDB with. Under other
settings DuckDB computes other values, and there is no proved table for them
(#241): run the SQL with the defaults.

This interpreter is trusted, as the printer is: keep it small.
"""

from __future__ import annotations

import json
import subprocess
from collections.abc import Callable, Mapping, Sequence
from typing import Any

from sverify.contracts import decode_double

Json = Any

#: `error_on_division_by_zero`, which the table is for: DuckDB's default, the only one.
SETTING = "on"

_TABLE: list[Mapping[str, Json]] = []


def table() -> Mapping[str, Json]:
    """The templates by function (`"fdiv"`, `"fmath:sqrt"`, `"fit:silent:64"`,
    `"bit:bitwise_shift_left"`), read from the checker once."""
    if not _TABLE:
        from sverify.engine import checker_path

        out = subprocess.run(
            [str(checker_path()), "--lowering-table"], capture_output=True, text=True, check=True
        ).stdout
        _TABLE.append({e["fn"]: e["template"] for e in json.loads(out)[SETTING]})
    return _TABLE[0]


#: DuckDB's operators for the model's functions a template calls.
_BINARY = {
    "eq": "=", "lt": "<", "and": "AND", "or": "OR",
    "fadd": "+", "fsub": "-", "fmul": "*", "fdiv": "/", "fmod": "%", "imod": "%",
    "bit:bitwise_and": "&", "bit:bitwise_or": "|",
    "bit:bitwise_shift_left": "<<", "bit:bitwise_shift_right": ">>",
}  # fmt: skip
_CALLS = {"fpow": "POWER", "fatan2": "ATAN2", "bit:bitwise_xor": "xor", "ffloor": "FLOOR"}


def _hugeint(x: str) -> str:
    return f"CAST({x} AS HUGEINT)"


def render(
    fn: str,
    args: Sequence[str],
    raise_: Callable[[str, str], str],
    float_lit: Callable[[float], str],
    int_lit: Callable[[int], str],
    guards: bool = True,
) -> str | None:
    """`fn` of the arguments' SQL as its template writes it, or None where
    DuckDB's own function is the reference's (no template). `raise_` writes
    an error with its message and the value it depends on. Without `guards`
    (`to_sql(..., guards=False)`, for plans proved not to raise) the arms of
    a `CASE` that raise are left out: they would never be taken."""
    tmpl = table().get(fn)
    if tmpl is None:
        return None

    def go(t: Json) -> str:
        if "field" in t:
            return args[t["field"]]
        if "null" in t:
            return "NULL"
        if "bool" in t:
            return "TRUE" if t["bool"] else "FALSE"
        if "code" in t:
            return float_lit(decode_double(int(t["code"])))
        if "int" in t:
            i = int(t["int"])
            # The wrap-arounds compute in 128 bits (`BinFn.dadd`, …).
            return int_lit(i) if -(2**63) <= i < 2**63 else _hugeint(str(i))
        if "if" in t:
            # A chain of `CASE`s in the `ELSE` is one `CASE`.
            whens = []
            while "if" in t:
                if guards or t["then"].get("fn") != "raise":
                    whens.append(f"WHEN {go(t['if'])} THEN {go(t['then'])}")
                t = t["else"]
            last = go(t)
            return f"(CASE {' '.join(whens)} ELSE {last} END)" if whens else last
        name, xs = t["fn"], [go(a) for a in t["args"]]
        if name == "raise":
            return raise_(t["message"], xs[0])
        if name == "isNum":
            return f"({xs[0]} IS NOT NULL)"
        if name == "isNull":
            return f"({xs[0]} IS NULL)"
        if name == "not":
            return f"(NOT {xs[0]})"
        if name == "lt" and any(a.get("code") in ("1", "-1") for a in t["args"]):
            # Codes ±1 lie between 0 and the nearest doubles (the logarithms'
            # `FMath.lo?`): `x < 1` is `x <= 0`, `-1 < x` is `0 <= x`.
            zero = float_lit(0.0)
            a, b = t["args"]
            if b.get("code") in ("1", "-1"):
                return f"({xs[0]} {'<=' if b['code'] == '1' else '<'} {zero})"
            return f"({zero} {'<' if a['code'] == '1' else '<='} {xs[1]})"
        if name in ("dadd", "dsub", "dmul"):
            op = {"dadd": "+", "dsub": "-", "dmul": "*"}[name]
            return f"({_hugeint(xs[0])} {op} {xs[1]})"
        if name == "idiv":
            # DuckDB's `//` truncates integers.
            return f"({xs[0]} // {xs[1]})"
        if name.startswith("fmath:"):
            return f"{name.removeprefix('fmath:').upper()}({xs[0]})"
        if name in _BINARY:
            return f"({xs[0]} {_BINARY[name]} {xs[1]})"
        if name in _CALLS:
            return f"{_CALLS[name]}({', '.join(xs)})"
        raise ValueError(f"lowering table: no SQL for {name}")

    return go(tmpl)
