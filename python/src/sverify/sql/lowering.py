"""The generated lowering to DuckDB, as SQL (#241).

For each function DuckDB does not compute as the reference does, the Lean
build generates a template and proves it gives the reference's outcome under
DuckDB's profile (`engines/duckdb/Sverify/DuckDB/Lowering.lean`, `Lowering.duckdb_exact`).
`substrait-check --lowering-table` exports those templates, and this module
writes one as SQL: its fields are the arguments' SQL, its calls DuckDB's own
operators, its `CASE`s SQL's. The DuckDB printer (`sverify_duckdb.dialect`) asks
it first (`Dialect.lowered`), so the guards in DuckDB's SQL are the proved
ones rather than hand-written.

The table is for DuckDB's default settings, `error_on_division_by_zero` and
`ieee_floating_point_ops` on, which sverify runs DuckDB with. Under other
settings DuckDB computes other values, and there is no proved table for them
(#241): run the SQL with the defaults.

This interpreter is trusted, as the printer is: keep it small.
"""

from __future__ import annotations

import functools
import json
import subprocess
from collections.abc import Callable, Mapping, Sequence
from typing import Any

from sverify._checker import checker_path, decode_double

Json = Any

#: `error_on_division_by_zero`, which the table is for: DuckDB's default, the only one.
SETTING = "on"

_EXPORT: list[Mapping[str, Json]] = []


def _export() -> Mapping[str, Json]:
    """The checker's `--lowering-table`, read once."""
    if not _EXPORT:
        out = subprocess.run(
            [str(checker_path()), "--lowering-table"], capture_output=True, text=True, check=True
        ).stdout
        _EXPORT.append(json.loads(out))
    return _EXPORT[0]


@functools.cache
def table(engine: str = SETTING) -> Mapping[str, Json]:
    """The templates by function (`"fdiv"`, `"fmath:sqrt"`, `"fit:silent:64"`,
    `"bit:bitwise_shift_left"`): DuckDB's at its `SETTING`, `"polars"`'s
    (`sverify_polars.lowering`) or `"spark"`'s."""
    return {e["fn"]: e["template"] for e in _export()[engine]}


@functools.cache
def asks(engine: str) -> Mapping[tuple[str, str], str]:
    """What an engine's rendering of a function asks for (ruling 282's C8): the
    behaviour by function and option, from `--lowering-table`'s
    `"<engine>_asks"` (`Polars.asks`); empty for an engine without one."""
    return {(a["fn"], a["option"]): a["behaviour"] for a in _export().get(f"{engine}_asks", [])}


def floor_table() -> Mapping[str, Json]:
    """The core's `FLOOR` templates as JSON by kind (`"div"`, `"mod"`, `"fmod"`),
    from the `"floor"` key (`LoweringExport.floorJson`)."""
    return _export()["floor"]


#: DuckDB's operators for the model's functions a template calls.
_BINARY = {
    "eq": "=", "lt": "<", "and": "AND", "or": "OR",
    "fadd": "+", "fsub": "-", "fmul": "*", "fdiv": "/", "fdivIeee": "/", "fmod": "%", "imod": "%",
    "bit:bitwise_and": "&", "bit:bitwise_or": "|",
    "bit:bitwise_shift_left": "<<", "bit:bitwise_shift_right": ">>",
}  # fmt: skip
_CALLS = {
    "fpow": "POWER",
    "fatan2": "ATAN2",
    "bit:bitwise_xor": "xor",
    "ffloor": "FLOOR",
    "Substrait.UnFn.fround": "ROUND",
    "Substrait.UnFn.froundEven": "ROUND_EVEN",
    "Substrait.UnFn.fceil": "CEIL",
}


def _hugeint(x: str) -> str:
    return f"CAST({x} AS HUGEINT)"


def _value(t: Json, consts: Sequence[float | int | None]) -> float | int | None:
    """The value of a number term when the arguments' literals decide it."""
    if "field" in t:
        i = t["field"]
        return consts[i] if i < len(consts) else None
    if "code" in t:
        return decode_double(int(t["code"]))
    if "int" in t:
        return int(t["int"])
    return None


def reduce(t: Json, consts: Sequence[float | int | None]) -> Json:
    """The condition `t` with what the literal `consts` decide written out: a
    `{"bool": …}` where they decide all of it, else `t` without its decided
    parts (None where an argument is not a literal). NaN and the codes `±1`
    (`x < 1` is `x <= 0`, below) are left to the SQL."""
    name, args = t.get("fn"), t.get("args", [])

    def known(v: bool) -> Json:
        return {"bool": v}

    if name in ("eq", "lt"):
        x, y = (_value(a, consts) for a in args)
        if x is None or y is None or x != x or y != y:
            return t
        if name == "lt" and any(a.get("code") in ("1", "-1") for a in args):
            return t
        return known(x == y if name == "eq" else x < y)
    if name in ("isNum", "isNull"):
        # A literal is a number, not NULL.
        return t if _value(args[0], consts) is None else known(name == "isNum")
    if name == "not":
        v = reduce(args[0], consts)
        return known(not v["bool"]) if "bool" in v else {**t, "args": [v]}
    if name in ("and", "or"):
        stop = name == "or"
        vs = [reduce(a, consts) for a in args]
        if any(v.get("bool") is stop for v in vs):
            return known(stop)
        if name == "and" and any(
            a.get("fn") == "isNum" and {"fn": "isNull", "args": a["args"]} in args for a in args
        ):
            return known(False)  # `isNum x` and `isNull x`
        rest = [v for v in vs if "bool" not in v]
        if not rest:
            return known(not stop)
        return rest[0] if len(rest) == 1 else {**t, "args": rest}
    return t


def render(
    fn: str,
    args: Sequence[str],
    raise_: Callable[[str, str], str],
    float_lit: Callable[[float], str],
    int_lit: Callable[[int], str],
    guards: bool = True,
    consts: Sequence[float | int | None] = (),
    *,
    engine: str = SETTING,
    call: Callable[[str, list[str]], str | None] | None = None,
    date_lit: Callable[[int], str] | None = None,
) -> str | None:
    """`fn` of the arguments' SQL as its template writes it, or None where
    DuckDB's own function is the reference's (no template). `raise_` writes
    an error with its message and the value it depends on. Without `guards`
    (`to_sql(..., guards=False)`, for plans proved not to raise) the arms of
    a `CASE` that raise are left out: they would never be taken. That the
    templates without them still give the reference's rows is
    `Rel.duckdb_guardFree_sound` (`engines/duckdb/Sverify/DuckDB/Lowering.lean`).
    `consts` gives the value of each argument that is a literal, else None: an
    arm of a `CASE` whose condition is false for those values is left out, and
    a true one ends the `CASE` (`reduce`).

    `engine` picks the table (`table`). `call` writes a call the engine
    spells its own way (Spark's `FLOOR` gives a `BIGINT`), or None for the
    operators below; `date_lit` writes a date by its days since 1970-01-01."""
    tmpl = table(engine).get(fn)
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
        if "date" in t and date_lit is not None:
            return date_lit(int(t["date"]))
        if "int" in t:
            i = int(t["int"])
            # The wrap-arounds compute in 128 bits (`BinFn.dadd`, …).
            return int_lit(i) if -(2**63) <= i < 2**63 else _hugeint(str(i))
        if "if" in t:
            # A chain of `CASE`s in the `ELSE` is one `CASE`.
            whens = []
            while "if" in t:
                cond = reduce(t["if"], consts)
                if "bool" in cond:
                    t = t["then"] if cond["bool"] else t["else"]
                    continue
                if guards or t["then"].get("fn") != "raise":
                    whens.append(f"WHEN {go(cond)} THEN {go(t['then'])}")
                t = t["else"]
            last = go(t)
            return f"(CASE {' '.join(whens)} ELSE {last} END)" if whens else last
        name, xs = t["fn"], [go(a) for a in t["args"]]
        if name == "raise":
            return raise_(t["message"], xs[0])
        if call is not None and (own := call(name, xs)) is not None:
            return own
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
        if name == "Substrait.UnFn.ftoi":
            return f"CAST({xs[0]} AS BIGINT)"
        if name == "Substrait.UnFn.ftoiOrNull":
            return f"TRY_CAST({xs[0]} AS BIGINT)"
        if name in _BINARY:
            return f"({xs[0]} {_BINARY[name]} {xs[1]})"
        if name in _CALLS:
            # DuckDB's `round_even` takes its digits: zero (D55).
            tail = ", 0" if name == "Substrait.UnFn.froundEven" else ""
            return f"{_CALLS[name]}({', '.join(xs)}{tail})"
        raise ValueError(f"lowering table: no SQL for {name}")

    return go(tmpl)
