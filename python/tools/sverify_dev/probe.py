"""Probe DuckDB's functions for the Substrait options they implement (#242).

Maintainer tooling (`sverify_dev`): not in the wheel, and not part of sverify's
API.

For each DuckDB function and signature (a `Probe`), DuckDB evaluates it on
edge cases (zero, ±1, the 64-bit bounds, -0.0, ±inf, NaN, NULL), one row at a
time, natively. Lean evaluates the Substrait call on the same rows once per
candidate value of the option that may describe it (`overflow`,
`on_division_by_zero`, …), with the reference's outcomes (`substrait-check
--outcomes`: a value, or the error raised). The candidates whose outcomes all
match are DuckDB's options for that function; a probe that no candidate
matches is behaviour the model cannot express yet, and the rows that differ
say where.

`python -m sverify_dev.probe` writes `characterization/duckdb/probes.json`,
the evidence `Profile.duckdb` is seeded from (the `duckdb-R15-…` facts in
`characterization/duckdb/facts/` cite its constructs).
"""

from __future__ import annotations

import argparse
import itertools
import json
import math
from collections.abc import Callable, Sequence
from dataclasses import dataclass, field
from fractions import Fraction
from typing import Any

import duckdb
import ibis

from sverify import plan_json as pj
from sverify.contracts import INF_MAG, NAN_MAG
from sverify.engine import run_checker
from sverify_dev import slt

Json = dict[str, Any]

I64 = 2**63
INTS: list[int | None] = [0, 1, -1, 2, -2, 3, 7, -7, I64 - 1, -I64, None]
# No -0.0: the model has one zero (`canon` keeps -0.0 out of sverify's SQL).
DOUBLES: list[float | None] = [
    0.0, 0.5, 1.0, -1.0, 2.5, -2.5, 7.0, 1e308, math.inf, -math.inf, math.nan, None
]  # fmt: skip

#: The DuckDB settings probed (all combinations): `Profile.duckdb`'s parameters.
SETTINGS = {"error_on_division_by_zero": (True, False), "ieee_floating_point_ops": (True, False)}

#: ASCII only: on other text, `\\d`, `\\w`, `\\s` and `\\b` are each engine's own,
#: and Lean does not evaluate them (`Text.classesDiffer`).
STRINGS: list[str | None] = ["", "a", "ab", "abc", "aaa", "a\nb", "xay", "say hi_2", None]

#: Ibis's and DuckDB's names of the probed types.
TYPES = {
    "int64": ("BIGINT", INTS),
    "float64": ("DOUBLE", DOUBLES),
    "string": ("VARCHAR", STRINGS),
}


@dataclass(frozen=True)
class Probe:
    """A DuckDB function at one signature, and the Substrait call that may
    describe it."""

    construct: str
    """DuckDB's SQL, the arguments as `{0}`, `{1}`."""
    function: str
    """The Substrait function's name."""
    args: tuple[str, ...]
    """The arguments' Ibis types (`TYPES`)."""
    result: str
    option: str | None = None
    """The option probed, if any, and its candidate values."""
    candidates: tuple[str, ...] = ()
    fixed: dict[str, str] = field(default_factory=dict)
    """Options every candidate carries."""
    constants: tuple[tuple[Any, str], ...] = ()
    """Constant arguments after the columns, with their Ibis types: in
    `construct` as the placeholders after the columns'."""


def _arith(sym: str, name: str) -> list[Probe]:
    return [
        Probe(f"{{0}} {sym} {{1}}", name, ("int64", "int64"), "int64",
              "overflow", ("ERROR", "SILENT", "SATURATE")),
        Probe(f"{{0}} {sym} {{1}}", name, ("float64", "float64"), "float64"),
    ]  # fmt: skip


PROBES: list[Probe] = [
    *_arith("+", "add"),
    *_arith("-", "subtract"),
    *_arith("*", "multiply"),
    Probe("-{0}", "negate", ("int64",), "int64", "overflow", ("ERROR", "SILENT", "SATURATE")),
    Probe("{0} // {1}", "divide", ("int64", "int64"), "int64",
          "on_division_by_zero", ("ERROR", "NULL")),
    Probe("{0} % {1}", "modulus", ("int64", "int64"), "int64",
          "on_division_by_zero", ("ERROR", "NULL")),
    Probe("{0} / {1}", "divide", ("float64", "float64"), "float64",
          "on_division_by_zero", ("ERROR", "IEEE", "NULL", "LIMIT")),
    Probe("{0} % {1}", "modulus", ("float64", "float64"), "float64",
          "on_division_by_zero", ("ERROR", "NULL")),
    Probe("abs({0})", "abs", ("int64",), "int64"),
    Probe("power({0}, {1})", "power", ("float64", "float64"), "float64"),
    Probe("floor({0})", "floor", ("float64",), "float64"),
    Probe("ceil({0})", "ceil", ("float64",), "float64"),
    Probe("round({0})", "round", ("float64",), "float64",
          "rounding", ("TIE_AWAY_FROM_ZERO",)),
    # To `d` digits (#335), down to beyond the doubles' range and up past it.
    *(
        Probe("round({0}, {1})", "round", ("float64",), "float64",
              constants=((d, "int64"),))
        for d in (-1000, -309, -308, -20, -1, 1, 2, 16, 308, 309, 400)
    ),
    *(
        Probe(f"{f}({{0}})", f, ("float64",), "float64")
        for f in ("sqrt", "exp", "ln", "log10", "log2", "sin", "cos", "tan",
                  "asin", "acos", "atan")
    ),
    Probe("atan2({0}, {1})", "atan2", ("float64", "float64"), "float64"),
    Probe("{0} << {1}", "shift_left", ("int64", "int64"), "int64"),
    Probe("{0} >> {1}", "shift_right", ("int64", "int64"), "int64"),
    # Regular expressions with a constant pattern (#50).
    *(
        Probe("regexp_extract({0}, {1}, {2})", "regexp_extract", ("string",), "string",
              constants=((p, "string"), (g, "int64")))
        for p, g in [("^(a+)(b)?", 2), ("(a|ab)(c|bcd)?", 0), ("(a*)*", 1), ("\\b(\\w)", 1),
                     ("x(?:a)(y)", 1), (".$", 0), ("(b)", 3)]
    ),
    *(
        Probe(f"regexp_replace({{0}}, {{1}}, {{2}}{flags})", "regexp_replace", ("string",),
              "string", constants=((p, "string"), (r, "string"), *extra))
        for p, r in [("a+", "<\\0>"), ("b*", "-"), ("(a)|(b)", "[\\2\\1]"), ("\\b", "|"),
                     ("$", "!")]
        for flags, extra in [("", ()), (", {3}", (("g", "string"),))]
    ),
    Probe("md5({0})", "md5", ("string",), "string"),
    Probe("sha256({0})", "sha256", ("string",), "string"),
]  # fmt: skip


def encode_double(x: float) -> int:
    """A double's code in the Lean model (`FloatCode.ofFloat`): zero (-0.0
    too) is 0, magnitudes m = |x| · 2¹⁰⁷⁴ are ±(2m + 1), one NaN."""
    if math.isnan(x):
        return 2 * NAN_MAG + 1
    if x == 0:
        return 0
    mag = INF_MAG if math.isinf(x) else int(Fraction(abs(x)) * 2**1074)
    return (2 * mag + 1) * (1 if x > 0 else -1)


def _sql_literal(v: Any, t: str) -> str:
    name = TYPES[t][0]
    if v is None:
        return f"CAST(NULL AS {name})"
    if isinstance(v, str):
        return _sql_constant(v)
    return f"CAST('{v!r}' AS {name})"


def _sql_constant(v: Any) -> str:
    """A constant argument as DuckDB's literal (`regexp_extract` takes its
    group as an INTEGER literal, not a BIGINT)."""
    return "'" + v.replace("'", "''") + "'" if isinstance(v, str) else str(v)


Outcome = tuple[str, Any]
"""`("ok", value)` (doubles as codes) or `("error", why)`."""


def duckdb_outcome(con: Any, p: Probe, row: Sequence[Any]) -> Outcome:
    # Columns, not literals: DuckDB folds constants, and `-CAST(x AS BIGINT)`
    # of a constant is a HUGEINT.
    cols = ", ".join(
        f"{_sql_literal(v, t)} AS a{i}" for i, (v, t) in enumerate(zip(row, p.args, strict=True))
    )
    consts = [_sql_constant(v) for v, _ in p.constants]
    sql = p.construct.format(*(f"a{i}" for i in range(len(p.args))), *consts)
    try:
        ((v,),) = con.execute(f"SELECT {sql} FROM (SELECT {cols})").fetchall()
    except duckdb.Error as e:
        return "error", str(e).splitlines()[0]
    if isinstance(v, float):
        return "ok", encode_double(v)
    return "ok", v


def _plan(p: Probe, rows: Sequence[Sequence[Any]], option: str | None) -> str:
    schema = ibis.schema({f"a{i}": t for i, t in enumerate(p.args)})
    with pj.compiling() as c:
        rel = pj.values_rel(
            schema,
            [[pj.literal(v, ibis.dtype(t)) for v, t in zip(r, p.args, strict=True)] for r in rows],
        )
        consts = [pj.literal(v, ibis.dtype(t)) for v, t in p.constants]
        e = pj.call(p.function, [pj.field_ref(i) for i in range(len(p.args))] + consts)
        opts = dict(p.fixed)
        if p.option is not None and option is not None:
            opts[p.option] = option
        if opts:
            e["scalarFunction"]["options"] = [
                {"name": k, "preference": [v]} for k, v in opts.items()
            ]
        e["scalarFunction"]["outputType"] = pj.type_json(ibis.dtype(p.result))
        return json.dumps(pj.plan(c, pj.project_rel(rel, len(p.args), [e]), ["r"]))


def lean_outcomes(p: Probe, rows: Sequence[Sequence[Any]], option: str | None) -> list[Outcome]:
    """Lean's outcome of `p` with `option` on each row, or a refusal for all."""
    code, out, err = run_checker(("--outcomes",), _plan(p, rows, option))
    if code != 0:
        why = ((err or out).strip().splitlines() or ["?"])[-1]
        return [("refused", why)] * len(rows)
    found: list[Outcome] = []
    for line in out.splitlines():
        (o,) = json.loads(line)
        found.append(("ok", o["ok"]) if "ok" in o else ("error", o["error"]))
    return found


def _same(a: Outcome, b: Outcome) -> bool:
    return a[0] == b[0] == "error" or a == b


def _show(row: Sequence[Any], o: Outcome, p: Probe) -> str:
    from sverify.contracts import decode_double

    v = o[1]
    if o[0] == "ok" and p.result == "float64" and isinstance(v, int):
        v = decode_double(v)
    return f"{list(row)} -> {o[0]} {v}"


def run_probe(con: Any, p: Probe) -> Json:
    """`p`'s matching candidates, and for each candidate the rows that differ."""
    rows = list(itertools.product(*(TYPES[t][1] for t in p.args)))
    engine = [duckdb_outcome(con, p, r) for r in rows]
    tried: dict[str, Json] = {}
    for cand in p.candidates or (None,):
        lean = lean_outcomes(p, rows, cand)
        diff = [
            {"row": _show(r, e, p).split(" -> ")[0], "duckdb": _show(r, e, p).split(" -> ")[1],
             "lean": _show(r, x, p).split(" -> ")[1]}
            for r, e, x in zip(rows, engine, lean, strict=True)
            if not _same(e, x)
        ]  # fmt: skip
        tried[cand or "(none)"] = {"differ": len(diff), "examples": diff[:4]}
    matching = [c for c, t in tried.items() if t["differ"] == 0]
    return {
        "construct": p.construct.format(
            *(TYPES[t][0] for t in p.args), *(_sql_constant(v) for v, _ in p.constants)
        ),
        "function": p.function,
        "option": p.option,
        "rows": len(rows),
        "matching": matching,
        "candidates": tried,
    }


def probe_all(probes: Sequence[Probe] = PROBES, log: Callable[[str], None] = print) -> list[Json]:
    """Every probe under every combination of `SETTINGS`."""
    found = []
    for values in itertools.product(*SETTINGS.values()):
        settings = dict(zip(SETTINGS, values, strict=True))
        con = duckdb.connect()
        for k, v in settings.items():
            con.execute(f"SET {k} = {str(v).lower()}")
        log(f"-- {settings}")
        for p in probes:
            r = {"settings": settings, **run_probe(con, p)}
            verdict = ", ".join(r["matching"]) or "NO MATCH"
            log(f"{r['construct']}: {verdict}")
            found.append(r)
    return found


def main(argv: Sequence[str] | None = None) -> None:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("--write", action="store_true", help="write probes.json")
    args = parser.parse_args(argv)
    found = probe_all()
    if args.write:
        out = slt.REPLAY_DIR / "probes.json"
        head = {"duckdb": duckdb.__version__, "probes": found}
        out.write_text(json.dumps(head, indent=1) + "\n")
        print(f"-> {out}")


if __name__ == "__main__":
    main()
