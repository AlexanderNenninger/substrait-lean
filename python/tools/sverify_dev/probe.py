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

An `Observation` is a DuckDB query whose result the reference has no single
call for (a sort, a grouping, a decimal's type, a time zone): its result is
recorded as it is, after the probes, under `TimeZone = 'UTC'` unless its setup
says otherwise. `--observations` reruns those alone, keeping the recorded
probes, and needs no Lean.

`python -m sverify_dev.probe --write` writes `characterization/duckdb/probes.json`,
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
from sverify.contracts import INF_MAG, NAN_MAG, NEG_ZERO
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
    """A double's code in the Lean model (`FloatCode.ofFloat`): zero is 0 and
    -0.0 `NEG_ZERO` (D31), magnitudes m = |x| · 2¹⁰⁷⁴ are ±(2m + 1), one NaN."""
    if math.isnan(x):
        return 2 * NAN_MAG + 1
    if x == 0:
        return NEG_ZERO if math.copysign(1.0, x) < 0 else 0
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


@dataclass(frozen=True)
class Observation:
    """A DuckDB query whose result the reference has no single call for (a
    sort, a grouping, a decimal's type, a time zone): its result is recorded
    as it is, for the facts to cite."""

    construct: str
    """Its name, which facts cite."""
    area: str
    sql: str
    """One query; `setup` runs first."""
    setup: tuple[str, ...] = ()


def _o(construct: str, area: str, sql: str, *setup: str) -> Observation:
    return Observation(construct, area, sql, setup)


#: A macro printing a double as text with any NaN as `nan`, whatever its sign.
_NAN_TEXT = ("CREATE MACRO nan_text(x) AS CASE WHEN isnan(x) THEN 'nan' ELSE x::VARCHAR END",)


#: Two bags with duplicates, NULLs, both NaNs and both zeros, for the set
#: operations and the NaN keys.
_BAGS = (
    "CREATE TABLE a AS SELECT * FROM (VALUES (1.0), (1.0), (1.0), (2.0), (NULL), (NULL),"
    " ('nan'::DOUBLE), (-0.0::DOUBLE)) t(x)",
    "CREATE TABLE b AS SELECT * FROM (VALUES (1.0), (1.0), (NULL), (3.0), (-'nan'::DOUBLE),"
    " (0.0::DOUBLE)) t(x)",
)

#: Rows of a window: ties, and NULLs in the order key.
_WIN = "(VALUES (1, 10), (2, 20), (2, 30), (3, 40), (NULL, 50), (NULL, 60)) t(i, x)"

#: A join's input with a row the filter `10 // x > 1` raises on, and two rows
#: for a guarded division, for the evaluation-order observations.
_A = "CREATE TABLE a AS SELECT * FROM (VALUES (1, 0), (2, 5)) t(k, x)"
_T05 = "CREATE TABLE t AS SELECT * FROM (VALUES (0), (5)) v(x)"

#: Lists for UNNEST: a full one, an empty one, a NULL one, one of a NULL.
_LISTS = "(VALUES (1, [1, 2]), (2, []), (3, NULL), (4, [NULL])) t(id, l)"

OBSERVATIONS: list[Observation] = [
    # Decimals.
    _o("dec-result-types", "decimals",
       "SELECT typeof(1.25::DECIMAL(4,2) + 1.5::DECIMAL(3,1)),"
       " typeof(1.25::DECIMAL(4,2) * 1.25::DECIMAL(4,2)),"
       " typeof(1::DECIMAL(10,2) * 1::DECIMAL(10,2)), typeof(1::DECIMAL(18,2) + 1::DECIMAL(18,2)),"
       " typeof(1::DECIMAL(20,10) * 1::DECIMAL(20,10)),"
       " typeof(1::DECIMAL(38,0) + 1::DECIMAL(38,0)),"
       " typeof(1.25::DECIMAL(4,2) / 1.5::DECIMAL(3,1)), typeof(-1.25::DECIMAL(4,2)),"
       " typeof(round(1.25::DECIMAL(4,2), 1))"),
    _o("dec-aggregate-types", "decimals",
       "SELECT typeof(sum(x)), typeof(avg(x)), typeof(min(x)), sum(x), avg(x)"
       " FROM (VALUES (1.25::DECIMAL(4,2)), (1.26::DECIMAL(4,2))) t(x)"),
    _o("dec-multiply-18", "decimals",
       "SELECT 9999999999999.99::DECIMAL(15,2) * 9999999999999.99::DECIMAL(15,2)"),
    _o("dec-multiply-scale-38", "decimals",
       "SELECT 0.5::DECIMAL(38,37) * 0.5::DECIMAL(38,37)"),
    _o("dec-add-overflow", "decimals",
       "SELECT 99999999999999999999999999999999999999::DECIMAL(38,0) + 1::DECIMAL(38,0)"),
    _o("dec-sum-overflow", "decimals",
       "SELECT sum(x) FROM (VALUES (99999999999999999999999999999999999999::DECIMAL(38,0)),"
       " (1::DECIMAL(38,0))) t(x)"),
    _o("dec-rescale", "decimals",
       "SELECT CAST(1.25::DECIMAL(4,2) AS DECIMAL(3,1)), CAST(-1.25::DECIMAL(4,2) AS DECIMAL(3,1)),"
       " CAST(1.35::DECIMAL(4,2) AS DECIMAL(3,1)), CAST(0.125::DECIMAL(4,3) AS DECIMAL(3,2)),"
       " CAST(2.5::DECIMAL(3,1) AS DECIMAL(2,0)), CAST(-2.5::DECIMAL(3,1) AS DECIMAL(2,0)),"
       " CAST(0.05::DECIMAL(10,2) * 0.5::DECIMAL(10,1) AS DECIMAL(10,2))"),
    _o("dec-round", "decimals",
       "SELECT round(2.5::DECIMAL(3,1)), round(-2.5::DECIMAL(3,1)), round(1.25::DECIMAL(4,2), 1),"
       " round(-1.25::DECIMAL(4,2), 1)"),
    _o("dec-to-int", "decimals",
       "SELECT CAST(2.5::DECIMAL(3,1) AS INTEGER), CAST(-2.5::DECIMAL(3,1) AS INTEGER),"
       " CAST(3.5::DECIMAL(3,1) AS INTEGER)"),
    _o("dec-from-double", "decimals",
       "SELECT CAST(0.625::DOUBLE AS DECIMAL(3,2)), CAST(-0.125::DOUBLE AS DECIMAL(3,2)),"
       " CAST(2.675::DOUBLE AS DECIMAL(3,2)), CAST('2.675' AS DECIMAL(3,2))"),
    _o("dec-divide", "decimals",
       "SELECT 1.00::DECIMAL(10,2) / 8::DECIMAL(10,0), 10::DECIMAL(10,0) / 3::DECIMAL(10,0),"
       " CAST(1.00::DECIMAL(10,2) / 8::DECIMAL(10,0) AS DECIMAL(10,2))"),
    # NaN in equality and keys.
    _o("nan-compare", "doubles",
       "SELECT 'nan'::DOUBLE = 'nan'::DOUBLE, 'nan'::DOUBLE <> 'nan'::DOUBLE,"
       " 'nan'::DOUBLE = -'nan'::DOUBLE, 'nan'::DOUBLE IN (1.0, 'nan'::DOUBLE),"
       " 'nan'::DOUBLE IS DISTINCT FROM 'nan'::DOUBLE, 'nan'::FLOAT = 'nan'::FLOAT,"
       " list_contains([1.0, 'nan'::DOUBLE], 'nan'::DOUBLE),"
       " list_position([1.0, 'nan'::DOUBLE], 'nan'::DOUBLE)"),
    _o("nan-group", "doubles",
       "SELECT count(*), list(x::VARCHAR ORDER BY x::VARCHAR) FROM (SELECT x FROM a UNION ALL"
       " SELECT x FROM b) GROUP BY x ORDER BY min(x)", *_BAGS),
    _o("nan-distinct", "doubles",
       "SELECT count(DISTINCT x), count(*) FROM (SELECT x FROM a UNION ALL SELECT x FROM b)"
       " WHERE isnan(x)", *_BAGS),
    _o("nan-join", "doubles",
       "SELECT a.x::VARCHAR, b.x::VARCHAR FROM a JOIN b ON a.x = b.x ORDER BY a.x", *_BAGS),
    # Case mapping.
    _o("case-unicode", "strings",
       "SELECT upper('straße'), upper('ß'), upper('ﬁ'), upper('ǆ'), lower('İ'), length(lower('İ')),"
       " lower('ΣΑΣ'), upper('éÿ'), lower('ÀΩ')"),
    # Dates and timestamps past the reference's range.
    _o("date-past-9999", "temporal",
       "SELECT (DATE '9999-12-31' + 1)::VARCHAR, (DATE '0001-01-01' - 1)::VARCHAR,"
       " (DATE '9999-12-31' + INTERVAL 1 MONTH)::VARCHAR,"
       " (DATE '0001-01-01' - INTERVAL 1 YEAR)::VARCHAR,"
       " (TIMESTAMP '9999-12-31 23:59:59' + INTERVAL 1 SECOND)::VARCHAR,"
       " year(DATE '0001-01-01' - 1),"
       " date_diff('day', DATE '0001-01-01', DATE '9999-12-31')"),
    _o("date-limits", "temporal",
       "SELECT (DATE '5877642-06-25 (BC)')::VARCHAR, (DATE '5881580-07-10')::VARCHAR"),
    _o("date-beyond-max", "temporal", "SELECT DATE '5881580-07-10' + 1"),
    _o("date-beyond-min", "temporal", "SELECT DATE '5877642-06-25 (BC)' - 1"),
    _o("date-interval-beyond-timestamp", "temporal",
       "SELECT DATE '5881580-07-10' + INTERVAL 1 DAY"),
    _o("timestamp-beyond-max", "temporal",
       "SELECT TIMESTAMP '294247-01-10 04:00:54.775806' + INTERVAL 1 SECOND"),
    # Time zones (ICU), under a set TimeZone: its default is the host's.
    _o("tz-gap-overlap", "temporal",
       "SELECT (TIMESTAMPTZ '2024-03-31 02:30:00')::VARCHAR,"
       " (TIMESTAMPTZ '2024-10-27 02:30:00')::VARCHAR,"
       " (TIMESTAMP '2024-03-31 02:30:00' AT TIME ZONE 'Europe/Berlin')::VARCHAR,"
       " (TIMESTAMP '2024-10-27 02:30:00' AT TIME ZONE 'Europe/Berlin')::VARCHAR",
       "SET TimeZone = 'Europe/Berlin'"),
    _o("tz-to-local", "temporal",
       "SELECT (TIMESTAMPTZ '2024-10-27 00:30:00+00' AT TIME ZONE 'Europe/Berlin')::VARCHAR,"
       " (TIMESTAMPTZ '2024-10-27 01:30:00+00' AT TIME ZONE 'Europe/Berlin')::VARCHAR,"
       " (TIMESTAMPTZ '2024-01-01 00:00:00 America/New_York')::VARCHAR,"
       " (TIMESTAMPTZ '2024-03-31 12:00:00+00')::DATE::VARCHAR,"
       " date_part('hour', TIMESTAMPTZ '2024-03-31 12:00:00+00')",
       "SET TimeZone = 'Europe/Berlin'"),
    _o("tz-interval", "temporal",
       "SELECT (TIMESTAMPTZ '2024-03-30 12:00:00+01' + INTERVAL 1 DAY)::VARCHAR,"
       " (TIMESTAMPTZ '2024-03-30 12:00:00+01' + INTERVAL 24 HOUR)::VARCHAR,"
       " date_trunc('day', TIMESTAMPTZ '2024-03-31 12:00:00+02')::VARCHAR,"
       " date_diff('hour', TIMESTAMPTZ '2024-03-31 00:00:00+01',"
       " TIMESTAMPTZ '2024-04-01 00:00:00+02')",
       "SET TimeZone = 'Europe/Berlin'"),
    _o("tz-utc", "temporal",
       "SELECT (TIMESTAMPTZ '2024-03-31 02:30:00')::VARCHAR,"
       " (TIMESTAMPTZ '2024-03-31 02:30:00+05:30')::VARCHAR,"
       " (TIMESTAMPTZ '2024-03-31 02:30:00+05:30')::TIMESTAMP::VARCHAR",
       "SET TimeZone = 'UTC'"),
    _o("tz-unknown", "temporal",
       "SELECT TIMESTAMPTZ '2024-01-01 00:00:00+00' AT TIME ZONE 'Nowhere/Land'"),
    # NULLs.
    _o("null-concat", "nulls",
       "SELECT 'a' || NULL, concat('a', NULL, 'b'), concat(NULL, NULL), concat_ws(',', 'a',"
       " NULL, 'b'),"
       " concat_ws(NULL, 'a'), [1] || NULL, list_concat([1], NULL)"),
    _o("null-functions", "nulls",
       "SELECT upper(NULL), length(NULL), substring('abc', NULL, 1), replace('abc', NULL, 'x'),"
       " greatest(1, NULL, 3), least(NULL, 2), greatest(NULL::INT, NULL), coalesce(NULL, 1)"),
    _o("null-logic", "nulls",
       "SELECT NULL AND FALSE, NULL AND TRUE, NULL OR TRUE, NULL OR FALSE, NOT NULL,"
       " NULL = NULL, NULL IN (1, NULL), 1 IN (1, NULL), 2 NOT IN (1, NULL)"),
    _o("null-bool-agg", "nulls",
       "SELECT bool_and(x), bool_or(x), count(x), count(*) FROM (VALUES (TRUE), (NULL)) t(x)"
       " UNION ALL SELECT bool_and(x), bool_or(x), count(x), count(*)"
       " FROM (VALUES (FALSE), (NULL)) t(x)"
       " UNION ALL SELECT bool_and(x), bool_or(x), count(x), count(*)"
       " FROM (VALUES (NULL::BOOLEAN)) t(x)"
       " UNION ALL SELECT bool_and(x), bool_or(x), count(x), count(*)"
       " FROM (SELECT TRUE x WHERE FALSE) t"),
    _o("null-join", "nulls",
       "SELECT 'eq', a.x, b.x FROM (VALUES (1), (NULL)) a(x) JOIN (VALUES (1), (NULL)) b(x)"
       " ON a.x = b.x UNION ALL SELECT 'indistinct', a.x, b.x FROM (VALUES (1), (NULL)) a(x)"
       " JOIN (VALUES (1), (NULL)) b(x) ON a.x IS NOT DISTINCT FROM b.x ORDER BY 1, 2"),
    _o("null-full-join", "nulls",
       "SELECT a.x, b.x FROM (VALUES (1), (NULL)) a(x) FULL JOIN (VALUES (1), (NULL)) b(x)"
       " ON a.x = b.x ORDER BY 1, 2"),
    _o("null-in-subquery", "nulls",
       "SELECT x, x IN (SELECT NULL::INT), x NOT IN (SELECT y FROM (VALUES (2), (NULL)) s(y))"
       " FROM (VALUES (1), (NULL)) a(x) ORDER BY x"),
    _o("null-group", "nulls",
       "SELECT x, count(*) FROM (VALUES (1), (NULL), (NULL)) t(x) GROUP BY x ORDER BY x"),
    _o("null-spaceship", "nulls", "SELECT 1 <=> NULL"),
    # Nested.
    _o("list-index", "nested",
       "SELECT [10, 20, 30][1], [10, 20, 30][0], [10, 20, 30][-1], [10, 20, 30][-3], [10, 20,"
       " 30][4],"
       " [10, 20, 30][-4], (NULL::INT[])[1], [10, 20, 30][NULL],"
       " [10, 20, 30][9223372036854775807], list_extract([10, 20, 30], 2)"),
    _o("list-slice", "nested",
       "SELECT [10, 20, 30][2:3], [10, 20, 30][-2:], [10, 20, 30][0:1], [10, 20, 30][3:2]"),
    _o("list-equality", "nested",
       "SELECT [1, NULL] = [1, NULL], [1, NULL] = [1, 2], [1, NULL] <> [1, 2], NULL::INT[] = [1]"),
    _o("struct-equality", "nested",
       "SELECT {'a': 1, 'b': NULL} = {'a': 1, 'b': NULL}, {'a': 1, 'b': NULL} = {'a': 1, 'b': 2},"
       " {'a': 1, 'b': NULL} <> {'a': 1, 'b': 2}, {'a': 1, 'b': NULL} < {'a': 1, 'b': 2},"
       " {'a': 1, 'b': NULL} > {'a': 1, 'b': 2}, NULL::STRUCT(a INT) = {'a': 1}"),
    _o("struct-order", "nested",
       "SELECT list(s ORDER BY s), list(s ORDER BY s DESC) FROM (VALUES ({'a': 1, 'b': 2}),"
       " ({'a': 1, 'b': NULL}), ({'a': NULL, 'b': 0}), ({'a': 0, 'b': 0})) t(s)"),
    _o("struct-group-join", "nested",
       "SELECT s, count(*), (SELECT count(*) FROM (VALUES ({'a': 1,"
       " 'b': NULL})) u(s2) WHERE s2 = s)"
       " FROM (VALUES ({'a': 1, 'b': NULL}), ({'a': 1, 'b': NULL}), ({'a': 1, 'b': 2}), (NULL))"
       " t(s) GROUP BY s ORDER BY s"),
    _o("unnest-select", "nested",
       f"SELECT id, unnest(l) FROM {_LISTS} ORDER BY id"),
    _o("unnest-lateral", "nested",
       f"SELECT id, u FROM {_LISTS}, unnest(l) AS v(u) ORDER BY id, u"),
    _o("unnest-left-lateral", "nested",
       f"SELECT id, u FROM {_LISTS} LEFT JOIN unnest(l) AS v(u) ON TRUE ORDER BY id, u"),
    _o("unnest-zip", "nested",
       "SELECT unnest([1, 2]), unnest([7]), unnest([]::INT[])"),
    # Windows.
    _o("ntile-spread", "windows",
       "SELECT n, list(t ORDER BY i) FROM (SELECT n, i, ntile(n) OVER (PARTITION BY n ORDER BY i) t"
       " FROM range(1, 11) r(i), (VALUES (2), (3), (4), (6), (7),"
       " (12)) k(n)) GROUP BY n ORDER BY n"),
    _o("ntile-args", "windows",
       "SELECT ntile(NULL) OVER (), ntile(2) OVER (), ntile(9223372036854775807) OVER ()"),
    _o("ntile-zero", "windows", "SELECT ntile(0) OVER ()"),
    _o("window-default-frame", "windows",
       f"SELECT i, x, sum(x) OVER (ORDER BY i), sum(x) OVER (), count(*) OVER (ORDER BY i),"
       f" last_value(x) OVER (ORDER BY i), first_value(x) OVER (ORDER BY i DESC),"
       f" sum(x) OVER (ORDER BY i ROWS BETWEEN UNBOUNDED PRECEDING AND CURRENT ROW)"
       f" FROM {_WIN} ORDER BY i, x"),
    _o("window-ranks", "windows",
       f"SELECT i, rank() OVER w, dense_rank() OVER w, percent_rank() OVER w, cume_dist() OVER w,"
       f" rank() OVER (ORDER BY i DESC) FROM {_WIN} WINDOW w AS (ORDER BY i) ORDER BY i, x"),
    _o("window-no-order", "windows",
       "SELECT rank() OVER (), dense_rank() OVER (), percent_rank() OVER (), cume_dist() OVER ()"
       " FROM (VALUES (1), (2)) t(i)"),
    _o("window-offsets", "windows",
       "SELECT i, lag(i) OVER w, lead(i, 1, -1) OVER w, nth_value(i, 2) OVER w,"
       " lag(i, 5) OVER w FROM (VALUES (1), (2), (3)) t(i) WINDOW w AS (ORDER BY i) ORDER BY i"),
    # Relations.
    _o("clustered-syntax", "relations", "SELECT 1 ORDER BY 1 CLUSTERED"),
    _o("set-operations", "relations",
       " UNION ALL ".join(
           f"SELECT '{name}',"
           f" list(v ORDER BY v)::VARCHAR FROM (SELECT CASE WHEN isnan(x) THEN 'NaN'"
           f" ELSE x::VARCHAR END v FROM (SELECT x FROM {lhs} WHERE x IS DISTINCT FROM 0 {op}"
           f" SELECT x FROM {r} WHERE x IS DISTINCT FROM 0))"
           for name, lhs, op, r in [
               ("union", "a", "UNION", "b"), ("union all", "a", "UNION ALL", "b"),
               ("intersect", "a", "INTERSECT", "b"), ("intersect all", "a", "INTERSECT ALL", "b"),
               ("except", "a", "EXCEPT", "b"), ("except all", "a", "EXCEPT ALL", "b"),
               ("b except all a", "b", "EXCEPT ALL", "a"),
           ]
       ),
       *_BAGS),
    _o("set-operation-types", "relations",
       "SELECT typeof(x) FROM (SELECT 1 x UNION SELECT 1.5) LIMIT 1"),
    # Evaluation order: what runs on rows the reference never evaluates.
    _o("exec-case-when-folded", "execution",
       "SELECT CASE WHEN x > 0 THEN 1 WHEN 1 // 0 = 1 THEN 2 END FROM t",
       "CREATE TABLE t AS SELECT 1 x"),
    _o("exec-case-when-folded-empty", "execution",
       "SELECT CASE WHEN x > 0 THEN 1 WHEN 1 // 0 = 1 THEN 2 END FROM t",
       "CREATE TABLE t (x INTEGER)"),
    _o("exec-case-when-folded-cast", "execution",
       "SELECT CASE WHEN x > 0 THEN 1 WHEN 'a'::INTEGER = 1 THEN 2 END FROM t",
       "CREATE TABLE t AS SELECT 1 x"),
    _o("exec-case-else-lazy", "execution",
       "SELECT CASE WHEN x > 0 THEN 1 ELSE 1 // 0 END FROM t", "CREATE TABLE t AS SELECT 1 x"),
    _o("exec-pushdown-empty-join", "execution",
       "SELECT * FROM a JOIN b ON a.k = b.k WHERE 10 // a.x > 1",
       _A, "CREATE TABLE b (k INTEGER)"),
    _o("exec-pushdown-empty-join-cast", "execution",
       "SELECT * FROM a JOIN b ON a.k = b.k WHERE a.s::INTEGER > 1",
       "CREATE TABLE a AS SELECT * FROM (VALUES (1, 'z'), (2, '5')) t(k, s)",
       "CREATE TABLE b (k INTEGER)"),
    _o("exec-pushdown-empty-left-join", "execution",
       "SELECT * FROM b LEFT JOIN a ON a.k = b.k WHERE 10 // a.x > 1",
       _A, "CREATE TABLE b (k INTEGER)"),
    _o("exec-pushdown-join", "execution",
       "SELECT * FROM a JOIN b ON a.k = b.k WHERE 10 // a.x > 1",
       _A,
       "CREATE TABLE b AS SELECT 2 k"),
    _o("exec-pushdown-join-no-join-filter", "execution",
       "SELECT * FROM a JOIN b ON a.k = b.k WHERE 10 // a.x > 1",
       _A,
       "CREATE TABLE b AS SELECT 2 k", "SET disabled_optimizers = 'join_filter_pushdown'"),
    _o("exec-and-value", "execution",
       "SELECT (x <> 0) AND (10 // x > 1) FROM t", _T05),
    _o("exec-and-value-one-row", "execution",
       "SELECT (x <> 0) AND (10 // x > 1) FROM t", "CREATE TABLE t AS SELECT 0 x"),
    _o("exec-or-value", "execution",
       "SELECT (x = 0) OR (10 // x > 1) FROM t", _T05),
    _o("exec-and-where", "execution",
       "SELECT x FROM t WHERE (x <> 0) AND (10 // x > 1)",
       _T05),
    _o("exec-and-where-raising-first", "execution",
       "SELECT x FROM t WHERE (10 // x > 1) AND (x <> 0)",
       _T05),
    _o("exec-and-where-raising-first-expr", "execution",
       "SELECT x FROM t WHERE (10 // x > 1) AND (x * x <> 0)",
       _T05),
    _o("exec-or-where", "execution",
       "SELECT x FROM t WHERE (x = 0) OR (10 // x > 1) ORDER BY x",
       _T05),
    _o("exec-and-case-when", "execution",
       "SELECT CASE WHEN (x <> 0) AND (10 // x > 1) THEN 1 ELSE 0 END FROM t ORDER BY x",
       _T05),
    _o("exec-and-aggregate-filter", "execution",
       "SELECT count(*) FILTER (WHERE (x <> 0) AND (10 // x > 1)) FROM t",
       _T05),
    # Signed zeros and NaNs.
    _o("zero-order-negative-first", "doubles",
       "SELECT v::VARCHAR, signbit(v) FROM (VALUES (-0.0::DOUBLE), (0.0::DOUBLE), (-0.0::DOUBLE))"
       " t(v) ORDER BY v"),
    _o("zero-order-positive-first", "doubles",
       "SELECT v::VARCHAR, signbit(v) FROM (VALUES (0.0::DOUBLE), (-0.0::DOUBLE), (0.0::DOUBLE))"
       " t(v) ORDER BY v"),
    _o("zero-order-desc", "doubles",
       "SELECT v::VARCHAR FROM (VALUES (0.0::DOUBLE), (-0.0::DOUBLE)) t(v) ORDER BY v DESC"),
    _o("zero-order-float", "doubles",
       "SELECT v::VARCHAR, signbit(v) FROM (VALUES (0.0::FLOAT), (-0.0::FLOAT), (0.0::FLOAT)) t(v)"
       " ORDER BY v"),
    _o("least-greatest-zero", "doubles",
       "SELECT least(-0.0::FLOAT, 0.0::FLOAT)::VARCHAR, least(0.0::FLOAT, -0.0::FLOAT)::VARCHAR,"
       " greatest(-0.0::FLOAT, 0.0::FLOAT)::VARCHAR, signbit(least(-0.0::FLOAT, -0.0::FLOAT)),"
       " signbit(greatest(-0.0::FLOAT, -0.0::FLOAT)), least(-0.0::DOUBLE, 0.0::DOUBLE)::VARCHAR,"
       " least(0.0::DOUBLE, -0.0::DOUBLE)::VARCHAR, greatest(-0.0::DOUBLE, 0.0::DOUBLE)::VARCHAR,"
       " signbit(least(-0.0::DOUBLE, -0.0::DOUBLE))"),
    _o("least-greatest-zero-columns", "doubles",
       "SELECT signbit(least(f, g)), signbit(greatest(f, g)), signbit(least(n, m)),"
       " signbit(least(d, e)), signbit(greatest(d, e)), signbit(least(f, f)) FROM t",
       "CREATE TABLE t AS SELECT -0.0::FLOAT f, -0.0::FLOAT g, -'nan'::FLOAT n, -'nan'::FLOAT m,"
       " -0.0::DOUBLE d, -0.0::DOUBLE e"),
    _o("least-greatest-nan-sign", "doubles",
       "SELECT signbit(-'nan'::FLOAT), signbit(least(-'nan'::FLOAT, -'nan'::FLOAT)),"
       " signbit(greatest(-'nan'::FLOAT, 1::FLOAT)), signbit(-'nan'::DOUBLE),"
       " signbit(least(-'nan'::DOUBLE, -'nan'::DOUBLE)),"
       " signbit(greatest(-'nan'::DOUBLE, 1::DOUBLE))"),
    _o("zero-sign-arith", "doubles",
       "SELECT signbit(-0.0::FLOAT + -0.0::FLOAT), signbit(-0.0::FLOAT + 0.0::FLOAT),"
       " signbit(0.0::FLOAT - 0.0::FLOAT), signbit(-1::FLOAT * 0::FLOAT),"
       " signbit(-0.0::FLOAT / 1::FLOAT), signbit(-0.0::DOUBLE + -0.0::DOUBLE),"
       " signbit(-0.0::DOUBLE + 0.0::DOUBLE), signbit(0.0::DOUBLE - 0.0::DOUBLE),"
       " signbit(-1::DOUBLE * 0::DOUBLE), signbit(1::DOUBLE - 1::DOUBLE)"),
    _o("zero-sign-arith-columns", "doubles",
       "SELECT signbit(d + d), signbit(f + f), signbit(d * 1), signbit(f * 1), signbit(d - d),"
       " signbit(-d), signbit(-f) FROM t",
       "CREATE TABLE t AS SELECT -0.0::DOUBLE d, -0.0::FLOAT f"),
    _o("zero-sign-mod", "doubles",
       "SELECT signbit(-4::FLOAT % 2::FLOAT), signbit(4::FLOAT % -2::FLOAT),"
       " signbit(-0.0::FLOAT % 1::FLOAT), signbit(-4::DOUBLE % 2::DOUBLE),"
       " signbit(4::DOUBLE % -2::DOUBLE), signbit(-0.0::DOUBLE % 1::DOUBLE)"),
    # A NaN an operation creates is negative on x86-64 and positive on arm64
    # (duckdb-exec-platform): `nan_text` prints either as `nan`.
    _o("float-div-nonfinite", "doubles",
       "SELECT typeof('inf'::FLOAT / 'inf'::FLOAT), nan_text('inf'::FLOAT / 'inf'::FLOAT),"
       " nan_text(0::FLOAT * 'inf'::FLOAT), nan_text('inf'::FLOAT - 'inf'::FLOAT),"
       " nan_text(1::FLOAT / 0::FLOAT), nan_text(0::FLOAT / 0::FLOAT),"
       " nan_text(-1::FLOAT / 0::FLOAT)", *_NAN_TEXT),
    _o("float-mod", "doubles",
       "SELECT typeof(-7::FLOAT % 3::FLOAT), nan_text(-7::FLOAT % 3::FLOAT),"
       " nan_text(7::FLOAT % -3::FLOAT), nan_text(-7.5::FLOAT % 2::FLOAT),"
       " nan_text(1::FLOAT % 0::FLOAT), nan_text('inf'::FLOAT % 1::FLOAT)", *_NAN_TEXT),
    # Narrow integers.
    _o("int-mod-narrow", "integers",
       "SELECT -7::TINYINT % 3::TINYINT, 7::TINYINT % -3::TINYINT,"
       " typeof(-7::TINYINT % 3::TINYINT), (-128)::TINYINT % 1::TINYINT,"
       " -7::SMALLINT % 3::SMALLINT, 7::SMALLINT % -3::SMALLINT,"
       " typeof(-7::SMALLINT % 3::SMALLINT), (-32768)::SMALLINT % 1::SMALLINT"),
    _o("int-mod-min-i8", "integers", "SELECT a % b FROM t",
       "CREATE TABLE t AS SELECT (-128)::TINYINT a, -1::TINYINT b"),
    _o("int-mod-min-i16", "integers", "SELECT a % b FROM t",
       "CREATE TABLE t AS SELECT (-32768)::SMALLINT a, -1::SMALLINT b"),
    _o("int-mod-min-i32", "integers", "SELECT a % b FROM t",
       "CREATE TABLE t AS SELECT (-2147483648)::INTEGER a, -1::INTEGER b"),
    _o("int-mod-min-i64", "integers", "SELECT a % b FROM t",
       "CREATE TABLE t AS SELECT (-9223372036854775808)::BIGINT a, -1::BIGINT b"),
    _o("int-pow-narrow", "integers",
       "SELECT typeof(2::TINYINT ** 3::TINYINT), 2::TINYINT ** 7::TINYINT,"
       " 2::TINYINT ** -1::TINYINT, 0::TINYINT ** -1::TINYINT, typeof(2::SMALLINT ** 3::SMALLINT),"
       " 2::SMALLINT ** 15::SMALLINT, 2::SMALLINT ** -1::SMALLINT, 0::SMALLINT ** -1::SMALLINT"),
    # Aggregates.
    _o("sum-narrow-int", "aggregates",
       "SELECT typeof(sum(a)), sum(a), typeof(sum(b)), sum(b), typeof(avg(a)), avg(a),"
       " typeof(avg(b)), avg(b) FROM t",
       "CREATE TABLE t AS SELECT * FROM (VALUES (127::TINYINT, 32767::SMALLINT),"
       " (126::TINYINT, 32766::SMALLINT)) v(a, b)"),
    _o("avg-bigint-large", "aggregates",
       "SELECT avg(x)::VARCHAR FROM (VALUES (9223372036854775807), (9223372036854775806),"
       " (9223372036854775805)) t(x) UNION ALL SELECT avg(x)::VARCHAR FROM"
       " (VALUES (9007199254740993), (9007199254740994)) t(x)"),
    _o("sum-float-accumulates-double", "aggregates",
       "SELECT typeof(sum(x)), sum(x)::VARCHAR FROM (VALUES (1e8::FLOAT), (1::FLOAT),"
       " (-1e8::FLOAT)) t(x)"),
    _o("sum-double-rounding", "aggregates",
       "SELECT sum(x)::VARCHAR, fsum(x)::VARCHAR FROM (VALUES (1e16::DOUBLE), (1::DOUBLE),"
       " (1::DOUBLE)) t(x)"),
    _o("sum-infinities", "aggregates",
       "SELECT nan_text(sum(d)), nan_text(sum(f)), typeof(sum(f)) FROM (VALUES ('inf'::DOUBLE,"
       " 'inf'::FLOAT), ('-inf'::DOUBLE, '-inf'::FLOAT)) t(d, f)", *_NAN_TEXT),
    # `sum`, `avg`, `fsum` and `favg` over ±inf: ungrouped, grouped and over a
    # framed window, whose frames 2-3 and 5-6 hold one infinity after a frame
    # with the other (#341).
    _o("sum-avg-infinities", "aggregates",
       "SELECT 'all' AS k, nan_text(sum(x)), nan_text(avg(x)), nan_text(fsum(x)),"
       " nan_text(favg(x)) FROM t UNION ALL SELECT g, nan_text(sum(x)), nan_text(avg(x)),"
       " nan_text(fsum(x)), nan_text(favg(x)) FROM t GROUP BY g UNION ALL SELECT 'w' || i,"
       " nan_text(sum(x) OVER w), nan_text(avg(x) OVER w), nan_text(fsum(x) OVER w),"
       " nan_text(favg(x) OVER w) FROM t"
       " WINDOW w AS (ORDER BY i ROWS BETWEEN 1 PRECEDING AND CURRENT ROW) ORDER BY k",
       *_NAN_TEXT,
       "CREATE TABLE t AS SELECT * FROM (VALUES (1, 'both', 'inf'::DOUBLE),"
       " (2, 'both', '-inf'::DOUBLE), (3, 'both', 1.0), (4, 'pos', 'inf'::DOUBLE),"
       " (5, 'pos', 1.0), (6, 'neg', '-inf'::DOUBLE), (7, 'neg', 1.0), (8, 'finite', 1.0),"
       " (9, 'finite', 2.0)) v(i, g, x)"),
    _o("sum-empty", "aggregates",
       "SELECT sum(d), avg(d), sum(f), avg(f), sum(i), avg(i), (SELECT sum(d) FROM"
       " (VALUES (NULL::DOUBLE)) n(d)) FROM (SELECT 1.0::DOUBLE AS d, 1.0::FLOAT AS f,"
       " 1::TINYINT AS i WHERE false) t"),
    _o("var-bigint-decimal", "aggregates",
       "SELECT typeof(var_samp(x)), round(var_samp(x), 12), round(var_pop(x), 12),"
       " typeof(var_samp(y)), round(var_samp(y), 12), round(stddev_samp(y), 12)"
       " FROM (VALUES (1::BIGINT, 1.5::DECIMAL(4,1)), (2, 2.5), (4, 4.0)) t(x, y)"),
    _o("stat-decimal-degenerate", "aggregates",
       "SELECT 'one', var_samp(y), var_pop(y), stddev_samp(y), corr(y, y), covar_samp(y, y),"
       " covar_pop(y, y) FROM (VALUES (1.5::DECIMAL(4,1))) t(y) UNION ALL"
       " SELECT 'constant', var_samp(x), var_pop(x), stddev_samp(x), corr(x, y), covar_samp(x, y),"
       " covar_pop(x, y) FROM (VALUES (1.5::DECIMAL(4,1), 2.0::DECIMAL(4,1)), (1.5, 3.0)) t(x, y)"
       " UNION ALL SELECT 'empty', var_samp(x), var_pop(x), stddev_samp(x), corr(x, x),"
       " covar_samp(x, x), covar_pop(x, x) FROM (SELECT 1.5::DECIMAL(4,1) x WHERE false)"
       " ORDER BY 1"),
    _o("stat-bigint-degenerate", "aggregates",
       "SELECT 'one', var_samp(x), var_pop(x), stddev_samp(x), corr(x, x), covar_samp(x, x),"
       " covar_pop(x, x) FROM (VALUES (7::BIGINT)) t(x) UNION ALL"
       " SELECT 'constant', var_samp(x), var_pop(x), stddev_samp(x), corr(x, y), covar_samp(x, y),"
       " covar_pop(x, y) FROM (VALUES (7::BIGINT, 1::BIGINT), (7, 2)) t(x, y)"
       " UNION ALL SELECT 'empty', var_samp(x), var_pop(x), stddev_samp(x), corr(x, x),"
       " covar_samp(x, x), covar_pop(x, x) FROM (SELECT 7::BIGINT x WHERE false) ORDER BY 1"),
    _o("minmax-zero-last-negative", "aggregates",
       "SELECT signbit(min(d)), signbit(max(d)), signbit(min(f)), signbit(max(f)) FROM"
       " (VALUES (0.0::DOUBLE, 0.0::FLOAT), (-0.0::DOUBLE, -0.0::FLOAT)) t(d, f)"),
    _o("minmax-zero-last-positive", "aggregates",
       "SELECT signbit(min(d)), signbit(max(d)), signbit(min(f)), signbit(max(f)) FROM"
       " (VALUES (-0.0::DOUBLE, -0.0::FLOAT), (0.0::DOUBLE, 0.0::FLOAT)) t(d, f)"),
    _o("quantile-nan", "aggregates",
       "SELECT median(x)::VARCHAR, quantile_cont(x, 0.5)::VARCHAR,"
       " quantile_cont(x, 0.75)::VARCHAR, quantile_disc(x, 0.75)::VARCHAR,"
       " quantile_cont(x, 1.0)::VARCHAR FROM (VALUES (1.0::DOUBLE), (2.0::DOUBLE),"
       " ('nan'::DOUBLE), (3.0::DOUBLE)) t(x) UNION ALL SELECT median(x)::VARCHAR,"
       " quantile_cont(x, 0.5)::VARCHAR, NULL, NULL, NULL FROM (VALUES (1.0::DOUBLE),"
       " ('nan'::DOUBLE)) t(x)"),
    # Collations.
    _o("default-collation-nocase", "strings",
       "SELECT v = 'hello', v LIKE 'h%', v ILIKE 'h%', contains(v, 'ELL'), starts_with(v, 'he'),"
       " strpos(v, 'EL'), ends_with(v, 'LO'), prefix(v, 'he'), replace(v, 'h', 'J') FROM s",
       "SET default_collation = 'nocase'", "CREATE TABLE s AS SELECT 'Hello' v"),
    _o("default-collation-nocase-literals", "strings",
       "SELECT 'Hello' = 'hello', 'Hello' LIKE 'h%', contains('Hello', 'ELL'),"
       " starts_with('Hello', 'he'), strpos('Hello', 'EL')",
       "SET default_collation = 'nocase'"),
    _o("default-collation-nocase-sort", "strings",
       "SELECT list(w ORDER BY w), count(DISTINCT w) FROM (VALUES ('b'), ('A'), ('a'), ('B')) t(w)",
       "SET default_collation = 'nocase'"),
    _o("default-collation-binary", "strings",
       "SELECT v = 'hello', v LIKE 'h%', contains(v, 'ELL'), starts_with(v, 'he'), strpos(v, 'EL')"
       " FROM s", "CREATE TABLE s AS SELECT 'Hello' v"),
]  # fmt: skip


def _render(v: Any) -> str:
    """A value as text that does not depend on the host: NULL, true and
    false, decimals as written, doubles as Python prints them, and lists and
    structs element by element."""
    if v is None:
        return "NULL"
    if isinstance(v, bool):
        return str(v).lower()
    if isinstance(v, list | tuple):
        return "[" + ", ".join(_render(x) for x in v) + "]"
    if isinstance(v, dict):
        return "{" + ", ".join(f"{k}: {_render(x)}" for k, x in v.items()) + "}"
    if isinstance(v, str):
        return repr(v)
    return str(v)


def observe(o: Observation) -> Json:
    """`o`'s rows (`;` between rows), or the error it raises."""
    con = duckdb.connect()
    con.execute("SET TimeZone = 'UTC'")
    try:
        for s in o.setup:
            con.execute(s)
        rows = con.execute(o.sql).fetchall()
        observed = "; ".join(", ".join(_render(v) for v in r) for r in rows)
    except duckdb.Error as e:
        observed = f"error {type(e).__name__}: {str(e).splitlines()[0]}"
    return {"construct": o.construct, "area": o.area, "setup": list(o.setup), "sql": o.sql,
            "observed": observed}  # fmt: skip


def observe_all(
    observations: Sequence[Observation] = OBSERVATIONS, log: Callable[[str], None] = print
) -> list[Json]:
    found = []
    for o in observations:
        r = observe(o)
        log(f"{o.construct}: {r['observed']}")
        found.append(r)
    return found


def main(argv: Sequence[str] | None = None) -> None:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("--write", action="store_true", help="write probes.json")
    parser.add_argument(
        "--observations",
        action="store_true",
        help="rerun the observations only, keeping the recorded probes (no Lean needed)",
    )
    args = parser.parse_args(argv)
    out = slt.REPLAY_DIR / "probes.json"
    if args.observations:
        recorded = json.loads(out.read_text())["probes"]
        found = [r for r in recorded if "sql" not in r] + observe_all()
    else:
        found = probe_all() + observe_all()
    if args.write:
        head = {"duckdb": duckdb.__version__, "probes": found}
        out.write_text(json.dumps(head, indent=1) + "\n")
        print(f"-> {out}")


if __name__ == "__main__":
    main()
