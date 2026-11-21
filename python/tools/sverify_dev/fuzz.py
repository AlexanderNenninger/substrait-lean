"""Random queries with Lean's semantics as the oracle (SQLancer-style).

Maintainer tooling (`sverify_dev`): not in the wheel, and not part of sverify's
API.

A Hypothesis strategy draws well-typed SQL queries over two small tables (`t`
with integer, double, string, boolean and timestamp columns, `u` with an
integer and a string) and random rows for them, NULLs included. Each query
is DuckDB's SQL and goes through the real producer (sverify's lift,
`sverify.sql_lift`), and `check` compares:

1. `rows`: if the checker accepts the plan, Lean's rows (`Rel.eval` on the
   plan with the tables inlined) equal DuckDB's on the SQL as bags, and those of the
   engines (`ENGINES`) on the plan Lean writes back out; doubles
   approximately (Lean prints six decimals). An `ORDER BY` over every output
   column also fixes the order.
2. `runtime`: if `verify` reports no possible runtime error, DuckDB does
   not raise.
3. `ensures`: a postcondition `verify` proves (from a precondition the
   generated input meets) holds on every output row of DuckDB.
4. `tlp`: ternary logic partitioning against Lean: the rows of a query are
   those where a predicate is TRUE, FALSE and NULL, together.

A query outside the model (the producer or the checker refuses it) is not a
finding. `python -m sverify_dev.fuzz` runs a budget of random queries and prints
each distinct, shrunk disagreement; `tests/test_fuzz.py` runs a small budget.

This module needs Hypothesis, which only the `dev` group installs.
"""

from __future__ import annotations

import argparse
import datetime as dt
import json
import math
import os
import random
import time
from collections.abc import Callable, Mapping, Sequence
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any

import ibis
import pyarrow as pa
from hypothesis import HealthCheck, find, settings
from hypothesis import strategies as st
from hypothesis.errors import NoSuchExample

from sverify._checker import CheckerMemoryError
from sverify._lean_eval import LeanRaised
from sverify.contracts import verify
from sverify.engine import (
    ENGINES,
    connect,
    plain_schema,
    run_checker,
    run_plan,
    substrait_json,
    written_plan,
)
from sverify.sql import core as sql_core
from sverify.testing import EPOCH, duckdb_sql, inline_tables, lean_values
from sverify_dev.checked import checked
from sverify_polars import engine as polars_engine

INT, DOUBLE, STRING, BOOL, TS = "int", "double", "string", "bool", "ts"
IBIS_TYPES = {INT: "int64", DOUBLE: "float64", STRING: "string", BOOL: "boolean", TS: "timestamp"}

TABLES: dict[str, dict[str, str]] = {
    "t": {"i": INT, "j": INT, "d": DOUBLE, "s": STRING, "b": BOOL, "ts": TS},
    "u": {"k": INT, "v": STRING},
}
SCHEMAS = {
    name: ibis.schema({c: IBIS_TYPES[ty] for c, ty in cols.items()})
    for name, cols in TABLES.items()
}

Scope = dict[str, str]
"""Column name to type, for the relation an expression is over."""


# --- data ------------------------------------------------------------------

# Small integers only: past 64 bits the model's unbounded integers and the
# engines' wrap-around differ, a known gap (#72, #19).
ints = st.one_of(st.none(), st.integers(-3, 3))
doubles = st.one_of(
    st.none(), st.sampled_from([0.0, -0.5, 1.5, 2.0, -3.25, math.inf, -math.inf, math.nan])
)
strings = st.one_of(st.none(), st.sampled_from(["", "a", "b", "ab", "B", "a b"]))
bools = st.one_of(st.none(), st.booleans())
timestamps = st.one_of(
    st.none(), st.sampled_from([dt.datetime(2024, 1, 1), dt.datetime(2024, 1, 1, 12), EPOCH])
)
VALUES = {INT: ints, DOUBLE: doubles, STRING: strings, BOOL: bools, TS: timestamps}


def rows_of(name: str) -> st.SearchStrategy[list[tuple]]:
    return st.lists(st.tuples(*(VALUES[ty] for ty in TABLES[name].values())), max_size=6)


# --- expressions -------------------------------------------------------------

LITERALS: dict[str, st.SearchStrategy[str]] = {
    INT: st.sampled_from(["0", "1", "2", "-1", "3", "CAST(NULL AS BIGINT)"]),
    # DuckDB reads `1.5` as a DECIMAL.
    DOUBLE: st.sampled_from(
        ["0.0::DOUBLE", "1.5::DOUBLE", "-2.0::DOUBLE", "0.25::DOUBLE", "CAST(NULL AS DOUBLE)"]
    ),
    STRING: st.sampled_from(["''", "'a'", "'b'", "'ab'", "CAST(NULL AS VARCHAR)"]),
    BOOL: st.sampled_from(["TRUE", "FALSE", "CAST(NULL AS BOOLEAN)"]),
    TS: st.sampled_from(["TIMESTAMP '2024-01-01 00:00:00'", "TIMESTAMP '2024-01-01 06:00:00'"]),
}


@st.composite
def expr(draw: st.DrawFn, scope: Scope, ty: str, depth: int = 2) -> str:
    """A SQL expression of type `ty` over the columns in `scope`."""
    cols = [c for c, t in scope.items() if t == ty]
    leaves = [st.sampled_from(cols)] if cols else []
    leaves.append(LITERALS[ty])
    if depth <= 0 or draw(st.integers(0, 3)) == 0:
        return draw(st.one_of(*leaves))

    def sub(t: str = ty) -> str:
        return draw(expr(scope, t, depth - 1))

    kind = draw(st.sampled_from(_KINDS[ty]))
    match kind:
        case "arith":
            # DuckDB's `/` divides as doubles; `//` divides integers.
            op = draw(st.sampled_from(["+", "-", "*", "/", "%"]))
            op = "//" if op == "/" and ty == INT else op
            return f"({sub()} {op} {sub()})"
        case "neg":
            return f"(- {sub()})"
        case "abs":
            return f"abs({sub()})"
        case "case":
            return f"CASE WHEN {sub(BOOL)} THEN {sub()} ELSE {sub()} END"
        case "coalesce":
            return f"COALESCE({sub()}, {sub()})"
        case "nullif":
            return f"NULLIF({sub()}, {sub()})"
        case "length":
            return f"CAST(length({sub(STRING)}) AS BIGINT)"
        case "cast_int":
            return f"CAST({sub(INT)} AS DOUBLE)"
        case "unary_str":
            fn = draw(st.sampled_from(["upper", "lower", "trim", "ltrim", "rtrim"]))
            return f"{fn}({sub()})"
        case "concat":
            return f"({sub()} || {sub()})"
        case "substr":
            return f"substr({sub()}, {draw(st.integers(0, 3))}, {draw(st.integers(0, 3))})"
        case "cmp":
            t = draw(st.sampled_from([INT, INT, DOUBLE, STRING, BOOL, TS]))
            ops = ["=", "<>", "IS DISTINCT FROM"]
            # String ordering is not fuzzed yet.
            ops += [] if t == STRING else ["<", "<=", ">", ">="]
            op = draw(st.sampled_from(ops))
            return f"({sub(t)} {op} {sub(t)})"
        case "logic":
            return f"({sub()} {draw(st.sampled_from(['AND', 'OR']))} {sub()})"
        case "not":
            return f"(NOT {sub()})"
        case "isnull":
            t = draw(st.sampled_from([INT, DOUBLE, STRING, BOOL, TS]))
            return f"({sub(t)} IS {draw(st.sampled_from(['', 'NOT ']))}NULL)"
        case "in":
            t = draw(st.sampled_from([INT, STRING]))
            items = draw(st.lists(LITERALS[t], min_size=1, max_size=3))
            neg = draw(st.sampled_from(["", "NOT "]))
            return f"({sub(t)} {neg}IN ({', '.join(items)}))"
        case "between":
            return f"({sub(INT)} BETWEEN {sub(INT)} AND {sub(INT)})"
        case "like":
            pattern = draw(st.sampled_from(["'a%'", "'%b'", "'_'", "'%'", "'a_b'"]))
            return f"({sub(STRING)} LIKE {pattern})"
    raise AssertionError(kind)


_KINDS = {
    INT: ["arith", "neg", "abs", "case", "coalesce", "nullif", "length"],
    DOUBLE: ["arith", "neg", "abs", "case", "coalesce", "cast_int"],
    STRING: ["unary_str", "concat", "substr", "case", "coalesce"],
    BOOL: ["cmp", "cmp", "logic", "not", "isnull", "in", "between", "like", "case"],
    TS: ["case", "coalesce"],
}


# --- queries -------------------------------------------------------------------


@dataclass(frozen=True)
class Query:
    sql: str
    out: Scope
    """Output column name to type."""
    ordered: bool = False
    """`ORDER BY` every output column: the order is fixed, not just the bag."""
    base: str | None = None
    """For `tlp`: the query as `SELECT * FROM (<from>) AS q`, without WHERE,
    whose rows the predicate `tlp_pred` partitions."""
    tlp_pred: str | None = None


@st.composite
def source(draw: st.DrawFn) -> tuple[str, Scope]:
    """A FROM item, aliased `q`, and its columns."""
    kind = draw(st.sampled_from(["t", "t", "u", "join", "setop"]))
    if kind in ("t", "u"):
        return f"{kind} AS q", dict(TABLES[kind])
    if kind == "join":
        how = draw(st.sampled_from(["JOIN", "LEFT JOIN", "RIGHT JOIN", "FULL JOIN"]))
        on = "t.i = u.k"
        if draw(st.booleans()):
            on += f" AND {draw(expr({'t.j': INT, 't.s': STRING, 'u.v': STRING}, BOOL, 1))}"
        cols = "t.i, t.j, t.s, u.k, u.v"
        scope = {"i": INT, "j": INT, "s": STRING, "k": INT, "v": STRING}
        return f"(SELECT {cols} FROM t {how} u ON {on}) AS q", scope
    op = draw(st.sampled_from(["UNION ALL", "UNION", "INTERSECT", "EXCEPT"]))
    left = f"SELECT i AS x, s AS y FROM t WHERE {draw(expr(TABLES['t'], BOOL, 1))}"
    right = f"SELECT k AS x, v AS y FROM u WHERE {draw(expr(TABLES['u'], BOOL, 1))}"
    return f"({left} {op} {right}) AS q", {"x": INT, "y": STRING}


@st.composite
def queries(draw: st.DrawFn) -> Query:
    """A random query over `t` and `u`."""
    src, scope = draw(source())
    where = draw(st.one_of(st.none(), expr(scope, BOOL)))
    where_sql = f" WHERE {where}" if where else ""
    if draw(st.integers(0, 3)) == 0:
        return _aggregate(draw, src, scope, where_sql)
    n = draw(st.integers(1, 3))
    types = [draw(st.sampled_from(sorted(set(scope.values()) | {INT, BOOL}))) for _ in range(n)]
    items = [draw(expr(scope, ty)) for ty in types]
    out = {f"c{i}": ty for i, ty in enumerate(types)}
    select = ", ".join(f"{e} AS c{i}" for i, e in enumerate(items))
    distinct = "DISTINCT " if draw(st.integers(0, 4)) == 0 else ""
    sql = f"SELECT {distinct}{select} FROM {src}{where_sql}"
    if draw(st.integers(0, 3)) == 0:
        dirs = [
            draw(st.sampled_from(["", " DESC", " NULLS FIRST", " DESC NULLS LAST"])) for _ in out
        ]
        sql += " ORDER BY " + ", ".join(f"c{i}{d}" for i, d in enumerate(dirs))
        if draw(st.booleans()):
            sql += f" LIMIT {draw(st.integers(0, 4))}"
        return Query(sql, out, ordered=True)
    base = f"SELECT * FROM {src}"
    return Query(sql, out, base=base, tlp_pred=draw(expr(scope, BOOL)))


def _aggregate(draw: st.DrawFn, src: str, scope: Scope, where_sql: str) -> Query:
    keys = draw(st.lists(st.sampled_from(sorted(scope)), max_size=2, unique=True))
    aggs: list[tuple[str, str]] = []
    for _ in range(draw(st.integers(1, 3))):
        col = draw(st.sampled_from(sorted(scope)))
        ty = scope[col]
        fns = ["COUNT", "MIN", "MAX"] + (["SUM"] if ty in (INT, DOUBLE) else [])
        fns += ["AVG"] if ty == INT else []
        fn = draw(st.sampled_from(fns + ["COUNT(*)"]))
        if fn == "COUNT(*)":
            aggs.append(("COUNT(*)", INT))
        else:
            out_ty = INT if fn == "COUNT" else DOUBLE if fn == "AVG" else ty
            aggs.append((f"{fn}({col})", out_ty))
    items = [(k, scope[k]) for k in keys] + aggs
    out = {f"c{i}": ty for i, (_, ty) in enumerate(items)}
    select = ", ".join(f"{e} AS c{i}" for i, (e, _) in enumerate(items))
    group = f" GROUP BY {', '.join(keys)}" if keys else ""
    having = ""
    if keys and draw(st.integers(0, 3)) == 0:
        having = f" HAVING {aggs[0][0]} IS NOT NULL"
    return Query(f"SELECT {select} FROM {src}{where_sql}{group}{having}", out)


# --- contracts -----------------------------------------------------------------

PRECONDITIONS: dict[str, Callable[[tuple], bool]] = {
    "i IS NOT NULL": lambda r: r[0] is not None,
    "i > 0": lambda r: r[0] is not None and r[0] > 0,
    "i BETWEEN -2 AND 2": lambda r: r[0] is not None and -2 <= r[0] <= 2,
    "s IS NOT NULL": lambda r: r[3] is not None,
    "d >= 0.0": lambda r: r[2] is not None and (r[2] >= 0 or math.isnan(r[2])),
}
"""Preconditions on `t`, as SQL and as a filter on generated rows."""


@st.composite
def postconditions(draw: st.DrawFn, out: Scope) -> str:
    return draw(expr(out, BOOL, 1))


# --- checking ------------------------------------------------------------------


@dataclass
class Finding:
    oracle: str
    """`rows`, `rows:<engine>`, `types:<engine>`, `runtime`, `ensures` or `tlp`."""
    sql: str
    tables: dict[str, list[tuple]]
    detail: str
    extra: dict[str, Any] = field(default_factory=dict)
    case: tuple | None = field(default=None, repr=False, compare=False)
    """The case `search` found it on (a `cases` or `contract_cases` draw), for
    `to_json` and `replay`."""

    def __str__(self) -> str:
        data = "\n".join(f"  {name}: {rows!r}" for name, rows in self.tables.items() if rows)
        extra = "".join(f"\n{k}: {v}" for k, v in self.extra.items())
        return f"[{self.oracle}] {self.sql}\n{data}{extra}\n{self.detail}"

    def signature(self) -> tuple[str, str]:
        return self.oracle, self.sql


class Refused(Exception):
    """The query is outside the model (the lift or the checker refuses it)."""


#: An engine translation refusing a plan on purpose: not a finding.
REFUSALS = (polars_engine.Unsupported, sql_core.Unsupported)

KNOWN: list[tuple[int, Callable[[Finding], bool]]] = [
    # One integer kind in the model: a widening cast of an `int32` is
    # dropped, and an `int32` literal (DuckDB's `0`) comes back as an `int64`
    # from an engine.
    (
        18,
        lambda f: (
            f.oracle.startswith("types:")
            and {"int32", "int64"}
            <= {t for line in f.detail.splitlines()[-2:] for t in ("int32", "int64") if t in line}
            and f.detail.splitlines()[-1].replace("int64", "int32").split(": ", 1)[-1]
            == f.detail.splitlines()[-2].replace("int64", "int32").split(": ", 1)[-1]
        ),
    ),
]
"""Open issues, by the findings they explain."""


def known(f: Finding) -> int | None:
    """The open issue a finding is an instance of, if any."""
    return next((n for n, matches in KNOWN if matches(f)), None)


def _norm(v: object) -> object:
    """A value as Lean prints it: timestamps are microseconds, doubles floats."""
    if isinstance(v, dt.datetime):
        return (v.replace(tzinfo=None) - EPOCH) // dt.timedelta(microseconds=1)
    if isinstance(v, dt.date):
        return (v - EPOCH.date()).days
    return v


def _key(v: object) -> tuple:
    if v is None:
        return (0,)
    if isinstance(v, bool):
        return (1, v)
    if isinstance(v, int | float):
        if isinstance(v, float) and math.isnan(v):
            return (3,)
        return (2, round(float(v), 4))
    return (4, str(v))


def _same(a: object, b: object) -> bool:
    if a is None or b is None:
        return a is b
    if isinstance(a, bool) or isinstance(b, bool):
        return a is b
    if isinstance(a, int | float) and isinstance(b, int | float):
        if isinstance(a, float) and math.isnan(a) or isinstance(b, float) and math.isnan(b):
            return isinstance(a, float) and isinstance(b, float) and math.isnan(a) and math.isnan(b)
        if math.isinf(a) or math.isinf(b):
            return a == b
        # Lean prints doubles with six decimals.
        return math.isclose(a, b, rel_tol=1e-9, abs_tol=1e-6)
    return a == b


def same_rows(got: Sequence[tuple], expected: Sequence[tuple], ordered: bool = False) -> bool:
    """Equal as bags (or as lists if `ordered`), doubles approximately."""
    got = [tuple(map(_norm, r)) for r in got]
    expected = [tuple(map(_norm, r)) for r in expected]
    if len(got) != len(expected):
        return False
    if not ordered:
        got = sorted(got, key=lambda r: tuple(map(_key, r)))
        expected = sorted(expected, key=lambda r: tuple(map(_key, r)))
    return all(
        len(a) == len(b) and all(map(_same, a, b)) for a, b in zip(got, expected, strict=True)
    )


def _arrow_rows(table: Any) -> list[tuple]:
    # Column-wise: a join may repeat a column name.
    return list(zip(*(c.to_pylist() for c in table.columns), strict=True))


def lean_plan(plan: str) -> str:
    """The plan as `substrait-check` prints it (`Rel.render`)."""
    out = run_checker((), plan)[1]
    return out.split("\ntables:")[0].split("\narity:")[0]


def _types(table: Any) -> list[str]:
    """Column types, with Substrait's one string type and timestamps of any
    unit (an engine may give a timestamp literal nanoseconds, plans have
    microseconds); an all-NULL column of Arrow's `null` type matches any."""

    def name(t: pa.DataType) -> str:
        if pa.types.is_null(t):
            return "?"
        if pa.types.is_timestamp(t):
            return f"timestamp[{t.tz}]" if t.tz else "timestamp"
        return str(t)

    return [name(f.type) for f in plain_schema(table.schema)]


class Session:
    """A connection holding the generated tables."""

    def __init__(self, tables: Mapping[str, list[tuple]]):
        self.tables = {name: list(tables.get(name, [])) for name in TABLES}
        self.con = connect()
        for name, rows in self.tables.items():
            self.con.create(name, SCHEMAS[name], rows)

    def plan(self, sql: str) -> str:
        try:
            plan = substrait_json(self.con, sql, semantics="duckdb")
        except Exception as e:  # noqa: BLE001 - the producer refusing is not a finding
            raise Refused(f"producer: {e}") from e
        code, out, err = run_checker((), plan)
        if code != 0 or "well-formed: yes" not in out:
            raise Refused(f"checker: {(err or out).strip()[-200:]}")
        return plan

    def lean(self, plan: str) -> list[tuple]:
        inlined = inline_tables(json.loads(plan), self.tables)
        return lean_values(json.dumps(inlined))

    def duckdb(self, sql: str) -> list[tuple]:
        return _arrow_rows(duckdb_sql(self.con, sql))

    def written_with_data(self, plan: str) -> str:
        """The plan as written for the engines, with the tables inlined."""
        return json.dumps(inline_tables(json.loads(written_plan(plan)), self.tables))


def listed_issues(sql: str) -> list[str]:
    """What the report lists for the query: its errors and its assumptions."""
    report = verify(sql, tables=SCHEMAS)
    return [str(i) for i in report.issues + report.assumed]


def reports_runtime_error(s: Session, sql: str) -> bool:
    """Whether `verify` reports the possible runtime error on this input: it
    names one, assumes one (a `SUM` that may leave 64 bits), or the input
    breaks a precondition it needs (`x IS NULL OR x <> 0`), which the proof
    rests on (#638, #2101)."""
    report = verify(sql, tables=SCHEMAS)
    if report.errors or report.assumed:
        return True
    return any(
        duckdb_sql(s.con, f"SELECT 1 FROM {n.table} WHERE ({n.sql}) IS FALSE LIMIT 1").num_rows
        for n in report.needs
    )


def check(
    query: Query,
    tables: Mapping[str, list[tuple]],
    oracles: Sequence[str] = ("rows", "engines", "runtime", "tlp"),
) -> list[Finding]:
    """Disagreements between Lean and the engines on one query and input.

    Raises `Refused` when the query is outside the model."""
    s = Session(tables)
    plan = s.plan(query.sql)
    findings: list[Finding] = []

    def found(oracle: str, detail: str, **extra: Any) -> None:
        extra["Lean's plan"] = lean_plan(plan)
        findings.append(Finding(oracle, query.sql, s.tables, detail, extra))

    try:
        lean = s.lean(plan)
    except LeanRaised as e:
        # The reference raises (a zero divisor, an overflow): `verify` must
        # report the possible runtime error, as for an engine that raises.
        if not reports_runtime_error(s, query.sql):
            found("runtime", f"Lean raises {e}; verify reports no runtime error")
        return findings
    try:
        df_table = duckdb_sql(s.con, query.sql)
        df, df_error = _arrow_rows(df_table), None
    except Exception as e:  # noqa: BLE001 - recorded below
        df_table, df, df_error = None, None, e

    if "runtime" in oracles and df_error is not None and not reports_runtime_error(s, query.sql):
        found("runtime", f"DuckDB raises {df_error!r}; verify reports no runtime error")
    if "rows" in oracles and df is not None and not same_rows(lean, df, query.ordered):
        found("rows", f"Lean:   {lean!r}\nDuckDB: {df!r}")
    if "engines" in oracles and df_error is None:
        written = written_plan(plan)
        for engine in ENGINES:
            try:
                out = run_plan(s.con, written, engine)
            except REFUSALS:
                continue
            except Exception as e:  # noqa: BLE001 - recorded
                # The written plan's own check of a reported assumption: the
                # report lists it and Lean finds it on this data (#2162).
                if "sverify:" in str(e) and checked(
                    str(e), listed_issues(query.sql), s.written_with_data(plan)
                ):
                    continue
                found(f"rows:{engine}", f"{engine} raises {e!r} (Lean: {lean!r})")
                continue
            got = _arrow_rows(out)
            if not same_rows(lean, got, query.ordered):
                found(f"rows:{engine}", f"Lean: {lean!r}\n{engine}: {got!r}")
            elif (types := _types(out)) != (expected := _types(df_table)):
                found(f"types:{engine}", f"DuckDB's SQL: {expected}\n{engine}: {types}")
    if "tlp" in oracles and query.base and query.tlp_pred:
        p = query.tlp_pred
        parts = [
            f"{query.base} WHERE {p}",
            f"{query.base} WHERE NOT ({p})",
            f"{query.base} WHERE ({p}) IS NULL",
        ]
        try:
            whole = s.lean(s.plan(query.base))
            split = [r for part in parts for r in s.lean(s.plan(part))]
        except (Refused, LeanRaised):
            # A predicate that raises (a zero divisor) partitions nothing;
            # the runtime oracle covers the raise itself.
            pass
        else:
            if not same_rows(whole, split):
                found("tlp", f"whole: {whole!r}\nTRUE+FALSE+NULL parts: {split!r}", predicate=p)
    return findings


def check_contract(
    query: Query, tables: Mapping[str, list[tuple]], pre: str | None, post: str
) -> list[Finding]:
    """If `verify` proves `post` from `pre` (on `t`), it holds on DuckDB's
    output for `tables`, whose `t` must meet `pre`."""
    s = Session(tables)
    s.plan(query.sql)
    requires = {"t": [pre]} if pre else {}
    try:
        report = verify(query.sql, requires=requires, ensures=[post], tables=SCHEMAS)
    except Exception as e:  # noqa: BLE001 - e.g. the producer refusing the condition query
        raise Refused(f"verify: {e}") from e
    if not report.ensures[0].proved:
        return []
    check_sql = f"SELECT * FROM ({query.sql}) AS r WHERE NOT COALESCE(({post}), FALSE)"
    try:
        bad = s.duckdb(check_sql)
    except Exception:  # noqa: BLE001 - a runtime error is the `runtime` oracle's business
        return []
    if not bad:
        return []
    return [
        Finding(
            "ensures",
            query.sql,
            s.tables,
            f"proved {post!r} from {pre!r}, but DuckDB gives violating rows {bad!r}",
            {"requires": pre, "ensures": post},
        )
    ]


# --- search ----------------------------------------------------------------------

cases = st.tuples(queries(), st.fixed_dictionaries({name: rows_of(name) for name in TABLES}))


@st.composite
def contract_cases(draw: st.DrawFn) -> tuple[Query, dict[str, list[tuple]], str | None, str]:
    q = draw(queries())
    pre = draw(st.one_of(st.none(), st.sampled_from(sorted(PRECONDITIONS))))
    tables = draw(st.fixed_dictionaries({name: rows_of(name) for name in TABLES}))
    if pre:
        tables["t"] = [r for r in tables["t"] if PRECONDITIONS[pre](r)]
    return q, tables, pre, draw(postconditions(q.out))


def note(case: tuple) -> None:
    """Write the case about to be checked to `$SVERIFY_FUZZ_PROGRESS`, if set,
    so a batch the nightly run's watchdog stops (`sverify_dev.fuzz_nightly`)
    still names the case it was on. Written whole, then renamed into place."""
    if path := os.environ.get("SVERIFY_FUZZ_PROGRESS"):
        tmp = f"{path}.tmp"
        Path(tmp).write_text(json.dumps(case_json(case)))
        os.replace(tmp, path)


def checker_memory(case: tuple, e: CheckerMemoryError) -> Finding:
    """The checker went over its memory cap on a case (#1074): a finding of
    its own, with the plan the producer writes for the query."""
    query, tables = case[0], case[1]
    try:
        plan: str = substrait_json(Session(tables).con, query.sql, semantics="duckdb")
    except Exception as err:  # noqa: BLE001 - the plan is extra detail
        plan = f"(not produced: {err!r})"
    return Finding("checker", query.sql, dict(tables), f"memory cap: {e}", {"plan": plan}, case)


def _findings(case: tuple) -> list[Finding]:
    """The findings on a case that no open issue explains."""
    note(case)
    try:
        found = check_contract(*case) if len(case) == 4 else check(*case)
    except Refused:
        return []
    except CheckerMemoryError as e:
        return [checker_memory(case, e)]
    except Exception as e:  # noqa: BLE001 - a harness error is a finding; it must not end the run
        query, tables = case[0], case[1]
        return [Finding("harness", query.sql, dict(tables), f"{type(e).__name__}: {e}", {}, case)]
    return [f for f in found if known(f) is None]


def search(budget: float, seed: int = 0, contracts: bool = True) -> list[Finding]:
    """Distinct, shrunk findings within `budget` seconds."""
    rng = random.Random(seed)
    deadline = time.monotonic() + budget
    found: dict[tuple[str, str], Finding] = {}
    while time.monotonic() < deadline:
        strategy = contract_cases() if contracts and rng.random() < 0.3 else cases
        cfg = settings(
            max_examples=200,
            database=None,
            deadline=None,
            suppress_health_check=list(HealthCheck),
        )

        def new(case: tuple) -> bool:
            # A checker over its memory cap is kept as found, unshrunk:
            # shrinking would run the runaway again and again.
            fs = _findings(case)
            for f in fs:
                if f.oracle == "checker" and f.signature() not in found:
                    found[f.signature()] = f
                    print(f, end="\n\n", flush=True)
            return any(f.signature() not in found for f in fs if f.oracle != "checker")

        try:
            case = find(
                strategy,
                new,
                settings=cfg,
                random=random.Random(rng.random()),
            )
        except NoSuchExample:
            continue
        for f in _findings(case):
            f.case = case
            found.setdefault(f.signature(), f)
            print(f, end="\n\n", flush=True)
    return list(found.values())


# --- records and replay ------------------------------------------------------------


def _encode(v: object) -> object:
    """A table value as JSON: timestamps, dates and non-finite doubles tagged."""
    if isinstance(v, dt.datetime):
        return {"ts": v.isoformat()}
    if isinstance(v, dt.date):
        return {"date": v.isoformat()}
    if isinstance(v, float) and not math.isfinite(v):
        return {"float": repr(v)}
    return v


def _decode(v: object) -> object:
    if isinstance(v, dict):
        if "ts" in v:
            return dt.datetime.fromisoformat(v["ts"])
        if "date" in v:
            return dt.date.fromisoformat(v["date"])
        return float(v["float"])
    return v


def case_json(case: tuple) -> dict[str, Any]:
    """A case (a `cases` or `contract_cases` draw) as JSON; `case_of` reads it."""
    query, tables, *contract = case
    record: dict[str, Any] = {
        "sql": query.sql,
        "query": {
            "sql": query.sql,
            "out": query.out,
            "ordered": query.ordered,
            "base": query.base,
            "tlp_pred": query.tlp_pred,
        },
        "tables": {k: [[_encode(v) for v in r] for r in rows] for k, rows in tables.items()},
    }
    if contract:
        record["requires"], record["ensures"] = contract
    return record


def case_of(record: Mapping[str, Any]) -> tuple:
    """The case a `case_json` record holds."""
    q = record["query"]
    query = Query(q["sql"], q["out"], q["ordered"], q["base"], q["tlp_pred"])
    tables = {
        k: [tuple(_decode(v) for v in r) for r in rows] for k, rows in record["tables"].items()
    }
    if "ensures" in record:
        return (query, tables, record["requires"], record["ensures"])
    return (query, tables)


def to_json(f: Finding, seed: int) -> dict[str, Any]:
    """A finding with the case it was found on, which `replay` checks again."""
    record: dict[str, Any] = {
        "oracle": f.oracle,
        "sql": f.sql,
        "detail": f.detail,
        "extra": {k: str(v) for k, v in f.extra.items()},
        "seed": seed,
    }
    if f.case is not None:
        record.update(case_json(f.case))
    return record


def replay(record: Mapping[str, Any]) -> list[Finding]:
    """The findings on a recorded case (`to_json`, `case_json`) today: the same
    oracle again means the disagreement reproduces."""
    return _findings(case_of(record))


def main(argv: Sequence[str] | None = None) -> None:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("--budget", type=float, default=60.0, help="seconds (default 60)")
    parser.add_argument("--seed", type=int, default=0)
    parser.add_argument("--json", type=Path, help="also write the findings, with their cases, here")
    parser.add_argument(
        "--replay", type=Path, help="check a recorded finding (`--json`) again; 1 if it reproduces"
    )
    args = parser.parse_args(argv)
    if args.replay:
        record = json.loads(args.replay.read_text())
        again = [f for f in replay(record) if f.oracle == record.get("oracle", f.oracle)]
        for f in again:
            print(f, end="\n\n")
        print("reproduces" if again else "does not reproduce")
        raise SystemExit(1 if again else 0)
    findings = search(args.budget, args.seed)
    if args.json:
        args.json.write_text(json.dumps([to_json(f, args.seed) for f in findings], indent=1))
    print(f"{len(findings)} distinct finding(s)")


if __name__ == "__main__":
    main()
