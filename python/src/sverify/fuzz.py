"""Random queries with Lean's semantics as the oracle (SQLancer-style).

A Hypothesis strategy draws well-typed SQL queries over two small tables (`t`
with integer, double, string, boolean and timestamp columns, `u` with an
integer and a string) and random rows for them, NULLs included. Each query
goes through the real producer (DataFusion's SQL to Substrait), and `check`
compares:

1. `rows`: if the checker accepts the plan, Lean's rows (`Rel.eval` on the
   plan with the tables inlined) equal DataFusion's as bags, and those of the
   engines (`ENGINES`) on the plan Lean writes back out; doubles
   approximately (Lean prints six decimals). An `ORDER BY` over every output
   column also fixes the order.
2. `runtime`: if `verify` reports no possible runtime error, DataFusion does
   not raise.
3. `ensures`: a postcondition `verify` proves (from a precondition the
   generated input meets) holds on every output row of DataFusion.
4. `tlp`: ternary logic partitioning against Lean: the rows of a query are
   those where a predicate is TRUE, FALSE and NULL, together.

A query outside the model (the producer or the checker refuses it) is not a
finding. `python -m sverify.fuzz` runs a budget of random queries and prints
each distinct, shrunk disagreement; `tests/test_fuzz.py` runs a small budget.

This module needs Hypothesis, which only the `dev` group installs.
"""

from __future__ import annotations

import argparse
import datetime as dt
import json
import math
import random
import time
from collections.abc import Callable, Mapping, Sequence
from dataclasses import dataclass, field
from typing import Any

import ibis
import pyarrow as pa
from hypothesis import HealthCheck, find, settings
from hypothesis import strategies as st
from hypothesis.errors import NoSuchExample

from sverify import polars_engine
from sverify.contracts import verify
from sverify.engine import (
    ENGINES,
    connect,
    create_table,
    plain_schema,
    run_checker,
    run_plan,
    run_sql,
    substrait_json,
    written_plan,
)
from sverify.sql import core as sql_core
from sverify.testing import EPOCH, inline_tables, lean_values

INT, DOUBLE, STRING, BOOL, TS = "int", "double", "string", "bool", "ts"
SQL_TYPES = {INT: "BIGINT", DOUBLE: "DOUBLE", STRING: "VARCHAR", BOOL: "BOOLEAN", TS: "TIMESTAMP"}
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
    DOUBLE: st.sampled_from(["0.0", "1.5", "-2.0", "0.25", "CAST(NULL AS DOUBLE)"]),
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
            return f"({sub()} {draw(st.sampled_from(['+', '-', '*', '/', '%']))} {sub()})"
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

    def __str__(self) -> str:
        data = "\n".join(f"  {name}: {rows!r}" for name, rows in self.tables.items() if rows)
        extra = "".join(f"\n{k}: {v}" for k, v in self.extra.items())
        return f"[{self.oracle}] {self.sql}\n{data}{extra}\n{self.detail}"

    def signature(self) -> tuple[str, str]:
        return self.oracle, self.sql


class Refused(Exception):
    """The query is outside the model (producer, checker or DataFusion refuse it)."""


#: An engine translation refusing a plan on purpose: not a finding.
REFUSALS = (polars_engine.Unsupported, sql_core.Unsupported)

KNOWN: list[tuple[int, Callable[[Finding], bool]]] = [
    # Lean's written plan types a bare literal by its value: a double becomes
    # an `i64` holding its code, a timestamp an integer, a NULL an `i64` NULL.
    (
        96,
        lambda f: (
            f.oracle.startswith("rows:")
            and any(
                m in f.detail
                for m in (
                    "does not fit in 64 bits",
                    "incompatible type",
                    "Expect TypeSignatureClass",
                    "must be boolean type, but got Int64",
                    "dtype Null",
                    "got `null`",
                    "and BIGINT",
                    "BIGINT and TIMESTAMP",
                    "i64 field: Value out of range",
                    "Failed to coerce then (Int64)",
                )
            )
        ),
    ),
    # The same, seen as a column type: the literal comes back as an integer.
    (
        96,
        lambda f: (
            f.oracle.startswith("types:")
            and any(t in f.detail.splitlines()[-1] for t in ("int64", "'?'"))
        ),
    ),
    # DataFusion's consumer takes `a = b` over one join input for a join key.
    (98, lambda f: f.oracle == "rows:datafusion" and "FieldNotFound" in f.detail),
    # The DuckDB guard raises on `NULL / 0` (DataFusion, which ran fine, gives NULL).
    (111, lambda f: f.oracle == "rows:duckdb" and "sverify: division by zero" in f.detail),
    # One integer kind in the model: a widening cast of an `int32` is dropped.
    (
        18,
        lambda f: (
            f.oracle.startswith("types:")
            and "int32" in f.detail.splitlines()[-1]
            and "int64" in f.detail.splitlines()[-2]
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
    unit (DataFusion's SQL gives a timestamp literal nanoseconds, plans have
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
            create_table(self.con, name, SCHEMAS[name], rows)

    def plan(self, sql: str) -> str:
        try:
            plan = substrait_json(self.con, sql)
        except Exception as e:  # noqa: BLE001 - the producer refusing is not a finding
            raise Refused(f"producer: {e}") from e
        code, out, err = run_checker((), plan)
        if code != 0 or "well-formed: yes" not in out:
            raise Refused(f"checker: {(err or out).strip()[-200:]}")
        return plan

    def lean(self, plan: str) -> list[tuple]:
        inlined = inline_tables(json.loads(plan), self.tables)
        return lean_values(json.dumps(inlined))

    def datafusion(self, sql: str) -> list[tuple]:
        return _arrow_rows(run_sql(self.con, sql))


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

    lean = s.lean(plan)
    try:
        df_table = run_sql(s.con, query.sql)
        df, df_error = _arrow_rows(df_table), None
    except Exception as e:  # noqa: BLE001 - recorded below
        df_table, df, df_error = None, None, e

    if "runtime" in oracles and df_error is not None:
        report = verify(query.sql, tables=SCHEMAS)
        if not report.errors:
            found("runtime", f"DataFusion raises {df_error!r}; verify reports no runtime error")
    if "rows" in oracles and df is not None and not same_rows(lean, df, query.ordered):
        found("rows", f"Lean:       {lean!r}\nDataFusion: {df!r}")
    if "engines" in oracles and df_error is None:
        written = written_plan(plan)
        for engine in ENGINES:
            try:
                out = run_plan(s.con, written, engine)
            except REFUSALS:
                continue
            except Exception as e:  # noqa: BLE001 - recorded
                found(f"rows:{engine}", f"{engine} raises {e!r} (Lean: {lean!r})")
                continue
            got = _arrow_rows(out)
            if not same_rows(lean, got, query.ordered):
                found(f"rows:{engine}", f"Lean: {lean!r}\n{engine}: {got!r}")
            elif (types := _types(out)) != (expected := _types(df_table)):
                found(f"types:{engine}", f"DataFusion's SQL: {expected}\n{engine}: {types}")
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
        except Refused:
            pass
        else:
            if not same_rows(whole, split):
                found("tlp", f"whole: {whole!r}\nTRUE+FALSE+NULL parts: {split!r}", predicate=p)
    return findings


def check_contract(
    query: Query, tables: Mapping[str, list[tuple]], pre: str | None, post: str
) -> list[Finding]:
    """If `verify` proves `post` from `pre` (on `t`), it holds on DataFusion's
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
        bad = s.datafusion(check_sql)
    except Exception:  # noqa: BLE001 - a runtime error is the `runtime` oracle's business
        return []
    if not bad:
        return []
    return [
        Finding(
            "ensures",
            query.sql,
            s.tables,
            f"proved {post!r} from {pre!r}, but DataFusion gives violating rows {bad!r}",
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


def _findings(case: tuple) -> list[Finding]:
    """The findings on a case that no open issue explains."""
    try:
        found = check_contract(*case) if len(case) == 4 else check(*case)
    except Refused:
        return []
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
            return any(f.signature() not in found for f in _findings(case))

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
            found.setdefault(f.signature(), f)
            print(f, end="\n\n", flush=True)
    return list(found.values())


def main(argv: Sequence[str] | None = None) -> None:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("--budget", type=float, default=60.0, help="seconds (default 60)")
    parser.add_argument("--seed", type=int, default=0)
    args = parser.parse_args(argv)
    findings = search(args.budget, args.seed)
    print(f"{len(findings)} distinct finding(s)")


if __name__ == "__main__":
    main()
