"""DuckDB SQL to Substrait plans, through SQLGlot (#231, M1: #239).

Internal: not part of sverify's public API, which is `sverify`, `sverify.io`,
`sverify.engines` and `sverify.errors`; it may change in any release. Users
reach it through `sv.sql(query, dialect="duckdb", semantics=...)`.

    plan = lift("SELECT region, sum(amount) AS total FROM orders GROUP BY region",
                {"orders": ibis.schema({"region": "string", "amount": "float64"})},
                semantics="duckdb")

SQLGlot parses the query (`read="duckdb"`, strict) and resolves and types its
names against the inputs' schemas (`qualify`, `annotate_types`). The lift then
writes one Substrait plan, reading each input as a named table, in which every
choice DuckDB's SQL leaves implicit is explicit: casts where DuckDB coerces,
the output type of every function, the options Substrait defines for them
(`on_division_by_zero`, …), and the direction and NULL order of every sort
key. SQLGlot is trusted for parsing and name resolution only; the types of
expressions come from the profile, not from SQLGlot's typing.

How the SQL text reads is DuckDB's in both modes (`characterization/duckdb/
FACTS.md`, F1–F3): `/` divides as doubles, `//` divides integers, NULLs sort
last, an integer literal has the narrowest type that holds it, `1.5` is a
`DECIMAL(2, 1)`. The **semantics** (`Profile`) is what the functions then do
where DuckDB and the reference (#185, #209) differ:

* `semantics="duckdb"` (`DUCKDB`): DuckDB's own. A double `/` by zero is
  `±inf` or NaN (`on_division_by_zero: IEEE`), even with
  `error_on_division_by_zero` on. The plan means what DuckDB computes, and the
  checker proves contracts of that.
* `semantics="reference"` (`REFERENCE`): sverify's reference. A double `/`
  by zero raises (`ERROR`, decided on #185), and a cast of a double to an
  integer truncates (R9, decided on #209). The written SQL is guarded where
  DuckDB differs.

The subset (#239): SELECT, WHERE, arithmetic, comparisons, AND/OR/NOT,
IS NULL, IS [NOT] DISTINCT FROM, BETWEEN, IN lists, CASE, CAST, COALESCE,
NULLIF; numbers (`power`, `abs`, `round`, `floor`, `ceil`, `sign`, `isnan`,
`greatest`, `least`, square roots, logarithms, `exp` and trigonometry); dates and timestamps
(`date_trunc`, date parts: `EXTRACT`, `date_part`, `year()`, …, a date or
timestamp plus or minus a constant interval, `DATE - DATE`, `datediff`);
strings (`length`, `substring`, `trim`, `strpos`, `contains`, `starts_with`,
LIKE and ILIKE, `||`, `concat`, `replace`, `repeat`, `left`, `upper`,
`lower`); inner, left, right, full, semi, anti and cross joins; subqueries
in FROM, uncorrelated scalar, IN and EXISTS subqueries, and non-recursive
CTEs; GROUP BY with `count`, `sum`, `avg`, `min` and
`max`, DISTINCT and FILTER (WHERE …) in them, HAVING; window functions (ranking, `lag`/`lead`, first/last/nth
value, aggregates; ROWS and RANGE frames); DISTINCT, ORDER BY, LIMIT and
OFFSET. Anything else, unknown functions (`Anonymous`) included, raises
`Unsupported` saying what.
"""

from __future__ import annotations

import contextlib
import dataclasses
import datetime as dt_
import re
from collections.abc import Callable, Mapping, Sequence
from decimal import Decimal
from typing import Any

import ibis
import ibis.expr.datatypes as dt
import sqlglot as sg
import sqlglot.expressions as sge
from ibis.backends.sql.datatypes import DuckDBType
from ibis.common.temporal import IntervalUnit
from sqlglot.errors import ErrorLevel
from sqlglot.optimizer.annotate_types import annotate_types
from sqlglot.optimizer.normalize_identifiers import normalize_identifiers
from sqlglot.optimizer.qualify import qualify

from sverify.plan_json import (
    Json,
    Unsupported,
    anchor,
    call,
    cast_json,
    chain,
    column_of,
    compiling,
    distinct_rel,
    emit_rel,
    field_ref,
    if_then,
    interval_json,
    literal,
    plan,
    read_rel,
    select,
    type_json,
    values_rel,
)

__all__ = ["DUCKDB", "PROFILES", "REFERENCE", "Lifted", "Profile", "lift", "parse"]

DIALECT = "duckdb"

#: DuckDB's functions SQLGlot parses as `Anonymous`, which the lift reads.
_KNOWN = {"date_part", "datepart", "prefix", "suffix"}


# --------------------------------------------------------------------------
# Profiles


@dataclasses.dataclass(frozen=True)
class Profile:
    """What DuckDB SQL means, as data the lift reads (#231: "keep it
    simple"). The Lean side is `Profile.reference` and `Profile.duckdb` in
    `SubstraitLean/Profile.lean`.

    The first group of fields is how the SQL text reads, which is DuckDB's
    in both profiles; the second is what the functions do.

    Attributes:
        name: `"duckdb"` or `"reference"`, as `sv.sql`'s `semantics`.
        divide: SQL `/` on integers and decimals: `"double"`, both operands
            cast to `fp64` and divided (DuckDB's `/` without
            `integer_division`, F1).
        int_divide: SQL `//`: `"truncate"`, Substrait's integer `divide`
            (F1).
        null_ordering: Where NULLs sort when a key doesn't say:
            `"nulls_are_last"`, in both directions (F2; SQLGlot's
            `NULL_ORDERING` for DuckDB, checked when parsing).
        avg_integer: The output type of `avg` of integers: `"fp64"` (DuckDB;
            #209 R6, the plan's declared type).
        overflow: Integer `+ - *`, negation, `//` and `sum` that leave the
            declared width: `"ERROR"` (DuckDB, and #185's reference default).
        on_division_by_zero: `//` and `%` by zero: `"ERROR"` (DuckDB with
            `error_on_division_by_zero`, its default, and the reference).
        float_division_by_zero: `/` by zero, which divides doubles:
            `"IEEE"` (DuckDB: `1 / 0` is `inf`) or `"ERROR"` (reference).
        float_to_int: A cast of a double to an integer: `"TIE_TO_EVEN"`
            (DuckDB rounds, `CAST(2.5 AS INT)` is 2) or `"TRUNCATE"`
            (reference, #209 R9).
        decimal_to_int: A cast of a decimal to an integer:
            `"TIE_AWAY_FROM_ZERO"` (DuckDB, `CAST(2.5 AS INT)` is 3) or
            `"TRUNCATE"` (reference, R9).
        float_modulus_by_zero: `%` of doubles by zero: `"NAN"` (DuckDB) or
            `"ERROR"` (reference).
        domain_error: Elementary functions and `power` outside their domain
            (`sqrt(-1)`, `power(-8, 1/3)`): `"NAN"` (DuckDB) or `"ERROR"`
            (reference, #257).
        log_zero: A logarithm of 0: `"MINUS_INFINITY"` (DuckDB) or `"ERROR"`
            (reference).
    """

    name: str
    divide: str = "double"
    int_divide: str = "truncate"
    null_ordering: str = "nulls_are_last"
    avg_integer: str = "fp64"
    overflow: str = "ERROR"
    on_division_by_zero: str = "ERROR"
    float_division_by_zero: str = "ERROR"
    float_to_int: str = "TRUNCATE"
    decimal_to_int: str = "TRUNCATE"
    float_modulus_by_zero: str = "ERROR"
    domain_error: str = "ERROR"
    log_zero: str = "ERROR"


DUCKDB = Profile(
    "duckdb",
    float_division_by_zero="IEEE",
    float_to_int="TIE_TO_EVEN",
    decimal_to_int="TIE_AWAY_FROM_ZERO",
    float_modulus_by_zero="NAN",
    domain_error="NAN",
    log_zero="MINUS_INFINITY",
)
REFERENCE = Profile("reference")
PROFILES = {p.name: p for p in (DUCKDB, REFERENCE)}


# --------------------------------------------------------------------------
# Parsing and typing


def _sql_type(dtype: Any) -> str:
    return DuckDBType.from_ibis(dtype).sql(DIALECT)


def parse(query: str, schemas: Mapping[str, Any]) -> sge.Select:
    """`query` parsed as DuckDB SQL, at SQLGlot's strict error level, with
    every name resolved (`qualify`) and typed (`annotate_types`) against the
    tables `schemas` (Ibis schemas by table name).

    Raises:
        Unsupported: SQLGlot cannot parse the query, or a name in it is not
            a column or table of the inputs.
    """
    try:
        tree = sg.parse_one(query, read=DIALECT, error_level=ErrorLevel.RAISE)
    except sg.errors.ParseError as e:
        raise Unsupported(f"cannot parse the SQL as DuckDB's: {str(e).splitlines()[0]}") from e
    for f in tree.find_all(sge.Anonymous):
        if f.name.lower() not in _KNOWN:
            raise Unsupported(f"unknown function {f.name}(): DuckDB SQL here has no such function")
    _check_aliases(tree, schemas)
    catalog: dict[str, object] = {
        name: {col: _sql_type(t) for col, t in schema.items()} for name, schema in schemas.items()
    }
    try:
        tree = qualify(
            tree,
            schema=catalog,
            dialect=DIALECT,
            validate_qualify_columns=True,
            quote_identifiers=False,
        )
        tree = annotate_types(tree, schema=catalog, dialect=DIALECT)
    except sg.errors.OptimizeError as e:
        raise Unsupported(f"cannot resolve the SQL's names: {str(e).splitlines()[0]}") from e
    if not isinstance(tree, sge.Select):
        raise Unsupported(f"{type(tree).__name__} is not supported; only SELECT queries are")
    return tree


def _check_aliases(tree: Any, schemas: Mapping[str, Any]) -> None:
    """Refuse a name in WHERE, GROUP BY or HAVING that is both an output
    alias and an input column: DuckDB reads it as the column there, and
    SQLGlot's `qualify` as the alias (`select a + 1 as a … having a = 42`)."""
    columns = {_normalized(c) for s in schemas.values() for c in s.names}
    for sel in tree.find_all(sge.Select):
        aliases = {
            _normalized(e.alias)
            for e in sel.expressions
            if isinstance(e, sge.Alias)
            and not (isinstance(e.this, sge.Column) and e.this.name == e.alias)
        }
        for clause in ("where", "group", "having"):
            node = sel.args.get(clause)
            if node is None:
                continue
            for col in node.find_all(sge.Column):
                name = _normalized(col.name)
                if not col.table and name in aliases and name in columns:
                    raise Unsupported(
                        f"{name} in {clause.upper()} is both an input column and an output "
                        "alias, which SQLGlot and DuckDB resolve differently; rename the alias"
                    )


# --------------------------------------------------------------------------
# Lifting


#: No Python value: the expression is not a constant.
_NO_VALUE = object()


@dataclasses.dataclass
class E:
    """A lifted expression: its JSON, its type in the plan, and its value if
    it is a constant (which coercions write as a literal of the new type).

    `midnight`: DuckDB types it a TIMESTAMP, but it is always a date at
    midnight (`DATE + INTERVAL 1 DAY`, `date_trunc` of a DATE), so the plan
    holds the date. It compares, truncates and has date parts exactly as
    the timestamp; only where a timestamp is needed (an output column, a
    comparison with a timestamp column) is it refused, for Lean has no cast
    of a DATE column to a timestamp yet (#240)."""

    json: Json
    type: Any
    value: Any = _NO_VALUE
    midnight: bool = False

    @property
    def constant(self) -> bool:
        return self.value is not _NO_VALUE


class Bound(dict):
    """The expressions that are columns of the relation an expression is
    over: each grouping expression and measure of an aggregate (`grouped`:
    any other column is refused), and each window function."""

    def __init__(self, items: Any = (), grouped: bool = False) -> None:
        super().__init__(items)
        self.grouped = grouped


@dataclasses.dataclass
class Column:
    table: str | None
    name: str
    type: Any


@dataclasses.dataclass
class Lifted:
    """A lifted query: its plan (protobuf JSON) and its output schema."""

    plan: Json
    schema: ibis.Schema


#: Integer widths as DuckDB's decimals: `DECIMAL(p, 0)` holding each.
_INT_DIGITS = {8: 3, 16: 5, 32: 10, 64: 19}

#: Measures and the Substrait function each lifts to.
_AGGREGATES: dict[type, str] = {
    sge.Count: "count",
    sge.Sum: "sum",
    sge.Avg: "avg",
    sge.Min: "min",
    sge.Max: "max",
}

#: Joins with a condition, by SQLGlot's (side, kind).
_JOIN_TYPES = {
    ("", ""): "JOIN_TYPE_INNER",
    ("", "INNER"): "JOIN_TYPE_INNER",
    ("LEFT", ""): "JOIN_TYPE_LEFT",
    ("LEFT", "OUTER"): "JOIN_TYPE_LEFT",
    ("RIGHT", ""): "JOIN_TYPE_RIGHT",
    ("RIGHT", "OUTER"): "JOIN_TYPE_RIGHT",
    ("FULL", ""): "JOIN_TYPE_OUTER",
    ("FULL", "OUTER"): "JOIN_TYPE_OUTER",
    ("", "SEMI"): "JOIN_TYPE_LEFT_SEMI",
    ("LEFT", "SEMI"): "JOIN_TYPE_LEFT_SEMI",
    ("", "ANTI"): "JOIN_TYPE_LEFT_ANTI",
    ("LEFT", "ANTI"): "JOIN_TYPE_LEFT_ANTI",
}

_COMPARISONS: dict[type, str] = {
    sge.EQ: "equal",
    sge.NEQ: "not_equal",
    sge.LT: "lt",
    sge.LTE: "lte",
    sge.GT: "gt",
    sge.GTE: "gte",
}

_ARITHMETIC: dict[type, str] = {sge.Add: "add", sge.Sub: "subtract", sge.Mul: "multiply"}

#: The arguments of a SELECT the lift reads; any other one set is refused.
_SELECT_ARGS = {
    "with_",
    "expressions",
    "from_",
    "joins",
    "where",
    "group",
    "having",
    "order",
    "limit",
    "offset",
    "distinct",
}

#: The clauses of the queries SQLGlot reads that the subset lacks, by name.
_CLAUSES = {
    "qualify": "QUALIFY",
    "windows": "WINDOW",
    "laterals": "LATERAL",
    "pivots": "PIVOT",
    "sample": "SAMPLE",
}


def _option(name: str, value: str) -> Json:
    return {"name": name, "preference": [value]}


def _fn(name: str, args: list[Json], out: Any, options: Sequence[Json] = ()) -> Json:
    """A call of `name` with its output type and options written out."""
    c = call(name, args)
    c["scalarFunction"]["outputType"] = type_json(out)
    if options:
        c["scalarFunction"]["options"] = list(options)
    return c


def _decimal(p: int, s: int) -> Any:
    return dt.Decimal(precision=min(p, 38), scale=s)


def _digits(t: Any) -> tuple[int, int]:
    """`(precision, scale)` of a decimal or an integer, as DuckDB widens it."""
    if t.is_decimal():
        return t.precision, t.scale
    return _INT_DIGITS[t.nbytes * 8], 0


def _numeric(t: Any) -> bool:
    return t.is_integer() or t.is_float64() or t.is_decimal()


def _same(a: Any, b: Any) -> bool:
    return a.copy(nullable=True) == b.copy(nullable=True)


def _shown(node: sge.Expression) -> str:
    text = node.sql(DIALECT)
    return text if len(text) <= 60 else text[:57] + "..."


class _Lift:
    """Lifts one query with one profile, inside one `compiling` block."""

    def __init__(self, profile: Profile, schemas: Mapping[str, Any]):
        self.profile = profile
        # The inputs by their normalized names, as `qualify` writes them.
        self.schemas = {_normalized(n): (n, s) for n, s in schemas.items()}
        # The CTEs in scope, by name, and the scopes of the queries a
        # subquery is in (which it may not read: no correlated subqueries).
        self.ctes: dict[str, sge.Expression] = {}
        self.outer: list[list[Column]] = []

    # -- relations ---------------------------------------------------------

    def query(self, node: sge.Expression) -> tuple[Json, list[Column]]:
        """A query's relation and its output columns."""
        if isinstance(node, sge.Subquery):
            return self.query(node.this)
        if not isinstance(node, sge.Select):
            raise Unsupported(f"{type(node).__name__} is not supported; only SELECT queries are")
        if (with_ := node.args.get("with_")) is not None:
            # CTEs are inlined where they are read; each sees the ones before.
            if with_.args.get("recursive"):
                raise Unsupported("WITH RECURSIVE is not supported")
            saved = self.ctes
            self.ctes = dict(saved)
            for cte in with_.expressions:
                self.ctes[_normalized(cte.alias)] = cte.this
            body = node.copy()
            body.set("with_", None)
            try:
                return self.query(body)
            finally:
                self.ctes = saved
        for arg, what in _CLAUSES.items():
            if node.args.get(arg):
                raise Unsupported(f"{what} is not supported yet")
        extra = [k for k, v in node.args.items() if v and k not in _SELECT_ARGS]
        if extra:
            raise Unsupported(f"SELECT with {', '.join(sorted(extra))} is not supported")
        distinct = node.args.get("distinct")
        if distinct is not None and distinct.args.get("on") is not None:
            raise Unsupported("DISTINCT ON is not supported")
        rel, scope = self.from_(node)
        if (where := node.args.get("where")) is not None:
            rel = {"filter": {"input": rel, "condition": self.condition(where.this, scope)}}

        group = node.args.get("group")
        aggs = _aggregates([*node.expressions, node.args.get("having"), node.args.get("order")])
        bound: Bound = Bound()
        if group is not None or aggs:
            rel, scope, bound = self.aggregate(rel, scope, group, aggs)
            if (having := node.args.get("having")) is not None:
                cond = self.condition(having.this, scope, bound)
                rel = {"filter": {"input": rel, "condition": cond}}
        elif node.args.get("having") is not None:
            raise Unsupported("HAVING without GROUP BY or an aggregate")
        if wins := _windows([*node.expressions, node.args.get("order")]):
            rel, scope, bound = self.windows(rel, scope, bound, wins)

        outs = [self.expr(e.unalias(), scope, bound) for e in node.expressions]
        names = [e.alias_or_name for e in node.expressions]
        outs = [
            self.timestamp_of(e, n) if e.midnight else e for e, n in zip(outs, names, strict=True)
        ]
        # Sort keys that are not output columns are computed after them, and
        # dropped after the sort.
        keys: list[Json] = []
        extra_keys: list[E] = []
        if (order := node.args.get("order")) is not None:
            for o in order.expressions:
                i = self.output_index(o.this, names, node.expressions)
                if i is None:
                    if distinct is not None:
                        raise Unsupported(
                            f"ORDER BY {_shown(o.this)} of a SELECT DISTINCT must be an "
                            "output column"
                        )
                    extra_keys.append(self.expr(o.this, scope, bound))
                    i = len(outs) + len(extra_keys) - 1
                desc = bool(o.args.get("desc"))
                nulls = "FIRST" if o.args.get("nulls_first") else "LAST"
                direction = f"SORT_DIRECTION_{'DESC' if desc else 'ASC'}_NULLS_{nulls}"
                keys.append({"expr": field_ref(i), "direction": direction})
        width = len(scope)
        rel = select(rel, width, [e.json for e in outs + extra_keys])
        if distinct is not None:
            rel = distinct_rel(rel, len(outs))
        if keys:
            rel = {"sort": {"input": rel, "sorts": keys}}
        rel = self.fetch(rel, node)
        if extra_keys:
            rel = emit_rel(rel, list(range(len(outs))))
        return rel, [Column(None, n, e.type) for n, e in zip(names, outs, strict=True)]

    def timestamp_of(self, e: E, name: str) -> E:
        """An output column DuckDB types a TIMESTAMP that the plan holds as a
        date at midnight: a constant becomes the timestamp; a column needs a
        cast Lean lacks."""
        if e.constant:
            return self.to(E(e.json, e.type, e.value), dt.timestamp(scale=6))
        raise Unsupported(
            f"output column {name} is a TIMESTAMP in DuckDB (a DATE at midnight), and Lean "
            "has no cast of a DATE column to a timestamp yet (#240)"
        )

    def output_index(
        self, key: sge.Expression, names: list[str], outs: list[sge.Expression]
    ) -> int | None:
        """The output column a sort key names (an alias or an ordinal, which
        `qualify` writes as the alias), or the output expression it repeats."""
        if isinstance(key, sge.Column) and not key.table and key.name in names:
            return names.index(key.name)
        for i, o in enumerate(outs):
            if o.unalias() == key:
                return i
        return None

    def fetch(self, rel: Json, node: sge.Select) -> Json:
        limit, offset = node.args.get("limit"), node.args.get("offset")
        if limit is None and offset is None:
            return rel
        body: Json = {"input": rel, "offsetExpr": literal(0, dt.int64)}
        if offset is not None:
            body["offsetExpr"] = literal(_count(offset.expression, "OFFSET"), dt.int64)
        if limit is not None:
            body["countExpr"] = literal(_count(limit.expression, "LIMIT"), dt.int64)
        return {"fetch": body}

    def from_(self, node: sge.Select) -> tuple[Json, list[Column]]:
        if node.args.get("from_") is None:
            # `SELECT 1 + 1` reads one row, of one column no name can refer
            # to (the SQL printers have no relation of no columns).
            one = values_rel(ibis.schema({"": "int32"}), [[literal(0, dt.int32)]])
            return one, [Column(None, "", dt.int32)]
        rel, scope = self.source(node.args["from_"].this)
        for join in node.args.get("joins") or []:
            right, cols = self.source(join.this)
            side, kind = (join.side or "").upper(), (join.kind or "").upper()
            on = join.args.get("on")
            if join.args.get("using"):
                raise Unsupported("JOIN … USING is not supported")
            if kind == "CROSS" or (not side and not kind and on is None):
                rel = {"cross": {"left": rel, "right": right}}
                scope = scope + cols
                continue
            how = _JOIN_TYPES.get((side, kind))
            if how is None or on is None:
                what = " ".join(w for w in (side, kind) if w) or "this"
                raise Unsupported(f"{what} JOIN is not supported yet")
            cond = self.condition(on, scope + cols)
            rel = {"join": {"left": rel, "right": right, "expression": cond, "type": how}}
            # A semi or anti join keeps the left side's columns only.
            if kind not in ("SEMI", "ANTI"):
                scope = scope + cols
        return rel, scope

    def source(self, node: sge.Expression) -> tuple[Json, list[Column]]:
        """A relation in FROM or JOIN, and its columns under its alias."""
        alias = node.alias_or_name
        if isinstance(node, sge.Table) and not node.args.get("db") and node.name in self.ctes:
            rel, cols = self.query(self.ctes[node.name])
            return rel, [Column(alias, c.name, c.type) for c in cols]
        if isinstance(node, sge.Table):
            if (
                node.args.get("db")
                or node.args.get("catalog")
                or not isinstance(node.this, sge.Identifier)
            ):
                raise Unsupported(f"FROM {_shown(node)}: only the inputs' tables can be read")
            found = self.schemas.get(node.name)
            if found is None:
                raise Unsupported(f"the query reads {node.name}, which is not an input")
            name, schema = found
            cols = [Column(alias, _normalized(c), t) for c, t in schema.items()]
            return read_rel(name, schema), cols
        if isinstance(node, sge.Subquery):
            rel, cols = self.query(node.this)
            return rel, [Column(alias, c.name, c.type) for c in cols]
        raise Unsupported(f"FROM {_shown(node)} is not supported")

    def windows(
        self,
        rel: Json,
        scope: list[Column],
        bound: Bound,
        wins: list[sge.Window],
    ) -> tuple[Json, list[Column], Bound]:
        """The window functions `wins` over `rel`, each a column after
        `scope`'s (and after the expressions their arguments need: the model
        reads a window function's arguments as columns)."""
        width = len(scope)
        pre: list[E] = []

        def column(e: E) -> Json:
            if column_of(e.json) is not None:
                return e.json
            pre.append(e)
            return field_ref(width + len(pre) - 1)

        funcs = [self.window(w, scope, bound, column) for w in wins]
        if pre:
            rel = {"project": {"input": rel, "expressions": [e.json for e in pre]}}
        rel = {"project": {"input": rel, "expressions": [j for js, _ in funcs for j, _ in js]}}
        cols = scope + [Column(None, "", e.type) for e in pre]
        bound = Bound(bound, grouped=bound.grouped)
        for w, (js, value) in zip(wins, funcs, strict=True):
            refs = []
            for _, t in js:
                refs.append(field_ref(len(cols)))
                cols.append(Column(None, "", t))
            bound[w] = value(refs)
        return rel, cols, bound

    def window(
        self,
        w: sge.Window,
        scope: list[Column],
        bound: Mapping[sge.Expression, E],
        column: Callable[[E], Json],
    ) -> tuple[list[tuple[Json, Any]], Callable[[list[Json]], E]]:
        """One window function: the window functions (JSON and type) it is
        computed from, and its value from their columns."""
        if w.args.get("alias") is not None or w.args.get("first") is not None:
            raise Unsupported(f"{_shown(w)}: named windows are not supported yet")
        f = w.this
        if isinstance(f, sge.IgnoreNulls | sge.RespectNulls | sge.Filter):
            raise Unsupported(f"{_shown(w)} is not supported yet")

        def arg(n: sge.Expression) -> E:
            return self.expr(n, scope, bound)

        args: list[Json] = []
        if type(f) in _RANKING:
            name, out = _RANKING[type(f)]
            if isinstance(f, sge.Ntile):
                n = arg(f.this)
                if not (n.constant and isinstance(n.value, int) and n.value > 0):
                    raise Unsupported("ntile needs a positive integer constant")
                return self.ntile(w, n.value, scope, bound)
        elif isinstance(f, sge.Lag | sge.Lead):
            name = "lag" if isinstance(f, sge.Lag) else "lead"
            x = arg(f.this)
            out = x.type
            offset = f.args.get("offset")
            k = arg(offset) if offset is not None else E({}, dt.int64, 1)
            if not (k.constant and isinstance(k.value, int) and k.value >= 0):
                raise Unsupported(f"{name} needs a non-negative integer constant offset")
            args = [column(x), literal(k.value, dt.int64)]
            if (default := f.args.get("default")) is not None:
                d = arg(default)
                t = self.common([x, d], name)
                if not _same(t, x.type):
                    raise Unsupported(f"{name} with a default of another type is not supported")
                args.append(self.to(d, t).json)
        elif isinstance(f, sge.FirstValue | sge.LastValue | sge.NthValue):
            x = arg(f.this)
            out = x.type
            name = (
                "first_value"
                if isinstance(f, sge.FirstValue)
                else "last_value"
                if isinstance(f, sge.LastValue)
                else "nth_value"
            )
            args = [column(x)]
            if isinstance(f, sge.NthValue):
                k = arg(f.args["offset"])
                if not (k.constant and isinstance(k.value, int) and k.value > 0):
                    raise Unsupported("nth_value needs a positive integer constant")
                args.append(literal(k.value, dt.int64))
        elif type(f) in _AGGREGATES:
            m, out = self.measure(f, scope, bound)
            agg = m["measure"]
            if agg["invocation"] != "AGGREGATION_INVOCATION_ALL":
                raise Unsupported(f"{_shown(w)}: DISTINCT in a window is not supported")
            name = _AGGREGATES[type(f)]
            values = [E(a["value"], dt.null) for a in agg["arguments"]]
            args = [column(v) for v in values]
        else:
            raise Unsupported(f"window function {_shown(f)} is not supported yet")
        fn = self.window_json(w, name, args, scope, bound)
        return [(fn, out)], lambda refs: E(refs[0], out)

    def window_json(
        self,
        w: sge.Window,
        name: str,
        args: list[Json],
        scope: list[Column],
        bound: Mapping[sge.Expression, E],
        frame: Json | None = None,
    ) -> Json:
        partitions = [self.expr(p, scope, bound).json for p in w.args.get("partition_by") or []]
        order = w.args.get("order")
        sorts = []
        for o in order.expressions if order is not None else []:
            desc = bool(o.args.get("desc"))
            nulls = "FIRST" if o.args.get("nulls_first") else "LAST"
            sorts.append(
                {
                    "expr": self.expr(o.this, scope, bound).json,
                    "direction": f"SORT_DIRECTION_{'DESC' if desc else 'ASC'}_NULLS_{nulls}",
                }
            )
        fn = {
            "functionReference": anchor(name),
            "partitions": partitions,
            "sorts": sorts,
            "arguments": [{"value": a} for a in args],
            **(frame or _frame(w, bool(sorts))),
        }
        return {"windowFunction": fn}

    def ntile(
        self, w: sge.Window, k: int, scope: list[Column], bound: Mapping[sge.Expression, E]
    ) -> tuple[list[tuple[Json, Any]], Callable[[list[Json]], E]]:
        """DuckDB's `NTILE(k)`, the SQL standard's: of `n` rows, the first
        `n % k` buckets have `n // k + 1` rows, the rest `n // k`. (The
        model's `ntile` is DataFusion's, ⌊i · min(k, n) / n⌋ + 1.) From the
        row's number `i` (from 0) and `n`, the partition's count: with
        `q = n // k` and `r = n % k`, `i // (q + 1) + 1` for `i < r · (q + 1)`,
        else `(i - r) // q + 1`."""
        whole = {
            "lowerBound": {"unbounded": {}},
            "upperBound": {"unbounded": {}},
            "boundsType": "BOUNDS_TYPE_ROWS",
        }
        rn = self.window_json(w, "row_number", [], scope, bound)
        count = self.window_json(w, "count", [], scope, bound, whole)
        count["windowFunction"]["sorts"] = []
        i64 = dt.int64

        def value(refs: list[Json]) -> E:
            one, kk = literal(1, i64), literal(k, i64)

            def f(name: str, *a: Json) -> Json:
                return _fn(name, list(a), i64)

            i, n = f("subtract", refs[0], one), refs[1]
            q, r = f("divide", n, kk), f("modulus", n, kk)
            big = f("add", f("divide", i, f("add", q, one)), one)
            # `greatest`: q is 0 only where every row is in the first branch.
            small = f("add", f("divide", f("subtract", i, r), f("greatest", q, one)), one)
            first = _fn("lt", [i, f("multiply", r, f("add", q, one))], dt.boolean)
            return E(if_then([(first, big)], small), i64)

        return [(rn, i64), (count, i64)], value

    def nested(self, node: sge.Expression, scope: list[Column]) -> tuple[Json, list[Column]]:
        """A subquery inside an expression over `scope`."""
        self.outer.append(scope)
        try:
            return self.query(node)
        finally:
            self.outer.pop()

    def aggregate(
        self,
        rel: Json,
        scope: list[Column],
        group: sge.Group | None,
        aggs: list[sge.Expression],
    ) -> tuple[Json, list[Column], Bound]:
        """The aggregate relation, its columns, and the expressions that are
        its columns (each grouping expression and each measure)."""
        keys = list(group.expressions) if group is not None else []
        if group is not None and any(
            group.args.get(k) for k in ("grouping_sets", "cube", "rollup")
        ):
            raise Unsupported("GROUPING SETS, CUBE and ROLLUP are not supported yet")
        groups = [self.expr(k, scope) for k in keys]
        measures = [self.measure(a, scope) for a in aggs]
        body: Json = {
            "input": rel,
            "groupingExpressions": [g.json for g in groups],
            "groupings": [{"expressionReferences": list(range(len(groups)))}] if groups else [],
            "measures": [m for m, _ in measures],
        }
        types = [g.type for g in groups] + [t for _, t in measures]
        bound = Bound(
            {k: E(field_ref(i), types[i], midnight=groups[i].midnight) for i, k in enumerate(keys)},
            grouped=True,
        )
        for j, a in enumerate(aggs):
            bound[a] = E(field_ref(len(keys) + j), types[len(keys) + j])
        cols = [Column(None, f"_{i}", t) for i, t in enumerate(types)]
        return {"aggregate": body}, cols, bound

    def measure(
        self,
        node: sge.Expression,
        scope: list[Column],
        bound: Mapping[sge.Expression, E] | None = None,
    ) -> tuple[Json, Any]:
        where = None
        if isinstance(node, sge.Filter):
            # `agg(…) FILTER (WHERE c)`: the rows where `c` is TRUE.
            where = self.condition(node.expression.this, scope, bound)
            node = node.this
        name = _AGGREGATES[type(node)]
        arg = node.this
        distinct = isinstance(arg, sge.Distinct)
        if distinct:
            if len(arg.expressions) != 1:
                raise Unsupported(f"{_shown(node)}: DISTINCT of several values is not supported")
            arg = arg.expressions[0]
        if isinstance(node, sge.Count) and (arg is None or isinstance(arg, sge.Star)):
            args: list[E] = []
            out: Any = dt.int64
        else:
            if not isinstance(node, sge.Count) and node.expressions:
                raise Unsupported(f"{_shown(node)} takes one argument")
            a = self.expr(arg, scope, bound)
            if a.midnight:
                raise Unsupported(
                    f"{_shown(node)}: an aggregate of a DATE at midnight that DuckDB types a "
                    "TIMESTAMP is not supported yet (#240)"
                )
            args = [a]
            t = a.type
            if name == "count":
                out = dt.int64
            elif name in ("min", "max"):
                out = t
            elif not _numeric(t):
                raise Unsupported(f"{name} of {t} is not supported")
            elif name == "sum":
                # DuckDB sums integers as HUGEINTs; the plan's 64-bit sum
                # raises where one leaves 64 bits (#202), as the written
                # SQL's cast back to BIGINT does.
                out = (
                    _decimal(38, t.scale)
                    if t.is_decimal()
                    else dt.int64
                    if t.is_integer()
                    else dt.float64
                )
            else:
                # DuckDB's AVG of a DECIMAL is a DOUBLE too: the plan says so,
                # and Lean divides the exact sum by the count in doubles.
                out = dt.float64
        agg: Json = {
            "functionReference": anchor(name),
            "arguments": [{"value": a.json} for a in args],
            "outputType": type_json(out),
            **({"options": _overflow(self, out)} if name == "sum" else {}),
            "invocation": (
                "AGGREGATION_INVOCATION_DISTINCT" if distinct else "AGGREGATION_INVOCATION_ALL"
            ),
        }
        return {"measure": agg, **({"filter": where} if where is not None else {})}, out

    # -- expressions -------------------------------------------------------

    def condition(
        self,
        node: sge.Expression,
        scope: list[Column],
        bound: Mapping[sge.Expression, E] | None = None,
    ) -> Json:
        e = self.expr(node, scope, bound)
        if not (e.type.is_boolean() or e.type.is_null()):
            raise Unsupported(f"{_shown(node)} is a {e.type}, not a condition")
        return e.json

    def expr(
        self,
        node: sge.Expression,
        scope: list[Column],
        bound: Mapping[sge.Expression, E] | None = None,
    ) -> E:
        bound = bound or {}
        if node in bound:
            return bound[node]
        if getattr(bound, "grouped", False) and isinstance(node, sge.Column):
            raise Unsupported(f"column {_shown(node)} must be in GROUP BY or inside an aggregate")
        if type(node) in _AGGREGATES:
            raise Unsupported(f"aggregate {_shown(node)} is not allowed here")
        if node.args.get("negate"):
            # SQLGlot writes `s NOT LIKE p` as `LIKE` with `negate`.
            inner = node.copy()
            inner.set("negate", None)
            e = self.expr(inner, scope, bound)
            return E(_fn("not", [_bool_json(self, e)], dt.boolean), dt.boolean)
        rule = _RULES.get(type(node))
        if rule is None:
            raise Unsupported(f"{type(node).__name__} ({_shown(node)}) is not supported yet")
        return rule(self, node, lambda n: self.expr(n, scope, bound), scope)

    def column(self, node: sge.Column, scope: list[Column]) -> E:
        table, name = node.table, node.name
        found = [
            i for i, c in enumerate(scope) if c.name == name and (not table or c.table == table)
        ]
        if len(found) != 1:
            if not found and any(
                c.name == name and (not table or c.table == table) for o in self.outer for c in o
            ):
                raise Unsupported(
                    f"correlated subqueries are not supported yet (it reads {_shown(node)})"
                )
            what = "unknown" if not found else "ambiguous"
            raise Unsupported(f"{what} column {_shown(node)}")
        return E(field_ref(found[0]), scope[found[0]].type)

    def to(self, e: E, t: Any) -> E:
        """`e` as a `t`: a constant as a literal of `t`, else a cast."""
        if _same(e.type, t):
            return e
        if e.constant:
            v = e.value
            if v is not None:
                if t.is_float64():
                    v = float(v)
                elif t.is_decimal():
                    v = Decimal(v)
                elif t.is_integer() and isinstance(v, Decimal):
                    v = None if v != v.to_integral_value() else int(v)
                elif t.is_timestamp() and type(v) is dt_.date:
                    v = dt_.datetime.combine(v, dt_.time())
            if v is not None or e.value is None:
                return E(literal(v, t), t, v)
        if e.type.is_null():
            return E(literal(None, t), t, None)
        if e.type.is_date() and t.is_timestamp():
            raise Unsupported(
                "a DATE column as a TIMESTAMP is not supported yet: Lean has no cast of a "
                "DATE column to a timestamp (#240)"
            )
        return E(cast_json(e.json, t), t)

    def common(self, es: list[E], what: str, sum_digits: bool = False) -> Any:
        """The type DuckDB brings `es` to as one value: the widest integer;
        a double if one is; else a decimal with the most integer digits and
        the largest scale (plus a digit for `+` and `-`)."""
        ts = [e.type for e in es if not e.type.is_null()]
        if not ts:
            return dt.null
        if all(_numeric(t) for t in ts):
            if any(t.is_float64() for t in ts):
                return dt.float64
            if any(t.is_decimal() for t in ts):
                ds = [_digits(t) for t in ts]
                s = max(s for _, s in ds)
                return _decimal(max(p - s0 for p, s0 in ds) + s + int(sum_digits), s)
            return max(ts, key=lambda t: t.nbytes).copy(nullable=True)
        first = ts[0]
        if all(_same(t, first) for t in ts):
            return first.copy(nullable=True)
        if all(t.is_temporal() and not t.is_time() for t in ts):
            return dt.timestamp(scale=6)
        shown = ", ".join(str(t) for t in ts)
        raise Unsupported(f"{what} of {shown} is not supported")


# -- expression rules -------------------------------------------------------

Sub = Callable[[sge.Expression], E]


def _column(lf: _Lift, node: sge.Column, sub: Sub, scope: list[Column]) -> E:
    return lf.column(node, scope)


def _literal(lf: _Lift, node: sge.Literal, sub: Sub, scope: list[Column]) -> E:
    text = node.this
    if node.is_string:
        return E(literal(text, dt.string), dt.string, text)
    return _number(text)


def _number(text: str, negative: bool = False) -> E:
    """A number as DuckDB types it: the narrowest of `INTEGER` and `BIGINT`,
    a `DECIMAL(p, s)` with the digits as written, or a `DOUBLE` with an
    exponent or more than 38 digits."""
    sign = "-" if negative else ""
    if re.fullmatch(r"\d+", text):
        v = int(sign + text)
        for t in (dt.int32, dt.int64):
            if t.bounds.lower <= v <= t.bounds.upper:
                return E(literal(v, t), t, v)
        raise Unsupported(f"the integer {sign}{text} is a HUGEINT, which is not supported")
    m = re.fullmatch(r"(\d*)\.(\d*)", text)
    if m and len(m.group(1)) + len(m.group(2)) <= 38:
        v = Decimal(sign + text)
        t = _decimal(max(len(m.group(1)) + len(m.group(2)), 1), len(m.group(2)))
        return E(literal(v, t), t, v)
    v = float(sign + text)
    return E(literal(v, dt.float64), dt.float64, v)


def _boolean(lf: _Lift, node: sge.Boolean, sub: Sub, scope: list[Column]) -> E:
    return E(literal(bool(node.this), dt.boolean), dt.boolean, bool(node.this))


def _null(lf: _Lift, node: sge.Null, sub: Sub, scope: list[Column]) -> E:
    # Typed where it is used (`to`); alone, an INTEGER NULL.
    return E(literal(None, dt.int32), dt.null, None)


def _paren(lf: _Lift, node: sge.Paren, sub: Sub, scope: list[Column]) -> E:
    return sub(node.this)


def _neg(lf: _Lift, node: sge.Neg, sub: Sub, scope: list[Column]) -> E:
    inner = node.this
    if isinstance(inner, sge.Literal) and not inner.is_string:
        return _number(inner.this, negative=True)
    a = sub(inner)
    if not _numeric(a.type):
        raise Unsupported(f"-{a.type} is not supported")
    return E(_fn("negate", [a.json], a.type, _overflow(lf, a.type)), a.type)


def _overflow(lf: _Lift, t: Any) -> list[Json]:
    """`overflow` for exact arithmetic (integers, decimals) at the declared
    width; doubles have none."""
    return [] if t.is_float64() else [_option("overflow", lf.profile.overflow)]


def _arith(lf: _Lift, node: sge.Expression, sub: Sub, scope: list[Column]) -> E:
    name = _ARITHMETIC[type(node)]
    a, b = sub(node.this), sub(node.expression)
    if a.type.is_interval() or b.type.is_interval():
        return _temporal_plus(name, a, b)
    if name == "subtract" and a.type.is_date() and b.type.is_date():
        # DuckDB's DATE - DATE is a BIGINT of days.
        if a.midnight or b.midnight:
            raise Unsupported("a TIMESTAMP minus a DATE (an interval) is not supported yet")
        return E(_fn("date_diff", [a.json, b.json], dt.int64), dt.int64)
    if not (_numeric(a.type) or a.type.is_null()) or not (_numeric(b.type) or b.type.is_null()):
        raise Unsupported(f"{name} of {a.type} and {b.type} is not supported yet")
    t = lf.common([a, b], name, sum_digits=name != "multiply")
    if t.is_null():
        t = dt.int32
    if t.is_decimal():
        # The model computes decimals at their exact scales itself; the
        # output type is DuckDB's: `+`/`-` at the larger scale with one more
        # integer digit, `×` at the sum of the precisions and scales, but at
        # most 18 digits when both fit in 18 (a checked 64-bit product).
        (p1, s1), (p2, s2) = (
            _digits(lf.to(x, t).type if x.type.is_null() else x.type) for x in (a, b)
        )
        if name == "multiply":
            p = p1 + p2
            if p1 <= 18 and p2 <= 18 and p > 18:
                p = 18
            t = _decimal(p, s1 + s2)
        args = [x if not x.type.is_null() else lf.to(x, t) for x in (a, b)]
        return E(_fn(name, [x.json for x in args], t, _overflow(lf, t)), t)
    return E(_fn(name, [lf.to(a, t).json, lf.to(b, t).json], t, _overflow(lf, t)), t)


def _div(lf: _Lift, node: sge.Div, sub: Sub, scope: list[Column]) -> E:
    a, b = sub(node.this), sub(node.expression)
    for x in (a, b):
        if not (_numeric(x.type) or x.type.is_null()):
            raise Unsupported(f"/ of {a.type} and {b.type} is not supported")
    if node.args.get("typed") or node.args.get("safe"):
        raise Unsupported("typed or safe division is not DuckDB's /")
    # DuckDB's `/` divides as doubles (F1); by zero it gives ±inf or NaN.
    opt = _option("on_division_by_zero", lf.profile.float_division_by_zero)
    args = [lf.to(a, dt.float64).json, lf.to(b, dt.float64).json]
    return E(_fn("divide", args, dt.float64, [opt]), dt.float64)


def _int_div(lf: _Lift, node: sge.IntDiv, sub: Sub, scope: list[Column]) -> E:
    a, b = sub(node.this), sub(node.expression)
    t = lf.common([a, b], "//")
    if not t.is_integer():
        raise Unsupported(f"// of {a.type} and {b.type} is not supported; it divides integers")
    opts = [
        _option("overflow", lf.profile.overflow),
        _option("on_division_by_zero", lf.profile.on_division_by_zero),
    ]
    return E(_fn("divide", [lf.to(a, t).json, lf.to(b, t).json], t, opts), t)


def _mod(lf: _Lift, node: sge.Mod, sub: Sub, scope: list[Column]) -> E:
    a, b = sub(node.this), sub(node.expression)
    t = lf.common([a, b], "%")
    if t.is_float64():
        if lf.profile.float_modulus_by_zero != "ERROR":
            raise Unsupported(
                "% of doubles is not supported with DuckDB's semantics: by zero DuckDB "
                "gives NaN, which the model's modulus cannot state"
            )
        # sverify's own remainder of doubles, C's `fmod` (#256): Substrait's
        # `modulus` has no double impl.
        opt = _option("on_division_by_zero", "ERROR")
        return E(_fn("sverify_fmod", [lf.to(a, t).json, lf.to(b, t).json], t, [opt]), t)
    elif not t.is_integer():
        raise Unsupported(f"% of {a.type} and {b.type} is not supported yet")
    # The remainder takes the dividend's sign (`division_type` TRUNCATE, #209
    # R3), in DuckDB and the model.
    opts = [
        _option("on_division_by_zero", lf.profile.on_division_by_zero),
        _option("division_type", "TRUNCATE"),
    ]
    return E(_fn("modulus", [lf.to(a, t).json, lf.to(b, t).json], t, opts), t)


def _operands(lf: _Lift, es: list[E], what: str) -> list[Json]:
    """Arguments of a comparison: decimals and integers as they are (the
    model compares them at a common scale), anything else at one type."""
    ts = [e.type for e in es if not e.type.is_null()]
    if any(t.is_decimal() for t in ts) and all(t.is_decimal() or t.is_integer() for t in ts):
        t = lf.common(es, what)
        return [(e if not e.type.is_null() else lf.to(e, t)).json for e in es]
    es = _temporal_literals(es)
    t = lf.common(es, what)
    if t.is_null():
        t = dt.int32
    return [lf.to(e, t).json for e in es]


def _temporal_literals(es: list[E]) -> list[E]:
    """String constants next to a date or timestamp read as one, as DuckDB
    casts them."""
    temporal = [e.type for e in es if e.type.is_date() or e.type.is_timestamp()]
    if not temporal:
        return es
    es = [_temporal(e, temporal[0]) if e.type.is_string() and e.constant else e for e in es]
    # Next to a DATE column, a timestamp constant at midnight compares as its
    # date (exactly); Lean cannot cast the column to a timestamp (#240).
    if any(e.type.is_date() and not e.constant for e in es):
        es = [_as_date(e) if e.type.is_timestamp() and e.constant else e for e in es]
    return es


def _as_date(e: E) -> E:
    v = e.value
    if v is None:
        return E(literal(None, dt.date), dt.date, None)
    if v.time() != dt_.time():
        raise Unsupported(
            f"comparing a DATE column with the timestamp {v} is not supported yet: Lean has "
            "no cast of a DATE column to a timestamp (#240)"
        )
    return E(literal(v.date(), dt.date), dt.date, v.date())


def _temporal(e: E, t: Any) -> E:
    # DuckDB reads a date with spaces around it, and a timestamp with spaces
    # before it, or after it if it has a time of day.
    text = e.value
    if isinstance(text, str):
        if t.is_date() or re.search(r"\d[ T]\d", text.strip()):
            text = text.strip()
        elif text != text.rstrip():
            raise Unsupported(f"DuckDB cannot read {text!r} as a {t}")
        text = text.lstrip()
    try:
        if t.is_date():
            v: Any = dt_.date.fromisoformat(text)
            return E(literal(v, dt.date), dt.date, v)
        v = dt_.datetime.fromisoformat(text)
    except (TypeError, ValueError) as err:
        raise Unsupported(f"cannot read {text!r} as a {t}") from err
    if v.tzinfo is not None:
        raise Unsupported("timestamps with a time zone are not supported")
    ts = dt.timestamp(scale=6)
    return E(literal(v, ts), ts, v)


def _compare(lf: _Lift, node: sge.Expression, sub: Sub, scope: list[Column]) -> E:
    name = _COMPARISONS[type(node)]
    args = _operands(lf, [sub(node.this), sub(node.expression)], name)
    return E(_fn(name, args, dt.boolean), dt.boolean)


def _logical(name: str) -> Callable[..., E]:
    def rule(lf: _Lift, node: sge.Expression, sub: Sub, scope: list[Column]) -> E:
        args = [sub(node.this), sub(node.expression)]
        for a in args:
            if not (a.type.is_boolean() or a.type.is_null()):
                raise Unsupported(f"{name.upper()} of a {a.type} is not supported")
        return E(_fn(name, [lf.to(a, dt.boolean).json for a in args], dt.boolean), dt.boolean)

    return rule


def _not(lf: _Lift, node: sge.Not, sub: Sub, scope: list[Column]) -> E:
    inner = node.this
    if isinstance(inner, sge.Is) and isinstance(inner.expression, sge.Null):
        return E(_fn("is_not_null", [sub(inner.this).json], dt.boolean), dt.boolean)
    a = sub(inner)
    if not (a.type.is_boolean() or a.type.is_null()):
        raise Unsupported(f"NOT of a {a.type} is not supported")
    return E(_fn("not", [lf.to(a, dt.boolean).json], dt.boolean), dt.boolean)


def _is(lf: _Lift, node: sge.Is, sub: Sub, scope: list[Column]) -> E:
    if not isinstance(node.expression, sge.Null):
        raise Unsupported(f"IS {_shown(node.expression)} is not supported; only IS [NOT] NULL is")
    return E(_fn("is_null", [sub(node.this).json], dt.boolean), dt.boolean)


def _between(lf: _Lift, node: sge.Between, sub: Sub, scope: list[Column]) -> E:
    if node.args.get("symmetric"):
        raise Unsupported("BETWEEN SYMMETRIC is not supported")
    x, lo, hi = _operands(
        lf, [sub(node.this), sub(node.args["low"]), sub(node.args["high"])], "BETWEEN"
    )
    both = [_fn("gte", [x, lo], dt.boolean), _fn("lte", [x, hi], dt.boolean)]
    return E(_fn("and", both, dt.boolean), dt.boolean)


def _in(lf: _Lift, node: sge.In, sub: Sub, scope: list[Column]) -> E:
    if node.args.get("unnest") is not None:
        raise Unsupported("IN UNNEST is not supported yet")
    if (query := node.args.get("query")) is not None:
        # SQL's NULLs: NULL when no value matches and the needle or a value
        # is NULL (the model lifts it so, `Parse.liftSubquery`).
        needle = sub(node.this)
        rel, cols = lf.nested(query, scope)
        if len(cols) != 1:
            raise Unsupported("an IN subquery must return one column")
        t = cols[0].type
        if not needle.type.is_null() and not _same(lf.common([needle, E({}, t)], "IN"), t):
            raise Unsupported(f"IN of a {needle.type} in a subquery of {t} is not supported yet")
        x = lf.to(needle, t).json
        return E({"subquery": {"inPredicate": {"needles": [x], "haystack": rel}}}, dt.boolean)
    es = [sub(node.this), *(sub(o) for o in node.expressions)]
    es = _temporal_literals(es)
    t = lf.common(es, "IN")
    if t.is_null():
        t = dt.int32
    value, *options = [lf.to(e, t).json for e in es]
    return E({"singularOrList": {"value": value, "options": options}}, dt.boolean)


def _case(lf: _Lift, node: sge.Case, sub: Sub, scope: list[Column]) -> E:
    ifs = node.args.get("ifs") or []
    base = node.this
    results = [sub(i.args["true"]) for i in ifs]
    default = node.args.get("default")
    dflt = sub(default) if default is not None else E(literal(None, dt.int32), dt.null, None)
    t = lf.common([*results, dflt], "CASE")
    if t.is_null():
        t = dt.int32
    conds = []
    for i in ifs:
        if base is not None:
            conds.append(_fn("equal", _operands(lf, [sub(base), sub(i.this)], "CASE"), dt.boolean))
        else:
            c = sub(i.this)
            if not (c.type.is_boolean() or c.type.is_null()):
                raise Unsupported(f"CASE WHEN {_shown(i.this)}: a {c.type}, not a condition")
            conds.append(lf.to(c, dt.boolean).json)
    pairs = [(c, lf.to(r, t).json) for c, r in zip(conds, results, strict=True)]
    midnight = t.is_date() and any(r.midnight for r in [*results, dflt])
    return E(if_then(pairs, lf.to(dflt, t).json), t, midnight=midnight)


def _coalesce(lf: _Lift, node: sge.Coalesce, sub: Sub, scope: list[Column]) -> E:
    es = [sub(node.this), *(sub(a) for a in node.expressions)]
    t = lf.common(es, "COALESCE")
    if t.is_null():
        t = dt.int32
    midnight = t.is_date() and any(e.midnight for e in es)
    return E(_fn("coalesce", [lf.to(e, t).json for e in es], t), t, midnight=midnight)


def _cast(lf: _Lift, node: sge.Cast, sub: Sub, scope: list[Column]) -> E:
    if isinstance(node, sge.TryCast) or node.args.get("safe"):
        raise Unsupported("TRY_CAST is not supported yet")
    if node.args.get("format"):
        raise Unsupported("CAST … FORMAT is not supported")
    try:
        t: Any = DuckDBType.to_ibis(node.to).copy(nullable=True)
    except Exception as e:  # noqa: BLE001 - Ibis raises a variety
        raise Unsupported(f"CAST to {node.to.sql(DIALECT)} is not supported") from e
    if node.to.this in (sge.DataType.Type.INT128, sge.DataType.Type.UINT128):
        raise Unsupported(f"CAST to {node.to.sql(DIALECT)} (HUGEINT) is not supported")
    if t.is_array() and getattr(t, "length", None) is not None:
        raise Unsupported(f"CAST to the fixed-size array {node.to.sql(DIALECT)} is not supported")
    type_json(t)  # refuses the types outside the model
    a = sub(node.this)
    if a.constant and a.type.is_string() and (t.is_date() or t.is_timestamp()):
        return _temporal(a, t)
    if a.constant and a.type.is_string() and t.is_decimal():
        a = _number(a.value.strip())
    if t.is_integer() and (a.type.is_float64() or a.type.is_decimal()):
        rounding = lf.profile.float_to_int if a.type.is_float64() else lf.profile.decimal_to_int
        if rounding != "TRUNCATE":
            raise Unsupported(
                f"CAST of a {a.type} to {t} rounds ({rounding}) in DuckDB, which the "
                "model's casts (they truncate) cannot state yet; use semantics='reference', "
                "or round() first"
            )
    if t.is_decimal() and a.type.is_decimal() and t.scale < a.type.scale:
        raise Unsupported(f"CAST of a {a.type} to {t} rounds, which is not supported yet")
    # A numeric constant becomes a literal of the type, where that is exact
    # (not a double or decimal made an integer, nor one that doesn't fit).
    exact = not (t.is_integer() and not a.type.is_integer())
    if a.constant and a.value is not None and _numeric(a.type) and _numeric(t) and exact:
        with contextlib.suppress(Unsupported):
            return lf.to(a, t)
    if a.constant and a.type.is_date() and t.is_timestamp():
        return lf.to(a, t)  # the timestamp at the date's midnight
    return lf.to(E(a.json, a.type), t)


#: The units `date_trunc` truncates a timestamp to (`SubstraitLean/Time.lean`).
_TRUNC_UNITS = ("second", "minute", "hour", "day", "week", "month", "quarter", "year")


def _date_trunc(lf: _Lift, node: sge.TimestampTrunc, sub: Sub, scope: list[Column]) -> E:
    # DuckDB returns a timestamp, of a date too (the timestamp at its
    # midnight); weeks start on Monday.
    unit = node.args.get("unit")
    name = unit.name.lower() if isinstance(unit, sge.Var | sge.Literal) else None
    if name not in _TRUNC_UNITS:
        raise Unsupported(
            f"date_trunc to {_shown(unit) if unit is not None else '?'} is not supported; "
            f"the unit must be one of {', '.join(_TRUNC_UNITS)}"
        )
    a = sub(node.this)
    ts = dt.timestamp(scale=6)
    if a.type.is_date():
        # A DATE truncates to a date: to a day or less it is itself.
        if name in ("second", "minute", "hour", "day"):
            return E(a.json, dt.date, a.value, midnight=True)
        out = _fn("date_trunc", [literal(name, dt.string), a.json], dt.date)
        return E(out, dt.date, midnight=True)
    if not (a.type.is_timestamp() or a.type.is_null()):
        raise Unsupported(f"date_trunc of a {a.type} is not supported")
    if a.type.is_timestamp() and a.type.timezone is not None:
        raise Unsupported("timestamps with a time zone are not supported")
    return E(_fn("date_trunc", [literal(name, dt.string), lf.to(a, ts).json], ts), ts)


#: An interval unit as (months, microseconds) per unit.
_INTERVAL_UNITS = {
    "microsecond": (0, 1),
    "millisecond": (0, 1_000),
    "second": (0, 1_000_000),
    "minute": (0, 60_000_000),
    "hour": (0, 3_600_000_000),
    "day": (0, 86_400_000_000),
    "week": (0, 7 * 86_400_000_000),
    "month": (1, 0),
    "quarter": (3, 0),
    "year": (12, 0),
}


def _interval(lf: _Lift, node: sge.Interval, sub: Sub, scope: list[Column]) -> E:
    """A constant interval: `INTERVAL '10' MILLISECONDS`, `INTERVAL 1 DAY`,
    `INTERVAL '1 month 2 days'`."""
    unit, value = node.args.get("unit"), node.this
    text = value.this if isinstance(value, sge.Literal) else None
    if isinstance(unit, sge.Var) and text is not None:
        text = f"{text} {unit.name}"
    # `INTERVAL '1 month 2 days'`: integers, each with a unit.
    pairs = re.findall(r"(-?\d+)\s*([a-z]+)", (text or "").lower())
    rest = re.sub(r"(-?\d+)\s*([a-z]+)", "", (text or "").lower()).strip()
    units = [u.removesuffix("s") for _, u in pairs]
    if not pairs or rest or any(u not in _INTERVAL_UNITS for u in units):
        raise Unsupported(
            f"{_shown(node)} is not supported yet; an interval is integers, each with a "
            f"unit ({', '.join(_INTERVAL_UNITS)})"
        )
    parts = (0, 0)
    for (n, _), u in zip(pairs, units, strict=True):
        months, micros = _INTERVAL_UNITS[u]
        parts = (parts[0] + int(n) * months, parts[1] + int(n) * micros)
    return E(interval_json(*parts), dt.Interval(unit=IntervalUnit.MICROSECOND), parts)


_DAY = 86_400_000_000


def _add_months(d: dt_.date, months: int) -> dt_.date:
    """`d` plus `months`, clamped to the month's last day, as DuckDB adds
    (`DATE '2024-01-31' + INTERVAL 1 MONTH` is February 29)."""
    y, m = divmod(d.year * 12 + d.month - 1 + months, 12)
    last = (dt_.date(y + (m + 1) // 12, (m + 1) % 12 + 1, 1) - dt_.timedelta(days=1)).day
    return dt_.date(y, m + 1, min(d.day, last))


def _temporal_plus(name: str, a: E, b: E) -> E:
    """A timestamp or date plus or minus a constant interval. DuckDB's
    `DATE ± INTERVAL` is a TIMESTAMP; of whole days or months it is the date
    at midnight, which the plan holds as a date (`E.midnight`)."""
    if name == "add" and a.type.is_interval():
        a, b = b, a
    if name == "multiply" or not b.type.is_interval() or not b.constant:
        raise Unsupported(f"{name} of {a.type} and {b.type} is not supported yet")
    months, micros = b.value
    if name == "subtract":
        months, micros = -months, -micros
    ts = dt.timestamp(scale=6)
    if a.type.is_date():
        if a.constant:
            if a.value is None:
                return E(literal(None, ts), ts, None)
            d = _add_months(a.value, months)
            if micros % _DAY == 0:
                d += dt_.timedelta(days=micros // _DAY)
                return E(literal(d, dt.date), dt.date, d, midnight=True)
            v = dt_.datetime.combine(d, dt_.time()) + dt_.timedelta(microseconds=micros)
            return E(literal(v, ts), ts, v)
        if micros % _DAY != 0:
            raise Unsupported(
                "a DATE column plus an interval of hours or less is a TIMESTAMP, which needs a "
                "cast Lean lacks (#240)"
            )
        return E(_fn(name, [a.json, b.json], dt.date), dt.date, midnight=True)
    if not a.type.is_timestamp() or a.type.timezone is not None:
        raise Unsupported(f"{name} of {a.type} and an interval is not supported yet")
    return E(_fn(name, [a.json, b.json], ts), ts)


#: Date parts, by the names DuckDB's SQL gives them, as `Time.DatePart`'s.
_DATE_PARTS = {
    "year": "year",
    "quarter": "quarter",
    "month": "month",
    "week": "week",
    "weekofyear": "week",
    "day": "day",
    "dayofmonth": "day",
    "dow": "dow",
    "dayofweek": "dow",
    "doy": "doy",
    "dayofyear": "doy",
    "hour": "hour",
    "minute": "minute",
    "second": "second",
    "millisecond": "millisecond",
    "milliseconds": "millisecond",
    "microsecond": "microsecond",
    "microseconds": "microsecond",
}
_TIME_PARTS = ("hour", "minute", "second", "millisecond", "microsecond")


def _date_part(lf: _Lift, part: str, a: E) -> E:
    """`date_part(part, a)`, a BIGINT: DuckDB's parts, which Lean's are
    (ISO weeks, Sunday as day 0 of the week)."""
    p = _DATE_PARTS.get(part.lower())
    if p is None:
        raise Unsupported(f"the date part {part} is not supported yet")
    if a.type.is_date() and not a.midnight and p in _TIME_PARTS:
        raise Unsupported(f"the {p} of a DATE is not supported")
    if not (a.type.is_date() or a.type.is_timestamp() or a.type.is_null()):
        raise Unsupported(f"date parts of a {a.type} are not supported")
    if a.type.is_timestamp() and a.type.timezone is not None:
        raise Unsupported("timestamps with a time zone are not supported")
    if a.type.is_date() and p in _TIME_PARTS:
        return E(literal(0, dt.int64), dt.int64, 0)  # a DATE at midnight
    return E(_fn("date_part", [literal(p, dt.string), a.json], dt.int64), dt.int64)


def _extract(lf: _Lift, node: sge.Extract, sub: Sub, scope: list[Column]) -> E:
    return _date_part(lf, node.this.name, sub(node.expression))


def _part_fn(part: str) -> Callable[..., E]:
    """`year(d)`, `month(d)`, …"""
    return lambda lf, node, sub, scope: _date_part(lf, part, sub(node.this))


def _anonymous(lf: _Lift, node: sge.Anonymous, sub: Sub, scope: list[Column]) -> E:
    """The functions SQLGlot does not know but DuckDB has (`_KNOWN`)."""
    name = node.name.lower()
    args = node.expressions
    if name in _ANONYMOUS_STRINGS and len(args) == 2:
        return _ANONYMOUS_STRINGS[name](lf, [sub(a) for a in args])
    if name in ("date_part", "datepart") and len(args) == 2:
        part = args[0]
        if not (isinstance(part, sge.Literal) and part.is_string):
            raise Unsupported(f"{name} needs a constant part")
        return _date_part(lf, part.this, sub(args[1]))
    raise Unsupported(f"unknown function {node.name}(): DuckDB SQL here has no such function")


def _date_diff(lf: _Lift, node: sge.DateDiff, sub: Sub, scope: list[Column]) -> E:
    # DuckDB's `datediff('day', a, b)` is `b - a` in days.
    unit = node.args.get("unit")
    name = unit.name.lower() if unit is not None else "day"
    if name not in ("day", "days"):
        raise Unsupported(f"datediff in {name} is not supported yet")
    later, earlier = sub(node.this), sub(node.expression)
    for e in (later, earlier):
        if not e.type.is_date() or e.midnight:
            raise Unsupported(f"datediff of a {e.type} is not supported yet")
    return E(_fn("date_diff", [later.json, earlier.json], dt.int64), dt.int64)


# -- strings ---------------------------------------------------------------


def _strings(lf: _Lift, es: list[E], what: str) -> list[Json]:
    """Arguments that must be strings (a NULL is a string NULL)."""
    for e in es:
        if not (e.type.is_string() or e.type.is_null()):
            raise Unsupported(f"{what} of a {e.type} is not supported yet")
    return [lf.to(e, dt.string).json for e in es]


def _string_fn(name: str, out: Any = dt.string) -> Callable[..., E]:
    """A function of strings: `upper(s)`, `reverse(s)`, `starts_with(s, t)`, …"""

    def rule(lf: _Lift, node: sge.Expression, sub: Sub, scope: list[Column]) -> E:
        args = [node.this, *(a for a in [node.args.get("expression")] if a is not None)]
        return E(_fn(name, _strings(lf, [sub(a) for a in args], name), out), out)

    return rule


def _bool_json(lf: _Lift, e: E) -> Json:
    if not (e.type.is_boolean() or e.type.is_null()):
        raise Unsupported(f"NOT of a {e.type} is not supported")
    return lf.to(e, dt.boolean).json


def _reverse(lf: _Lift, node: sge.Reverse, sub: Sub, scope: list[Column]) -> E:
    raise Unsupported(
        "reverse is not supported yet: DuckDB reverses grapheme clusters, the model code points"
    )


def _length(lf: _Lift, node: sge.Length, sub: Sub, scope: list[Column]) -> E:
    # Characters (code points), a BIGINT; `strlen` (bytes) is another node.
    if node.args.get("binary"):
        raise Unsupported("the length of a BLOB is not supported")
    (s_,) = _strings(lf, [sub(node.this)], "length")
    return E(_fn("character_length", [s_], dt.int64), dt.int64)


def _trim(lf: _Lift, node: sge.Trim, sub: Sub, scope: list[Column]) -> E:
    # DuckDB trims spaces, or the characters given.
    position = (node.args.get("position") or "BOTH").upper()
    name = {"BOTH": "btrim", "LEADING": "ltrim", "TRAILING": "rtrim"}.get(position)
    if name is None or node.args.get("collation"):
        raise Unsupported(f"{_shown(node)} is not supported yet")
    chars = node.args.get("expression")
    s_, c = _strings(
        lf, [sub(node.this), sub(chars) if chars is not None else _const_str(" ")], name
    )
    return E(_fn(name, [s_, c], dt.string), dt.string)


def _const_str(v: str) -> E:
    return E(literal(v, dt.string), dt.string, v)


def _substring(lf: _Lift, node: sge.Substring, sub: Sub, scope: list[Column]) -> E:
    # DuckDB counts from 1, and from the end for a negative start: Substrait's
    # `negative_start` WRAP_FROM_END, the reference's default (#209 R13).
    s_ = sub(node.this)
    start, length = node.args.get("start"), node.args.get("length")
    args = _strings(lf, [s_], "substring")
    for a in (start, length):
        if a is None:
            continue
        e = sub(a)
        if not (e.type.is_integer() or e.type.is_null()):
            raise Unsupported(f"substring with a {e.type} position is not supported")
        if a is length and e.constant and e.value is not None and e.value < 0:
            raise Unsupported("substring with a negative length is not supported yet")
        args.append(lf.to(e, dt.int64).json)
    if start is None:
        raise Unsupported("substring needs a start")
    opt = _option("negative_start", "WRAP_FROM_END")
    return E(_fn("substring", args, dt.string, [opt]), dt.string)


def _strpos(lf: _Lift, node: sge.StrPosition, sub: Sub, scope: list[Column]) -> E:
    # 1-based, 0 if absent; `strpos(s, '')` is 1.
    if node.args.get("position") is not None or node.args.get("occurrence") is not None:
        raise Unsupported(f"{_shown(node)} is not supported yet")
    args = _strings(lf, [sub(node.this), sub(node.args["substr"])], "strpos")
    return E(_fn("strpos", args, dt.int64), dt.int64)


def _contains(lf: _Lift, node: sge.Contains, sub: Sub, scope: list[Column]) -> E:
    s_, t = _strings(lf, [sub(node.this), sub(node.expression)], "contains")
    pos = _fn("strpos", [s_, t], dt.int64)
    return E(_fn("gt", [pos, literal(0, dt.int64)], dt.boolean), dt.boolean)


def _like(name: str) -> Callable[..., E]:
    def rule(lf: _Lift, node: sge.Expression, sub: Sub, scope: list[Column]) -> E:
        # DuckDB's LIKE has no escape character without ESCAPE: a backslash
        # is itself. The model's (DataFusion's) escapes with a backslash, so
        # a pattern must be a constant without one.
        p = sub(node.expression)
        if not p.constant:
            raise Unsupported(f"{name.upper()} with a pattern that is not a constant")
        if isinstance(p.value, str) and "\\" in p.value:
            raise Unsupported(
                f"{name.upper()} with a backslash in the pattern is not supported yet"
            )
        args = _strings(lf, [sub(node.this), p], name)
        return E(_fn(name, args, dt.boolean), dt.boolean)

    return rule


def _dpipe(lf: _Lift, node: sge.DPipe, sub: Sub, scope: list[Column]) -> E:
    # `a || b` is NULL if either is.
    args = _strings(lf, [sub(node.this), sub(node.expression)], "||")
    return E(_fn("str_concat", args, dt.string), dt.string)


def _concat(lf: _Lift, node: sge.Concat, sub: Sub, scope: list[Column]) -> E:
    # `concat(…)` leaves out NULLs: '' for all of them.
    args = _strings(lf, [sub(a) for a in node.expressions], "concat")
    empty = literal("", dt.string)
    parts = [_fn("coalesce", [a, empty], dt.string) for a in args]
    return E(chain("str_concat", parts) if parts else empty, dt.string)


def _replace(lf: _Lift, node: sge.Replace, sub: Sub, scope: list[Column]) -> E:
    pattern, replacement = sub(node.expression), sub(node.args["replacement"])
    if not (pattern.constant and replacement.constant):
        raise Unsupported("replace needs a constant pattern and replacement")
    args = _strings(lf, [sub(node.this), pattern, replacement], "replace")
    return E(_fn("replace", args, dt.string), dt.string)


def _repeat(lf: _Lift, node: sge.Repeat, sub: Sub, scope: list[Column]) -> E:
    n = sub(node.args["times"])
    if not (n.type.is_integer() or n.type.is_null()):
        raise Unsupported(f"repeat by a {n.type} is not supported")
    (s_,) = _strings(lf, [sub(node.this)], "repeat")
    return E(_fn("repeat", [s_, lf.to(n, dt.int64).json], dt.string), dt.string)


def _left(lf: _Lift, node: sge.Left, sub: Sub, scope: list[Column]) -> E:
    # The first `n` characters; a negative `n` is not supported.
    n = sub(node.expression)
    if not (n.constant and isinstance(n.value, int) and n.value >= 0):
        raise Unsupported("left needs a constant count of 0 or more")
    (s_,) = _strings(lf, [sub(node.this)], "left")
    args = [s_, literal(1, dt.int64), literal(n.value, dt.int64)]
    return E(_fn("substring", args, dt.string), dt.string)


def _affix(name: str) -> Callable[[_Lift, list[E]], E]:
    """`prefix(s, t)`, `suffix(s, t)` (DuckDB's names)."""

    def rule(lf: _Lift, args: list[E]) -> E:
        return E(_fn(name, _strings(lf, args, name), dt.boolean), dt.boolean)

    return rule


_ANONYMOUS_STRINGS = {"prefix": _affix("starts_with"), "suffix": _affix("ends_with")}


def _scalar_subquery(lf: _Lift, node: sge.Subquery, sub: Sub, scope: list[Column]) -> E:
    # At most one row, which the checker must prove (an aggregate without
    # groups, LIMIT 1); no row is NULL.
    rel, cols = lf.nested(node.this, scope)
    if len(cols) != 1:
        raise Unsupported("a scalar subquery must return one column")
    return E({"subquery": {"scalar": {"input": rel}}}, cols[0].type.copy(nullable=True))


def _exists(lf: _Lift, node: sge.Exists, sub: Sub, scope: list[Column]) -> E:
    rel, _ = lf.nested(node.this, scope)
    exists_ = {"predicateOp": "PREDICATE_OP_EXISTS", "tuples": rel}
    return E({"subquery": {"setPredicate": exists_}}, dt.boolean)


# -- numbers ------------------------------------------------------------------


def _prefer(name: str, value: str) -> Json:
    """An option preferring `value`, then ERROR: DuckDB's behaviour first,
    which the model may not support, and the reference's, which it does. A
    plan whose rows may meet the difference "may raise" (#185); where
    `verify` rules that out, the two agree."""
    prefs = [value] if value == "ERROR" else [value, "ERROR"]
    return {"name": name, "preference": prefs}


def _doubles(lf: _Lift, es: list[E], what: str) -> list[Json]:
    """Numbers as doubles, as DuckDB's elementary functions take them."""
    for e in es:
        if not (_numeric(e.type) or e.type.is_null()):
            raise Unsupported(f"{what} of a {e.type} is not supported")
    return [lf.to(e, dt.float64).json for e in es]


#: Elementary functions of doubles, by SQLGlot's node: the model's name.
_ELEMENTARY: dict[type, str] = {
    cls: name
    for cls, name in (
        (getattr(sge, n, None), name)
        for n, name in (
            ("Sqrt", "sqrt"),
            ("Exp", "exp"),
            ("Ln", "ln"),
            ("Sin", "sin"),
            ("Cos", "cos"),
            ("Tan", "tan"),
            ("Asin", "asin"),
            ("Acos", "acos"),
            ("Atan", "atan"),
        )
    )
    if cls is not None
}
_LOGS = ("ln", "log10", "log2", "logb")


def _elementary_call(lf: _Lift, name: str, args: list[Json]) -> E:
    opts = [_prefer("on_domain_error", lf.profile.domain_error)]
    if name in _LOGS:
        opts.append(_prefer("on_log_zero", lf.profile.log_zero))
    return E(_fn(name, args, dt.float64, opts), dt.float64)


def _elementary(lf: _Lift, node: sge.Expression, sub: Sub, scope: list[Column]) -> E:
    name = _ELEMENTARY[type(node)]
    return _elementary_call(lf, name, _doubles(lf, [sub(node.this)], name))


def _log(lf: _Lift, node: sge.Log, sub: Sub, scope: list[Column]) -> E:
    # DuckDB's `log(x)` is base 10, `log(b, x)` base b; `log2`, `log10`
    # are SQLGlot's `Log` with the base set.
    if node.expression is None:
        return _elementary_call(lf, "log10", _doubles(lf, [sub(node.this)], "log"))
    base, x = node.this, node.expression
    if isinstance(base, sge.Literal) and base.this in ("2", "10"):
        return _elementary_call(lf, f"log{base.this}", _doubles(lf, [sub(x)], "log"))
    x_, b = _doubles(lf, [sub(x), sub(base)], "log")
    return _elementary_call(lf, "logb", [x_, b])


def _pow(lf: _Lift, node: sge.Pow, sub: Sub, scope: list[Column]) -> E:
    # DuckDB's `power` is of doubles, whatever its arguments.
    args = _doubles(lf, [sub(node.this), sub(node.expression)], "power")
    opts = [_prefer("on_domain_error", lf.profile.domain_error)]
    return E(_fn("power", args, dt.float64, opts), dt.float64)


def _abs(lf: _Lift, node: sge.Abs, sub: Sub, scope: list[Column]) -> E:
    a = sub(node.this)
    if not (_numeric(a.type) or a.type.is_null()):
        raise Unsupported(f"abs of a {a.type} is not supported")
    t = dt.int32 if a.type.is_null() else a.type
    return E(_fn("abs", [lf.to(a, t).json], t, _overflow(lf, t)), t)


def _rounding(name: str) -> Callable[..., E]:
    """`floor`, `ceil`, `round`: of a double, a double (an integer is one
    first for `floor` and `ceil`, as in DuckDB); `round` rounds halves away
    from zero, as DuckDB's of doubles does."""

    def rule(lf: _Lift, node: sge.Expression, sub: Sub, scope: list[Column]) -> E:
        a = sub(node.this)
        if a.type.is_decimal():
            raise Unsupported(f"{name} of a DECIMAL is not supported yet")
        digits = node.args.get("decimals") if name == "round" else None
        if name == "round" and a.type.is_integer() and digits is None:
            return a  # DuckDB's `round` of an integer is itself
        args = _doubles(lf, [a], name)
        if digits is not None:
            d = sub(digits)
            if not (d.constant and isinstance(d.value, int)):
                raise Unsupported("round needs a constant number of digits")
            if a.type.is_integer():
                raise Unsupported("round of an integer to digits is not supported yet")
            args.append(literal(d.value, dt.int32))
        return E(_fn(name, args, dt.float64), dt.float64)

    return rule


def _extremum(name: str) -> Callable[..., E]:
    def rule(lf: _Lift, node: sge.Expression, sub: Sub, scope: list[Column]) -> E:
        # DuckDB's `greatest` and `least` leave NULLs out.
        es = [sub(node.this), *(sub(a) for a in node.expressions)]
        t = lf.common(es, name)
        if t.is_null():
            t = dt.int32
        return E(_fn(f"{name}_skip_null", [lf.to(e, t).json for e in es], t), t)

    return rule


def _nullif(lf: _Lift, node: sge.Nullif, sub: Sub, scope: list[Column]) -> E:
    a, b = sub(node.this), sub(node.expression)
    t = lf.common([a, b], "nullif")
    if t.is_null():
        t = dt.int32
    return E(_fn("nullif", [lf.to(a, t).json, lf.to(b, t).json], t), t)


def _sign(lf: _Lift, node: sge.Sign, sub: Sub, scope: list[Column]) -> E:
    # A TINYINT: -1, 0 or 1; 0 for NaN, as DuckDB's.
    a = sub(node.this)
    if not (_numeric(a.type) or a.type.is_null()) or a.type.is_decimal():
        raise Unsupported(f"sign of a {a.type} is not supported yet")
    t = dt.int64 if a.type.is_null() else a.type
    x = lf.to(a, t).json
    i8 = dt.int8
    ifs = [
        (_fn("lt", [x, literal(0, t)], dt.boolean), literal(-1, i8)),
        (_fn("gt", [x, literal(0, t)], dt.boolean), literal(1, i8)),
    ]
    if t.is_float64():
        ifs.insert(0, (_fn("is_nan", [x], dt.boolean), literal(0, i8)))
    null = _fn("is_null", [x], dt.boolean)
    return E(if_then([(null, literal(None, i8)), *ifs], literal(0, i8)), i8)


def _isnan(lf: _Lift, node: sge.IsNan, sub: Sub, scope: list[Column]) -> E:
    # NULL for NULL, as in DuckDB.
    (x,) = _doubles(lf, [sub(node.this)], "isnan")
    return E(_fn("is_nan", [x], dt.boolean), dt.boolean)


def _distinct_from(negate: bool) -> Callable[..., E]:
    def rule(lf: _Lift, node: sge.Expression, sub: Sub, scope: list[Column]) -> E:
        args = _operands(lf, [sub(node.this), sub(node.expression)], "IS DISTINCT FROM")
        same = _fn("is_not_distinct_from", args, dt.boolean)
        return E(_fn("not", [same], dt.boolean) if negate else same, dt.boolean)

    return rule


_RULES: dict[type, Callable[..., E]] = {
    sge.Column: _column,
    sge.Literal: _literal,
    sge.Boolean: _boolean,
    sge.Null: _null,
    sge.Paren: _paren,
    sge.Neg: _neg,
    sge.Add: _arith,
    sge.Sub: _arith,
    sge.Mul: _arith,
    sge.Div: _div,
    sge.IntDiv: _int_div,
    sge.Mod: _mod,
    sge.EQ: _compare,
    sge.NEQ: _compare,
    sge.LT: _compare,
    sge.LTE: _compare,
    sge.GT: _compare,
    sge.GTE: _compare,
    sge.And: _logical("and"),
    sge.Or: _logical("or"),
    sge.Not: _not,
    sge.Is: _is,
    sge.Between: _between,
    sge.In: _in,
    sge.Case: _case,
    sge.Coalesce: _coalesce,
    sge.Cast: _cast,
    sge.TimestampTrunc: _date_trunc,
    sge.Interval: _interval,
    sge.Extract: _extract,
    sge.Anonymous: _anonymous,
    sge.DateDiff: _date_diff,
    sge.Subquery: _scalar_subquery,
    sge.Pow: _pow,
    sge.Abs: _abs,
    sge.Log: _log,
    sge.Floor: _rounding("floor"),
    sge.Ceil: _rounding("ceil"),
    sge.Round: _rounding("round"),
    sge.Greatest: _extremum("greatest"),
    sge.Least: _extremum("least"),
    sge.Nullif: _nullif,
    sge.Sign: _sign,
    sge.IsNan: _isnan,
    sge.NullSafeEQ: _distinct_from(False),
    sge.NullSafeNEQ: _distinct_from(True),
    **{cls: _elementary for cls in _ELEMENTARY},
    sge.Exists: _exists,
    sge.Length: _length,
    sge.Upper: _string_fn("upper"),
    sge.Lower: _string_fn("lower"),
    sge.Reverse: _reverse,
    sge.StartsWith: _string_fn("starts_with", dt.boolean),
    sge.EndsWith: _string_fn("ends_with", dt.boolean),
    sge.Trim: _trim,
    sge.Substring: _substring,
    sge.StrPosition: _strpos,
    sge.Contains: _contains,
    sge.Like: _like("like"),
    sge.ILike: _like("ilike"),
    sge.DPipe: _dpipe,
    sge.Concat: _concat,
    sge.Replace: _replace,
    sge.Repeat: _repeat,
    sge.Left: _left,
    **{
        cls: _part_fn(part)
        for cls, part in (
            (getattr(sge, n, None), part)
            for n, part in (
                ("Year", "year"),
                ("Quarter", "quarter"),
                ("Month", "month"),
                ("Week", "week"),
                ("WeekOfYear", "week"),
                ("Day", "day"),
                ("DayOfMonth", "day"),
                ("DayOfWeek", "dow"),
                ("DayOfYear", "doy"),
                ("Hour", "hour"),
                ("Minute", "minute"),
                ("Second", "second"),
            )
        )
        if cls is not None
    },
}


#: Ranking window functions: the Substrait name and the type (DuckDB's).
_RANKING: dict[type, tuple[str, Any]] = {
    sge.RowNumber: ("row_number", dt.int64),
    sge.Rank: ("rank", dt.int64),
    sge.DenseRank: ("dense_rank", dt.int64),
    sge.PercentRank: ("percent_rank", dt.float64),
    sge.CumeDist: ("cume_dist", dt.float64),
    sge.Ntile: ("ntile", dt.int64),
}


def _frame(w: sge.Window, ordered: bool) -> Json:
    """The frame: the one written, else DuckDB's default, from the start of
    the partition to the current row and its peers with an ORDER BY (RANGE),
    the whole partition without."""
    spec = w.args.get("spec")
    if spec is None:
        upper = {"currentRow": {}} if ordered else {"unbounded": {}}
        return {
            "lowerBound": {"unbounded": {}},
            "upperBound": upper,
            "boundsType": "BOUNDS_TYPE_RANGE",
        }
    if spec.args.get("exclude"):
        raise Unsupported("a window frame with EXCLUDE is not supported")
    kind = (spec.args.get("kind") or "").upper()
    if kind not in ("ROWS", "RANGE"):
        raise Unsupported(f"{kind} frames are not supported")

    def bound(value: Any, side: str | None) -> Json:
        if isinstance(value, str) and value.upper() == "UNBOUNDED":
            return {"unbounded": {}}
        if value is None or (isinstance(value, str) and value.upper() == "CURRENT ROW"):
            return {"currentRow": {}}
        if not (isinstance(value, sge.Literal) and not value.is_string and value.this.isdigit()):
            raise Unsupported(f"frame offset {value} is not supported; use an integer constant")
        n = int(value.this)
        if n == 0:
            return {"currentRow": {}}
        return {(side or "preceding").lower(): {"offset": str(n)}}

    return {
        "lowerBound": bound(spec.args.get("start"), spec.args.get("start_side")),
        "upperBound": bound(spec.args.get("end"), spec.args.get("end_side")),
        "boundsType": f"BOUNDS_TYPE_{kind}",
    }


def _windows(nodes: list[sge.Expression | None]) -> list[sge.Window]:
    """The window functions in `nodes`, each once, in order; not those of
    subqueries."""
    found: list[sge.Window] = []
    for n in nodes:
        if n is None:
            continue
        for w in n.find_all(sge.Window):
            nested = any(isinstance(p, sge.Subquery | sge.Select) for p in _parents(w, n))
            if not nested and w not in found:
                found.append(w)
    return found


def _parents(node: Any, top: Any) -> list[Any]:
    out: list[Any] = []
    p = node.parent
    while p is not None and p is not top:
        out.append(p)
        p = p.parent
    return out


def _aggregates(nodes: list[sge.Expression | None]) -> list[sge.Expression]:
    """The aggregate calls in `nodes`, each once, in order; not those of
    subqueries."""
    found: list[sge.Expression] = []

    def walk(n: sge.Expression) -> None:
        if isinstance(n, sge.Window):
            # The window's own function is not an aggregate of the query; an
            # aggregate in its arguments, partitions or order is.
            for child in [*n.this.iter_expressions(), *n.iter_expressions()]:
                if child is not n.this:
                    walk(child)
            return
        if isinstance(n, sge.Subquery | sge.Select):
            return
        if isinstance(n, sge.Filter) and type(n.this) in _AGGREGATES:
            if n not in found:
                found.append(n)
            return
        if type(n) in _AGGREGATES:
            if any(type(a) in _AGGREGATES for a in n.find_all(*_AGGREGATES) if a is not n):
                raise Unsupported(f"nested aggregates ({_shown(n)}) are not allowed")
            if n not in found:
                found.append(n)
            return
        if isinstance(n, sge.AggFunc):
            raise Unsupported(f"aggregate {n.sql_name()}() is not supported yet")
        for child in n.iter_expressions():
            walk(child)

    for n in nodes:
        if n is not None:
            walk(n)
    return found


def _count(node: sge.Expression, what: str) -> int:
    if isinstance(node, sge.Literal) and not node.is_string and node.this.isdigit():
        return int(node.this)
    raise Unsupported(f"{what} must be a non-negative integer constant")


def _normalized(name: str) -> str:
    """A table or column name as `qualify` normalizes it: DuckDB's names are
    case-insensitive."""
    return normalize_identifiers(sge.to_identifier(name), dialect=DIALECT).name


# --------------------------------------------------------------------------
# Entry point


def lift(query: str, schemas: Mapping[str, Any], semantics: str = "duckdb") -> Lifted:
    """The plan of the DuckDB SQL `query` over input tables of the Ibis
    schemas `schemas` (by table name), read as named tables, with the
    `semantics` profile ("duckdb" or "reference").

    Raises:
        Unsupported: The query is outside the subset, saying what.
        ValueError: `semantics` is not a profile.
    """
    profile = PROFILES.get(semantics)
    if profile is None:
        raise ValueError(f"semantics must be one of {', '.join(PROFILES)}, not {semantics!r}")
    if profile.null_ordering != sg.Dialect.get_or_raise(DIALECT).NULL_ORDERING:
        raise Unsupported("SQLGlot's DuckDB dialect no longer sorts NULLs as DuckDB does")
    tree = parse(query, schemas)
    with compiling() as compiler:
        rel, cols = _Lift(profile, schemas).query(tree)
        out = plan(compiler, rel, [c.name for c in cols])
    names = [c.name for c in cols]
    if len(set(names)) != len(names):
        dup = next(n for n in names if names.count(n) > 1)
        raise Unsupported(f"the query has two output columns named {dup}; alias one of them")
    # Every output column may be NULL, as the plan's computed values are
    # (a LEFT JOIN's right side, an aggregate of no rows, …).
    schema = ibis.schema(
        {c.name: (dt.int32 if c.type.is_null() else c.type.copy(nullable=True)) for c in cols}
    )
    return Lifted(out, schema)
