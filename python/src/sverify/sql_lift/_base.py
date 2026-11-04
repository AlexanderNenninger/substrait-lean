"""The lift's shared parts (`sverify.sql_lift`): profiles, the generated lift
table, parsing, the `_Lift` class, which lifts the relations (reads, joins,
set operations, aggregates, windows, sorts, limits), the helpers the areas
share, and `RULES`, the rule of each expression node, which each area's module
fills with `register`."""

from __future__ import annotations

import copy
import dataclasses
import datetime as dt_
import re
from collections.abc import Callable, Mapping, Sequence
from decimal import Decimal, localcontext
from typing import Any

import ibis
import ibis.expr.datatypes as dt
import sqlglot as sg
import sqlglot.expressions as sge
from ibis.backends.sql.datatypes import DuckDBType
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
    column_of,
    compiling,
    decimal_literal,
    distinct_rel,
    emit_rel,
    field_ref,
    if_then,
    literal,
    plan,
    project_rel,
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
        avg_integer: The output type of `avg` of integers: `"fp64"` (#209
            R6, the plan's declared type).
        overflow: Integer `+ - *`, negation, `//` and `sum` that leave the
            declared width: `"ERROR"` (DuckDB, and #185's reference default).
        on_division_by_zero: `//` and `%` by zero: `"ERROR"` (DuckDB with
            `error_on_division_by_zero`, its default, and the reference).
        float_division_by_zero: `/` by zero, which divides doubles:
            `"ERROR"` (reference). DuckDB's `/` is the generated lift's.
        float_to_int: A cast of a double to an integer: `"TIE_TO_EVEN"`
            (DuckDB rounds, `CAST(2.5 AS INT)` is 2) or `"TRUNCATE"`
            (reference, #209 R9).
        decimal_to_int: A cast of a decimal to an integer:
            `"TIE_AWAY_FROM_ZERO"` (DuckDB, `CAST(2.5 AS INT)` is 3) or
            `"TRUNCATE"` (reference, R9).
        domain_error: Elementary functions and `power` outside their domain
            (`sqrt(-1)`, `power(-8, 1/3)`): `"NAN"` (DuckDB) or `"ERROR"`
            (reference, #257).
        log_zero: A logarithm of 0: `"MINUS_INFINITY"` (DuckDB) or `"ERROR"`
            (reference).
        corr_degenerate: `CORR` of one pair or of a side whose values are
            all equal: `"NAN"` (DuckDB, `duckdb-corr`) or `"NULL"`
            (reference, `corrOf`). Of no pairs it is NULL in both.
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
    domain_error: str = "ERROR"
    log_zero: str = "ERROR"
    corr_degenerate: str = "NULL"


DUCKDB = Profile(
    "duckdb",
    float_to_int="TIE_TO_EVEN",
    decimal_to_int="TIE_AWAY_FROM_ZERO",
    domain_error="NAN",
    log_zero="MINUS_INFINITY",
    corr_degenerate="NAN",
)
REFERENCE = Profile("reference")
PROFILES = {p.name: p for p in (DUCKDB, REFERENCE)}


# --------------------------------------------------------------------------
# The generated lift (#268)
#
# With DuckDB's semantics, the constructs the generated lift table covers are
# lifted as the table says: Lean generates each entry and proves it means
# what DuckDB computes (`SubstraitLean/LiftDuckDB.lean`), NaN and ±inf
# included, and `substrait-check --lift-table` exports it. The rules below
# that say "pending generation" are still written by hand.


@dataclasses.dataclass(frozen=True)
class LiftTable:
    """The DuckDB semantics' part of `substrait-check --lift-table`.

    Attributes:
        functions: The templates' function anchors: the functions' names.
        scalars: By construct (`"DOUBLE / DOUBLE"`): the entry, with its
            `args` and `result` types and its `template` or why it is
            `refused`.
        aggregates: By construct (`"avg(BIGINT)"`): its `measures` and the
            `finish` over them.
    """

    functions: Mapping[int, str]
    scalars: Mapping[str, Json]
    aggregates: Mapping[str, Json]


_LIFT_TABLE: list[LiftTable] = []


def lift_table() -> LiftTable:
    """The generated lift table, read from the checker once."""
    if not _LIFT_TABLE:
        import json
        import subprocess

        from sverify.engine import checker_path

        out = subprocess.run(
            [str(checker_path()), "--lift-table"], capture_output=True, text=True, check=True
        ).stdout
        raw = json.loads(out)
        _LIFT_TABLE.append(
            LiftTable(
                {f["anchor"]: f["name"].split(":")[0] for f in raw["functions"]},
                {e["construct"]: e for e in raw["lift"] if e["semantics"] == "duckdb"},
                {
                    e["construct"]: e["aggregate"]
                    for e in raw["aggregates"]
                    if e["semantics"] == "duckdb" and e["aggregate"] is not None
                },
            )
        )
    return _LIFT_TABLE[0]


#: The table's types.
_TABLE_TYPES: dict[str, Any] = {
    "i8": dt.int8,
    "i64": dt.int64,
    "fp64": dt.float64,
    "boolean": dt.boolean,
}


def _instantiate(template: Any, args: Sequence[Json]) -> Any:
    """A template (or a part of one) with its field references `i` replaced
    by `args[i]`, and its functions anchored in the plan being built."""
    if isinstance(template, list):
        return [_instantiate(t, args) for t in template]
    if not isinstance(template, dict):
        return template
    sel = template.get("selection")
    if isinstance(sel, dict) and "rootReference" in sel:
        return copy.deepcopy(args[sel["directReference"]["structField"].get("field", 0)])
    out: dict[str, Any] = {k: _instantiate(v, args) for k, v in template.items()}
    if "functionReference" in out:
        functions: Mapping[int, str] = lift_table().functions
        out["functionReference"] = anchor(functions[out["functionReference"]])
    return out


def _generated(lf: _Lift, construct: str, args: Sequence[E]) -> E | None:
    """`construct` of `args` as the generated table lifts it with DuckDB's
    semantics (the arguments brought to its types first), or None with the
    reference's semantics, whose rules are written by hand. Raises
    `Unsupported` where the table refuses it."""
    if lf.profile is not DUCKDB:
        return None
    entry = lift_table().scalars[construct]
    if "refused" in entry:
        raise Unsupported(f"{construct}: {entry['refused']}")
    ts = [_TABLE_TYPES[a] for a in entry["args"]]
    js = [lf.to(a, t).json for a, t in zip(args, ts, strict=True)]
    return E(_instantiate(entry["template"], js), _TABLE_TYPES[entry["result"]])


@dataclasses.dataclass(frozen=True)
class Measures:
    """An aggregate as measures and the value computed from their columns.

    Attributes:
        parts: Each measure's function name, argument and output type.
        finish: The aggregate's value from the measures' columns.
    """

    parts: list[tuple[str, list[Json], Any]]
    finish: Callable[[list[Json]], E]


def _generated_avg(lf: _Lift, a: E) -> Measures | None:
    """DuckDB's `avg` of an integer as the generated table lifts it (the
    exact sum and the count, divided as doubles), or None with the
    reference's semantics."""
    if lf.profile is not DUCKDB or not a.type.is_integer():
        return None
    table = lift_table()
    agg = table.aggregates["avg(BIGINT)"]
    x = lf.to(a, dt.int64).json
    parts = []
    for m in agg["measures"]:
        m = m["measure"]
        args = [_instantiate(v["value"], [x]) for v in m["arguments"]]
        out = _TABLE_TYPES[next(iter(m["outputType"]))]
        parts.append((table.functions[m["functionReference"]], args, out))
    count = [f for f, _, _ in parts].index("count")

    def finish(refs: list[Json]) -> E:
        # A group whose values are all NULL has a count of 0 and a NULL sum,
        # so the quotient is NULL; the guard says so, for the check that
        # nothing divides by zero (#434).
        value = _instantiate(agg["finish"], refs)
        nonempty = call("gt", [refs[count], literal(0, dt.int64)])
        return E(if_then([(nonempty, value)], literal(None, dt.float64)), dt.float64)

    return Measures(parts, finish)


# --------------------------------------------------------------------------
# Parsing and typing


def _sql_type(dtype: Any) -> str:
    return DuckDBType.from_ibis(dtype).sql(DIALECT)


def expand_table_shorthand(query: str) -> str:
    """`query` with DuckDB's `TABLE t` (`SELECT * FROM t`) written out where a
    query may stand: at the start, after `(`, or as an operand of `UNION`,
    `EXCEPT` or `INTERSECT`. SQLGlot does not parse the shorthand
    (upstream/bugs/SG-6.json); DuckDB's tests use it to compare results."""
    from sqlglot.tokens import TokenType

    try:
        tokens = sg.Dialect.get_or_raise(DIALECT).tokenize(query)
    except sg.errors.TokenError:
        return query
    starts = {TokenType.L_PAREN, TokenType.UNION, TokenType.EXCEPT, TokenType.INTERSECT,
              TokenType.ALL, TokenType.DISTINCT}  # fmt: skip
    names = {TokenType.VAR, TokenType.IDENTIFIER}
    out, last, i = [], 0, 0
    while i < len(tokens):
        tok = tokens[i]
        prev = tokens[i - 1].token_type if i else None
        if tok.token_type == TokenType.TABLE and (prev is None or prev in starts):
            j = i + 1
            if j < len(tokens) and tokens[j].token_type in names:
                while (
                    j + 2 < len(tokens)
                    and tokens[j + 1].token_type == TokenType.DOT
                    and tokens[j + 2].token_type in names
                ):
                    j += 2
                name = query[tokens[i + 1].start : tokens[j].end + 1]
                out += [query[last : tok.start], f"(SELECT * FROM {name})"]
                last = tokens[j].end + 1
                i = j
        i += 1
    return "".join(out) + query[last:]


def parse(query: str, schemas: Mapping[str, Any]) -> sge.Select | sge.SetOperation:
    """`query` parsed as DuckDB SQL, at SQLGlot's strict error level, with
    every name resolved (`qualify`) and typed (`annotate_types`) against the
    tables `schemas` (Ibis schemas by table name).

    Raises:
        Unsupported: SQLGlot cannot parse the query, or a name in it is not
            a column or table of the inputs.
    """
    _check_numbers(query)
    query = expand_table_shorthand(query)
    try:
        tree = sg.parse_one(query, read=DIALECT, error_level=ErrorLevel.RAISE)
    except sg.errors.ParseError as e:
        raise Unsupported(f"cannot parse the SQL as DuckDB's: {str(e).splitlines()[0]}") from e
    for rewrite in PARSE_REWRITES:
        tree = rewrite(tree)
    for f in tree.find_all(sge.Anonymous):
        if f.name.lower() not in _KNOWN:
            raise Unsupported(f"unknown function {f.name}(): DuckDB SQL here has no such function")
    _check_aliases(tree, schemas)
    _check_using_stars(tree)
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
    if not isinstance(tree, sge.Select | sge.SetOperation):
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
    # The variance family (#433), as the Ibis producer writes them (#54):
    # each engine's own algorithm, of doubles or of integers converted.
    sge.Variance: "variance",
    sge.VariancePop: "variance",
    sge.Stddev: "std_dev",
    sge.StddevSamp: "std_dev",
    sge.StddevPop: "std_dev",
    sge.CovarSamp: "covar_samp",
    sge.CovarPop: "covar_pop",
    sge.Corr: "corr",
    # Exact quantiles, the mode and arg_min/arg_max (#53). DuckDB's `quantile`
    # is `quantile_disc`.
    sge.Median: "median",
    sge.PercentileCont: "quantile_cont",
    sge.PercentileDisc: "quantile_disc",
    sge.Quantile: "quantile_disc",
    sge.Mode: "mode",
    sge.ArgMin: "arg_min",
    sge.ArgMax: "arg_max",
}

#: The aggregates that need every value of a group, which `_Lift.holistic`
#: reads (#53).
_HOLISTIC = {"median", "quantile_cont", "quantile_disc", "mode", "arg_min", "arg_max"}

#: The variance family's population measures; the others are a sample's.
_POPULATION = (sge.VariancePop, sge.StddevPop)

#: Aggregates of a pair of values.
_PAIRED = {"covar_samp", "covar_pop", "corr"}

#: Joins with a condition, by SQLGlot's (side, kind).
#: The arguments of a table or subquery in FROM that the lift reads.
_SOURCE_ARGS = {"this", "alias", "db", "catalog"}

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
        if isinstance(node, sge.SetOperation):
            return self.set_op(node)
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
        parts = [*node.expressions, node.args.get("having"), node.args.get("order")]
        aggs = _aggregates(parts)
        groupings = _groupings(node, parts)
        bound: Bound = Bound()
        if group is not None or aggs:
            rel, scope, bound = self.aggregate(rel, scope, group, aggs, groupings)
            if (having := node.args.get("having")) is not None:
                cond = self.condition(having.this, scope, bound)
                rel = {"filter": {"input": rel, "condition": cond}}
        elif node.args.get("having") is not None:
            raise Unsupported("HAVING without GROUP BY or an aggregate")
        if wins := _windows([*node.expressions, node.args.get("order")]):
            rel, scope, bound = self.windows(rel, scope, bound, wins)
        if explodes := _explodes(node.expressions):
            if group is not None or aggs or wins:
                raise Unsupported("UNNEST next to an aggregate or a window is not supported yet")
            rel, scope, bound = self.unnest(rel, scope, bound, explodes)

        outs = [self.expr(e.unalias(), scope, bound) for e in node.expressions]
        names = [e.alias_or_name for e in node.expressions]
        outs = [
            self.timestamp_of(e, n) if e.midnight else e for e, n in zip(outs, names, strict=True)
        ]
        # Sort keys that are not output columns are computed after them, and
        # dropped after the sort.
        keys: list[Json] = []
        extra_keys: list[E] = []
        # In an ORDER BY expression, a bare name is the output column of that
        # name, as in DuckDB (`qualify` leaves it bare).
        aliased = Bound(bound, grouped=bound.grouped)
        for n, e in zip(names, outs, strict=True):
            aliased.setdefault(sge.column(n), e)
        if (order := node.args.get("order")) is not None:
            for o in order.expressions:
                i = self.output_index(o.this, names, node.expressions)
                if i is None:
                    if distinct is not None:
                        raise Unsupported(
                            f"ORDER BY {_shown(o.this)} of a SELECT DISTINCT must be an "
                            "output column"
                        )
                    extra_keys.append(self.expr(o.this, scope, aliased))
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

    def unnest(
        self, rel: Json, scope: list[Column], bound: Bound, explodes: list[sge.Explode]
    ) -> tuple[Json, list[Column], Bound]:
        """`UNNEST(l)` in the select list (#348): one row per element of `l`,
        the other columns repeated, and no row for a NULL or empty list
        (`Rel.unnest`). The list is computed as a column, unnested in place."""
        if len(set(explodes)) != 1:
            raise Unsupported("more than one UNNEST in a SELECT is not supported yet")
        node = explodes[0]
        if node.args.get("expressions"):
            raise Unsupported(f"{_shown(node)} with options is not supported yet")
        x = self.expr(node.this, scope, bound)
        if not x.type.is_array():
            raise Unsupported(f"UNNEST of a {x.type} is not supported")
        width = len(scope)
        rel = {"project": {"input": rel, "expressions": [x.json]}}
        detail = {"@type": "type.googleapis.com/sverify.Unnest", "column": width}
        rel = {"extensionSingle": {"input": rel, "detail": detail}}
        elem = x.type.value_type
        out = Bound(bound, grouped=bound.grouped)
        out[node] = E(field_ref(width), elem)
        return rel, [*scope, Column(None, "", elem)], out

    def set_op(self, node: sge.SetOperation) -> tuple[Json, list[Column]]:
        """`UNION`, `EXCEPT`, `INTERSECT` [`ALL`] (#344): the branches at
        their common column types, named as the first. `UNION` is the model's
        union; `INTERSECT` and `EXCEPT` keep the left rows with (without) an
        equal right row, NULLs equal, by a semi (anti) join. With `ALL`, each
        side's equal rows are numbered first and the number joins too, so
        `m` and `n` copies leave `min(m, n)` (`max(m - n, 0)`)."""
        what = type(node).__name__.upper()
        if node.args.get("by_name"):
            raise Unsupported(f"{what} BY NAME is not supported yet")
        allowed = ("this", "expression", "distinct", "order", "limit", "offset")
        unknown = [k for k, v in node.args.items() if v and k not in allowed]
        if unknown:
            raise Unsupported(f"{what} with {', '.join(sorted(unknown))} is not supported")
        left, lcols = self.query(node.this)
        right, rcols = self.query(node.expression)
        if len(lcols) != len(rcols):
            raise Unsupported(f"{what} of {len(lcols)} and {len(rcols)} columns")
        n = len(lcols)
        types = [
            self.common([E(field_ref(i), a.type), E(field_ref(i), b.type)], what)
            for i, (a, b) in enumerate(zip(lcols, rcols, strict=True))
        ]

        def at_types(rel: Json, cols: list[Column]) -> Json:
            if all(_same(c.type, t) for c, t in zip(cols, types, strict=True)):
                return rel
            exprs = [
                self.to(E(field_ref(i), c.type), t).json
                for i, (c, t) in enumerate(zip(cols, types, strict=True))
            ]
            return select(rel, n, exprs)

        left, right = at_types(left, lcols), at_types(right, rcols)
        distinct = node.args.get("distinct") is not False
        if isinstance(node, sge.Union):
            op = "SET_OP_UNION_DISTINCT" if distinct else "SET_OP_UNION_ALL"
            rel: Json = {"set": {"inputs": [left, right], "op": op}}
        else:
            width = n if distinct else n + 1
            if not distinct:
                left, right = _numbered(left, n), _numbered(right, n)
            same = [
                _fn("is_not_distinct_from", [field_ref(i), field_ref(width + i)], dt.boolean)
                for i in range(width)
            ]
            cond = same[0]
            for c in same[1:]:
                cond = _fn("and", [cond, c], dt.boolean)
            how = (
                "JOIN_TYPE_LEFT_SEMI" if isinstance(node, sge.Intersect) else "JOIN_TYPE_LEFT_ANTI"
            )
            rel = {"join": {"left": left, "right": right, "expression": cond, "type": how}}
            rel = distinct_rel(rel, n) if distinct else emit_rel(rel, list(range(n)))
        cols = [Column(None, c.name, t) for c, t in zip(lcols, types, strict=True)]
        names = [c.name for c in cols]
        # Sort keys that are not output columns are expressions over them,
        # computed after them and dropped after the sort.
        extra: list[E] = []
        if (order := node.args.get("order")) is not None:
            keys = []
            for o in order.expressions:
                i = self.output_index(o.this, names, [sge.column(nm) for nm in names])
                if i is None:
                    extra.append(self.expr(o.this, cols, Bound()))
                    i = n + len(extra) - 1
                desc = bool(o.args.get("desc"))
                nulls = "FIRST" if o.args.get("nulls_first") else "LAST"
                direction = f"SORT_DIRECTION_{'DESC' if desc else 'ASC'}_NULLS_{nulls}"
                keys.append({"expr": field_ref(i), "direction": direction})
            if extra:
                rel = {"project": {"input": rel, "expressions": [e.json for e in extra]}}
            rel = {"sort": {"input": rel, "sorts": keys}}
        rel = self.fetch(rel, node)
        if extra:
            rel = emit_rel(rel, list(range(n)))
        return rel, cols

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

    def fetch(self, rel: Json, node: sge.Select | sge.SetOperation) -> Json:
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
            if method := join.args.get("method"):
                # Not the inner join of its ON: an ASOF join keeps each left
                # row's latest match, a POSITIONAL join pairs rows by position.
                raise Unsupported(f"{str(method).upper()} JOIN is not supported yet")
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
        # SQLGlot hangs a table's TABLESAMPLE, PIVOT and FROM-first joins on
        # the table itself; read none of them as the plain table.
        extra = sorted(k for k, v in node.args.items() if v and k not in _SOURCE_ARGS)
        if extra and isinstance(node, sge.Table | sge.Subquery):
            raise Unsupported(f"FROM {_shown(node)} with {', '.join(extra)} is not supported yet")
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
                return self.ntile(w, n.value, scope, bound, column)
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
        elif _AGGREGATES.get(type(f)) in ("variance", "std_dev", *_PAIRED, *_HOLISTIC):
            # Lean's `parseWindow` refuses them too.
            raise Unsupported(f"{_shown(f)} over a window is not supported")
        elif type(f) in AGG_RULES:
            raise Unsupported(f"{_shown(f)} over a window is not supported yet")
        elif type(f) in _AGGREGATES:
            # Each measure over the window, with its type (DuckDB's AVG of a
            # DECIMAL is a DOUBLE).
            ms, finish = self.measure(f, scope, bound)
            fns = []
            for m, t in ms:
                agg = m["measure"]
                if agg["invocation"] != "AGGREGATION_INVOCATION_ALL":
                    raise Unsupported(f"{_shown(w)}: DISTINCT in a window is not supported")
                values = [column(E(a["value"], dt.null)) for a in agg["arguments"]]
                fn = self.window_json(w, agg["functionReference"], values, scope, bound, column)
                fn["windowFunction"]["outputType"] = agg["outputType"]
                fns.append((fn, t))
            return fns, finish
        else:
            raise Unsupported(f"window function {_shown(f)} is not supported yet")
        fn = self.window_json(w, name, args, scope, bound, column)
        return [(fn, out)], lambda refs: E(refs[0], out)

    def window_json(
        self,
        w: sge.Window,
        name: str | int,
        args: list[Json],
        scope: list[Column],
        bound: Mapping[sge.Expression, E],
        column: Callable[[E], Json],
        frame: Json | None = None,
    ) -> Json:
        """A window function; its partitions and sort keys as columns (the
        model reads them so), computed before it where they are not."""
        partitions = [column(self.expr(p, scope, bound)) for p in w.args.get("partition_by") or []]
        order = w.args.get("order")
        sorts = []
        for o in order.expressions if order is not None else []:
            desc = bool(o.args.get("desc"))
            nulls = "FIRST" if o.args.get("nulls_first") else "LAST"
            sorts.append(
                {
                    "expr": column(self.expr(o.this, scope, bound)),
                    "direction": f"SORT_DIRECTION_{'DESC' if desc else 'ASC'}_NULLS_{nulls}",
                }
            )
        fn = {
            "functionReference": anchor(name) if isinstance(name, str) else name,
            "partitions": partitions,
            "sorts": sorts,
            "arguments": [{"value": a} for a in args],
            **(frame or _frame(w, bool(sorts))),
        }
        return {"windowFunction": fn}

    def ntile(
        self,
        w: sge.Window,
        k: int,
        scope: list[Column],
        bound: Mapping[sge.Expression, E],
        column: Callable[[E], Json],
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
        rn = self.window_json(w, "row_number", [], scope, bound, column)
        count = self.window_json(w, "count", [], scope, bound, column, whole)
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
        groupings: list[sge.Grouping],
    ) -> tuple[Json, list[Column], Bound]:
        """The aggregate relation, its columns, and the expressions that are
        its columns (each grouping key, each aggregate and each
        `GROUPING(…)`)."""
        keys, sets = _grouping_sets(group)
        groups = [self.expr(k, scope) for k in keys]
        measures = [self.measure(a, scope) for a in aggs]
        parts = [p for ms, _ in measures for p in ms]
        if len(sets) == 1 and not groupings:
            body: Json = {
                "input": rel,
                "groupingExpressions": [g.json for g in groups],
                "groupings": (
                    [{"expressionReferences": list(range(len(groups)))}] if groups else []
                ),
                "measures": [m for m, _ in parts],
            }
            agg: Json = {"aggregate": body}
        else:
            agg = self.grouping_sets(rel, keys, groups, sets, parts, groupings)
        types = [g.type for g in groups] + [t for _, t in parts] + [dt.int64] * len(groupings)
        bound = Bound(
            {k: E(field_ref(i), types[i], midnight=groups[i].midnight) for i, k in enumerate(keys)},
            grouped=True,
        )
        j = len(keys)
        for a, (ms, finish) in zip(aggs, measures, strict=True):
            bound[a] = finish([field_ref(j + i) for i in range(len(ms))])
            j += len(ms)
        for g in groupings:
            bound[g] = E(field_ref(j), dt.int64)
            j += 1
        cols = [Column(None, f"_{i}", t) for i, t in enumerate(types)]
        return agg, cols, bound

    def grouping_sets(
        self,
        rel: Json,
        keys: list[sge.Expression],
        groups: list[E],
        sets: list[list[int]],
        parts: list[tuple[Json, Any]],
        groupings: list[sge.Grouping],
    ) -> Json:
        """GROUP BY with several grouping sets (or `GROUPING(…)`): one
        aggregate per set, each with every key (NULL where the set leaves it
        out), the measures, and the value of each `GROUPING(…)` in that set,
        all UNION ALL'd, as DuckDB computes them."""
        branches = []
        for s in sets:
            ms = [copy.deepcopy(m) for m, _ in parts]
            if not s and not ms:
                # The model's aggregate without keys needs a measure.
                ms = [_count_star()]
            body = {
                "input": copy.deepcopy(rel),
                "groupingExpressions": [copy.deepcopy(groups[i].json) for i in s],
                "groupings": [{"expressionReferences": list(range(len(s)))}] if s else [],
                "measures": ms,
            }
            exprs = [
                field_ref(s.index(i)) if i in s else literal(None, g.type)
                for i, g in enumerate(groups)
            ]
            exprs += [field_ref(len(s) + j) for j in range(len(parts))]
            exprs += [literal(_grouping_value(g, keys, s), dt.int64) for g in groupings]
            branches.append(project_rel({"aggregate": body}, len(s) + len(ms), exprs))
        return {"set": {"inputs": branches, "op": "SET_OP_UNION_ALL"}}

    def measure(
        self,
        node: sge.Expression,
        scope: list[Column],
        bound: Mapping[sge.Expression, E] | None = None,
    ) -> tuple[list[tuple[Json, Any]], Callable[[list[Json]], E]]:
        """An aggregate's measures (JSON and type), and its value from their
        columns: one measure, or with DuckDB's semantics, those the generated
        lift computes `avg` of an integer from."""
        where = None
        if isinstance(node, sge.Filter):
            # `agg(…) FILTER (WHERE c)`: the rows where `c` is TRUE.
            where = self.condition(node.expression.this, scope, bound)
            node = node.this
        name = _AGGREGATES[type(node)]
        if name in _HOLISTIC:
            return self.holistic(node, name, where, scope, bound)
        agg_rule = AGG_RULES.get(type(node))
        arg = node.this
        distinct = isinstance(arg, sge.Distinct)
        if distinct:
            if len(arg.expressions) != 1:
                raise Unsupported(f"{_shown(node)}: DISTINCT of several values is not supported")
            arg = arg.expressions[0]
        if isinstance(node, sge.Count) and (arg is None or isinstance(arg, sge.Star)):
            args: list[E] = []
            out: Any = dt.int64
        elif name in _PAIRED:
            if distinct:
                raise Unsupported(f"{_shown(node)}: DISTINCT is not supported")
            args = [self.expr(a, scope, bound) for a in (arg, node.expression)]
            for a in args:
                if not (a.type.is_integer() or a.type.is_float64()):
                    raise Unsupported(f"{name} of {a.type} is not supported")
            out = dt.float64
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
            if agg_rule is not None:
                name, out = agg_rule(self, node, a)
            elif name == "count":
                out = dt.int64
            elif name in ("min", "max"):
                out = t
            elif not _numeric(t):
                raise Unsupported(f"{name} of {t} is not supported")
            elif name in ("variance", "std_dev"):
                if t.is_decimal():
                    raise Unsupported(f"{_shown(node)}: {name} of a DECIMAL is not supported yet")
                out = dt.float64
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
        invocation = "AGGREGATION_INVOCATION_DISTINCT" if distinct else "AGGREGATION_INVOCATION_ALL"
        if name == "avg" and (gen := _generated_avg(self, args[0])):
            # DISTINCT and FILTER apply to each measure alike.
            parts = [
                {
                    "functionReference": anchor(f),
                    "arguments": [{"value": j} for j in js],
                    "outputType": type_json(t),
                    "invocation": invocation,
                }
                for f, js, t in gen.parts
            ]
            types, finish = [t for _, _, t in gen.parts], gen.finish
        elif name == "corr" and self.profile.corr_degenerate == "NAN":
            return _nan_corr(args, out, invocation, where)
        else:
            # Pending generation (#268), but for `avg` of an integer.
            parts = [
                {
                    "functionReference": anchor(name),
                    "arguments": [{"value": a.json} for a in args],
                    "outputType": type_json(out),
                    **({"options": _overflow(self, out)} if name == "sum" else {}),
                    **(
                        {"options": [_distribution(isinstance(node, _POPULATION))]}
                        if name in ("variance", "std_dev")
                        else {}
                    ),
                    "invocation": invocation,
                }
            ]
            types, finish = [out], lambda refs: E(refs[0], out)
        filt = {"filter": where} if where is not None else {}
        return [({"measure": m, **filt}, t) for m, t in zip(parts, types, strict=True)], finish

    def holistic(
        self,
        node: sge.Expression,
        name: str,
        where: Json | None,
        scope: list[Column],
        bound: Mapping[sge.Expression, E] | None,
    ) -> tuple[list[tuple[Json, Any]], Callable[[list[Json]], E]]:
        """`median`, `quantile_cont`/`quantile_disc`, `mode` and `arg_min`/
        `arg_max` (#53), as `Parse.parseMeasure` reads them: a quantile's
        fraction is a decimal constant, `mode` needs an `ORDER BY` to break
        its ties, and `arg_min` orders by a column."""
        arg = node.this
        order = None
        if isinstance(arg, sge.Order):
            # `mode(x ORDER BY …)`
            order, arg = arg, arg.this
        distinct = isinstance(arg, sge.Distinct)
        if distinct:
            if len(arg.expressions) != 1:
                raise Unsupported(f"{_shown(node)}: DISTINCT of several values is not supported")
            arg = arg.expressions[0]
        if arg is None:
            raise Unsupported(f"{_shown(node)} needs an argument")
        a = self.expr(arg, scope, bound)
        if a.midnight:
            raise Unsupported(
                f"{_shown(node)}: an aggregate of a DATE at midnight that DuckDB types a "
                "TIMESTAMP is not supported yet (#240)"
            )
        t = a.type
        args = [a.json]
        sorts: list[Json] = []
        if name == "median" and not _numeric(t):
            # DuckDB's median of other ordered values is the 0.5 quantile_disc.
            name = "quantile_disc"
            args.append(decimal_literal("0.5", dt.Decimal()))
        elif name in ("quantile_cont", "quantile_disc"):
            q = node.args.get("quantile") or node.expression
            if isinstance(q, sge.Neg):
                # DuckDB reads a negative fraction from the largest value.
                raise Unsupported(f"{_shown(node)}: the fraction must be between 0 and 1")
            if not (isinstance(q, sge.Literal) and not q.is_string):
                raise Unsupported(f"{_shown(node)}: the fraction must be one number")
            if not 0 <= Decimal(q.this) <= 1:
                raise Unsupported(f"{_shown(node)}: the fraction must be between 0 and 1")
            args.append(decimal_literal(q.this, dt.Decimal()))
        if name in ("median", "quantile_cont"):
            if t.is_decimal():
                raise Unsupported(
                    f"{_shown(node)} of a DECIMAL is not supported yet (DuckDB interpolates "
                    "it as a DECIMAL); cast it to DOUBLE"
                )
            if not (t.is_integer() or t.is_float64()):
                raise Unsupported(f"{_shown(node)} of {t} is not supported")
            out: Any = dt.float64
        else:
            out = t
        if name == "mode":
            if order is None:
                raise Unsupported(
                    f"{_shown(node)} breaks ties in the engine's order; give it an order "
                    "(mode(x ORDER BY x) takes the smallest of the most frequent values)"
                )
            for o in order.expressions:
                key = self.expr(o.this, scope, bound).json
                if "selection" not in key:
                    raise Unsupported(f"{_shown(node)}: ORDER BY a column only")
                desc = bool(o.args.get("desc"))
                nulls = "FIRST" if o.args.get("nulls_first") else "LAST"
                sorts.append(
                    {"expr": key, "direction": f"SORT_DIRECTION_{'DESC' if desc else 'ASC'}_NULLS_{nulls}"}
                )
        elif order is not None:
            raise Unsupported(f"{_shown(node)}: ORDER BY in {name} is not supported")
        if name in ("arg_min", "arg_max"):
            if distinct:
                raise Unsupported(f"{_shown(node)}: DISTINCT is not supported")
            by = self.expr(node.expression, scope, bound).json
            if "selection" not in by:
                raise Unsupported(f"{_shown(node)} orders by a column only")
            args.append(by)
        measure: Json = {
            "functionReference": anchor(name),
            "arguments": [{"value": j} for j in args],
            "outputType": type_json(out),
            "invocation": (
                "AGGREGATION_INVOCATION_DISTINCT" if distinct else "AGGREGATION_INVOCATION_ALL"
            ),
            **({"sorts": sorts} if sorts else {}),
        }
        filt = {"filter": where} if where is not None else {}
        return [({"measure": measure, **filt}, out)], lambda refs: E(refs[0], out)

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
        rule = RULES.get(type(node))
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
                    # A double's exact binary value: `_fits` folds it only
                    # where the decimal holds it exactly (10.0, 2.5, not 0.1).
                    v = Decimal(v)
                elif t.is_integer() and isinstance(v, Decimal):
                    v = None if v != v.to_integral_value() else int(v)
                elif t.is_timestamp() and type(v) is dt_.date:
                    v = dt_.datetime.combine(v, dt_.time())
            # A constant becomes a literal of `t` only where it fits; else
            # the cast is written, which raises where DuckDB's does.
            if (v is not None and _fits(v, t)) or e.value is None:
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
#: A rule lifts one node type: `rule(lf, node, sub, scope)`.
Rule = Callable[..., E]

#: The rule of each node type. Each area (`sql_lift/<area>.py`) registers its
#: own; `sverify.sql_lift` imports them all.
RULES: dict[type, Rule] = {}

#: Rewrites of the parsed tree, before its functions are checked: the black
#: boxes' (`blackbox.py`, #325) give their calls nodes of their own.
PARSE_REWRITES: list[Callable[[sge.Expr], sge.Expr]] = []

#: The aggregates of nodes of their own (the black boxes', #325), each also in
#: `_AGGREGATES`: the Substrait function and output type of a measure, from
#: the node and its lifted argument.
AGG_RULES: dict[type, Callable[[_Lift, sge.Expression, E], tuple[str, Any]]] = {}


def register(rules: Mapping[type, Rule]) -> None:
    """Add one area's rules to `RULES`; each node type has one rule."""
    if dup := RULES.keys() & rules.keys():
        raise ValueError(f"rules registered twice: {sorted(t.__name__ for t in dup)}")
    RULES.update(rules)


def _fits(v: Any, t: Any) -> bool:
    """Whether the value `v` is one of `t`'s: an integer in its bounds, a
    decimal with at most its digits."""
    if t.is_integer():
        return isinstance(v, int) and t.bounds.lower <= v <= t.bounds.upper
    if t.is_decimal():
        d = Decimal(v)
        with localcontext() as ctx:
            ctx.prec = 100  # past DECIMAL(38)'s digits, so nothing rounds
            exact = d.quantize(Decimal(1).scaleb(-t.scale)) == d
            return exact and abs(d) < Decimal(1).scaleb(t.precision - t.scale)
    return True


def _overflow(lf: _Lift, t: Any) -> list[Json]:
    """`overflow` for exact arithmetic (integers, decimals) at the declared
    width; doubles have none."""
    return [] if t.is_float64() else [_option("overflow", lf.profile.overflow)]


def _nan_corr(
    args: list[E], out: Any, invocation: str, where: Json | None
) -> tuple[list[tuple[Json, Any]], Callable[[list[Json]], E]]:
    """DuckDB's `CORR` (`duckdb-corr`): the reference's, but NaN where that
    is NULL and some pair has no NULL (one pair, or a side whose values are
    all equal). Two measures: the correlation, and a count of those pairs."""
    pair = _fn(
        "and",
        [_fn("not", [_fn("is_null", [a.json], dt.boolean)], dt.boolean) for a in args],
        dt.boolean,
    )
    corr = {
        "functionReference": anchor("corr"),
        "arguments": [{"value": a.json} for a in args],
        "outputType": type_json(out),
        "invocation": invocation,
    }
    pairs = {
        "functionReference": anchor("count"),
        "arguments": [],
        "outputType": type_json(dt.int64),
        "invocation": "AGGREGATION_INVOCATION_ALL",
    }
    both = pair if where is None else _fn("and", [where, pair], dt.boolean)
    measures = [
        ({"measure": corr, **({"filter": where} if where is not None else {})}, out),
        ({"measure": pairs, "filter": both}, dt.int64),
    ]

    def finish(refs: list[Json]) -> E:
        r, n = refs
        degenerate = _fn(
            "and",
            [
                _fn("is_null", [r], dt.boolean),
                _fn("gt", [n, literal(0, dt.int64)], dt.boolean),
            ],
            dt.boolean,
        )
        return E(if_then([(degenerate, literal(float("nan"), dt.float64))], r), out)

    return measures, finish


def _distribution(population: bool) -> Json:
    """The variance family's `distribution`: a sample's or a population's."""
    return _option("distribution", "POPULATION" if population else "SAMPLE")


def _bool_json(lf: _Lift, e: E) -> Json:
    if not (e.type.is_boolean() or e.type.is_null()):
        raise Unsupported(f"NOT of a {e.type} is not supported")
    return lf.to(e, dt.boolean).json


def _explodes(parts: list[sge.Expression | None]) -> list[sge.Explode]:
    """The `UNNEST`s of the select list (SQLGlot's `Explode`)."""
    return [x for p in parts if p is not None for x in p.find_all(sge.Explode)]


def _numbered(rel: Json, n: int) -> Json:
    """`rel` (of `n` columns) with a column numbering its equal rows 1, 2, …:
    `ROW_NUMBER() OVER (PARTITION BY` every column`)`. Equal rows are the
    same, so which gets which number does not matter."""
    fn = {
        "functionReference": anchor("row_number"),
        "partitions": [field_ref(i) for i in range(n)],
        "sorts": [],
        "arguments": [],
        "lowerBound": {"unbounded": {}},
        "upperBound": {"unbounded": {}},
        "boundsType": "BOUNDS_TYPE_ROWS",
    }
    return {"project": {"input": rel, "expressions": [{"windowFunction": fn}]}}


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
        if isinstance(n, sge.Grouping):
            return  # a column of the grouping sets, not a measure
        if isinstance(n, sge.AggFunc):
            raise Unsupported(f"aggregate {n.sql_name()}() is not supported yet")
        for child in n.iter_expressions():
            walk(child)

    for n in nodes:
        if n is not None:
            walk(n)
    return found


def _groupings(select: sge.Select, nodes: list[sge.Expression | None]) -> list[sge.Grouping]:
    """The `GROUPING(…)` calls of `select` in `nodes`, each once, in order;
    not those of subqueries."""
    found: list[sge.Grouping] = []
    for n in nodes:
        for g in n.find_all(sge.Grouping) if n is not None else ():
            if g.find_ancestor(sge.Select) in (select, None) and g not in found:
                found.append(g)
    return found


def _grouping_sets(group: sge.Group | None) -> tuple[list[sge.Expression], list[list[int]]]:
    """GROUP BY's keys, each once, and its grouping sets, as indices into
    them: one set for a plain GROUP BY; ROLLUP, CUBE and GROUPING SETS give
    several, and several of those listed give their cross product."""
    keys: list[sge.Expression] = []

    def index(e: sge.Expression) -> int:
        for i, k in enumerate(keys):
            if k == e:
                return i
        keys.append(e)
        return len(keys) - 1

    def element(e: sge.Expression) -> list[int]:
        # An element of ROLLUP or CUBE: a key, or a tuple of keys.
        return [index(x) for x in e.expressions] if isinstance(e, sge.Tuple) else [index(e)]

    def sets_of(item: sge.Expression) -> list[list[int]]:
        if isinstance(item, sge.Rollup):
            es = [element(e) for e in item.expressions]
            return [[k for e in es[:n] for k in e] for n in range(len(es), -1, -1)]
        if isinstance(item, sge.Cube):
            es = [element(e) for e in item.expressions]
            n = len(es)
            return [
                [k for j, e in enumerate(es) if not mask >> (n - 1 - j) & 1 for k in e]
                for mask in range(2**n)
            ]
        if isinstance(item, sge.GroupingSets):
            return [s for x in item.expressions for s in sets_of(x)]
        if isinstance(item, sge.Tuple):
            return [[index(e) for e in item.expressions]]
        if isinstance(item, sge.Paren):
            return [[index(item.this)]]
        return [[index(item)]]

    # SQLGlot before 30.18 keeps ROLLUP, CUBE and GROUPING SETS in their own
    # arguments; later versions list them with the keys (#442).
    items = [] if group is None else [
        *group.expressions,
        *(x for a in ("grouping_sets", "cube", "rollup") for x in group.args.get(a) or []),
    ]  # fmt: skip
    sets: list[list[int]] = [[]]
    for item in items:
        sets = [a + [k for k in b if k not in a] for a in sets for b in sets_of(item)]
    return keys, sets


def _grouping_value(node: sge.Grouping, keys: list[sge.Expression], s: list[int]) -> int:
    """`GROUPING(a, b, …)` in the grouping set `s`: a bit per argument, the
    first the highest, set where the set leaves the key out."""
    value = 0
    for a in node.expressions:
        i = next((i for i, k in enumerate(keys) if k == a), None)
        if i is None:
            raise Unsupported(f"{_shown(node)}: GROUPING of {_shown(a)}, which is not a key")
        value = value * 2 + (i not in s)
    return value


def _count_star() -> Json:
    return {
        "measure": {
            "functionReference": anchor("count"),
            "arguments": [],
            "outputType": type_json(dt.int64),
            "invocation": "AGGREGATION_INVOCATION_ALL",
        }
    }


#: Quoted text (strings, quoted names) and comments, which hold no numbers.
_QUOTED = re.compile(r"'(?:[^']|'')*'|\"(?:[^\"]|\"\")*\"|--[^\n]*|/\*.*?\*/", re.S)
#: A number as written, from its first digit (not inside a name).
_NUMBER = re.compile(r"(?<![\w$.])\d[\w.]*")


def _check_numbers(query: str) -> None:
    """Refuse a number with an underscore that is not between two digits
    (`1__2`, `1._5`). DuckDB reads such an underscore as the start of an
    alias (`1__2` is 1 named `__2`); SQLGlot reads every underscore as a digit
    separator (12), upstream/bugs/SG-4.json."""
    for m in _NUMBER.finditer(_QUOTED.sub(" ", query)):
        if re.search(r"(?<!\d)_|_(?!\d)", m.group()):
            raise Unsupported(
                f"the number {m.group()!r}: an underscore not between two digits is read "
                "differently by DuckDB and SQLGlot"
            )


def _check_using_stars(tree: Any) -> None:
    """Refuse `t.*` in a SELECT whose joins have USING: `qualify` leaves the
    USING columns out of the right table's `t.*`, where DuckDB keeps them."""
    for node in tree.find_all(sge.Select):
        if not any(j.args.get("using") for j in node.args.get("joins") or []):
            continue
        for e in node.expressions:
            if isinstance(e, sge.Column) and isinstance(e.this, sge.Star) and e.table:
                raise Unsupported(
                    f"{e.table}.* with JOIN … USING is not supported yet; list the columns"
                )


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
    for c in cols:
        if c.type.is_interval():
            # The model holds an interval as microseconds; DuckDB keeps its
            # months, days and microseconds apart (`INTERVAL 2 DAYS` is not
            # `48:00:00`), and the written plan returns the microseconds.
            raise Unsupported(f"the INTERVAL output column {c.name} is not supported yet")
    # Every output column may be NULL, as the plan's computed values are
    # (a LEFT JOIN's right side, an aggregate of no rows, …).
    schema = ibis.schema(
        {c.name: (dt.int32 if c.type.is_null() else c.type.copy(nullable=True)) for c in cols}
    )
    return Lifted(out, schema)
