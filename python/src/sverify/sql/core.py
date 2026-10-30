"""Substrait plans as SQL, with the semantics of the Lean `Rel` model.

`to_sql(plan, dialect)` reads a Substrait JSON plan the way
`SubstraitLean/Parse.lean` does, so it accepts exactly the plans the checker
accepts: the same operators, the same functions and the same constant folding,
with every other construct rejected (`Unsupported`). It then writes one SQL
query whose result is `Rel.eval` of the plan. Nothing is left to engine
defaults:

* Every subquery names its columns positionally (`c0`, `c1`, …), so field
  references are unambiguous whatever the input tables call their columns.
* Integers are `BIGINT`: operands are cast, and arithmetic must raise on
  overflow (Lean's integers are unbounded; a wrapped result would be wrong).
  Division and remainder truncate. Where DataFusion fails at run time
  (division by zero, `MIN / -1`, a bad `POWER` or `CAST(double AS BIGINT)`),
  Lean's value is NULL and `SubstraitLean/Safety.lean` says when that can
  happen; the SQL raises there too (`Dialect.raise_`).
* Doubles compare by the total order of `SubstraitLean/Float.lean`
  (`-NaN < -inf < … < -0.0 < +0.0 < … < inf < NaN`, NaN equal to itself), in
  comparisons, join conditions, window partitions and sort keys.
* Filters keep a row only when the condition is TRUE, `AND`/`OR`/`NOT` are
  Kleene's, and every `ORDER BY` key says where NULLs go.
* Row order follows `Rel.eval`'s list order wherever it matters. Below a
  `FETCH` or a window, subqueries carry an ordinal column `o`: scan order for
  tables, row index for `VALUES`, left-major for joins, branch order for
  `UNION ALL` and sort order for windows. Window sorts break ties by it, as
  Lean's stable merge sort does, and the query's result is ordered by it when
  the plan has a `FETCH` or a window.

Engines differ in syntax and in a few semantics; those go through the hooks of
a `Dialect` (see `sverify.sql.duckdb`).
"""

from __future__ import annotations

import base64
import json
import math
import re
from collections.abc import Callable, Sequence
from dataclasses import dataclass
from datetime import date, datetime, timedelta
from fractions import Fraction
from typing import Any, Literal

I64_MIN, I64_MAX = -(2**63), 2**63 - 1

Kind = Literal["int", "float", "time", "date", "interval", "str", "bool"]
"""What a value is in SQL. `time` is a microsecond TIMESTAMP without time
zone, `interval` a day/second interval of microseconds. `None` (unknown) is
used for columns whose Substrait type the model does not know."""

LeanKind = Literal["int", "float", "time", "date", "str", "bool", "other"]
"""`Parse.Kind`: what Lean's parser knows about a value. The parser decides
between integer and double arithmetic by it, so this module tracks it too."""


class Unsupported(ValueError):
    """The plan is outside the Lean model, or the dialect cannot express it."""


# --------------------------------------------------------------------------
# Dialects


@dataclass(frozen=True)
class Dialect:
    """SQL syntax and semantics of one engine.

    Every hook takes SQL text for its operands (each already self-contained,
    e.g. parenthesised) and returns SQL text. The defaults are ANSI SQL;
    subclasses override what their engine writes differently and raise
    `Unsupported` for what it cannot do.
    """

    name: str

    # Identifiers and types

    def quote(self, ident: str) -> str:
        return '"' + ident.replace('"', '""') + '"'

    def type_name(self, kind: Kind) -> str:
        return {
            "int": "BIGINT",
            "float": "DOUBLE PRECISION",
            "time": "TIMESTAMP",
            "date": "DATE",
            "interval": "INTERVAL",
            "str": "VARCHAR",
            "bool": "BOOLEAN",
        }[kind]

    def cast(self, sql: str, kind: Kind) -> str:
        return f"CAST({sql} AS {self.type_name(kind)})"

    # Literals

    def null(self, kind: Kind | None) -> str:
        return "NULL" if kind is None else self.cast("NULL", kind)

    def bool_lit(self, b: bool) -> str:
        return "TRUE" if b else "FALSE"

    def int_lit(self, i: int) -> str:
        """A BIGINT constant; `i` is in the 64-bit range."""
        return self.cast(str(i), "int")

    def float_lit(self, f: float) -> str:
        """A double, including NaN and -NaN (sign bit set), ±inf and -0.0."""
        if math.isnan(f) or f == 0:
            positive = self.cast("'NaN'" if math.isnan(f) else "'0'", "float")
            return self.float_neg(positive) if math.copysign(1.0, f) < 0 else positive
        if math.isinf(f):
            return self.cast("'Infinity'" if f > 0 else "'-Infinity'", "float")
        return self.cast(f"'{f!r}'", "float")

    def str_lit(self, s: str) -> str:
        return "'" + s.replace("'", "''") + "'"

    def timestamp_lit(self, micros: int) -> str:
        return f"TIMESTAMP '{_timestamp_text(micros)}'"

    def date_lit(self, days: int) -> str:
        return f"DATE '{_date_text(days)}'"

    def interval_lit(self, micros: int) -> str:
        sign = "-" if micros < 0 else ""
        d, rest = divmod(abs(micros), 86_400_000_000)
        s, us = divmod(rest, 1_000_000)
        h, s = divmod(s, 3600)
        m, s = divmod(s, 60)
        return f"INTERVAL '{sign}{d} {h:02}:{m:02}:{s:02}.{us:06}' DAY TO SECOND"

    # Integer arithmetic on BIGINT operands; must raise on 64-bit overflow.

    def int_add(self, a: str, b: str) -> str:
        return f"({a} + {b})"

    def int_sub(self, a: str, b: str) -> str:
        return f"({a} - {b})"

    def int_mul(self, a: str, b: str) -> str:
        return f"({a} * {b})"

    def int_neg(self, a: str) -> str:
        return f"(- {a})"

    def raise_(self, message: str, dep: str, kind: Kind) -> str:
        """An expression of type `kind` that fails at run time with `message`
        when evaluated (and is NULL when `dep` is NULL). Only evaluated in a
        `CASE` branch that needs it."""
        raise Unsupported(f"{self.name} has no way to raise an error at run time")

    def trunc_div(self, a: str, b: str) -> str:
        """`a / b` rounded toward zero, for `b <> 0`; must raise on `MIN / -1`."""
        raise Unsupported(f"{self.name}: integer division is not implemented")

    def trunc_mod(self, a: str, b: str) -> str:
        """The remainder of `trunc_div`, with the sign of `a`, for `b` not 0 or -1."""
        raise Unsupported(f"{self.name}: integer remainder is not implemented")

    def int_div(self, a: str, b: str) -> str:
        """`BinFn.idiv`: truncating; division by zero raises (Lean: NULL)."""
        fail = self.raise_("division by zero", b, "int")
        return f"(CASE WHEN {b} = {self.int_lit(0)} THEN {fail} ELSE {self.trunc_div(a, b)} END)"

    def int_mod(self, a: str, b: str) -> str:
        """`BinFn.imod`: the sign of `a`; by zero raises (Lean: NULL), by -1 is 0."""
        fail = self.raise_("division by zero", b, "int")
        zero = self.int_mul(a, self.int_lit(0))
        return (
            f"(CASE WHEN {b} = {self.int_lit(0)} THEN {fail} WHEN {b} = {self.int_lit(-1)} "
            f"THEN {zero} ELSE {self.trunc_mod(a, b)} END)"
        )

    def int_pow(self, a: str, b: int) -> str:
        """`BinFn.ipow` with a constant exponent: a negative exponent, or a
        result outside 64 bits, raises (Lean: NULL); NULL stays NULL."""
        null = self.null("int")
        if b < 0:
            fail = self.raise_("negative exponent", a, "int")
            return f"(CASE WHEN {a} IS NULL THEN {null} ELSE {fail} END)"
        if b > 64:
            # Only -1, 0 and 1 have powers that fit; `a * a` is |a| for them.
            small = a if b % 2 else self.int_mul(a, a)
            fail = self.raise_("integer overflow", a, "int")
            lo, hi = self.int_lit(-1), self.int_lit(1)
            return (
                f"(CASE WHEN {a} IS NULL THEN {null} WHEN {a} >= {lo} AND {a} <= {hi} "
                f"THEN {small} ELSE {fail} END)"
            )
        if b == 0:
            return f"(CASE WHEN {a} IS NULL THEN {null} ELSE {self.int_lit(1)} END)"
        # Partial products grow in magnitude, so checked multiplication raises
        # exactly when the result leaves 64 bits.
        out = a
        for _ in range(b - 1):
            out = self.int_mul(out, a)
        return out

    def int_product(self, a: str, n: str) -> str:
        """`a` multiplied `n` times (1 ≤ n ≤ 64), raising on 64-bit overflow."""
        raise Unsupported(f"{self.name}: POWER with a non-constant exponent is not implemented")

    def int_pow_var(self, a: str, b: str) -> str:
        """`BinFn.ipow` with an exponent column: as `int_pow`, row by row."""
        null, one = self.null("int"), self.int_lit(1)
        lo, sixty_four = self.int_lit(-1), self.int_lit(64)
        small = (
            f"(CASE WHEN {self.trunc_mod(b, self.int_lit(2))} = {one} "
            f"THEN {a} ELSE {self.int_mul(a, a)} END)"
        )
        big = (
            f"(CASE WHEN {a} >= {lo} AND {a} <= {one} THEN {small} "
            f"ELSE {self.raise_('integer overflow', a, 'int')} END)"
        )
        return (
            f"(CASE WHEN {a} IS NULL OR {b} IS NULL THEN {null} "
            f"WHEN {b} < {self.int_lit(0)} THEN {self.raise_('negative exponent', b, 'int')} "
            f"WHEN {b} = {self.int_lit(0)} THEN {one} WHEN {b} > {sixty_four} THEN {big} "
            f"ELSE {self.int_product(a, b)} END)"
        )

    # Doubles: IEEE 754, so x / 0 is ±inf or NaN rather than an error.

    def float_add(self, a: str, b: str) -> str:
        return f"({a} + {b})"

    def float_sub(self, a: str, b: str) -> str:
        return f"({a} - {b})"

    def float_mul(self, a: str, b: str) -> str:
        return f"({a} * {b})"

    def float_div(self, a: str, b: str) -> str:
        return f"({a} / {b})"

    def float_neg(self, a: str) -> str:
        return f"(- {a})"

    def int_to_float(self, a: str) -> str:
        return self.cast(a, "float")

    def int_to_str(self, a: str) -> str:
        """Decimal digits with a leading `-` for negatives (Lean's `toString`)."""
        return self.cast(a, "str")

    def float_floor(self, x: str) -> str:
        """Exact; keeps the sign of a zero result and NaN/±inf as they are."""
        return f"FLOOR({x})"

    def float_ceil(self, x: str) -> str:
        """Exact; `CEIL(-0.5)` is -0.0; NaN/±inf stay."""
        return f"CEIL({x})"

    def float_round(self, x: str) -> str:
        """To an integer, halves away from zero; `ROUND(-0.4)` is -0.0."""
        return f"ROUND({x})"

    def float_round_to(self, x: str, digits: int) -> str:
        """`ROUND(x, d)` as DataFusion computes it: `round(x · 10ᵈ) / 10ᵈ`."""
        p = self.float_lit(10.0**digits)
        return self.float_div(self.float_round(self.float_mul(x, p)), p)

    def float_pow(self, a: str, b: str) -> str:
        """C's `pow`: IEEE results, no errors."""
        return f"POWER({a}, {b})"

    def float_to_int(self, x: str) -> str:
        """`CAST(x AS BIGINT)`: truncation toward zero; NaN, ±inf and values
        outside 64 bits must raise (Lean: NULL)."""
        raise Unsupported(f"{self.name}: CAST(double AS BIGINT) is not implemented")

    def is_nan(self, x: str) -> str:
        """TRUE for NaN of either sign, NULL for NULL."""
        return f"({x} <> {x})"

    def sign_bit(self, x: str) -> str:
        """TRUE when the sign bit is set (also for -0.0 and -NaN), NULL for NULL."""
        raise Unsupported(f"{self.name} has no way to read the sign bit of a double")

    def float_rank(self, x: str) -> str:
        """-1 for -NaN, 1 for NaN, 0 for other doubles, NULL for NULL: the
        coarse part of the total order."""
        return (
            f"(CASE WHEN {x} IS NULL THEN NULL WHEN {self.is_nan(x)} THEN "
            f"(CASE WHEN {self.sign_bit(x)} THEN -1 ELSE 1 END) ELSE 0 END)"
        )

    def float_eq(self, a: str, b: str) -> str:
        """Equality in the total order: NaN = NaN, -0.0 <> +0.0."""
        ra, rb = self.float_rank(a), self.float_rank(b)
        return (
            f"({ra} = {rb} AND ({ra} <> 0 OR {a} = {b}) "
            f"AND {self.sign_bit(a)} = {self.sign_bit(b)})"
        )

    def float_lt(self, a: str, b: str) -> str:
        """`<` in the total order: -NaN < -inf < … < -0.0 < +0.0 < … < inf < NaN."""
        ra, rb = self.float_rank(a), self.float_rank(b)
        return (
            f"({ra} < {rb} OR ({ra} = 0 AND {rb} = 0 AND ({a} < {b} OR ({a} = {b} "
            f"AND {self.sign_bit(a)} AND NOT {self.sign_bit(b)}))))"
        )

    # Timestamps and intervals

    def time_add_interval(self, ts: str, iv: str) -> str:
        return f"({ts} + {iv})"

    def time_sub_interval(self, ts: str, iv: str) -> str:
        return f"({ts} - {iv})"

    def time_diff(self, a: str, b: str) -> str:
        """`a - b` for timestamps, as an interval."""
        return f"({a} - {b})"

    def interval_add(self, a: str, b: str) -> str:
        return f"({a} + {b})"

    def interval_sub(self, a: str, b: str) -> str:
        return f"({a} - {b})"

    # Three-valued logic and comparisons (NULL-propagating)

    def eq(self, a: str, b: str) -> str:
        return f"({a} = {b})"

    def lt(self, a: str, b: str) -> str:
        return f"({a} < {b})"

    def and3(self, a: str, b: str) -> str:
        return f"({a} AND {b})"

    def or3(self, a: str, b: str) -> str:
        return f"({a} OR {b})"

    def not3(self, a: str) -> str:
        return f"(NOT {a})"

    def is_null(self, a: str) -> str:
        return f"({a} IS NULL)"

    def is_true(self, a: str) -> str:
        """TRUE when `a` is TRUE, FALSE when it is FALSE or NULL."""
        return f"({a} IS TRUE)"

    def case_when(self, c: str, t: str, e: str) -> str:
        """`t` when `c` is TRUE, else `e` (also when `c` is NULL)."""
        return f"(CASE WHEN {c} THEN {t} ELSE {e} END)"

    # Ordering and windows

    def sort_key(self, expr: str, desc: bool, nulls_first: bool, kind: Kind | None = None) -> str:
        """One ORDER BY key; `kind` is what `expr` is (a double's sort is
        already split into rank, value and sign keys)."""
        return f"{expr} {'DESC' if desc else 'ASC'} NULLS {'FIRST' if nulls_first else 'LAST'}"

    def partition_keys(self, x: str, kind: Kind | None) -> list[str]:
        """PARTITION BY expressions grouping rows equal on column `x` (NULLs
        together): doubles also split on the sign, so -0.0 and +0.0 (and -NaN
        and NaN) are different partitions."""
        return [x, self.sign_bit(x)] if kind == "float" else [x]

    def over(self, partition: Sequence[str], order: Sequence[str]) -> str:
        parts = []
        if partition:
            parts.append("PARTITION BY " + ", ".join(partition))
        if order:
            parts.append("ORDER BY " + ", ".join(order))
        return f"OVER ({' '.join(parts)})"

    def row_number(self, over: str) -> str:
        return f"ROW_NUMBER() {over}"

    def lag(self, x: str, offset: int, default: str, over: str) -> str:
        return f"LAG({x}, {offset}, {default}) {over}"

    def lead(self, x: str, offset: int, default: str, over: str) -> str:
        return f"LEAD({x}, {offset}, {default}) {over}"

    # Relations

    def row_ordinal(self) -> str:
        """An expression numbering a base table's rows in a fixed scan order,
        used where Lean's list order matters (below FETCH and windows)."""
        raise Unsupported(f"{self.name} has no stable row order for tables")

    def subquery(self, select: str, alias: str) -> str:
        return f"({select}) AS {alias}"

    def values(self, rows: Sequence[Sequence[str]], columns: Sequence[str]) -> str:
        """A FROM item with these rows (at least one) and column names."""
        body = ", ".join("(" + ", ".join(r) + ")" for r in rows)
        return f"(VALUES {body}) AS v({', '.join(columns)})"

    def limit_offset(self, offset: int, count: int | None) -> str:
        parts = [] if count is None else [f"LIMIT {count}"]
        if offset:
            parts.append(f"OFFSET {offset}")
        return " ".join(parts)

    def cross_join(self, left: str, right: str) -> str:
        return f"{left} CROSS JOIN {right}"

    def union_all(self, a: str, b: str) -> str:
        return f"{a} UNION ALL {b}"


def _timestamp_text(micros: int) -> str:
    try:
        ts = datetime(1970, 1, 1) + timedelta(microseconds=micros)
    except OverflowError as e:
        raise Unsupported(f"timestamp {micros}µs is out of range") from e
    return ts.strftime("%Y-%m-%d %H:%M:%S.%f")


def _date_text(days: int) -> str:
    try:
        return (date(1970, 1, 1) + timedelta(days=days)).isoformat()
    except OverflowError as e:
        raise Unsupported(f"date {days} is out of range") from e


# --------------------------------------------------------------------------
# The model: `Expr` and `Rel` of the Lean development


@dataclass(frozen=True)
class Lit:
    """A constant. `value` is None (NULL), bool, int, str or float; `kind`
    says what an int is (integer, microseconds, days) and types NULLs."""

    value: Any
    kind: Kind | None


@dataclass(frozen=True)
class Field:
    index: int


@dataclass(frozen=True)
class Un:
    op: Literal[
        "not", "is_null", "neg", "itof", "fneg", "ffloor", "fceil", "fround", "froundTo",
        "ftoi", "itos",
    ]  # fmt: skip
    arg: Expr
    digits: int = 0
    """The `d` of `froundTo d`."""


@dataclass(frozen=True)
class Bin:
    op: Literal[
        "add", "sub", "mul", "eq", "lt", "and", "or", "fadd", "fsub", "fmul", "fdiv",
        "idiv", "imod", "ipow", "fpow",
    ]  # fmt: skip
    left: Expr
    right: Expr


@dataclass(frozen=True)
class If:
    cond: Expr
    then: Expr
    orelse: Expr


Expr = Lit | Field | Un | Bin | If


@dataclass(frozen=True)
class SortKey:
    col: int
    desc: bool
    nulls_first: bool


@dataclass(frozen=True)
class WinFn:
    fn: Literal["row_number", "lag", "lead"]
    col: int = 0
    offset: int = 0
    default: Lit = Lit(None, None)


@dataclass(frozen=True)
class Read:
    name: tuple[str, ...]
    columns: tuple[str, ...]
    kinds: tuple[Kind | None, ...]
    lean_kinds: tuple[LeanKind, ...]


@dataclass(frozen=True)
class Values:
    arity: int
    rows: tuple[tuple[Expr, ...], ...]
    kinds: tuple[Kind | None, ...]
    lean_kinds: tuple[LeanKind, ...]


@dataclass(frozen=True)
class Filter:
    input: Rel
    cond: Expr


@dataclass(frozen=True)
class Project:
    input: Rel
    exprs: tuple[Expr, ...]


@dataclass(frozen=True)
class Emit:
    input: Rel
    mapping: tuple[int, ...]


@dataclass(frozen=True)
class Cross:
    left: Rel
    right: Rel


@dataclass(frozen=True)
class Join:
    left: Rel
    right: Rel
    type: Literal["inner", "left"]
    on: Expr


@dataclass(frozen=True)
class Fetch:
    input: Rel
    offset: int
    count: int | None


@dataclass(frozen=True)
class UnionAll:
    left: Rel
    right: Rel


@dataclass(frozen=True)
class Window:
    input: Rel
    part: tuple[int, ...]
    sort: tuple[SortKey, ...]
    fns: tuple[WinFn, ...]


Rel = Read | Values | Filter | Project | Emit | Cross | Join | Fetch | UnionAll | Window


# Kinds of columns and expressions. `kinds` is what SQL sees; `lean_kinds`
# mirrors `Rel.kinds`/`Expr.kind`, which the parser's choices depend on.


def kinds(r: Rel) -> list[Kind | None]:
    match r:
        case Read() | Values():
            return list(r.kinds)
        case Filter(input=i) | Fetch(input=i):
            return kinds(i)
        case Project(input=i, exprs=es):
            ks = kinds(i)
            return ks + [expr_kind(e, ks) for e in es]
        case Emit(input=i, mapping=m):
            ks = kinds(i)
            return [ks[j] if j < len(ks) else None for j in m]
        case Cross(left=a, right=b) | Join(left=a, right=b):
            return kinds(a) + kinds(b)
        case UnionAll(left=a):
            return kinds(a)
        case Window(input=i, fns=fns):
            ks = kinds(i)
            return ks + [_win_kind(f, ks, None) for f in fns]


def lean_kinds(r: Rel) -> list[LeanKind]:
    match r:
        case Read():
            return list(r.lean_kinds)
        case Values():
            # `Rel.kinds` reads them from the `baseSchema`, as for tables.
            return list(r.lean_kinds)
        case Filter(input=i) | Fetch(input=i):
            return lean_kinds(i)
        case Project(input=i, exprs=es):
            ks = lean_kinds(i)
            return ks + [lean_expr_kind(e, ks) for e in es]
        case Emit(input=i, mapping=m):
            ks = lean_kinds(i)
            return [ks[j] if j < len(ks) else "other" for j in m]
        case Cross(left=a, right=b) | Join(left=a, right=b):
            return lean_kinds(a) + lean_kinds(b)
        case UnionAll(left=a):
            return lean_kinds(a)
        case Window(input=i, fns=fns):
            ks = lean_kinds(i)
            return ks + [_win_kind(f, ks, "other") for f in fns]


def _win_kind[K](f: WinFn, cols: list[K], unknown: K) -> K | Literal["int"]:
    """`WinFn.kind`."""
    if f.fn == "row_number":
        return "int"
    return cols[f.col] if f.col < len(cols) else unknown


def _get(ks: list, i: int) -> Any:
    return ks[i] if i < len(ks) else None


def _lean_lit_kind(v: Any) -> LeanKind:
    # `litKind`: doubles, timestamps, dates and intervals are all `Value.int`.
    if v is None:
        return "other"
    if isinstance(v, bool):
        return "bool"
    return "str" if isinstance(v, str) else "int"


def lean_expr_kind(e: Expr, cols: list[LeanKind]) -> LeanKind:
    match e:
        case Lit(value=v):
            return _lean_lit_kind(v)
        case Field(index=i):
            return cols[i] if i < len(cols) else "other"
        case Un(op="neg", arg=a):
            return lean_expr_kind(a, cols)
        case Un(op="itof" | "fneg" | "ffloor" | "fceil" | "fround" | "froundTo"):
            return "float"
        case Un(op="ftoi"):
            return "int"
        case Un(op="itos"):
            return "str"
        case Un():
            return "bool"
        case Bin(op="add" | "sub" | "mul", left=a, right=b):
            return lean_expr_kind(b if isinstance(a, Lit) else a, cols)
        case Bin(op="fadd" | "fsub" | "fmul" | "fdiv" | "fpow"):
            return "float"
        case Bin(op="idiv" | "imod" | "ipow"):
            return "int"
        case Bin():
            return "bool"
        case If(then=Lit(value=v), orelse=o):
            return _lean_lit_kind(v) if isinstance(o, Lit) else lean_expr_kind(o, cols)
        case If(then=t):
            return lean_expr_kind(t, cols)


def expr_kind(e: Expr, cols: list[Kind | None]) -> Kind | None:
    match e:
        case Lit(kind=k):
            return k
        case Field(index=i):
            return _get(cols, i)
        case Un(op="neg", arg=a):
            return expr_kind(a, cols)
        case Un(op="itof" | "fneg" | "ffloor" | "fceil" | "fround" | "froundTo"):
            return "float"
        case Un(op="ftoi"):
            return "int"
        case Un(op="itos"):
            return "str"
        case Un():
            return "bool"
        case Bin(op="add" | "sub", left=a, right=b):
            ka, kb = expr_kind(a, cols), expr_kind(b, cols)
            if ka == "time" and kb == "time":
                return "interval"
            return ka if ka in ("time", "interval") or kb is None else kb
        case Bin(op="mul", left=a, right=b):
            return expr_kind(a, cols) or expr_kind(b, cols)
        case Bin(op="fadd" | "fsub" | "fmul" | "fdiv" | "fpow"):
            return "float"
        case Bin(op="idiv" | "imod" | "ipow"):
            return "int"
        case Bin():
            return "bool"
        case If(then=t, orelse=o):
            return expr_kind(t, cols) or expr_kind(o, cols)


# --------------------------------------------------------------------------
# Parsing: a transcription of `SubstraitLean/Parse.lean`


def _field(j: dict, k: str) -> Any:
    """`field?`: a present, non-null member."""
    v = j.get(k) if isinstance(j, dict) else None
    return v


def _req(j: dict, k: str) -> Any:
    v = _field(j, k)
    if v is None:
        raise Unsupported(f"missing field '{k}' in {_short(j)}")
    return v


def _short(j: Any) -> str:
    s = json.dumps(j, separators=(",", ":"))
    return s if len(s) <= 80 else s[:80] + "…"


def _arr(j: dict, k: str) -> list:
    v = _field(j, k)
    if v is None:
        return []
    if not isinstance(v, list):
        raise Unsupported(f"expected an array in '{k}'")
    return v


def _int(j: Any) -> int:
    if isinstance(j, bool):
        raise Unsupported(f"expected integer, got {j!r}")
    if isinstance(j, int):
        return j
    if isinstance(j, str) and re.fullmatch(r"-?\d+", j):
        return int(j)
    raise Unsupported(f"expected integer, got {j!r}")


def _nat(j: Any) -> int:
    i = _int(j)
    if i < 0:
        raise Unsupported(f"expected non-negative integer, got {i}")
    return i


def _nat_d(j: dict, k: str) -> int:
    v = _field(j, k)
    return 0 if v is None else _nat(v)


def _oneof(what: str, j: dict, keys: Sequence[str]) -> tuple[str, Any]:
    for k in keys:
        v = _field(j, k)
        if v is not None:
            return k, v
    raise Unsupported(f"unsupported {what}: {_short(j)}")


def _base_name(name: str) -> str:
    return name.split(":")[0]


def _type_kinds(ty: Any) -> tuple[LeanKind, Kind | None]:
    """`typeKind`, and the SQL kind of the same type."""
    if not isinstance(ty, dict):
        return "other", None
    if any(k in ty for k in ("i8", "i16", "i32", "i64")):
        return "int", "int"
    if any(k in ty for k in ("fp32", "fp64")):
        return "float", "float"
    if "precisionTimestamp" in ty or "timestamp" in ty:
        return "time", "time"
    if "date" in ty:
        return "date", "date"
    if any(k in ty for k in ("string", "varchar", "fixedChar")):
        return "str", "str"
    if "bool" in ty:
        return "bool", "bool"
    return "other", None


def _lean_type_kind(ty: Any) -> LeanKind:
    return _type_kinds(ty)[0]


def _schema_types(schema: Any) -> list:
    st = _field(schema, "struct") if isinstance(schema, dict) else None
    types = _field(st, "types") if isinstance(st, dict) else None
    return types if isinstance(types, list) else []


@dataclass
class Const:
    """`Parse.Const`, plus what an integer stands for."""

    tag: Literal["int", "flt", "dec", "str", "bool", "null"]
    value: Any = None
    scale: int = 0
    kind: Kind | None = None

    def to_float(self) -> float | None:
        match self.tag:
            case "int":
                return float(self.value)
            case "flt":
                return self.value
            case "dec":
                return float(Fraction(self.value, 10**self.scale))
            case "str":
                t = self.value.strip().lower()
                if t in ("inf", "+inf", "infinity", "+infinity"):
                    return math.inf
                if t in ("-inf", "-infinity"):
                    return -math.inf
                if t == "nan":
                    return math.nan
                try:
                    n = json.loads(t)
                except ValueError:
                    return None
                return float(n) if isinstance(n, int | float) and not isinstance(n, bool) else None
        return None

    def to_int(self) -> int | None:
        match self.tag:
            case "int":
                return self.value
            case "flt":
                if math.isnan(self.value) or math.isinf(self.value):
                    return None
                return _round_half_away(Fraction(self.value))
            case "dec":
                return _round_half_away(Fraction(self.value, 10**self.scale))
            case "str":
                t = self.value.strip()
                return int(t) if re.fullmatch(r"-?\d+", t) else None
        return None


def _round_half_away(x: Fraction) -> int:
    mag = math.floor(abs(x) + Fraction(1, 2))
    return -mag if x < 0 else mag


def _int_bits(ty: dict) -> int:
    for k, b in (("i8", 8), ("i16", 16), ("i32", 32)):
        if k in ty:
            return b
    return 64


_TIMESTAMP = re.compile(r"(\d+)-(\d+)-(\d+)(?: (\d+):(\d+):(\d+)(?:\.(\d*))?)?")


def _parse_date(s: str) -> int | None:
    m = re.fullmatch(r"(\d+)-(\d+)-(\d+)", s)
    if m is None:
        return None
    return _days_from_civil(*map(int, m.groups()))


def _days_from_civil(y: int, m: int, d: int) -> int:
    """`Time.daysFromCivil` (Lean's `/` and `%` on these operands floor)."""
    y = y - 1 if m <= 2 else y
    era = (y if y >= 0 else y - 399) // 400
    yoe = y - era * 400
    mp = (m + 9) % 12
    doy = (153 * mp + 2) // 5 + d - 1
    doe = yoe * 365 + yoe // 4 - yoe // 100 + doy
    return era * 146097 + doe - 719468


def _parse_timestamp(s: str) -> int | None:
    m = _TIMESTAMP.fullmatch(s)
    if m is None:
        return None
    y, mo, d, h, mi, sec, frac = m.groups()
    days = _days_from_civil(int(y), int(mo), int(d))
    if h is None:
        return days * 86_400_000_000
    micros = int((frac + "000000")[:6]) if frac else 0
    return ((days * 24 + int(h)) * 60 + int(mi)) * 60_000_000 + int(sec) * 1_000_000 + micros


def _cast_const(ty: dict, c: Const) -> Const:
    lean, kind = _type_kinds(ty)
    if c.tag == "null":
        return Const("null", kind=kind)
    match lean:
        case "float":
            f = c.to_float()
            if f is None:
                raise Unsupported("cannot cast this value to a double")
            return Const("flt", f, kind="float")
        case "int":
            i = c.to_int()
            if i is None:
                raise Unsupported("cannot cast this value to an integer")
            bits = _int_bits(ty)
            if not -(2 ** (bits - 1)) <= i < 2 ** (bits - 1):
                raise Unsupported(f"cast of {i} to a {bits}-bit integer overflows")
            return Const("int", i, kind="int")
        case "time" | "date":
            if c.tag == "str":
                parse = _parse_timestamp if lean == "time" else _parse_date
                v = parse(c.value.strip())
                if v is None:
                    raise Unsupported(
                        f"cannot parse {'timestamp' if lean == 'time' else 'date'} '{c.value}'"
                    )
                return Const("int", v, kind=lean)
            if c.tag == "int":
                return Const("int", c.value, kind=lean)
            raise Unsupported(
                f"cannot cast this value to a {'timestamp' if lean == 'time' else 'date'}"
            )
        case "str":
            if c.tag == "str":
                return c
            raise Unsupported("casts to strings are not supported")
    raise Unsupported("unsupported cast type")


def _interval_micros(d: dict) -> int:
    days = _int(_field(d, "days") or 0)
    secs = _int(_field(d, "seconds") or 0)
    sub = _int(_field(d, "subseconds") or 0)
    p = _nat_d(d, "precision")
    # Lean's `Int` division rounds toward negative infinity here (`Int.div` is `ediv`
    # for a positive divisor), like Python's `//`.
    sub_us = sub // 10 ** (p - 6) if p >= 6 else sub * 10 ** (6 - p)
    return (days * 86400 + secs) * 1_000_000 + sub_us


def _decode_decimal(s: str) -> int:
    try:
        raw = base64.b64decode(s, validate=False)
    except ValueError as e:
        raise Unsupported("malformed decimal literal") from e
    return int.from_bytes(raw, "little", signed=True) if raw else 0


_LITERAL_KEYS = (
    "boolean", "i8", "i16", "i32", "i64", "fp32", "fp64", "string", "null", "decimal",
    "precisionTimestamp", "timestamp", "date", "intervalDayToSecond", "intervalCompound",
)  # fmt: skip


def _const_literal(j: dict) -> Const:
    key, v = _oneof("literal", j, _LITERAL_KEYS)
    match key:
        case "boolean":
            if not isinstance(v, bool):
                raise Unsupported("malformed boolean literal")
            return Const("bool", v, kind="bool")
        case "string":
            if not isinstance(v, str):
                raise Unsupported("malformed string literal")
            return Const("str", v, kind="str")
        case "null":
            return Const("null", kind=_type_kinds(v)[1])
        case "fp32" | "fp64":
            if isinstance(v, bool):
                raise Unsupported("malformed floating-point literal")
            if isinstance(v, int | float):
                return Const("flt", float(v), kind="float")
            if isinstance(v, str):
                f = Const("str", v).to_float()
                if f is None:
                    raise Unsupported(f"cannot parse double {v}")
                return Const("flt", f, kind="float")
            raise Unsupported("malformed floating-point literal")
        case "decimal":
            return Const("dec", _decode_decimal(_req(v, "value")), _nat_d(v, "scale"))
        case "intervalDayToSecond":
            return Const("int", _interval_micros(v), kind="interval")
        case "intervalCompound":
            ym = _field(v, "intervalYearToMonth")
            if ym is not None and (_nat_d(ym, "years") != 0 or _nat_d(ym, "months") != 0):
                raise Unsupported("month and year intervals are not supported")
            ds = _field(v, "intervalDayToSecond")
            return Const("int", 0 if ds is None else _interval_micros(ds), kind="interval")
        case "precisionTimestamp":
            if _nat_d(v, "precision") != 6:
                raise Unsupported("only microsecond timestamps are supported")
            return Const("int", _int(_req(v, "value")), kind="time")
        case "timestamp":
            return Const("int", _int(v), kind="time")
        case "date":
            return Const("int", _int(v), kind="date")
    return Const("int", _int(v), kind="int")


def _arrow_cast(c: Const, ty: str) -> Const | None:
    if ty.startswith("Timestamp("):
        target = "precisionTimestamp"
    elif ty in ("Float64", "Float32"):
        target = "fp64"
    elif ty == "Date32":
        target = "date"
    elif ty.startswith("Int"):
        target = "i64"
    elif ty == "Utf8":
        target = "string"
    else:
        return None
    try:
        return _cast_const({target: {}}, c)
    except Unsupported:
        return None


def _trunc(f: float) -> float:
    if math.isnan(f) or math.isinf(f):
        return f
    return math.copysign(float(math.floor(f) if f >= 0 else math.ceil(f)), f)


def _fold_call(name: str, cs: list[Const]) -> Const | None:
    """`foldCall`: a function the parser evaluates on constants."""
    match name, cs:
        case "arrow_cast", [c, Const(tag="str", value=ty)]:
            return _arrow_cast(c, ty)
        case "negate", [Const(tag="int") as c]:
            return Const("int", -c.value, kind=c.kind)
        case "negate", [c]:
            f = c.to_float()
            return None if f is None else Const("flt", -f, kind="float")
        case "trunc", [c]:
            f = c.to_float()
            return None if f is None else Const("flt", _trunc(f), kind="float")
        case "to_seconds", [c]:
            f = c.to_float()
            us = None if f is None else Const("flt", f * 1000000.0).to_int()
            return None if us is None else Const("int", us, kind="interval")
        case (("to_minutes" | "to_hours" | "to_days"), [c]):
            i = c.to_int()
            unit = {"to_minutes": 60_000_000, "to_hours": 3_600_000_000, "to_days": 86_400_000_000}
            return None if i is None else Const("int", i * unit[name], kind="interval")
        case "normalized_interval", [c]:
            return c
    return None


def _lit(c: Const) -> Lit:
    """`constExpr`."""
    match c.tag:
        case "int":
            return Lit(c.value, c.kind)
        case "flt":
            return Lit(c.value, "float")
        case "str":
            return Lit(c.value, "str")
        case "bool":
            return Lit(c.value, "bool")
        case "null":
            return Lit(None, c.kind)
    raise Unsupported("DECIMAL values are not supported; cast them to DOUBLE")


@dataclass
class _Cols:
    lean: list[LeanKind]
    sql: list[Kind | None]


class _Parser:
    def __init__(self, plan: dict):
        self.fns: dict[int, str] = {}
        for e in _arr(plan, "extensions"):
            f = _field(e, "extensionFunction")
            if f is not None:
                self.fns.setdefault(_nat_d(f, "functionAnchor"), _req(f, "name"))

    def name(self, anchor: int) -> str:
        if anchor not in self.fns:
            raise Unsupported(f"function reference {anchor} is not declared in extensions")
        return self.fns[anchor]

    # Constants

    def const(self, j: Any) -> Const | None:
        """`constOf?`."""
        if (lit := _field(j, "literal")) is not None:
            return _const_literal(lit)
        if (c := _field(j, "cast")) is not None:
            x = self.const(_req(c, "input"))
            return None if x is None else _cast_const(_req(c, "type"), x)
        if (f := _field(j, "scalarFunction")) is not None:
            name = self.fns.get(_nat_d(f, "functionReference"))
            if name is None:
                return None
            args = [self.const(_req(a, "value")) for a in _arr(f, "arguments")]
            if any(a is None for a in args):
                return None
            return _fold_call(_base_name(name), args)  # type: ignore[arg-type]
        return None

    # Expressions

    def expr(self, j: Any, cols: _Cols) -> Expr:
        """`parseExpr`."""
        if (c := self.const(j)) is not None:
            return _lit(c)
        key, v = _oneof(
            "expression", j, ("selection", "scalarFunction", "ifThen", "cast", "singularOrList")
        )
        match key:
            case "selection":
                if _field(v, "outerReference") is not None:
                    raise Unsupported("outer references are not supported")
                sf = _req(_req(v, "directReference"), "structField")
                if _field(sf, "child") is not None:
                    raise Unsupported("nested field references are not supported")
                return Field(_nat_d(sf, "field"))
            case "scalarFunction":
                name = _base_name(self.name(_nat_d(v, "functionReference")))
                arg_js = [_req(a, "value") for a in _arr(v, "arguments")]
                parsed = [self.expr(a, cols) for a in arg_js]

                def keep_int(k: int) -> bool:
                    # `ROUND(x, d)`: the digits stay an integer.
                    return name == "round" and k == 1

                # An integer constant next to a double stands for that double.
                if any(lean_expr_kind(e, cols.lean) == "float" for e in parsed):
                    parsed = [
                        e if keep_int(k) else self._as_double(a, e)
                        for k, (a, e) in enumerate(zip(arg_js, parsed, strict=True))
                    ]
                out = _lean_type_kind(_field(v, "outputType"))
                floats = (
                    "add", "subtract", "multiply", "divide", "negate", "abs", "power", "floor",
                    "ceil", "round",
                )  # fmt: skip
                if name in floats and (
                    out == "float" or any(lean_expr_kind(e, cols.lean) == "float" for e in parsed)
                ):
                    # Integer arguments of a double function are converted.
                    parsed = [
                        Un("itof", e)
                        if lean_expr_kind(e, cols.lean) == "int"
                        and not keep_int(k)
                        and not isinstance(e, Lit)
                        else e
                        for k, e in enumerate(parsed)
                    ]
                    return _float_call(name, parsed)
                return _call(name, parsed)
            case "ifThen":
                # A `CASE` without `ELSE` is `ELSE NULL`.
                orelse = _field(v, "else")
                acc = Lit(None, None) if orelse is None else self.expr(orelse, cols)
                for clause in reversed(_arr(v, "ifs")):
                    acc = If(
                        self.expr(_req(clause, "if"), cols),
                        self.expr(_req(clause, "then"), cols),
                        acc,
                    )
                return acc
            case "cast":
                e = self.expr(_req(v, "input"), cols)
                target = _lean_type_kind(_req(v, "type"))
                k = lean_expr_kind(e, cols.lean)
                if target == "float" and k == "int":
                    return Un("itof", e)
                # Fails on NaN, ±inf and out-of-range values.
                if target == "int" and k == "float":
                    return Un("ftoi", e)
                if target == "str" and k == "int":
                    return Un("itos", e)
                if target == k and target != "other":
                    return e
                raise Unsupported(f"unsupported cast from {k} to {target}")
            case "singularOrList":
                value = self.expr(_req(v, "value"), cols)
                is_float = lean_expr_kind(value, cols.lean) == "float"
                opts = [
                    self._as_double(o, self.expr(o, cols)) if is_float else self.expr(o, cols)
                    for o in _arr(v, "options")
                ]
                if not opts:
                    return Lit(False, "bool")
                acc: Expr = Bin("eq", value, opts[0])
                for o in opts[1:]:
                    acc = Bin("or", acc, Bin("eq", value, o))
                return acc
        raise Unsupported(f"unsupported expression: {key}")

    def _as_double(self, j: Any, e: Expr) -> Expr:
        c = self.const(j)
        if c is not None and c.tag == "int":
            return Lit(float(c.value), "float")
        return e

    # Windows

    def column(self, j: Any, cols: _Cols, what: str) -> int:
        e = self.expr(j, cols)
        if not isinstance(e, Field):
            raise Unsupported(f"window {what} must be columns")
        return e.index

    def sort_key(self, s: dict, cols: _Cols) -> SortKey:
        col = self.column(_req(s, "expr"), cols, "sort keys")
        d = _field(s, "direction")
        dirs = {
            "SORT_DIRECTION_ASC_NULLS_FIRST": (False, True),
            "SORT_DIRECTION_ASC_NULLS_LAST": (False, False),
            "SORT_DIRECTION_DESC_NULLS_FIRST": (True, True),
            "SORT_DIRECTION_DESC_NULLS_LAST": (True, False),
        }
        if d not in dirs:
            raise Unsupported(f"unsupported sort direction: {'unspecified' if d is None else d}")
        return SortKey(col, *dirs[d])

    def window(self, w: dict, cols: _Cols) -> tuple[tuple[int, ...], tuple[SortKey, ...], WinFn]:
        name = _base_name(self.name(_nat_d(w, "functionReference")))
        part = tuple(self.column(p, cols, "partitions") for p in _arr(w, "partitions"))
        sort = tuple(self.sort_key(s, cols) for s in _arr(w, "sorts"))
        args = [_req(a, "value") for a in _arr(w, "arguments")]
        match name:
            case "row_number":
                if args:
                    raise Unsupported("row_number takes no arguments")
                return part, sort, WinFn("row_number")
            case "lag" | "lead":
                if not args:
                    raise Unsupported(f"{name} needs a column")
                c = self.column(args[0], cols, "function arguments")
                offset = 1
                if len(args) > 1:
                    k = self.const(args[1])
                    if k is None or k.tag != "int":
                        raise Unsupported(f"{name} offsets must be integer constants")
                    if k.value < 0:
                        raise Unsupported(f"negative {name} offset")
                    offset = k.value
                default = Lit(None, None)
                if len(args) > 2:
                    d = self.const(args[2])
                    if d is None:
                        raise Unsupported(f"{name} defaults must be constants")
                    if d.tag == "int" and _get(cols.lean, c) == "float":
                        default = Lit(float(d.value), "float")
                    else:
                        default = _lit(d)
                return part, sort, WinFn(name, c, offset, default)
        raise Unsupported(f"unsupported window function: {name}")

    def window_project(self, inp: Rel, cols: _Cols, es: list) -> Rel:
        """`parseWindowProject`."""
        n = len(cols.lean)
        parsed: list[tuple[str, Any]] = []
        for e in es:
            w = _field(e, "windowFunction")
            parsed.append(
                ("w", self.window(w, cols)) if w is not None else ("e", self.expr(e, cols))
            )
        groups: list[tuple[tuple[int, ...], tuple[SortKey, ...], list[WinFn]]] = []
        for tag, p in parsed:
            if tag != "w":
                continue
            part, sort, f = p
            for g in groups:
                if g[0] == part and g[1] == sort:
                    g[2].append(f)
                    break
            else:
                groups.append((part, sort, [f]))
        windowed = inp
        for part, sort, fs in groups:
            windowed = Window(windowed, part, sort, tuple(fs))
        width = sum(len(g[2]) for g in groups)

        def column(part: tuple, sort: tuple, f: WinFn, seen: int) -> int:
            off = n
            for p, s, fs in groups:
                if p == part and s == sort:
                    idxs = [i for i, g in enumerate(fs) if g == f]
                    return off + (idxs[seen] if seen < len(idxs) else 0)
                off += len(fs)
            return off

        scalars = [p for tag, p in parsed if tag == "e"]
        mapping: list[int] = []
        seen: list[Any] = []
        j = 0
        for tag, p in parsed:
            if tag == "w":
                part, sort, f = p
                mapping.append(column(part, sort, f, seen.count(p)))
                seen.append(p)
            else:
                mapping.append(n + width + j)
                j += 1
        full = list(range(n)) + mapping
        if not scalars and full == list(range(n + width)):
            return windowed
        core = windowed if not scalars else Project(windowed, tuple(scalars))
        return Emit(core, tuple(full))

    # Relations

    def read(self, r: dict) -> Rel:
        schema = _req(r, "baseSchema")
        st = _field(schema, "struct")
        arity = len(_arr(st, "types")) if st is not None else len(_arr(schema, "names"))
        types = _schema_types(schema)
        sql_kinds = tuple(_type_kinds(t)[1] for t in types) + (None,) * (arity - len(types))
        lean = [_lean_type_kind(t) for t in types]
        key, v = _oneof("read type", r, ("namedTable", "virtualTable"))
        base: Rel
        if key == "namedTable":
            base = Read(
                tuple(_arr(v, "names")), tuple(_arr(schema, "names")), sql_kinds, tuple(lean)
            )
        else:
            if _field(v, "expressions") is not None:
                rows = tuple(
                    tuple(self.expr(e, _Cols([], [])) for e in _arr(row, "fields"))
                    for row in _arr(v, "expressions")
                )
            else:
                rows = tuple(
                    tuple(_lit(_const_literal(e)) for e in _arr(row, "fields"))
                    for row in _arr(v, "values")
                )
            base = Values(arity, rows, _values_kinds(rows, sql_kinds), tuple(lean))
        cond = _field(r, "filter")
        if cond is not None:
            base = Filter(base, self.expr(cond, _Cols(lean, kinds(base))))
        mask = _field(r, "projection")
        if mask is not None:
            items = _arr(_req(mask, "select"), "structItems")
            if any(_field(i, "child") is not None for i in items):
                raise Unsupported("nested projection masks are not supported")
            base = Emit(base, tuple(_nat_d(i, "field") for i in items))
        return base

    def cols(self, r: Rel) -> _Cols:
        return _Cols(lean_kinds(r), kinds(r))

    def rel(self, j: dict) -> Rel:
        """`parseRel`."""
        kind, r = _oneof(
            "relation", j, ("read", "filter", "project", "cross", "join", "fetch", "set")
        )
        core: Rel
        match kind:
            case "read":
                core = self.read(r)
            case "filter":
                inp = self.rel(_req(r, "input"))
                core = Filter(inp, self.expr(_req(r, "condition"), self.cols(inp)))
            case "project":
                inp = self.rel(_req(r, "input"))
                cols = self.cols(inp)
                ejs = _arr(r, "expressions")
                if any(_field(e, "windowFunction") is not None for e in ejs):
                    core = self.window_project(inp, cols, ejs)
                else:
                    es = tuple(self.expr(e, cols) for e in ejs)
                    core = Project(inp, es) if es else inp
            case "cross":
                core = Cross(self.rel(_req(r, "left")), self.rel(_req(r, "right")))
            case "join":
                types: dict[str, tuple[Literal["inner", "left"], bool]] = {
                    "JOIN_TYPE_INNER": ("inner", False),
                    "JOIN_TYPE_LEFT": ("left", False),
                    "JOIN_TYPE_RIGHT": ("left", True),
                }
                t = _field(r, "type")
                if t not in types:
                    raise Unsupported(f"unsupported join type: {'unspecified' if t is None else t}")
                ty, swap = types[t]
                if _field(r, "postJoinFilter") is not None:
                    raise Unsupported("JoinRel.postJoinFilter is not supported")
                left, right = self.rel(_req(r, "left")), self.rel(_req(r, "right"))
                lc, rc = self.cols(left), self.cols(right)
                n, m = len(lc.lean), len(rc.lean)
                cols = _Cols(lc.lean + rc.lean, lc.sql + rc.sql)
                e = _field(r, "expression")
                on = Lit(True, "bool") if e is None else self.expr(e, cols)
                if not swap:
                    core = Join(left, right, ty, on)
                else:
                    on = _map_fields(on, lambda i: m + i if i < n else i - n)
                    core = Emit(
                        Join(right, left, "left", on),
                        tuple([m + i for i in range(n)] + list(range(m))),
                    )
            case "fetch":
                offset = self.fetch_int(r, "offset")
                if offset is not None and offset < 0:
                    raise Unsupported("negative FetchRel offset")
                count = self.fetch_int(r, "count")
                core = Fetch(
                    self.rel(_req(r, "input")),
                    offset or 0,
                    None if count is None or count < 0 else count,
                )
            case _:
                op = _field(r, "op")
                if op != "SET_OP_UNION_ALL":
                    raise Unsupported(
                        f"unsupported set operation: {'unspecified' if op is None else op}"
                    )
                inputs = [self.rel(i) for i in _arr(r, "inputs")]
                if not inputs:
                    raise Unsupported("SetRel without inputs")
                core = inputs[0]
                for i in inputs[1:]:
                    core = UnionAll(core, i)
        common = _field(r, "common")
        emit = _field(common, "emit") if common is not None else None
        if emit is not None:
            m = [_nat(i) for i in _arr(emit, "outputMapping")]
            if isinstance(core, Emit):
                return Emit(
                    core.input, tuple(core.mapping[i] if i < len(core.mapping) else 0 for i in m)
                )
            return Emit(core, tuple(m))
        return core

    def fetch_int(self, r: dict, key: str) -> int | None:
        e = _field(r, key + "Expr")
        if e is not None:
            c = self.const(e)
            if c is not None and c.tag == "int":
                return c.value
            if c is not None and c.tag == "null":
                return None
            raise Unsupported(f"FetchRel.{key}Expr must be an integer constant")
        v = _field(r, key)
        return None if v is None else _int(v)


def _values_kinds(rows: tuple, schema: tuple[Kind | None, ...]) -> tuple[Kind | None, ...]:
    """Column kinds of a virtual table: what its constants are, else what its
    `baseSchema` says (Lean ignores both, and writes placeholder `i64` types)."""
    out = []
    for j, k in enumerate(schema):
        # NULLs say nothing: Lean writes every one as an `i64` NULL.
        values = [row[j] for row in rows if j < len(row)]
        nonnull = [e for e in values if not (isinstance(e, Lit) and e.value is None)]
        seen = {expr_kind(e, []) for e in nonnull} - {None}
        if len(seen) > 1:
            raise Unsupported(f"virtual table column {j} mixes {sorted(seen)}")  # type: ignore[type-var]
        out.append(seen.pop() if seen else k)
    return tuple(out)


def _map_fields(e: Expr, f: Callable[[int], int]) -> Expr:
    match e:
        case Lit():
            return e
        case Field(index=i):
            return Field(f(i))
        case Un(op=op, arg=a):
            return Un(op, _map_fields(a, f))
        case Bin(op=op, left=a, right=b):
            return Bin(op, _map_fields(a, f), _map_fields(b, f))
        case If(cond=c, then=t, orelse=o):
            return If(_map_fields(c, f), _map_fields(t, f), _map_fields(o, f))


def _call(name: str, args: list[Expr]) -> Expr:
    """`mkCall`."""
    match name, args:
        case "not", [a]:
            return Un("not", a)
        case "is_null", [a]:
            return Un("is_null", a)
        case "is_not_null", [a]:
            return Un("not", Un("is_null", a))
        case (("negate" | "subtract"), [a]):
            return Un("neg", a)
        case "add", [a, b]:
            return Bin("add", a, b)
        case "subtract", [a, b]:
            return Bin("sub", a, b)
        case "multiply", [a, b]:
            return Bin("mul", a, b)
        case "equal", [a, b]:
            return Bin("eq", a, b)
        case "not_equal", [a, b]:
            return Un("not", Bin("eq", a, b))
        case "lt", [a, b]:
            return Bin("lt", a, b)
        case "gt", [a, b]:
            return Bin("lt", b, a)
        case "lte", [a, b]:
            return Un("not", Bin("lt", b, a))
        case "gte", [a, b]:
            return Un("not", Bin("lt", a, b))
        case "normalized_interval", [a]:
            return a
        case (("is_nan" | "isnan"), [a]):
            return Bin(
                "or", Bin("eq", a, Lit(math.nan, "float")), Bin("eq", a, Lit(-math.nan, "float"))
            )
        case (("and" | "or"), [a, *rest]):
            for b in rest:
                a = Bin(name, a, b)  # type: ignore[arg-type]
            return a
        case "coalesce", [a, *rest]:
            return _coalesce(a, rest)
        case "nullif", [a, b]:
            return If(Bin("eq", a, b), Lit(None, None), a)
        case "greatest", [a, *rest]:
            for b in rest:
                a = _pick(lambda x, y: Bin("lt", x, y), a, b)
            return a
        case "least", [a, *rest]:
            for b in rest:
                a = _pick(lambda x, y: Bin("lt", y, x), a, b)
            return a
        case "abs", [a]:
            return If(Bin("lt", a, Lit(0, "int")), Un("neg", a), a)
        # Integer division and remainder truncate; doubles go to `_float_call`.
        case "divide", [a, b]:
            return Bin("idiv", a, b)
        case "modulus", [a, b]:
            return Bin("imod", a, b)
        case "power", [a, b]:
            return Bin("ipow", a, b)
    raise Unsupported(f"unsupported function {name}/{len(args)}")


def _coalesce(a: Expr, rest: list[Expr]) -> Expr:
    if not rest:
        return a
    return If(Un("not", Un("is_null", a)), a, _coalesce(rest[0], rest[1:]))


def _pick(better: Callable[[Expr, Expr], Expr], a: Expr, b: Expr) -> Expr:
    return If(Un("is_null", a), b, If(Un("is_null", b), a, If(better(a, b), b, a)))


def _float_call(name: str, args: list[Expr]) -> Expr:
    """`mkFloatCall`."""
    match name, args:
        case "add", [a, b]:
            return Bin("fadd", a, b)
        case "subtract", [a, b]:
            return Bin("fsub", a, b)
        case "multiply", [a, b]:
            return Bin("fmul", a, b)
        case "divide", [a, b]:
            return Bin("fdiv", a, b)
        case (("subtract" | "negate"), [a]):
            return Un("fneg", a)
        case "abs", [a]:
            neg_zero, pos_zero = Lit(-0.0, "float"), Lit(0.0, "float")
            return If(
                Bin("lt", a, neg_zero), Un("fneg", a), If(Bin("lt", a, pos_zero), pos_zero, a)
            )
        case "power", [a, b]:
            return Bin("fpow", a, b)
        case "floor", [a]:
            return Un("ffloor", a)
        case "ceil", [a]:
            return Un("fceil", a)
        case "round", [a]:
            return Un("fround", a)
        case "round", [a, Lit(value=int(d), kind="int")] if not isinstance(d, bool):
            return Un("fround", a) if d == 0 else Un("froundTo", a, d)
    raise Unsupported(f"unsupported double function {name}/{len(args)}")


@dataclass
class Plan:
    root: Rel
    names: list[str]


def parse_plan(plan: dict) -> Plan:
    """Read a Substrait JSON plan (as a dict) into the model, as `parsePlan` does."""
    p = _Parser(plan)
    root = next((_field(r, "root") for r in _arr(plan, "relations") if _field(r, "root")), None)
    if root is None:
        raise Unsupported("plan has no root relation")
    rel = p.rel(_req(root, "input"))
    names = _arr(root, "names")
    if not all(isinstance(n, str) for n in names):
        raise Unsupported("root names must be strings")
    return Plan(rel, names)


# --------------------------------------------------------------------------
# Writing SQL


def arity(r: Rel) -> int:
    return len(kinds(r))


def order_matters(r: Rel) -> bool:
    """Does the result's row order matter (a FETCH or a window anywhere)?"""
    match r:
        case Fetch() | Window():
            return True
        case Read() | Values():
            return False
        case Filter(input=i) | Project(input=i) | Emit(input=i):
            return order_matters(i)
        case Cross(left=a, right=b) | Join(left=a, right=b) | UnionAll(left=a, right=b):
            return order_matters(a) or order_matters(b)


ORD = "o"


@dataclass
class _Writer:
    d: Dialect
    tie_free: bool = False
    n: int = 0

    def alias(self) -> str:
        self.n += 1
        return f"s{self.n}"

    def c(self, i: int) -> str:
        return self.d.quote(f"c{i}")

    def ref(self, alias: str, col: str) -> str:
        return f"{alias}.{col}"

    def ordinal(self, alias: str) -> str:
        return self.ref(alias, self.d.quote(ORD))

    def select(self, items: list[str], from_: str, rest: str = "") -> str:
        return f"SELECT {', '.join(items)} FROM {from_}" + (f" {rest}" if rest else "")

    def passthrough(self, alias: str, n: int, ordered: bool) -> list[str]:
        items = [f"{self.ref(alias, self.c(i))} AS {self.c(i)}" for i in range(n)]
        if ordered:
            items.append(f"{self.ordinal(alias)} AS {self.d.quote(ORD)}")
        return items

    def order_by(self, keys: list[str]) -> str:
        return self.d.over([], keys)

    def asc(self, x: str, nulls_first: bool = False) -> str:
        """An ascending key on an ordinal or tag (an integer)."""
        return self.d.sort_key(x, False, nulls_first, "int")

    # Relations: each returns a SELECT with columns c0… (and `o` when ordered).

    def rel(self, r: Rel, ordered: bool) -> str:
        d = self.d
        n = arity(r)
        if n == 0:
            raise Unsupported("relations without columns have no SQL form")
        match r:
            case Read(name=name, columns=columns):
                if len(columns) != n:
                    raise Unsupported(
                        f"table {'.'.join(name)} needs one name per column in its baseSchema"
                    )
                items = [f"{d.quote(col)} AS {self.c(i)}" for i, col in enumerate(columns)]
                if ordered:
                    items.append(f"{d.row_ordinal()} AS {d.quote(ORD)}")
                return self.select(items, ".".join(d.quote(p) for p in name))
            case Values(rows=rows, kinds=ks):
                cols = [self.c(i) for i in range(n)] + ([d.quote(ORD)] if ordered else [])
                for row in rows:
                    if len(row) != n:
                        raise Unsupported(
                            f"a virtual table row has {len(row)} fields, expected {n}"
                        )
                if not rows:
                    items = [f"{d.null(k)} AS {self.c(i)}" for i, k in enumerate(ks)]
                    if ordered:
                        items.append(f"{d.null('int')} AS {d.quote(ORD)}")
                    return f"SELECT {', '.join(items)} WHERE FALSE"
                sql_rows = []
                for idx, row in enumerate(rows):
                    vals = [
                        self.expr(e, lambda i: _no_fields(), [], k)
                        for e, k in zip(row, ks, strict=True)
                    ]
                    sql_rows.append(vals + ([d.int_lit(idx)] if ordered else []))
                a = "v"
                return self.select(
                    [f"{self.ref(a, c)} AS {c}" for c in cols], d.values(sql_rows, cols)
                )
            case Filter(input=i, cond=cond):
                a = self.alias()
                ks = kinds(i)
                self.check_refs(cond, len(ks))
                where = d.is_true(self.expr(cond, lambda j: self.ref(a, self.c(j)), ks, "bool"))
                return self.select(
                    self.passthrough(a, n, ordered),
                    d.subquery(self.rel(i, ordered), a),
                    f"WHERE {where}",
                )
            case Project(input=i, exprs=es):
                a = self.alias()
                ks = kinds(i)
                m = len(ks)
                items = [f"{self.ref(a, self.c(j))} AS {self.c(j)}" for j in range(m)]
                for j, e in enumerate(es):
                    self.check_refs(e, m)
                    sql = self.expr(e, lambda x: self.ref(a, self.c(x)), ks, expr_kind(e, ks))
                    items.append(f"{sql} AS {self.c(m + j)}")
                if ordered:
                    items.append(f"{self.ordinal(a)} AS {d.quote(ORD)}")
                return self.select(items, d.subquery(self.rel(i, ordered), a))
            case Emit(input=i, mapping=mapping):
                a = self.alias()
                m = arity(i)
                if any(j >= m for j in mapping):
                    raise Unsupported(f"emit refers to a column beyond the input's {m}")
                items = [f"{self.ref(a, self.c(j))} AS {self.c(k)}" for k, j in enumerate(mapping)]
                if ordered:
                    items.append(f"{self.ordinal(a)} AS {d.quote(ORD)}")
                return self.select(items, d.subquery(self.rel(i, ordered), a))
            case Cross(left=left, right=right) | Join(left=left, right=right):
                la, ra = self.alias(), self.alias()
                nl = arity(left)
                items = [f"{self.ref(la, self.c(j))} AS {self.c(j)}" for j in range(nl)]
                items += [f"{self.ref(ra, self.c(j))} AS {self.c(nl + j)}" for j in range(n - nl)]
                if ordered:
                    # Left-major, and a left join's unmatched row (no right ordinal) in place.
                    keys = [
                        self.asc(self.ordinal(la)),
                        self.asc(self.ordinal(ra), nulls_first=True),
                    ]
                    items.append(f"{d.row_number(self.order_by(keys))} AS {d.quote(ORD)}")
                lsub = d.subquery(self.rel(left, ordered), la)
                rsub = d.subquery(self.rel(right, ordered), ra)
                if isinstance(r, Cross):
                    return self.select(items, d.cross_join(lsub, rsub))
                ks = kinds(left) + kinds(right)
                self.check_refs(r.on, n)

                def side(j: int) -> str:
                    return self.ref(la, self.c(j)) if j < nl else self.ref(ra, self.c(j - nl))

                on = self.expr(r.on, side, ks, "bool")
                join = "INNER JOIN" if r.type == "inner" else "LEFT JOIN"
                return self.select(items, f"{lsub} {join} {rsub} ON {on}")
            case Fetch(input=i, offset=off, count=cnt):
                a = self.alias()
                rest = f"ORDER BY {self.asc(self.ordinal(a))}"
                if lo := d.limit_offset(off, cnt):
                    rest += " " + lo
                return self.select(
                    self.passthrough(a, n, ordered), d.subquery(self.rel(i, True), a), rest
                )
            case UnionAll(left=left, right=right):
                if arity(left) != arity(right):
                    raise Unsupported("UNION ALL inputs have different numbers of columns")
                if not ordered:
                    branches = []
                    for b in (left, right):
                        a = self.alias()
                        branches.append(
                            self.select(
                                self.passthrough(a, n, False), d.subquery(self.rel(b, False), a)
                            )
                        )
                    return d.union_all(*branches)
                branch = d.quote("b")
                branches = []
                for tag, b in enumerate((left, right)):
                    a = self.alias()
                    items = self.passthrough(a, n, True) + [f"{d.int_lit(tag)} AS {branch}"]
                    branches.append(self.select(items, d.subquery(self.rel(b, True), a)))
                u = self.alias()
                keys = [self.asc(self.ref(u, branch)), self.asc(self.ordinal(u))]
                items = self.passthrough(u, n, False) + [
                    f"{d.row_number(self.order_by(keys))} AS {d.quote(ORD)}"
                ]
                return self.select(items, d.subquery(d.union_all(*branches), u))
            case Window(input=i, part=part, sort=sort, fns=fns):
                return self.window(i, part, sort, fns, ordered)
        raise Unsupported(f"unsupported relation {type(r).__name__}")

    def window(self, i: Rel, part: tuple, sort: tuple, fns: tuple, ordered: bool) -> str:
        d = self.d
        a = self.alias()
        ks = kinds(i)
        m = len(ks)
        if (
            any(p >= m for p in part)
            or any(k.col >= m for k in sort)
            or any(f.fn != "row_number" and f.col >= m for f in fns)
        ):
            raise Unsupported("window refers to a column beyond its input")

        def col(j: int) -> str:
            return self.ref(a, self.c(j))

        partition = [x for p in part for x in d.partition_keys(col(p), ks[p])]
        keys: list[str] = []
        for k in sort:
            for x, kind in self.sort_exprs(col(k.col), ks[k.col]):
                keys.append(d.sort_key(x, k.desc, k.nulls_first, kind))
        if not self.tie_free:
            # Lean sorts with a stable merge sort: ties keep their input order.
            keys.append(self.asc(self.ordinal(a)))
        elif ordered and not keys:
            raise Unsupported(
                "without ORDER BY a window keeps its input's order, which needs ordinals"
            )
        over = d.over(partition, keys)
        items = [f"{col(j)} AS {self.c(j)}" for j in range(m)]
        for j, f in enumerate(fns):
            if f.fn == "row_number":
                sql = d.row_number(over)
            else:
                default = self.lit(f.default, ks[f.col])
                fn = d.lag if f.fn == "lag" else d.lead
                sql = fn(col(f.col), f.offset, default, over)
            items.append(f"{sql} AS {self.c(m + j)}")
        if ordered:
            # `windowEval` emits the rows in sort order.
            items.append(f"{d.row_number(self.order_by(keys))} AS {d.quote(ORD)}")
        return self.select(items, d.subquery(self.rel(i, not self.tie_free), a))

    def sort_exprs(self, x: str, kind: Kind | None) -> list[tuple[str, Kind | None]]:
        """Expressions (and their kinds) that sort like `Value.le` on a column,
        NULL exactly when the value is NULL."""
        if kind != "float":
            return [(x, kind)]
        d = self.d
        zero_sign = f"(CASE WHEN {d.sign_bit(x)} THEN 0 ELSE 1 END)"
        return [(d.float_rank(x), "int"), (x, "float"), (zero_sign, "int")]

    def check_refs(self, e: Expr, n: int) -> None:
        match e:
            case Field(index=i):
                if i >= n:
                    raise Unsupported(
                        f"field reference ${i} is out of range (the input has {n} columns)"
                    )
            case Un(arg=a):
                self.check_refs(a, n)
            case Bin(left=a, right=b):
                self.check_refs(a, n)
                self.check_refs(b, n)
            case If(cond=c, then=t, orelse=o):
                for x in (c, t, o):
                    self.check_refs(x, n)

    # Expressions

    def lit(self, lit: Lit, ctx: Kind | None) -> str:
        d = self.d
        v, k = lit.value, lit.kind
        if v is None:
            return d.null(k or ctx)
        match k:
            case "bool":
                return d.bool_lit(v)
            case "str":
                return d.str_lit(v)
            case "float":
                return d.float_lit(v)
        if not I64_MIN <= v <= I64_MAX:
            raise Unsupported(f"integer constant {v} does not fit in 64 bits")
        match k:
            case "time":
                return d.timestamp_lit(v)
            case "date":
                return d.date_lit(v)
            case "interval":
                return d.interval_lit(v)
        return d.int_lit(v)

    def expr(
        self, e: Expr, ref: Callable[[int], str], cols: list[Kind | None], ctx: Kind | None
    ) -> str:
        d = self.d

        def go(x: Expr, k: Kind | None = None) -> str:
            return self.expr(x, ref, cols, k)

        def kind(x: Expr) -> Kind | None:
            return expr_kind(x, cols)

        match e:
            case Lit():
                return self.lit(e, ctx)
            case Field(index=i):
                return ref(i)
            case Un(op="not", arg=a):
                return d.not3(go(a, "bool"))
            case Un(op="is_null", arg=a):
                return d.is_null(go(a))
            case Un(op="neg", arg=a):
                if kind(a) == "interval":
                    return d.interval_sub(d.interval_lit(0), go(a))
                return d.int_neg(self.int_operand(a, ref, cols, "negation"))
            case Un(op="itof", arg=a):
                return d.int_to_float(self.int_operand(a, ref, cols, "CAST to DOUBLE"))
            case Un(op="fneg", arg=a):
                return d.float_neg(self.float_operand(a, ref, cols))
            case Un(op="ffloor" | "fceil" | "fround" as op, arg=a):
                f = {"ffloor": d.float_floor, "fceil": d.float_ceil, "fround": d.float_round}[op]
                return f(self.float_operand(a, ref, cols))
            case Un(op="froundTo", arg=a, digits=digits):
                return d.float_round_to(self.float_operand(a, ref, cols), digits)
            case Un(op="ftoi", arg=a):
                return d.float_to_int(self.float_operand(a, ref, cols))
            case Un(op="itos", arg=a):
                return d.int_to_str(self.int_operand(a, ref, cols, "CAST to VARCHAR"))
            case Bin(op="and" | "or" as op, left=a, right=b):
                f = d.and3 if op == "and" else d.or3
                return f(go(a, "bool"), go(b, "bool"))
            case Bin(op="fadd" | "fsub" | "fmul" | "fdiv" | "fpow" as op, left=a, right=b):
                f = {
                    "fadd": d.float_add,
                    "fsub": d.float_sub,
                    "fmul": d.float_mul,
                    "fdiv": d.float_div,
                    "fpow": d.float_pow,
                }[op]
                return f(self.float_operand(a, ref, cols), self.float_operand(b, ref, cols))
            case Bin(op="add" | "sub" | "mul" as op, left=a, right=b):
                return self.arith(op, a, b, ref, cols)
            case Bin(op="idiv" | "imod" as op, left=a, right=b):
                what = "division" if op == "idiv" else "remainder"
                sa = self.int_operand(a, ref, cols, what)
                sb = self.int_operand(b, ref, cols, what)
                return d.int_div(sa, sb) if op == "idiv" else d.int_mod(sa, sb)
            case Bin(op="ipow", left=a, right=b):
                if isinstance(b, Lit) and b.value is None:
                    return d.null("int")
                sa = self.int_operand(a, ref, cols, "POWER")
                if isinstance(b, Lit) and isinstance(b.value, int) and b.kind == "int":
                    return d.int_pow(sa, b.value)
                return d.int_pow_var(sa, self.int_operand(b, ref, cols, "POWER"))
            case Bin(op="eq" | "lt" as op, left=a, right=b):
                ka, kb = kind(a), kind(b)
                k = ka or kb
                if ka is not None and kb is not None and ka != kb:
                    raise Unsupported(f"comparison of {ka} with {kb}; cast one side first")
                if op == "lt" and k in ("str", "bool"):
                    # `BinFn.apply .lt` is only defined on integers (and the codes).
                    raise Unsupported(
                        f"ordering comparisons of {k} values are not in the Lean model"
                    )
                sa, sb = go(a, k), go(b, k)
                if k == "float":
                    return d.float_eq(sa, sb) if op == "eq" else d.float_lt(sa, sb)
                return d.eq(sa, sb) if op == "eq" else d.lt(sa, sb)
            case If(cond=c, then=t, orelse=o):
                k = kind(e) or ctx
                return d.case_when(go(c, "bool"), go(t, k), go(o, k))
        raise Unsupported(f"unsupported expression {e!r}")

    def int_operand(
        self, e: Expr, ref: Callable[[int], str], cols: list[Kind | None], what: str
    ) -> str:
        k = expr_kind(e, cols)
        if k not in ("int", None) or (k is None and not (isinstance(e, Lit) and e.value is None)):
            raise Unsupported(f"{what} needs an integer, not {k or 'a value of unknown type'}")
        sql = self.expr(e, ref, cols, "int")
        # Columns may be narrower than 64 bits; widen them so overflow means 64 bits.
        return sql if isinstance(e, Lit) or _is_int_arith(e) else self.d.cast(sql, "int")

    def float_operand(self, e: Expr, ref: Callable[[int], str], cols: list[Kind | None]) -> str:
        k = expr_kind(e, cols)
        if k != "float" and not (isinstance(e, Lit) and e.value is None):
            # Lean would read the integer as a double's code.
            raise Unsupported(
                f"double arithmetic on {k or 'a value of unknown type'}; cast it to DOUBLE first"
            )
        return self.expr(e, ref, cols, "float")

    def arith(
        self, op: str, a: Expr, b: Expr, ref: Callable[[int], str], cols: list[Kind | None]
    ) -> str:
        d = self.d
        ka, kb = expr_kind(a, cols), expr_kind(b, cols)
        sym = {"add": "+", "sub": "-", "mul": "*"}[op]
        if "float" in (ka, kb):
            raise Unsupported(
                f"integer {sym} on a double (Lean reads it as a code): needs an fp64 outputType"
            )
        temporal = {ka, kb} & {"time", "date", "interval"}
        if not temporal:
            name = {"add": "addition", "sub": "subtraction", "mul": "multiplication"}[op]
            sa, sb = self.int_operand(a, ref, cols, name), self.int_operand(b, ref, cols, name)
            return {"add": d.int_add, "sub": d.int_sub, "mul": d.int_mul}[op](sa, sb)
        if "date" in temporal:
            raise Unsupported(
                "date arithmetic is not in the Lean model (dates are days, intervals microseconds)"
            )
        sa, sb = self.expr(a, ref, cols, ka or kb), self.expr(b, ref, cols, kb or ka)
        match op, ka or kb, kb or ka:
            case "add", "time", "interval":
                return d.time_add_interval(sa, sb)
            case "add", "interval", "time":
                return d.time_add_interval(sb, sa)
            case "sub", "time", "interval":
                return d.time_sub_interval(sa, sb)
            case "sub", "time", "time":
                return d.time_diff(sa, sb)
            case "add", "interval", "interval":
                return d.interval_add(sa, sb)
            case "sub", "interval", "interval":
                return d.interval_sub(sa, sb)
        raise Unsupported(f"{ka} {sym} {kb} is not supported")


def _is_int_arith(e: Expr) -> bool:
    """Is `e` computed as a BIGINT already?"""
    if isinstance(e, Bin):
        return e.op in ("add", "sub", "mul", "idiv", "imod", "ipow")
    return isinstance(e, Un) and e.op in ("neg", "ftoi")


def _no_fields() -> str:
    raise Unsupported("virtual table rows cannot refer to fields")


def to_sql(plan: dict, dialect: Dialect, *, tie_free: bool = False) -> str:
    """SQL for a Substrait JSON plan, with the semantics `Rel.eval` gives it.

    The result has the plan's output names (`RelRoot.names`, else `c0`, …),
    and is ordered as Lean orders it when the plan has a FETCH or a window.
    Raises `Unsupported` for plans outside the Lean model.

    `tie_free=True` promises that no two rows tie on any window's PARTITION BY
    and ORDER BY columns (what a contract report's `deterministic` says). Then
    windows need no ordinal tiebreak, so engines without a stable scan order
    can run them; FETCH still needs one.
    """
    p = parse_plan(plan)
    n = arity(p.root)
    names = p.names or [f"c{i}" for i in range(n)]
    if len(names) != n:
        raise Unsupported(f"root names {names} do not match the plan's {n} columns")
    w = _Writer(dialect, tie_free)
    ordered = order_matters(p.root)
    a = w.alias()
    items = [f"{w.ref(a, w.c(i))} AS {dialect.quote(name)}" for i, name in enumerate(names)]
    rest = f"ORDER BY {w.asc(w.ordinal(a))}" if ordered else ""
    return w.select(items, dialect.subquery(w.rel(p.root, ordered), a), rest)
