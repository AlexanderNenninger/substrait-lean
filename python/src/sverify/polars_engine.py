"""Polars as a Substrait consumer, for the plans Lean writes.

`to_lazy` translates a Substrait JSON plan into a Polars `LazyFrame`. It reads
the form `substrait-check` writes (`Write.writePlan`: `--write` and the delta
plans of `--delta`), which holds only constructs the Lean `Rel` model has, so
the plan Polars runs is the `Rel` Lean checked (`engine.written_plan` turns
any plan the checker accepts into that form). Anything outside it raises
`Unsupported`; nothing falls back to a Polars default.

Semantics are pinned to `Rel.eval` rather than left to Polars:

* Filters and join conditions keep a row only when the condition is TRUE
  (`Value.isTrue`); `and`/`or` are Kleene's `and3`/`or3`, written out.
* Rows come out in `Rel.eval`'s list order: joins are left-major (each left
  row with its matches in right order, a left join's unmatched row in its
  place), unions concatenate and windows emit rows in their sort order.
  `FetchRel` then takes the same rows as Lean.
* Doubles compare by DataFusion's total order, as the float codes of
  `SubstraitLean/Float.lean` do: `-NaN < -inf < … < -0.0 < +0.0 < … < inf < NaN`,
  NaN equal to itself. Comparisons, join keys, window partitions and sort keys
  use an integer key with that order (`_float_key`).
* Integers are unbounded in Lean. Columns are widened to `Int64` on read, and
  arithmetic runs on 128 bits. A result outside 64 bits raises
  `IntegerOverflow` instead of wrapping as DataFusion does. Division and
  remainder truncate toward zero (`Int.tdiv`, `Int.tmod`; Polars floors).
* Runtime errors are the `Issue`s of `SubstraitLean/Safety.lean`, which a
  checked plan is proved free of. Each expression carries a per-row flag for
  each issue, masked by `CASE` as `Expr.issues` masks it (both sides of
  `AND`/`OR` count), and the operator raises the matching `RuntimeIssue` if it
  hits on a row it evaluates: a filter on its input, a project on every
  expression and row, a join's residual condition on the key matches.
* Window sorts are stable and place NULLs as each sort key says; partitions
  group NULLs together, as `samePart` does.
"""

from __future__ import annotations

import json
import math
from collections.abc import Mapping
from dataclasses import dataclass
from typing import Any

import numpy as np
import polars as pl
import pyarrow as pa

I64_MIN, I64_MAX = -(2**63), 2**63 - 1
US = pl.Datetime("us")
INTERVAL = pl.Duration("us")
_LEFT, _RIGHT = "__sv_left", "__sv_right"

#: A Polars dtype, as a class (`pl.Int64`) or an instance (`pl.Datetime("us")`).
DType = pl.DataType | type[pl.DataType]
Tables = Mapping[str, pl.LazyFrame | pl.DataFrame | pa.Table]


class Unsupported(ValueError):
    """The plan uses something the translator does not map to Polars."""


class RuntimeIssue(ArithmeticError):
    """A runtime error happened on a row the operator evaluates: one of the
    `Issue`s of `SubstraitLean/Safety.lean`, which a checked plan is proved
    free of."""


class IntegerOverflow(RuntimeIssue):
    """`+`, `-`, `*` or negation left 64 bits. DataFusion wraps around; the
    model's integers are unbounded, so the only faithful answer is to stop."""


class Overflow(RuntimeIssue):
    """`MIN / -1` or an integer `POWER` outside 64 bits: DataFusion fails."""


class DivisionByZero(RuntimeIssue):
    """Integer division or remainder by zero."""


class NegativeExponent(RuntimeIssue):
    """`POWER` of integers with a negative exponent."""


class BadCast(RuntimeIssue):
    """`CAST(double AS BIGINT)` of NaN, ±∞ or a value outside 64 bits."""


def col(i: int) -> str:
    """Columns are positional (Substrait refers to fields by ordinal)."""
    return f"c{i}"


# --- Doubles in total order ------------------------------------------------


def _total_order_bits(s: pl.Series) -> pl.Series:
    """IEEE bits mapped so that integer order is `f64::total_cmp`, with every
    NaN payload collapsed to one NaN per sign (the model has one NaN code per
    sign). Nulls are masked by the caller."""
    x = s.cast(pl.Float64).to_numpy(allow_copy=True).astype(np.float64)
    bits = x.view(np.int64)
    key = np.where(bits < 0, bits ^ np.int64(I64_MAX), bits)
    key = np.where(np.isnan(x), np.where(bits < 0, np.int64(I64_MIN), np.int64(I64_MAX)), key)
    return pl.Series(key, dtype=pl.Int64)


def _float_key(e: pl.Expr) -> pl.Expr:
    return (
        pl.when(e.is_null())
        .then(pl.lit(None, pl.Int64))
        .otherwise(e.map_batches(_total_order_bits, return_dtype=pl.Int64, is_elementwise=True))
    )


def ordered(e: pl.Expr, dtype: DType) -> pl.Expr:
    """A value that compares like the model's `Value`."""
    return _float_key(e) if dtype == pl.Float64 else e


# --- Literals ----------------------------------------------------------------


def _int(v: Any) -> int:
    i = int(v)
    if not I64_MIN <= i <= I64_MAX:
        raise Unsupported(f"integer {i} does not fit in 64 bits")
    return i


def _double(v: Any) -> float:
    if isinstance(v, str):
        named = {"NaN": "nan", "Infinity": "inf", "-Infinity": "-inf"}
        if v not in named:
            raise Unsupported(f"malformed double literal {v!r}")
        return float(named[v])
    return float(v)


def interval_micros(d: dict) -> int:
    """`intervalDayToSecond` in microseconds, as `Parse.intervalMicros`."""
    p = int(d.get("precision", 0))
    sub = int(d.get("subseconds", 0))
    sub_us = sub // 10 ** (p - 6) if p >= 6 else sub * 10 ** (6 - p)
    return (int(d.get("days", 0)) * 86400 + int(d.get("seconds", 0))) * 1_000_000 + sub_us


def null_type(t: dict) -> DType:
    """The dtype of a typed NULL. The writer types unknown kinds as `i64`, so
    those stay untyped (`pl.Null`) and take the type of what they meet."""
    if "fp64" in t or "fp32" in t:
        return pl.Float64
    if "string" in t:
        return pl.String
    if "bool" in t:
        return pl.Boolean
    if "precisionTimestamp" in t:
        if int(t["precisionTimestamp"].get("precision", 0)) != 6:
            raise Unsupported("only microsecond timestamps are supported")
        return US
    if "date" in t:
        return pl.Date
    if "i64" in t:
        return pl.Null
    raise Unsupported(f"unsupported NULL type {json.dumps(t)}")


def literal(lit: dict) -> tuple[Any, DType]:
    """A literal as a Python value and its dtype."""
    value = {k: v for k, v in lit.items() if k not in ("nullable", "typeVariationReference")}
    if len(value) != 1:
        raise Unsupported(f"malformed literal {json.dumps(lit)}")
    ((kind, v),) = value.items()
    if kind == "boolean":
        return bool(v), pl.Boolean
    if kind == "i64":
        return _int(v), pl.Int64
    if kind == "string":
        return str(v), pl.String
    if kind == "fp64":
        return _double(v), pl.Float64
    if kind == "null":
        return None, null_type(v)
    if kind == "precisionTimestamp":
        if int(v.get("precision", 0)) != 6:
            raise Unsupported("only microsecond timestamps are supported")
        return _int(v["value"]), US
    if kind == "date":
        return _int(v), pl.Date
    if kind == "intervalDayToSecond":
        return _int(interval_micros(v)), INTERVAL
    raise Unsupported(f"unsupported literal {json.dumps(lit)}")


def lit_expr(value: Any, dtype: DType) -> pl.Expr:
    if value is not None and dtype in (US, INTERVAL, pl.Date):
        # Temporal literals are given as their integer encoding.
        return pl.lit(value, pl.Int64 if dtype != pl.Date else pl.Int32).cast(dtype)
    return pl.lit(value, dtype)


# --- Expressions -----------------------------------------------------------

INTEGRAL = (pl.Int64, US, INTERVAL)


@dataclass(frozen=True)
class Issue:
    """A runtime error `Expr.issues` (`SubstraitLean/Safety.lean`) reports:
    `flag` is TRUE (never NULL) on the rows where it happens."""

    flag: pl.Expr
    kind: type[RuntimeIssue]
    message: str


@dataclass(frozen=True)
class Val:
    """A translated expression: its value, dtype and possible issues."""

    expr: pl.Expr
    dtype: DType
    issues: tuple[Issue, ...] = ()


def issues(*vals: Val) -> tuple[Issue, ...]:
    return tuple(i for v in vals for i in v.issues)


def issue(when: pl.Expr, kind: type[RuntimeIssue], message: str) -> Issue:
    return Issue(when.fill_null(False), kind, message)


def unify(a: DType, b: DType, what: str) -> DType:
    if a == pl.Null:
        return b
    if b == pl.Null or a == b:
        return a
    raise Unsupported(f"{what} of {a} and {b}")


def wide(v: Val) -> pl.Expr:
    """The physical value (microseconds for times and intervals) in 128 bits."""
    return v.expr.to_physical().cast(pl.Int128)


def narrow(w: pl.Expr, out: DType, what: str, *vals: Val, kind=None) -> Val:
    """A 128-bit result back in 64 bits. Leaving them is an issue: an error
    for `MIN / -1` (`kind`), and where DataFusion would wrap, `IntegerOverflow`
    (the model's integers are unbounded, so wrapping would be wrong)."""
    outside = (w < I64_MIN) | (w > I64_MAX)
    return Val(
        pl.when(outside).then(None).otherwise(w).cast(pl.Int64).cast(out),
        out,
        (*issues(*vals), issue(outside, kind or IntegerOverflow, f"{what} leaves 64 bits")),
    )


def arith_type(name: str, a: DType, b: DType) -> DType:
    """Result type of integer-like arithmetic. Timestamps and intervals are
    microseconds in the model, so they add like integers."""
    if a == pl.Null or b == pl.Null:
        return unify(a, b, name) if a in INTEGRAL or b in INTEGRAL else pl.Int64
    types: dict[tuple[str, DType, DType], DType] = {
        ("add", pl.Int64, pl.Int64): pl.Int64,
        ("add", US, INTERVAL): US,
        ("add", INTERVAL, US): US,
        ("add", INTERVAL, INTERVAL): INTERVAL,
        ("subtract", pl.Int64, pl.Int64): pl.Int64,
        ("subtract", US, INTERVAL): US,
        ("subtract", US, US): INTERVAL,
        ("subtract", INTERVAL, INTERVAL): INTERVAL,
        ("multiply", pl.Int64, pl.Int64): pl.Int64,
    }
    out = types.get((name, a, b))
    if out is None:
        raise Unsupported(f"{name} of {a} and {b}")
    return out


def _ieee_divide(s: pl.Series) -> pl.Series:
    x = s.struct.field("x").cast(pl.Float64).to_numpy(allow_copy=True).astype(np.float64)
    y = s.struct.field("y").cast(pl.Float64).to_numpy(allow_copy=True).astype(np.float64)
    with np.errstate(divide="ignore", invalid="ignore"):
        return pl.Series(np.divide(x, y), dtype=pl.Float64)


def fdiv(x: pl.Expr, y: pl.Expr) -> pl.Expr:
    """IEEE division. Polars divides a column by a constant by multiplying with
    its reciprocal, which rounds differently (`1.0000000000000004e16 / 10`);
    numpy divides each pair."""
    both = pl.struct(x.alias("x"), y.alias("y"))
    q = both.map_batches(_ieee_divide, return_dtype=pl.Float64, is_elementwise=True)
    return pl.when(x.is_null() | y.is_null()).then(None).otherwise(q)


def tdiv(a: pl.Expr, b: pl.Expr) -> pl.Expr:
    """Quotient truncated toward zero (`Int.tdiv`); Polars' `//` floors."""
    q = a // b
    return pl.when((a % b != 0) & ((a < 0) != (b < 0))).then(q + 1).otherwise(q)


def _ipow(s: pl.Series) -> pl.Series:
    """`BinFn.ipow` where it is defined and fits 64 bits, else NULL."""
    out = []
    for a, b in zip(s.struct.field("a").to_list(), s.struct.field("b").to_list(), strict=True):
        ok = a is not None and b is not None and b >= 0 and (b <= 64 or abs(a) <= 1)
        p = a**b if ok else None
        out.append(p if p is not None and I64_MIN <= p <= I64_MAX else None)
    return pl.Series(out, dtype=pl.Int64)


def ipow(a: Val, b: Val) -> Val:
    """Integer powers. Exponents beyond 64 overflow unless `|a| ≤ 1`."""
    both = pl.struct(a.expr.alias("a"), b.expr.alias("b"))
    value = both.map_batches(_ipow, return_dtype=pl.Int64, is_elementwise=True)
    known = a.expr.is_not_null() & b.expr.is_not_null()
    negative = known & (b.expr < 0)
    return Val(
        value,
        pl.Int64,
        (
            *issues(a, b),
            issue(negative, NegativeExponent, "POWER with a negative exponent"),
            issue(known & ~negative & value.is_null(), Overflow, "POWER leaves 64 bits"),
        ),
    )


def and3(a: pl.Expr, b: pl.Expr) -> pl.Expr:
    """Kleene conjunction: FALSE dominates, otherwise any NULL gives NULL."""
    return (
        pl.when(a.eq_missing(False) | b.eq_missing(False))
        .then(False)
        .when(a.eq_missing(True) & b.eq_missing(True))
        .then(True)
        .otherwise(pl.lit(None, pl.Boolean))
    )


def or3(a: pl.Expr, b: pl.Expr) -> pl.Expr:
    """Kleene disjunction: TRUE dominates, otherwise any NULL gives NULL."""
    return (
        pl.when(a.eq_missing(True) | b.eq_missing(True))
        .then(True)
        .when(a.eq_missing(False) & b.eq_missing(False))
        .then(False)
        .otherwise(pl.lit(None, pl.Boolean))
    )


def is_true(e: pl.Expr) -> pl.Expr:
    """`Value.isTrue`: NULL is not true."""
    return e.eq_missing(True)


def ftoi(v: Val) -> Val:
    """`CAST(double AS BIGINT)`: truncation toward zero (`FloatCode.toInt?`);
    NaN, ±∞ and results outside 64 bits are errors."""
    x = v.expr.cast(pl.Float64)
    t = pl.when(x >= 0).then(x.floor()).otherwise(x.ceil())
    bad = v.expr.is_nan() | v.expr.is_infinite() | (t < -(2.0**63)) | (t >= 2.0**63)
    value = pl.when(bad).then(None).otherwise(t).cast(pl.Int64, strict=False)
    return Val(value, pl.Int64, (*v.issues, issue(bad, BadCast, "CAST to BIGINT out of range")))


class Exprs:
    """Translates expressions over input columns of the given dtypes."""

    def __init__(self, functions: Mapping[int, str], dtypes: list[DType]):
        self.functions, self.dtypes = functions, dtypes

    def function(self, ref: Any) -> str:
        anchor = int(ref or 0)
        if anchor not in self.functions:
            raise Unsupported(f"function reference {anchor} is not declared in extensions")
        return self.functions[anchor].split(":")[0]

    def field(self, j: dict) -> int:
        if "outerReference" in j:
            raise Unsupported("outer references are not supported")
        sf = j["directReference"]["structField"]
        if "child" in sf:
            raise Unsupported("nested field references are not supported")
        i = int(sf.get("field", 0))
        if i >= len(self.dtypes):
            raise Unsupported(f"field {i} is out of range ({len(self.dtypes)} columns)")
        return i

    def __call__(self, j: dict) -> Val:
        if "literal" in j:
            v, t = literal(j["literal"])
            return Val(lit_expr(v, t), t)
        if "selection" in j:
            i = self.field(j["selection"])
            return Val(pl.col(col(i)), self.dtypes[i])
        if "cast" in j:
            return self.cast(j["cast"])
        if "ifThen" in j:
            return self.if_then(j["ifThen"])
        if "scalarFunction" in j:
            f = j["scalarFunction"]
            name = self.function(f.get("functionReference"))
            arg_js = [a["value"] for a in f.get("arguments", [])]
            if name == "round" and len(arg_js) == 2:
                return self.round_to(self(arg_js[0]), arg_js[1])
            return self.call(name, [self(a) for a in arg_js])
        raise Unsupported(f"unsupported expression {json.dumps(j)[:80]}")

    def cast(self, c: dict) -> Val:
        v = self(c["input"])
        target = c.get("type", {})
        if ("fp64" in target or "fp32" in target) and v.dtype in (pl.Int64, pl.Null):
            return Val(v.expr.cast(pl.Float64), pl.Float64, v.issues)
        if "i64" in target and v.dtype == pl.Float64:
            return ftoi(v)
        if "string" in target and v.dtype in (pl.Int64, pl.Null):
            return Val(v.expr.cast(pl.String), pl.String, v.issues)
        raise Unsupported(f"unsupported cast from {v.dtype} to {json.dumps(target)}")

    def if_then(self, t: dict) -> Val:
        """A `CASE` only evaluates the branch a row takes, so a branch's issues
        count only on its rows (`Expr.issues`)."""
        out = self(t["else"])
        for clause in reversed(t.get("ifs", [])):
            c = self(clause["if"])
            if c.dtype not in (pl.Boolean, pl.Null):
                raise Unsupported(f"IF condition of type {c.dtype}")
            then = self(clause["then"])
            taken = is_true(c.expr)
            out = Val(
                pl.when(taken).then(then.expr).otherwise(out.expr),
                unify(then.dtype, out.dtype, "IF branches"),
                (
                    *c.issues,
                    *(Issue(taken & i.flag, i.kind, i.message) for i in then.issues),
                    *(Issue(~taken & i.flag, i.kind, i.message) for i in out.issues),
                ),
            )
        return out

    def call(self, name: str, args: list[Val]) -> Val:
        types = [v.dtype for v in args]
        if name in ("and", "or") and args:
            if any(t not in (pl.Boolean, pl.Null) for t in types):
                raise Unsupported(f"{name} of {types}")
            op = and3 if name == "and" else or3
            acc = args[0].expr
            for v in args[1:]:
                acc = op(acc, v.expr)
            # Both sides are evaluated, so all their issues count.
            return Val(acc, pl.Boolean, issues(*args))
        if len(args) == 1:
            return self.unary(name, args[0])
        if len(args) == 2:
            return self.binary(name, *args)
        raise Unsupported(f"unsupported function {name}/{len(args)} on {types}")

    def unary(self, name: str, a: Val) -> Val:
        e, t = a.expr, a.dtype
        if name == "not" and t in (pl.Boolean, pl.Null):
            return Val(~e, pl.Boolean, a.issues)
        if name == "is_null":
            return Val(e.is_null(), pl.Boolean, a.issues)
        if name in ("negate", "subtract"):
            if t == pl.Float64:
                return Val(-e, t, a.issues)  # flips the sign bit, also of zeros and NaN
            if t in (pl.Int64, INTERVAL, pl.Null):
                return narrow(
                    pl.lit(0, pl.Int128) - wide(a), pl.Int64 if t == pl.Null else t, "negation", a
                )
        if t == pl.Float64:
            # Exact on doubles; ROUND's halves go away from zero (`roundMag`).
            # The sign of a zero result is kept, as `onMag` keeps it.
            if name == "floor":
                return Val(e.floor(), t, a.issues)
            if name == "ceil":
                return Val(e.ceil(), t, a.issues)
            if name == "round":
                return Val(e.round(0, mode="half_away_from_zero"), t, a.issues)
        raise Unsupported(f"unsupported function {name}/1 on {t}")

    def binary(self, name: str, a: Val, b: Val) -> Val:
        ta, tb = a.dtype, b.dtype
        floats = ("add", "subtract", "multiply", "divide", "power")
        if name in floats and pl.Float64 in (ta, tb):
            if unify(ta, tb, name) != pl.Float64:
                raise Unsupported(f"{name} of {ta} and {tb}")
            x, y = a.expr, b.expr
            ops = {"add": x + y, "subtract": x - y, "multiply": x * y, "divide": fdiv(x, y),
                   "power": x.pow(y)}  # fmt: skip
            return Val(ops[name], pl.Float64, issues(a, b))
        if name in ("add", "subtract", "multiply"):
            out = arith_type(name, ta, tb)
            x, y = wide(a), wide(b)
            w = {"add": x + y, "subtract": x - y, "multiply": x * y}[name]
            return narrow(w, out, name, a, b)
        if name in ("divide", "modulus", "power"):
            if unify(ta, tb, name) not in (pl.Int64, pl.Null):
                raise Unsupported(f"{name} of {ta} and {tb}")
            if name == "power":
                return ipow(a, b)
            x, y = wide(a), wide(b)
            zero = b.expr.eq_missing(0)
            y = pl.when(zero).then(1).otherwise(y)
            by_zero = issue(zero & a.expr.is_not_null(), DivisionByZero, f"{name} by zero")
            if name == "modulus":
                r = (x - y * tdiv(x, y)).cast(pl.Int64)
                return Val(pl.when(zero).then(None).otherwise(r), pl.Int64,
                           (*issues(a, b), by_zero))  # fmt: skip
            q = narrow(tdiv(x, y), pl.Int64, "division", a, b, kind=Overflow)
            return Val(pl.when(zero).then(None).otherwise(q.expr), pl.Int64,
                       (*q.issues, by_zero))  # fmt: skip
        if name in ("equal", "lt"):
            t = unify(ta, tb, name)
            if name == "lt" and t not in (*INTEGRAL, pl.Date, pl.Float64, pl.Null):
                # `BinFn.lt` is only defined on integers (and the codes of
                # doubles and times); strings would differ from SQL.
                raise Unsupported(f"lt of {t}")
            ka, kb = ordered(a.expr, t), ordered(b.expr, t)
            return Val(ka == kb if name == "equal" else ka < kb, pl.Boolean, issues(a, b))
        raise Unsupported(f"unsupported function {name}/2 on {[ta, tb]}")

    def round_to(self, a: Val, digits: dict) -> Val:
        """`ROUND(x, d)`, as `FloatCode.roundTo`: `round(x · p) / p` with native
        doubles, `p = 10^d`."""
        if "literal" not in digits or literal(digits["literal"])[1] != pl.Int64:
            raise Unsupported("ROUND digits must be an integer literal")
        if a.dtype != pl.Float64:
            raise Unsupported(f"round of {a.dtype}")
        p = math.pow(10.0, float(literal(digits["literal"])[0]))
        r = fdiv((a.expr * p).round(0, mode="half_away_from_zero"), pl.lit(p, pl.Float64))
        return Val(r, pl.Float64, a.issues)


# --- Relations ---------------------------------------------------------------


def _raise_issues(issues: tuple[Issue, ...]):
    def check(s: pl.Series) -> pl.Series:
        for k, i in enumerate(issues):
            hits = s.struct.field(f"i{k}")
            if hits.any():
                raise i.kind(f"{i.message} ({hits.sum()} row(s))")
        return pl.Series([True] * len(s), dtype=pl.Boolean)

    return check


def guard(lf: pl.LazyFrame, vals: list[Val]) -> pl.LazyFrame:
    """Raise if any row of `lf` runs into an issue of `vals`, which an operator
    evaluates on exactly these rows. A filter is never pruned, and `collect`
    keeps it in place (no predicate pushdown), so it sees the same rows."""
    found = issues(*vals)
    if not found:
        return lf
    flags = pl.struct([i.flag.alias(f"i{k}") for k, i in enumerate(found)])
    return lf.filter(
        flags.map_batches(_raise_issues(found), return_dtype=pl.Boolean, is_elementwise=True)
    )


Frame = tuple[pl.LazyFrame, list[DType]]


def positional(lf: pl.LazyFrame) -> pl.LazyFrame:
    return lf.rename({c: col(i) for i, c in enumerate(lf.collect_schema().names())})


def type_of(t: dict) -> DType:
    """The engine dtype for a declared column type."""
    if any(k in t for k in ("i8", "i16", "i32", "i64")):
        return pl.Int64
    if "fp64" in t or "fp32" in t:
        return pl.Float64
    if "string" in t or "varchar" in t or "fixedChar" in t:
        return pl.String
    if "bool" in t:
        return pl.Boolean
    if "precisionTimestamp" in t or "timestamp" in t:
        return US
    if "date" in t:
        return pl.Date
    if "intervalDayToSecond" in t:
        return INTERVAL
    raise Unsupported(f"unsupported column type {json.dumps(t)}")


def conform(e: pl.Expr, have: DType, want: DType, where: str) -> pl.Expr:
    """Load a table column as the model sees it: integers widened to 64 bits,
    single floats to doubles. Anything that would change values is refused."""
    if have == want:
        return e
    if want == pl.Int64 and have.is_integer() and have not in (pl.UInt64, pl.Int128):
        return e.cast(pl.Int64)
    if want == pl.Float64 and have == pl.Float32:
        return e.cast(pl.Float64)
    if want == pl.String and have == pl.Categorical:
        raise Unsupported(f"{where}: categorical strings are not supported")
    if have == pl.Null:
        return e.cast(want)
    raise Unsupported(f"{where}: column has type {have}, the plan expects {want}")


def materialize(t: DType) -> DType:
    """Untyped NULL columns are `i64`, like the writer's placeholder types."""
    return pl.Int64 if t == pl.Null else t


class Translator:
    def __init__(self, plan: dict, tables: Tables):
        self.functions = {
            int(e["extensionFunction"].get("functionAnchor", 0)): e["extensionFunction"]["name"]
            for e in plan.get("extensions", [])
            if "extensionFunction" in e
        }
        self.tables = tables

    def exprs(self, dtypes: list[DType]) -> Exprs:
        return Exprs(self.functions, dtypes)

    def rel(self, j: dict) -> Frame:
        kinds = ["read", "filter", "project", "cross", "join", "fetch", "set"]
        found = [k for k in kinds if k in j]
        if len(found) != 1 or len(j) != 1:
            raise Unsupported(f"unsupported relation {json.dumps(j)[:80]}")
        kind = found[0]
        r = j[kind]
        lf, dtypes = getattr(self, kind)(r)
        emit = r.get("common", {}).get("emit")
        if emit is not None:
            mapping = [int(i) for i in emit.get("outputMapping", [])]
            for i in mapping:
                if i >= len(dtypes):
                    raise Unsupported(f"emit refers to column {i} of {len(dtypes)}")
            lf = lf.select([pl.col(col(i)).alias(col(k)) for k, i in enumerate(mapping)])
            dtypes = [dtypes[i] for i in mapping]
        elif "common" in r and r["common"]:
            raise Unsupported(f"unsupported RelCommon {json.dumps(r['common'])}")
        return lf, dtypes

    def read(self, r: dict) -> Frame:
        for k in ("filter", "bestEffortFilter", "projection"):
            if k in r:
                raise Unsupported(f"ReadRel.{k} is not in Lean's written form")
        schema = r.get("baseSchema", {})
        types = [type_of(t) for t in schema.get("struct", {}).get("types", [])]
        if "namedTable" in r:
            name = ".".join(r["namedTable"]["names"])
            if name not in self.tables:
                raise KeyError(f"no data for table {name!r}")
            src = self.tables[name]
            if isinstance(src, pa.Table):
                src = pl.from_arrow(src)
            assert isinstance(src, pl.DataFrame | pl.LazyFrame)
            lf = positional(src.lazy())
            have = list(lf.collect_schema().dtypes())
            if len(have) != len(types):
                raise Unsupported(f"table {name} has {len(have)} columns, the plan {len(types)}")
            lf = lf.select(
                [
                    conform(pl.col(col(i)), h, w, f"{name} column {i}").alias(col(i))
                    for i, (h, w) in enumerate(zip(have, types, strict=True))
                ]
            )
            return lf, types
        if "virtualTable" in r:
            return self.values(r["virtualTable"], len(types))
        raise Unsupported(f"unsupported read {json.dumps(r)[:80]}")

    def values(self, v: dict, arity: int) -> Frame:
        if "values" in v:
            raise Unsupported("the deprecated VirtualTable.values encoding is not written by Lean")
        rows = []
        for row in v.get("expressions", []):
            fields = row.get("fields", [])
            if len(fields) != arity:
                raise Unsupported(f"virtual table row has {len(fields)} fields, not {arity}")
            vals = []
            for f in fields:
                if "literal" not in f:
                    raise Unsupported("virtual table fields must be literals")
                vals.append(literal(f["literal"]))
            rows.append(vals)
        dtypes: list[DType] = []
        for i in range(arity):
            t: DType = pl.Null
            for row in rows:
                t = unify(t, row[i][1], f"virtual table column {i}")
            dtypes.append(materialize(t))
        data = {
            col(i): pl.Series([row[i][0] for row in rows], dtype=pl.Int64 if dt in INTEGRAL else dt)
            for i, dt in enumerate(dtypes)
        }
        lf = pl.LazyFrame(data).with_columns(
            [pl.col(col(i)).cast(dt) for i, dt in enumerate(dtypes)]
        )
        return lf, dtypes

    def filter(self, r: dict) -> Frame:
        lf, dtypes = self.rel(r["input"])
        cond = self.exprs(dtypes)(r["condition"])
        if cond.dtype not in (pl.Boolean, pl.Null):
            raise Unsupported(f"filter condition of type {cond.dtype}")
        return guard(lf, [cond]).filter(is_true(cond.expr)), dtypes

    def project(self, r: dict) -> Frame:
        lf, dtypes = self.rel(r["input"])
        es = r.get("expressions", [])
        wins = [e for e in es if "windowFunction" in e]
        if wins:
            if len(wins) != len(es):
                raise Unsupported("a project mixing window functions and scalars is not written")
            return self.window(lf, dtypes, [e["windowFunction"] for e in es])
        ex = self.exprs(dtypes)
        new = [ex(e) for e in es]
        out = [materialize(v.dtype) for v in new]
        n = len(dtypes)
        # Every expression is evaluated on every row, used later or not.
        lf = guard(lf, new).with_columns(
            [
                v.expr.cast(t).alias(col(n + k))
                for k, (v, t) in enumerate(zip(new, out, strict=True))
            ]
        )
        return lf, dtypes + out

    def window(self, lf: pl.LazyFrame, dtypes: list[DType], ws: list[dict]) -> Frame:
        """`Rel.window`: sort stably by the keys (NULLs placed per key), then
        each row sees its partition's rows before and after it."""
        ex = self.exprs(dtypes)
        part, sorts = ws[0].get("partitions", []), ws[0].get("sorts", [])
        for w in ws:
            if w.get("partitions", []) != part or w.get("sorts", []) != sorts:
                raise Unsupported("window functions in one project must share PARTITION/ORDER BY")
        by, desc, nulls_last = [], [], []
        directions = {
            "SORT_DIRECTION_ASC_NULLS_FIRST": (False, False),
            "SORT_DIRECTION_ASC_NULLS_LAST": (False, True),
            "SORT_DIRECTION_DESC_NULLS_FIRST": (True, False),
            "SORT_DIRECTION_DESC_NULLS_LAST": (True, True),
        }
        for s in sorts:
            d = s.get("direction")
            if d not in directions:
                raise Unsupported(f"unsupported sort direction {d}")
            key = self.column(ex, s["expr"])
            by.append(ordered(key.expr, key.dtype))
            desc.append(directions[d][0])
            nulls_last.append(directions[d][1])
        keys = [ordered(v.expr, v.dtype) for v in (self.column(ex, p) for p in part)]
        if by:
            lf = lf.sort(by, descending=desc, nulls_last=nulls_last, maintain_order=True)
        n = len(dtypes)
        new, out = [], []
        for k, w in enumerate(ws):
            name = ex.function(w.get("functionReference"))
            args = [a["value"] for a in w.get("arguments", [])]
            if name == "row_number" and not args:
                e: pl.Expr = pl.int_range(1, pl.len() + 1, dtype=pl.Int64)
                t: DType = pl.Int64
            elif name in ("lag", "lead") and 1 <= len(args) <= 3:
                arg = self.column(ex, args[0])
                c, t = arg.expr, arg.dtype
                offset = 1
                if len(args) > 1:
                    if "literal" not in args[1] or literal(args[1]["literal"])[1] != pl.Int64:
                        raise Unsupported(f"{name} offsets must be integer literals")
                    offset = literal(args[1]["literal"])[0]
                    if offset < 0:
                        raise Unsupported(f"negative {name} offset")
                default = pl.lit(None, t)
                if len(args) > 2:
                    if "literal" not in args[2]:
                        raise Unsupported(f"{name} defaults must be literals")
                    v, dt = literal(args[2]["literal"])
                    unify(t, dt, f"{name} default")
                    default = lit_expr(v, t if dt == pl.Null else dt)
                e = c.shift(offset if name == "lag" else -offset, fill_value=default)
            else:
                raise Unsupported(f"unsupported window function {name}/{len(args)}")
            new.append((e.over(keys) if keys else e).cast(materialize(t)).alias(col(n + k)))
            out.append(materialize(t))
        return lf.with_columns(new), dtypes + out

    @staticmethod
    def column(ex: Exprs, j: dict) -> Val:
        if "selection" not in j:
            raise Unsupported("window partitions, sort keys and arguments must be columns")
        return ex(j)

    def pair(self, r: dict) -> tuple[pl.LazyFrame, pl.LazyFrame, list[DType], int]:
        left, lt = self.rel(r["left"])
        right, rt = self.rel(r["right"])
        n = len(lt)
        right = right.rename({col(i): col(n + i) for i in range(len(rt))})
        return left, right, lt + rt, n

    def cross(self, r: dict) -> Frame:
        left, right, dtypes, _ = self.pair(r)
        return left.join(right, how="cross", maintain_order="left_right"), dtypes

    def join(self, r: dict) -> Frame:
        """`Rel.join`. Equalities between a left and a right column become
        hash-join keys with NULLs never matching (`nulls_equal=False`, as
        `isTrue (eq NULL _)` is false); the rest of the condition filters the
        matches. Row indices restore `Rel.eval`'s order."""
        how = {"JOIN_TYPE_INNER": "inner", "JOIN_TYPE_LEFT": "left"}.get(r.get("type", ""))
        if how is None:
            raise Unsupported(f"unsupported join type {r.get('type')}")
        if "postJoinFilter" in r:
            raise Unsupported("JoinRel.postJoinFilter is not supported")
        left, right, dtypes, n = self.pair(r)
        ex = self.exprs(dtypes)
        cond = r.get("expression", {"literal": {"boolean": True}})
        keys_l, keys_r, rest = [], [], []
        for c in self.conjuncts(cond, ex):
            pair = self.equi_key(c, ex, dtypes, n)
            if pair is None:
                rest.append(c)
            else:
                keys_l.append(pair[0])
                keys_r.append(pair[1])
        left = left.with_row_index(_LEFT)
        right = right.with_row_index(_RIGHT)
        if keys_l:
            matches = left.join(
                right,
                left_on=keys_l,
                right_on=keys_r,
                how="inner",
                nulls_equal=False,
                coalesce=False,
                maintain_order="left_right",
            )
        else:
            matches = left.join(right, how="cross", maintain_order="left_right")
        if rest:
            # The rest of the condition, as one `and3` evaluated on every match.
            conds = [ex(c) for c in rest]
            for c in conds:
                if c.dtype not in (pl.Boolean, pl.Null):
                    raise Unsupported(f"join condition of type {c.dtype}")
            on = conds[0].expr
            for c in conds[1:]:
                on = and3(on, c.expr)
            matches = guard(matches, conds).filter(is_true(on))
        cols = [col(i) for i in range(len(dtypes))]
        if how == "left":
            unmatched = left.join(matches.select(_LEFT), on=_LEFT, how="anti").with_columns(
                [pl.lit(None, dtypes[i]).alias(col(i)) for i in range(n, len(dtypes))]
                + [pl.lit(None, pl.UInt32).alias(_RIGHT)]
            )
            matches = pl.concat(
                [matches.select(_LEFT, _RIGHT, *cols), unmatched.select(_LEFT, _RIGHT, *cols)]
            )
        ordered_rows = matches.sort([_LEFT, _RIGHT], nulls_last=True, maintain_order=True)
        return ordered_rows.select(cols), dtypes

    def conjuncts(self, j: dict, ex: Exprs) -> list[dict]:
        f = j.get("scalarFunction")
        if f is not None and ex.function(f.get("functionReference")) == "and":
            return [c for a in f.get("arguments", []) for c in self.conjuncts(a["value"], ex)]
        return [j]

    def equi_key(
        self, j: dict, ex: Exprs, dtypes: list[DType], n: int
    ) -> tuple[pl.Expr, pl.Expr] | None:
        """`left col = right col` (either way round) of one type, as join keys."""
        f = j.get("scalarFunction")
        if f is None or ex.function(f.get("functionReference")) != "equal":
            return None
        args = [a["value"] for a in f.get("arguments", [])]
        if len(args) != 2 or not all("selection" in a for a in args):
            return None
        i, k = sorted(ex.field(a["selection"]) for a in args)
        if not (i < n <= k) or dtypes[i] != dtypes[k]:
            return None
        return ordered(pl.col(col(i)), dtypes[i]), ordered(pl.col(col(k)), dtypes[k])

    def fetch(self, r: dict) -> Frame:
        if "offsetExpr" in r or "countExpr" in r:
            raise Unsupported("FetchRel offsetExpr/countExpr are not in Lean's written form")
        lf, dtypes = self.rel(r["input"])
        offset = int(r.get("offset", 0))
        count = int(r["count"]) if "count" in r else -1
        if offset < 0:
            raise Unsupported("negative FetchRel offset")
        return lf.slice(offset, None if count < 0 else count), dtypes

    def set(self, r: dict) -> Frame:
        if r.get("op") != "SET_OP_UNION_ALL":
            raise Unsupported(f"unsupported set operation {r.get('op')}")
        inputs = [self.rel(i) for i in r.get("inputs", [])]
        if not inputs:
            raise Unsupported("SetRel without inputs")
        arity = len(inputs[0][1])
        if any(len(t) != arity for _, t in inputs):
            raise Unsupported("union inputs differ in arity")
        out: list[DType] = []
        for i in range(arity):
            t: DType = pl.Null
            for _, ts in inputs:
                t = unify(t, ts[i], f"union column {i}")
            out.append(t)
        frames = [
            lf.with_columns([pl.col(col(i)).cast(t) for i, t in enumerate(out)]) for lf, _ in inputs
        ]
        return pl.concat(frames, how="vertical"), out


def to_lazy(plan: str | dict, tables: Tables) -> pl.LazyFrame:
    """The `LazyFrame` for a plan in Lean's written form, over `tables`
    (by name; columns in schema order). Columns are named by `RelRoot.names`."""
    p = json.loads(plan) if isinstance(plan, str) else plan
    roots = [r["root"] for r in p.get("relations", []) if "root" in r]
    if len(roots) != 1:
        raise Unsupported("plan must have exactly one root relation")
    lf, dtypes = Translator(p, tables).rel(roots[0]["input"])
    names = roots[0].get("names") or [col(i) for i in range(len(dtypes))]
    if len(names) != len(dtypes):
        raise Unsupported(f"root names {names} do not match arity {len(dtypes)}")
    return lf.select([pl.col(col(i)).alias(name) for i, name in enumerate(names)])


def collect(lf: pl.LazyFrame) -> pl.DataFrame:
    """Run a translated plan. Predicate pushdown would move `guard`s (and
    filters) below the filters that come before them, onto rows the plan
    never evaluates there, so it is off."""
    return lf.collect(optimizations=pl.QueryOptFlags(predicate_pushdown=False))


def run(plan: str | dict, tables: Tables) -> pa.Table:
    """Run a plan in Lean's written form on Polars."""
    return collect(to_lazy(plan, tables)).to_arrow()
