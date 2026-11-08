"""Polars as a Substrait consumer, for the plans Lean writes.

Internal: not part of sverify's public API, which is `sverify`, `sverify.io`,
`sverify.engines` and `sverify.errors`; it may change in any release.

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
* Doubles have one zero and one NaN, as the float codes of
  `SubstraitLean/Float.lean` do: `-inf < … < 0.0 < … < inf < NaN`, `-0.0` is
  `0.0` and NaN equals itself. Comparisons, join keys, window partitions and
  sort keys use a key with that order (`_float_key`: the one zero and the
  one positive NaN, which Polars orders and compares that way), and doubles
  read from a table or made by an operation that can give `-0.0` go through
  `canon`.
* Integers are unbounded in Lean. Columns are widened to `Int64` on read.
  `+`, `-` and `*` of `Int64` run natively, and a guard on 128 bits raises
  `IntegerOverflow` where Polars would wrap. Division and remainder truncate
  toward zero (`Int.tdiv`, `Int.tmod`; Polars floors).
* Where Polars's native value differs from the reference's on inputs the
  reference does not raise on, a shim of `sverify._polars_shims` gives the
  reference's (#444): truncating division, `ROUND`'s halves, an empty `SUM`,
  the integer `AVG`, one zero, each sort key's NULL placement and stable
  ties. `SUM` and `AVG` of a group run as Polars's own aggregations, with
  those shims; Polars adds doubles in its own order (`sum_order`:
  `SEQUENTIAL`, `ANY` or `COMPENSATED`), within the plan's bound of the
  reference's correctly rounded sum (D25).
* Runtime errors are the `Issue`s of `SubstraitLean/Safety.lean`, which a
  checked plan is proved free of. Each expression carries a per-row flag for
  each issue, masked by `CASE` as `Expr.issues` masks it (both sides of
  `AND`/`OR` count), and the operator raises the matching `RuntimeIssue` if it
  hits on a row it evaluates: a filter on its input, a project on every
  expression and row, a join's residual condition on the key matches.
* Sorts (`SortRel`, and the sort of a window) are stable and place NULLs as
  each key says; window partitions group NULLs together, as `samePart` does,
  and `DISTINCT` keeps the first of equal rows (`dedup`), NULLs equal.
* Strings are sequences of Unicode scalar values (`SubstraitLean/Text.lean`):
  positions and lengths count characters, not bytes. `UPPER`, `LOWER` and
  regular expressions are black boxes in Lean; Polars computes them with the
  same Rust code DataFusion uses (`str::to_uppercase`, the `regex` crate).
* `date_part` and `date_trunc` follow `SubstraitLean/Time.lean`: sub-day
  parts and truncations are integer arithmetic on the microseconds, calendar
  ones go through Polars' calendar, and the calendar functions raise outside
  the reference's timestamps, 0001-01-01 to 9999-12-31 (D32).
"""

from __future__ import annotations

import itertools
import json
import math
import re
from collections.abc import Collection, Mapping
from dataclasses import dataclass
from decimal import Decimal
from typing import Any

import pyarrow as pa

from sverify import _decimals, _plan_read, _support
from sverify import _polars_shims as shims
from sverify._plan_read import REPEAT_MAX, SUBSTR_MAX, US_PER_DAY
from sverify._support import DUCKDB_ONLY
from sverify._unsupported import Unsupported as _Unsupported

try:
    import polars as pl
except ImportError as e:
    raise ImportError("the Polars engine needs polars: pip install 'sverify[polars]'") from e

I64_MIN, I64_MAX = -(2**63), 2**63 - 1
US = pl.Datetime("us")
INTERVAL = pl.Duration("us")
_LEFT, _RIGHT = "__sv_left", "__sv_right"

#: A Polars dtype, as a class (`pl.Int64`) or an instance (`pl.Datetime("us")`).
DType = pl.DataType | type[pl.DataType]
Tables = Mapping[str, pl.LazyFrame | pl.DataFrame | pa.Table]


class Unsupported(_Unsupported):
    """The plan uses something the translator does not map to Polars
    (`sverify.errors.UnsupportedError`). DuckDB runs what the translator
    refuses, so a message that names no exit of its own ends with
    `engine="duckdb"` (`DUCKDB_ONLY`)."""

    def __init__(self, message: str) -> None:
        if "engine=" not in message:
            message = f"{message}; {DUCKDB_ONLY}"
        super().__init__(message)


class RuntimeIssue(ArithmeticError):
    """A runtime error happened on a row the operator evaluates: one of the
    `Issue`s of `SubstraitLean/Safety.lean`, which a checked plan is proved
    free of. `issue` is its `Issue.name`, which `guards` selects by."""

    issue = "raised by a guard"


class IntegerOverflow(RuntimeIssue):
    """`+`, `-`, `*` or negation left 64 bits. DataFusion wraps around; the
    model's integers are unbounded, so the only faithful answer is to stop."""

    issue = "overflow"


class SumOverflow(IntegerOverflow):
    """An integer `SUM` left 64 bits (`Issue.sumWraps`); Polars wraps."""

    issue = "SUM overflow"


class Overflow(RuntimeIssue):
    """`MIN / -1` or an integer `POWER` outside 64 bits: DataFusion fails."""

    issue = "overflow"


class DivisionByZero(RuntimeIssue):
    """Integer division or remainder by zero, or a double divided by zero."""

    issue = "division by zero"


class NegativeExponent(RuntimeIssue):
    """`POWER` of integers with a negative exponent."""

    issue = "negative exponent"


class BadCast(RuntimeIssue):
    """`CAST(double AS BIGINT)` of NaN, ±∞ or a value outside 64 bits."""

    issue = "cast out of range"


class BadRegex(RuntimeIssue):
    """A regular expression that does not compile."""

    issue = "invalid regular expression"


class DomainError(RuntimeIssue):
    """An argument outside a function's domain (`sqrt` of a negative, a
    shift count outside 0–63, …): Substrait's `on_domain_error` = ERROR."""

    issue = "domain error"


class InfiniteResult(RuntimeIssue):
    """An operation on finite doubles whose result is `±∞` (`Issue.infinite`,
    #575): an error of the reference, which verification rules out by an
    inferred precondition (`Report.assumed`) that the job checks on the data.
    Checked with or without guards, as a `SUM`'s overflow is."""

    issue = "overflow to infinity"


class SubnormalDivisor(RuntimeIssue):
    """A double divided by a subnormal: the translation's precondition for
    Polars's division, which goes through the divisor's reciprocal (PL-3,
    polars-double-scalar-divisor) and is within 2 ulps of IEEE's otherwise;
    the reciprocal of a subnormal overflows."""

    issue = "subnormal divisor"


#: The issues `guards=True` checks: every one.
ALL_GUARDS = frozenset(
    {"overflow", "SUM overflow", "division by zero", "negative exponent", "cast out of range",
     "invalid regular expression", "domain error", "raised by a guard", "overflow to infinity",
     "subnormal divisor"}
)  # fmt: skip
#: `guards=False`: the checks of the preconditions a `guard_free` report
#: assumes (`Issue.assumed`): integer `SUM`s fit, and no operation on finite
#: doubles gives `±∞` (#575).
NO_GUARDS = frozenset({"SUM overflow", "overflow to infinity", "subnormal divisor"})


def col(i: int) -> str:
    """Columns are positional (Substrait refers to fields by ordinal)."""
    return f"c{i}"


# --- Doubles: one zero, one NaN ---------------------------------------------


canon = shims.one_zero


def _float_key(e: pl.Expr) -> pl.Expr:
    """A double with the model's order and equality: `-0.0` is `0.0`, and
    every NaN is the one positive NaN, which Polars puts above `inf` and
    makes equal to itself in sorts, comparisons, groups and joins
    (polars-nan-order, polars-nan-equality, on both engines). Each step names
    `e` once."""
    return canon(e).fill_nan(math.nan)


#: `BinFn.greatest`/`least`, as Lean writes them (and as DataFusion does).
_PICKS = ("greatest", "least", "greatest_skip_null", "least_skip_null")


def ordered(e: pl.Expr, dtype: DType) -> pl.Expr:
    """A value that compares like the model's `Value`."""
    return _float_key(e) if dtype == pl.Float64 else e


# --- Literals ----------------------------------------------------------------


def _int(v: Any) -> int:
    i = int(v)
    if not I64_MIN <= i <= I64_MAX:
        raise Unsupported(f"integer {i} does not fit in 64 bits")
    return i


def interval_micros(d: dict) -> int:
    """`intervalDayToSecond` in microseconds, as `Parse.intervalMicros`."""
    return _plan_read.interval_micros(d, Unsupported)


def null_type(t: dict) -> DType:
    """The dtype of a typed NULL. The writer types unknown kinds as `i64`, so
    those stay untyped (`pl.Null`) and take the type of what they meet."""
    match _plan_read.type_kind(t):
        case "float", _:
            return pl.Float64
        case "str", _:
            return pl.String
        case "bool", _:
            return pl.Boolean
        case "time", p:
            if p != 6:
                raise Unsupported("only microsecond timestamps are supported")
            return US
        case "date", _:
            return pl.Date
        case "tod", _:
            return pl.Time
        case "int", _:
            return pl.Null
        case "decimal", (p, s):
            return decimal_type(p, s)
        case "list", elem:
            return pl.List(materialize(null_type(elem or {"i64": {}})))
        case "struct", fields:
            return struct_type([materialize(null_type(f)) for f in fields])
    raise Unsupported(f"unsupported NULL type {json.dumps(t)}")


def struct_type(fields: list[DType]) -> DType:
    """A struct of these field dtypes. The model's structs are positional:
    fields are named `f0`, `f1`, … (`conform` renames a column's)."""
    return pl.Struct([pl.Field(f"f{i}", t) for i, t in enumerate(fields)])


def literal(lit: dict) -> tuple[Any, DType]:
    """A literal as a Python value and its dtype."""
    kind, v = _plan_read.literal(lit, Unsupported)
    match kind:
        case "bool":
            return v, pl.Boolean
        case "int":
            # A virtual table's narrow column (Lean writes its rows typed).
            key, i = v
            return _int(i), {"i8": pl.Int8, "i16": pl.Int16, "i32": pl.Int32}.get(key, pl.Int64)
        case "str":
            return v, pl.String
        case "float":
            return v + 0.0, pl.Float64  # the one zero
        case "decimal":
            m, p, s = v
            return Decimal(m).scaleb(-s), decimal_type(p, s)
        case "null":
            return None, null_type(v)
        case "time":
            return _int(v), US
        case "date":
            return _int(v), pl.Date
        case "interval" if v[0] == 0:
            return _int(v[1]), INTERVAL
        case "tod":
            return _int(v), pl.Time
        case "emptyList":
            return [], pl.List(materialize(null_type(v)))
        case "struct":
            fields = [literal(e) for e in v]
            dtype = struct_type([materialize(t) for _, t in fields])
            return {f"f{i}": f for i, (f, _) in enumerate(fields)}, dtype
        case "list":
            elems = [literal(e) for e in v]
            t: DType = pl.Null
            for _, et in elems:
                t = unify(t, et, "list literal")
            return [e for e, _ in elems], pl.List(materialize(t))
    raise Unsupported(f"unsupported literal {json.dumps(lit)}")


def lit_expr(value: Any, dtype: DType) -> pl.Expr:
    if value is not None and dtype == pl.Time:
        # Polars' times are nanoseconds.
        return pl.lit(value * 1000, pl.Int64).cast(pl.Time)
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
    if is_decimal(a) and is_decimal(b) and a.scale == b.scale:  # pyrefly: ignore
        # One scale: the larger precision holds both (`Parse.decimalPassThrough`).
        return decimal_type(max(a.precision, b.precision), a.scale)  # pyrefly: ignore
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


# --- Decimals (#27) -----------------------------------------------------------
#
# A `DECIMAL(p, s)` is its unscaled integer (`UnFn.decimal`), and a value has
# the plan's type, `pl.Decimal(p, s)`. Polars computes every result of `+`,
# `-`, `*` and `/` as a `Decimal(38, max(s₁, s₂))`, rounding half to even
# (polars-decimal-arith); the reference's product has scale `s₁ + s₂`, exactly,
# a rescale rounds half away from zero, and a result of more than `p` digits
# is an overflow. So `+` and `-` (exact at the larger scale) run natively and
# are checked against `p`; a product, a rescale and a division run on the
# unscaled values (`to_physical`, an `Int128`), with the reference's rounding
# (`shims.decimal_round_half_away`, `shims.decimal_div_half_away`).

#: Polars's largest precision, and the reference's.
DEC_DIGITS = 38


def decimal_type(p: int, s: int) -> DType:
    if not 0 <= s <= p <= DEC_DIGITS or p == 0:
        raise Unsupported(f"DECIMAL({p}, {s}) is not a decimal type Polars has")
    return pl.Decimal(p, s)


def is_decimal(t: DType) -> bool:
    return isinstance(t, pl.Decimal)


def decimal_of(t: DType, what: str) -> tuple[int, int]:
    """`(p, s)` of a decimal operand; an integer is a `DECIMAL(19, 0)` and an
    untyped NULL a `DECIMAL(1, 0)` (`decimalCall`)."""
    if is_decimal(t):
        return t.precision, t.scale  # pyrefly: ignore
    if t == pl.Int64:
        return 19, 0
    if t == pl.Null:
        return 1, 0
    if t == pl.Float64:
        raise Unsupported(f"{what} of a DECIMAL and a double is not supported; cast one of them")
    raise Unsupported(f"{what} of a DECIMAL and {t} is not supported")


def unscaled(v: Val) -> pl.Expr:
    """The unscaled value of a decimal, or an integer, as an `Int128`."""
    return v.expr.to_physical() if is_decimal(v.dtype) else v.expr.cast(pl.Int128)


def of_unscaled(u: pl.Expr, s: int) -> pl.Expr:
    """The `Decimal(38, s)` whose unscaled value is the `Int128` `u`, which has
    at most 38 digits: `u` at scale 0 times `10⁻ˢ`, a product Polars computes
    exactly (its scale is the result's)."""
    return u.cast(pl.Decimal(DEC_DIGITS, 0)) * pl.lit(
        Decimal(1).scaleb(-s), pl.Decimal(DEC_DIGITS, s)
    )


def i128(n: int) -> pl.Expr:
    return pl.lit(n, pl.Int128)


def fit_decimal(
    u: pl.Expr,
    p: int,
    s: int,
    what: str,
    *vals: Val,
    bad: pl.Expr | None = None,
    kind: type[RuntimeIssue] | None = None,
) -> Val:
    """The unscaled `Int128` result `u` as a `DECIMAL(p, s)`; more than `p`
    digits is an overflow (`UnFn.decimal`), as is `bad`, where `u` is not the
    result (it would leave 128 bits)."""
    out = u.abs() >= i128(10**p)
    if bad is not None:
        out = bad | out
    value = of_unscaled(pl.when(out).then(None).otherwise(u), s).cast(pl.Decimal(p, s))
    found = issue(out, kind or IntegerOverflow, f"{what} leaves DECIMAL({p}, {s})")
    return Val(value, pl.Decimal(p, s), (*issues(*vals), found))


def decimal_rescale(v: Val, p: int, s: int, what: str) -> Val:
    """A decimal or an integer as a `DECIMAL(p, s)` (`UnFn.decimal`, `dround`):
    exact to a larger scale, half away from zero to a smaller one, where
    Polars's cast rounds half to even (polars-decimal-arith)."""
    s0 = decimal_of(v.dtype, what)[1]
    if s == s0:
        return fit_decimal(unscaled(v), p, s, what, v)
    if s > s0:
        # Exact; NULL past 38 digits, which overflows any `p`.
        up = v.expr.cast(pl.Decimal(DEC_DIGITS, s), strict=False)
        lost = up.is_null() & v.expr.is_not_null()
        u = pl.when(lost).then(i128(0)).otherwise(up.to_physical())
        return fit_decimal(u, p, s, what, v, bad=lost)
    return fit_decimal(shims.decimal_round_half_away(unscaled(v), s0 - s), p, s, what, v)


def decimal_mul(a: Val, b: Val, p: int, s: int) -> Val:
    """`a × b` at scale `s₁ + s₂`, exactly (`BinFn.dmul`): the product of the
    unscaled values. Polars's own product rounds to `max(s₁, s₂)`. It is
    computed only where it has at most `p` digits, so it never leaves 128
    bits: `|x| ≤ (10ᵖ − 1) // |y|`."""
    x, y = unscaled(a), unscaled(b)
    ay = y.abs()
    bad = (ay != 0) & (x.abs() > (i128(10**p - 1) // pl.when(ay == 0).then(i128(1)).otherwise(ay)))
    u = pl.when(bad).then(i128(0)).otherwise(x) * y
    return fit_decimal(u, p, s, "multiply", a, b, bad=bad)


def decimal_div(a: Val, b: Val, p: int, s: int) -> Val:
    """`a / b`, a decimal of scale `s₁` by an integer, at scale `s ≥ s₁`, half
    away from zero (`BinFn.ddiv`, `roundDivInt?`); NULL for `b = 0`."""
    s1 = decimal_of(a.dtype, "sverify_decimal_div")[1]
    if s - s1 > 18:
        raise Unsupported("sverify_decimal_div by more than 18 decimal places is not supported")
    x, n = unscaled(a), b.expr.cast(pl.Int128)
    u, bad = shims.decimal_div_half_away(x, n, s - s1)
    out = fit_decimal(u, p, s, "sverify_decimal_div", a, b, bad=bad.fill_null(False) & (n != 0))
    return Val(pl.when(n == 0).then(None).otherwise(out.expr), out.dtype, out.issues)


def _numpy() -> Any:
    """numpy, for the two operations of doubles Polars cannot do exactly
    (`fdiv`, `fmod`); imported only when a plan has them."""
    try:
        import numpy as np
    except ImportError as e:
        raise ImportError(
            "dividing doubles on Polars needs numpy: pip install 'sverify[polars]'"
        ) from e
    return np


#: The smallest normal double, 2⁻¹⁰²².
MIN_NORMAL = 2.0**-1022


def fdiv(x: pl.Expr, y: pl.Expr) -> pl.Expr:
    """Division of doubles, Polars's own. Where the divisor is a constant
    (a literal, or a column made from one), Polars multiplies by its
    reciprocal (PL-3, polars-double-scalar-divisor): `49.0 / 49.0` is
    `0.9999999999999999`. The reference's division is `approx` there, within
    2 ulps per division, given a divisor that is not subnormal
    (`subnormal_divisor`, checked on the data)."""
    return x / y


def _exact_divide(s: pl.Series) -> pl.Series:
    np = _numpy()
    x = s.struct.field("x").cast(pl.Float64).to_numpy(allow_copy=True).astype(np.float64)
    y = s.struct.field("y").cast(pl.Float64).to_numpy(allow_copy=True).astype(np.float64)
    with np.errstate(divide="ignore", invalid="ignore", over="ignore"):
        return pl.Series(np.divide(x, y), dtype=pl.Float64)


def exact_div(x: pl.Expr, y: pl.Expr) -> pl.Expr:
    """IEEE division of each pair, by numpy: for `ROUND(x, d)`, whose
    division by `10^d` must round once (`FloatCode.roundTo`), and `log(x, b)`
    (`ln x / ln b`, `logb?`), where Polars's reciprocal (`fdiv`) would be an
    ulp off."""
    both = pl.struct(x.alias("x"), y.alias("y"))
    q = both.map_batches(_exact_divide, return_dtype=pl.Float64, is_elementwise=True)
    return pl.when(x.is_null() | y.is_null()).then(None).otherwise(q)


def subnormal_divisor(y: pl.Expr) -> pl.Expr:
    """Is `y` a subnormal double (not zero), whose reciprocal overflows?"""
    return (y != 0.0) & (y.abs() < MIN_NORMAL)


def _fmod(s: pl.Series) -> pl.Series:
    np = _numpy()
    x = s.struct.field("x").cast(pl.Float64).to_numpy(allow_copy=True).astype(np.float64)
    y = s.struct.field("y").cast(pl.Float64).to_numpy(allow_copy=True).astype(np.float64)
    with np.errstate(divide="ignore", invalid="ignore", over="ignore"):
        return pl.Series(np.fmod(x, y), dtype=pl.Float64)


def fmod(x: pl.Expr, y: pl.Expr) -> pl.Expr:
    """C's `fmod` (`FloatCode.fmod`), the sign of `x`, which is exact. Polars'
    `%` floors (the sign of `y`), makes `x % inf` NaN, and goes through the
    reciprocal of a constant divisor (PL-3: `49.0 % 49.0` is `49.0`); no
    Polars expression gives an exact remainder, and numpy's `fmod` is C's."""
    both = pl.struct(x.alias("x"), y.alias("y"))
    r = both.map_batches(_fmod, return_dtype=pl.Float64, is_elementwise=True)
    return pl.when(x.is_null() | y.is_null()).then(None).otherwise(r)


def _ipow(a: pl.Expr, b: pl.Expr) -> pl.Expr:
    """`BinFn.ipow` where it is defined and fits 64 bits, else NULL. For
    `|a| ≥ 2` a power past `2^64.5` (by `b · log2 |a|`, far from the
    boundary in doubles) overflows; below it Polars's `pow` on 128 bits is
    exact and the range is checked. `|a| ≤ 1` takes any exponent: `a`'s
    power by the exponent's parity."""
    tiny = a.is_between(-1, 1)
    huge = ~tiny & (a.cast(pl.Float64).abs().log(2) * b.cast(pl.Float64) > 64.5)
    e = pl.when(tiny | huge | (b < 0)).then(0).otherwise(b).clip(0, 127).cast(pl.UInt32)
    small = pl.when(b == 0).then(1).when(a == 1).then(1).when(a == 0).then(0)
    small = small.otherwise(1 - 2 * (b % 2))
    p = pl.when(tiny).then(small.cast(pl.Int128)).otherwise(a.cast(pl.Int128).pow(e))
    ok = a.is_not_null() & b.is_not_null() & (b >= 0) & ~huge & p.is_between(I64_MIN, I64_MAX)
    return pl.when(ok).then(p).cast(pl.Int64)


def ipow(a: Val, b: Val) -> Val:
    """Integer powers. Exponents beyond 64 overflow unless `|a| ≤ 1`."""
    value = _ipow(a.expr.cast(pl.Int64), b.expr.cast(pl.Int64))
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


# --- Strings (`SubstraitLean/Text.lean`) ------------------------------------


def _rows(fn, out: DType, *vals: Val) -> pl.Expr:
    """`fn` on each row's Python values, NULL if any argument is NULL. For
    the functions whose Polars counterparts count bytes or differ in edge
    cases; Python strings are sequences of code points, as Lean's are."""

    def apply(s: pl.Series) -> pl.Series:
        cols = [s.struct.field(f"a{k}").to_list() for k in range(len(vals))]
        return pl.Series(
            [None if None in xs else fn(*xs) for xs in zip(*cols, strict=True)], dtype=out
        )

    args = pl.struct([v.expr.alias(f"a{k}") for k, v in enumerate(vals)])
    return args.map_batches(apply, return_dtype=out, is_elementwise=True)


#: `FMath.name`s whose Polars counterparts are C's libm (as Lean's are).
FMATH_NATIVE = {
    "sqrt": pl.Expr.sqrt, "exp": pl.Expr.exp, "ln": pl.Expr.log, "sin": pl.Expr.sin,
    "cos": pl.Expr.cos, "tan": pl.Expr.tan, "asin": pl.Expr.arcsin, "acos": pl.Expr.arccos,
    "atan": pl.Expr.arctan,
}  # fmt: skip
#: Polars' `log10` is not libm's, and it has no `log2`: Python's `math` calls libm.
FMATH_ROWS = {"log10": math.log10, "log2": math.log2}


def fmath_domain_error(name: str, e: pl.Expr) -> pl.Expr | None:
    """`FMath.inDomain` fails (NaN is in every domain; Polars puts NaN
    above every number)."""
    if name == "sqrt":
        return e < 0.0
    if name in ("ln", "log10", "log2"):
        return e <= 0.0
    if name in ("asin", "acos"):
        return (e < -1.0) | ((e > 1.0) & ~e.is_nan())
    if name in ("sin", "cos", "tan"):
        # `±∞` would give NaN, which no operation creates (#257).
        return e.is_infinite()
    return None


def nan_case(name: str, x: pl.Expr, y: pl.Expr) -> pl.Expr:
    """Would IEEE make a new NaN of `x name y` (`nanCase`), which no
    operation creates (#257)? NaN arguments stay NaN."""
    inf = float("inf")
    x, y = x.cast(pl.Float64), y.cast(pl.Float64)
    if name in ("add", "subtract"):
        other = -inf if name == "add" else inf
        return ((x == inf) & (y == other)) | ((x == -inf) & (y == -other))
    if name == "multiply":
        return ((x == 0.0) & y.is_infinite()) | (x.is_infinite() & (y == 0.0))
    if name == "divide":
        return x.is_infinite() & y.is_infinite()
    if name == "modulus":
        return x.is_infinite() & ~y.is_nan()
    # `power`: a negative base, finite or `-inf` (`negInfPow`: IEEE's `+inf`
    # or `0`, Polars's NaN for `** 0.5`), to a finite power that is not a
    # whole number.
    return shims.fractional_power_of_negative(x, y)


#: `BitOp.name`.
BITWISE = (
    "bitwise_and", "bitwise_or", "bitwise_xor", "bitwise_shift_left", "bitwise_shift_right",
)  # fmt: skip


def shift_left(a: int, b: int) -> int:
    """`BitOp.shl` for `b` in 0–63: the bits shifted out are lost."""
    return ((a << b) + 2**63) % 2**64 - 2**63


_LIKE: dict[str, re.Pattern] = {}


def like(s: str, p: str) -> bool:
    """`Text.like`: `%` any characters, `_` one, a backslash makes the next
    character literal (a trailing one is itself)."""
    if p not in _LIKE:
        out, k = [], 0
        while k < len(p):
            c = p[k]
            if c == "\\" and k + 1 < len(p):
                out.append(re.escape(p[k + 1]))
                k += 2
                continue
            out.append(".*" if c == "%" else "." if c == "_" else re.escape(c))
            k += 1
        _LIKE[p] = re.compile("".join(out), re.DOTALL)
    return _LIKE[p].fullmatch(s) is not None


def ilike_regex(p: str) -> str:
    """`Text.ilike`'s pattern as a regular expression of the `regex` crate,
    whose `(?i)` folds case as DataFusion's `ILIKE` does (Unicode's simple
    case folding). Every literal character is an escape `\\x{…}`."""
    out, k = [], 0
    while k < len(p):
        c = p[k]
        if c == "\\" and k + 1 < len(p):
            c, k = p[k + 1], k + 1
            out.append(f"\\x{{{ord(c):X}}}")
        else:
            out.append(".*" if c == "%" else "." if c == "_" else f"\\x{{{ord(c):X}}}")
        k += 1
    return "(?is)^" + "".join(out) + "$"


def repeat(s: str, n: int) -> str:
    """`Text.repeatStr`, '' where it does not fit (the row raises)."""
    return s * n if n > 0 and len(s.encode()) * n <= REPEAT_MAX else ""


def ascii_code(s: str) -> int:
    """`Text.ascii`: the first code point, 0 for ''."""
    return ord(s[0]) if s else 0


def levenshtein(s: str, t: str) -> int:
    """`Text.levenshtein`: insertions, deletions and substitutions of characters."""
    prev = list(range(len(t) + 1))
    for i, c in enumerate(s, 1):
        cur = [i]
        for j, d in enumerate(t, 1):
            cur.append(min(prev[j] + 1, cur[j - 1] + 1, prev[j - 1] + (c != d)))
        prev = cur
    return prev[-1]


def substr(s: Val, a: Val, n: int | None) -> pl.Expr:
    """`Text.substr`: the characters at 1-based positions `a … a+n-1`."""
    start = wide(a) - 1
    lo = pl.max_horizontal(start, pl.lit(0, pl.Int128))
    if n is None:
        length = None
    else:
        # No string has 2^62 characters, so clipping changes nothing.
        hi = pl.max_horizontal(start + n, pl.lit(0, pl.Int128))
        length = pl.max_horizontal(hi - lo, pl.lit(0, pl.Int128)).clip(0, 2**62).cast(pl.Int64)
    lo = lo.clip(0, 2**62).cast(pl.Int64)
    return pl.when(a.expr.is_null()).then(None).otherwise(s.expr.str.slice(lo, length))


def regex_groups(p: str) -> int | None:
    """Entries of `regexp_match(s, p)` on a match (`_plan_read.regex_groups`).
    `None` if the pattern does not compile, asked of Polars, which compiles
    patterns with DataFusion's `regex` crate."""
    try:
        pl.Series([""], dtype=pl.String).str.contains(p)
    except pl.exceptions.ComputeError:
        return None
    return _plan_read.regex_groups(p, Unsupported)


# --- Times (`SubstraitLean/Time.lean`) ---------------------------------------

#: The reference's timestamps, 0001-01-01 00:00:00 to 9999-12-31
#: 23:59:59.999999 (`Time.tsMin`, `Time.tsMax`, D32), in microseconds.
TS_MIN, TS_MAX = -62135596800000000, 253402300799999999
OUTSIDE_TS = "outside the reference's timestamps (0001-01-01 to 9999-12-31)"
#: Sub-day parts as `(modulus, divisor)` of the microseconds (`Time.partOf`).
CLOCK_PARTS = {
    "hour": (US_PER_DAY, 3_600_000_000),
    "minute": (3_600_000_000, 60_000_000),
    "second": (60_000_000, 1_000_000),
    "millisecond": (60_000_000, 1000),
    "microsecond": (60_000_000, 1),
}
CLOCK_UNITS = {
    "microsecond": 1,
    "millisecond": 1000,
    "second": 1_000_000,
    "minute": 60_000_000,
    "hour": 3_600_000_000,
    "day": US_PER_DAY,
}
CALENDAR_UNITS = {"month": "1mo", "quarter": "1q", "year": "1y"}


def date_part(part: str, v: Val) -> Val:
    """`Time.datePart`, an error (`Overflow`) outside the reference's
    timestamps (`UnFn.issue`). A time of day is a timestamp on 1970-01-01, for
    its clock parts."""
    if v.dtype == pl.Time:
        if part not in CLOCK_PARTS:
            raise Unsupported(f"date_part {part!r} of a time of day")
        m, d = CLOCK_PARTS[part]
        tod = v.expr.to_physical().cast(pl.Int64) // 1000
        return Val((tod % m // d).cast(pl.Int64), pl.Int64, v.issues)
    us = v.expr.dt.epoch("us")
    if part in CLOCK_PARTS:
        m, d = CLOCK_PARTS[part]
        value = us % m // d
    elif part == "dow":
        # 1970-01-01 is a Thursday; Sunday is 0.
        value = (us // US_PER_DAY + 4) % 7
    else:
        dt = v.expr.dt
        calendar = {"year": dt.year, "quarter": dt.quarter, "month": dt.month,
                    "week": dt.week, "day": dt.day, "doy": dt.ordinal_day}  # fmt: skip
        if part not in calendar:
            raise Unsupported(f"unsupported date part {part!r}")
        value = calendar[part]()
    return ts_only(v, value.cast(pl.Int64), pl.Int64, f"date_part {part!r}")


def date_trunc(unit: str, v: Val) -> Val:
    """`Time.trunc` with the `Issue`s of `UnFn.issue`: to a week or longer,
    outside the reference's timestamps an error (`Overflow`); to a day or less,
    a result below 64 bits an error (`IntegerOverflow`)."""
    us = wide(v)
    if unit in CLOCK_UNITS:
        k = CLOCK_UNITS[unit]
        return narrow(us - us % k, US, f"date_trunc to a {unit}", v)
    if unit == "week":
        # Monday is 3 days before 1970-01-01.
        days = us // US_PER_DAY
        t = (days - (days + 3) % 7) * US_PER_DAY
    elif unit in CALENDAR_UNITS:
        # Polars's calendar on the timestamps the result counts for.
        inside = us.is_null() | ((us >= TS_MIN) & (us <= TS_MAX))
        safe = pl.when(inside).then(v.expr).otherwise(pl.lit(0, US))
        t = wide(Val(safe.dt.truncate(CALENDAR_UNITS[unit]), US))
    else:
        raise Unsupported(f"unsupported date_trunc unit {unit!r}")
    bad = (us > TS_MAX) | (us < TS_MIN) | (t < TS_MIN)
    value = pl.when(bad).then(None).otherwise(t).cast(pl.Int64).cast(US)
    return Val(value, US, (*v.issues, issue(bad, Overflow, f"date_trunc to a {unit} {OUTSIDE_TS}")))


#: The reference's dates, 0001-01-01 to 9999-12-31 (`Time.dayMin`, #251).
DAY_MIN, DAY_MAX = -719162, 2932896
#: The days Polars's calendar (chrono) computes, years -262143 to 262142:
#: wider ones are NULL before a calendar call, which Polars would fail on.
CHRONO_DAY_MIN, CHRONO_DAY_MAX = -96465292, 95026236


def _days(v: Val) -> pl.Expr:
    """A DATE as days since 1970-01-01 (`Int64`)."""
    return v.expr.to_physical().cast(pl.Int64)


def _as_date(d: pl.Expr) -> pl.Expr:
    return d.cast(pl.Int32).cast(pl.Date)


def add_months_days(m: int, d: pl.Expr) -> pl.Expr:
    """`Time.addMonths`: the same day `m` months later, or that month's last,
    as Polars's `offset_by` clamps it (polars-month-arith). Polars raises past
    the years chrono represents and evaluates every branch, so a day whose
    result could leave them is NULL before the call: a non-NULL day that
    gives NULL is out of range (`add_months` flags it)."""
    lo = CHRONO_DAY_MIN + 31 * (max(0, -m) + 1)
    hi = CHRONO_DAY_MAX - 31 * (max(0, m) + 1)
    if lo > hi:
        return pl.lit(None, pl.Int64)
    d = d.cast(pl.Int64)
    safe = pl.when((d >= lo) & (d <= hi)).then(d)
    return _as_date(safe).dt.offset_by(f"{m}mo").cast(pl.Int64)


def trunc_days(unit: str, d: pl.Expr) -> pl.Expr:
    """`Time.truncDay`, by Polars's calendar for months, quarters and years.
    `d` must be within the years chrono represents (the caller's range)."""
    if unit == "day":
        return d
    if unit == "week":
        return d - (d + 3) % 7
    every = {"month": "1mo", "quarter": "1q", "year": "1y"}.get(unit)
    if every is None:
        raise Unsupported(f"date_trunc of a date to a {unit} is not supported")
    d = d.cast(pl.Int64)
    safe = pl.when((d >= CHRONO_DAY_MIN) & (d <= CHRONO_DAY_MAX)).then(d)
    return _as_date(safe).dt.truncate(every).cast(pl.Int64)


def date_range(v: Val, days: pl.Expr, lo: int, hi: int, what: str, *vals: Val) -> Val:
    """`rangeIssue`: the DATE `days` computed from `v`, an error (`Overflow`)
    unless both are within `[lo, hi]` days."""
    x = _days(v)
    bad = (x < lo) | (x > hi) | (days < lo) | (days > hi)
    value = pl.when(bad).then(None).otherwise(days).cast(pl.Int32).cast(pl.Date)
    message = f"{what} outside the reference's dates (0001-01-01 to 9999-12-31)"
    return Val(value, pl.Date, (*issues(v, *vals), issue(bad, Overflow, message)))


def day_part(part: str, v: Val) -> Val:
    """`UnFn.dayPart`: the part of the date's midnight, an error (`Overflow`)
    outside the reference's dates."""
    x = _days(v)
    bad = (x < DAY_MIN) | (x > DAY_MAX)
    ts = (pl.when(bad).then(None).otherwise(x) * US_PER_DAY).cast(US)
    part_of = date_part(part, Val(ts, US, ()))
    message = f"date_part {part!r} outside the reference's dates (0001-01-01 to 9999-12-31)"
    return Val(part_of.expr, part_of.dtype, (*v.issues, issue(bad, Overflow, message)))


def add_months(m: int, v: Val) -> Val:
    """`UnFn.addMonths` of a date or a timestamp, with its `rangeIssue`."""
    if v.dtype == pl.Date:
        days = add_months_days(m, _days(v))
        # A day `add_months_days` cannot take: out of range.
        days = pl.when(v.expr.is_not_null() & days.is_null()).then(DAY_MAX + 1).otherwise(days)
        return date_range(v, days, DAY_MIN, DAY_MAX, "adding months")
    us = wide(v)
    shifted = add_months_days(m, us // US_PER_DAY)
    r = shifted * US_PER_DAY + us % US_PER_DAY
    lost = us.is_not_null() & shifted.is_null()
    bad = (us < TS_MIN) | (us > TS_MAX) | (r < TS_MIN) | (r > TS_MAX) | lost
    value = pl.when(bad).then(None).otherwise(r).cast(pl.Int64).cast(US)
    message = f"adding months {OUTSIDE_TS}"
    return Val(value, US, (*v.issues, issue(bad, Overflow, message)))


def ts_only(v: Val, value: pl.Expr, dtype: DType, what: str) -> Val:
    """`value`, an error (`Overflow`) where the timestamp `v` is outside the
    reference's timestamps (D32)."""
    us = wide(v)
    bad = (us < TS_MIN) | (us > TS_MAX)
    message = f"{what} {OUTSIDE_TS}"
    safe = pl.when(bad).then(None).otherwise(value)
    return Val(safe, dtype, (*v.issues, issue(bad, Overflow, message)))


def strftime(fmt: str, v: Val) -> Val:
    """`Time.strftime`: chrono's formatting, which Polars uses."""
    inside = (wide(v) >= TS_MIN) & (wide(v) <= TS_MAX)
    safe = pl.when(inside).then(v.expr)
    return ts_only(v, safe.dt.strftime(fmt), pl.String, "strftime")


def ftoi(v: Val) -> Val:
    """`CAST(double AS BIGINT)`: truncation toward zero (`FloatCode.toInt?`);
    NaN, ±∞ and results outside 64 bits are errors."""
    x = v.expr.cast(pl.Float64)
    t = pl.when(x >= 0).then(x.floor()).otherwise(x.ceil())
    bad = v.expr.is_nan() | v.expr.is_infinite() | (t < -(2.0**63)) | (t >= 2.0**63)
    value = pl.when(bad).then(None).otherwise(t).cast(pl.Int64, strict=False)
    return Val(value, pl.Int64, (*v.issues, issue(bad, BadCast, "CAST to BIGINT out of range")))


def narrow_int(v: Val, bits: int) -> Val:
    """`CAST(x AS INT)` to `bits` bits (`UnFn.narrow`): values that do not fit
    are errors."""
    lo, hi = -(2 ** (bits - 1)), 2 ** (bits - 1) - 1
    bad = (v.expr < lo) | (v.expr > hi)
    value = pl.when(bad).then(None).otherwise(v.expr).cast(pl.Int64)
    message = f"CAST to a {bits}-bit integer out of range"
    return Val(value, pl.Int64, (*v.issues, issue(bad, BadCast, message)))


def _floors(f: dict) -> bool:
    """Does the call state `division_type` = `FLOOR` (Polars's `//` and `%`)?"""
    return any(
        o.get("name") == "division_type" and (o.get("preference") or [None])[0] == "FLOOR"
        for o in f.get("options", [])
    )


class Exprs:
    """Translates expressions over input columns of the given dtypes, or, with
    `param`, a lambda's body over its parameter of that dtype (#94)."""

    def __init__(
        self, functions: Mapping[int, str], dtypes: list[DType], param: DType | None = None
    ):
        self.functions, self.dtypes, self.param = functions, dtypes, param

    def function(self, ref: Any) -> str:
        anchor = int(ref or 0)
        if anchor not in self.functions:
            raise Unsupported(f"function reference {anchor} is not declared in extensions")
        name = self.functions[anchor].split(":")[0]
        # sverify's own remainder of doubles (#256) is `modulus` on doubles.
        return "modulus" if name == "sverify_fmod" else name

    def field(self, j: dict) -> int:
        if "child" in j["directReference"]["structField"]:
            raise Unsupported("nested field references are not supported here")
        return self.field_index(j)

    def field_index(self, j: dict) -> int:
        if "outerReference" in j:
            raise Unsupported("outer references are not supported")
        if "expression" in j:
            raise Unsupported("a reference into an expression is not supported here")
        i = int(j["directReference"]["structField"].get("field", 0))
        if i >= len(self.dtypes):
            raise Unsupported(f"field {i} is out of range ({len(self.dtypes)} columns)")
        return i

    def __call__(self, j: dict) -> Val:
        if "literal" in j:
            v, t = literal(j["literal"])
            return Val(lit_expr(v, t), t)
        if "selection" in j:
            sel = j["selection"]
            if "expression" in sel:
                return self.segments(self(sel["expression"]), sel["directReference"])
            if self.param is not None:
                return self.parameter(sel)
            i = self.field_index(sel)
            column = Val(pl.col(col(i)), self.dtypes[i])
            child = sel["directReference"]["structField"].get("child")
            return column if child is None else self.segments(column, child)
        if "cast" in j:
            return self.cast(j["cast"])
        if "ifThen" in j:
            return self.if_then(j["ifThen"])
        if "scalarFunction" in j:
            f = j["scalarFunction"]
            name = self.function(f.get("functionReference"))
            arg_js = [a["value"] for a in f.get("arguments", [])]
            for o in f.get("options", []):
                # Lean's written plans spell the other modes as a `CASE`
                # (`Parse.divByZero`); this engine runs only those.
                prefs = o.get("preference") or ["ERROR"]
                if o.get("name") == "on_division_by_zero" and prefs[0] != "ERROR":
                    raise Unsupported(f"on_division_by_zero = {prefs}")
                # Wrap-around and clamping run on DuckDB only so far (#241).
                if o.get("name") == "overflow" and prefs[0] != "ERROR":
                    raise Unsupported(f"overflow = {prefs}")
            if name in ("divide", "modulus") and len(arg_js) == 2 and _floors(f):
                return self.floor_divide(name, self(arg_js[0]), self(arg_js[1]))
            if name in ("any_match", "all_match", "transform", "filter"):
                return self.higher_order(name, arg_js)
            if name in _PICKS:
                # A chain of `BinFn.greatest`/`least`, as one pick over its
                # values: nested `when`s would each read the whole chain.
                return self.pick(name, [self(v) for v in self.pick_leaves(name, arg_js)])
            if name == "round" and len(arg_js) == 2:
                return self.round_to(self(arg_js[0]), arg_js[1])
            if name == "power" and len(arg_js) == 2 and "literal" in arg_js[1]:
                # DataFusion's simplifier makes `power(x, 0)` a constant 1, even
                # for a NULL `x` (as `Parse.parseExpr`).
                v, t = literal(arg_js[1]["literal"])
                if repr(v) in ("0", "0.0"):
                    floats = pl.Float64 in (self(arg_js[0]).dtype, t)
                    one, dtype = (1.0, pl.Float64) if floats else (1, pl.Int64)
                    return Val(lit_expr(one, dtype), dtype)
            if name == "array_length" and len(arg_js) == 1:
                return self.regex_match(arg_js[0])
            if name == "replace" and len(arg_js) == 3:
                # `Text.replace` is Python's `str.replace` (an empty pattern too).
                s_, p_, r_ = (self(a) for a in arg_js)
                if any(v.dtype not in (pl.String, pl.Null) for v in (s_, p_, r_)):
                    raise Unsupported(f"replace of {[s_.dtype, p_.dtype, r_.dtype]}")
                out = _rows(str.replace, pl.String, s_, p_, r_)
                return Val(out, pl.String, issues(s_, p_, r_))

            if name in ("date_part", "date_trunc") and len(arg_js) == 2:
                which, ts = self.constant(arg_js[0], f"{name}'s unit"), self(arg_js[1])
                if not isinstance(which, str) or ts.dtype not in (US, pl.Date, pl.Time):
                    raise Unsupported(f"{name} of {ts.dtype} by {which!r}")
                if ts.dtype == pl.Time and name == "date_part":
                    return date_part(which.lower(), ts)
                if ts.dtype == pl.Time:
                    raise Unsupported("date_trunc of a time of day is not yet supported on Polars")
                if ts.dtype == pl.Date:
                    if name == "date_part":
                        return day_part(which.lower(), ts)
                    x = _days(ts)
                    safe = pl.when((x >= DAY_MIN) & (x <= DAY_MAX)).then(x)
                    t = trunc_days(which.lower(), safe)
                    return date_range(ts, t, DAY_MIN, DAY_MAX, f"date_trunc to a {which}")
                return (date_part if name == "date_part" else date_trunc)(which.lower(), ts)
            if name == "add" and len(arg_js) == 2:
                months = self.months(arg_js[1])
                if months is not None:
                    return add_months(months, self(arg_js[0]))
            if name == "date_bin" and len(arg_js) == 3:
                # `Time.bucket`, raising outside the reference's timestamps.
                iv, ts = self(arg_js[0]), self(arg_js[1])
                k, origin = self.constant(arg_js[0], "a bin"), self.constant(arg_js[2], "an origin")
                if iv.dtype != INTERVAL or ts.dtype != US or not isinstance(origin, int) or k <= 0:
                    raise Unsupported(f"date_bin of {ts.dtype} by {k!r} from {origin!r}")
                us = wide(ts)
                r = us - (us - origin) % k
                bad = (us < TS_MIN) | (us > TS_MAX) | (r < TS_MIN) | (r > TS_MAX)
                value = pl.when(bad).then(None).otherwise(r).cast(pl.Int64).cast(US)
                found = issue(bad, Overflow, f"date_bin {OUTSIDE_TS}")
                return Val(value, US, (*ts.issues, found))
            if name == "strftime" and len(arg_js) == 2:
                ts, fmt = self(arg_js[0]), self.constant(arg_js[1], "a strftime format")
                if ts.dtype != US or not isinstance(fmt, str):
                    raise Unsupported(f"strftime of {ts.dtype} by {fmt!r}")
                return strftime(fmt, ts)
            if name == "date_diff" and len(arg_js) == 2:
                a, b = self(arg_js[0]), self(arg_js[1])
                if a.dtype != pl.Date or b.dtype not in (pl.Date, pl.Null):
                    raise Unsupported(f"date_diff of {a.dtype} and {b.dtype}")
                return Val(_days(a) - _days(b), pl.Int64, issues(a, b))
            if name == "substring" and len(arg_js) in (2, 3):
                n = self.constant(arg_js[2], "substring length") if len(arg_js) == 3 else None
                if len(arg_js) == 3 and (not isinstance(n, int) or isinstance(n, bool) or n < 0):
                    raise Unsupported("substring lengths must be integer literals ≥ 0")
                start = next(
                    (o["preference"][0] for o in f.get("options", [])
                     if o.get("name") == "negative_start" and o.get("preference")),
                    "WRAP_FROM_END",
                )  # fmt: skip
                if start not in ("WRAP_FROM_END", "LEFT_OF_BEGINNING"):
                    raise Unsupported(f"substring with negative_start = {start}")
                wrap = start == "WRAP_FROM_END"
                return self.substring(self(arg_js[0]), self(arg_js[1]), n, wrap)
            args = [self(a) for a in arg_js]
            if any(is_decimal(v.dtype) for v in args):
                return self.decimal_call(name, args, f.get("outputType"))
            return self.call(name, args)
        raise Unsupported(f"unsupported expression {json.dumps(j)[:80]}")

    def decimal_call(self, name: str, args: list[Val], out_ty: dict | None) -> Val:
        """A call with a `DECIMAL` argument (#27), as `Parse.decimalCall` reads
        it: the result type from the operands', or the declared precision."""
        tys = [decimal_of(v.dtype, name) for v in args]
        declared = _plan_read.type_kind(out_ty) if isinstance(out_ty, dict) else None
        dp, ds = declared[1] if declared and declared[0] == "decimal" else (None, None)

        def scale(sc: int) -> int:
            # A plan that declares a smaller scale rounds, which is not modelled.
            if ds is not None and ds != sc:
                raise Unsupported(
                    f"{name}: a DECIMAL result of scale {ds} where the exact one has {sc} "
                    "is not supported"
                )
            return sc

        match name, args, tys:
            case (("add" | "subtract"), [a, b], [(p1, s1), (p2, s2)]):
                sc = scale(max(s1, s2))
                p = dp if dp is not None else _decimals.add((p1, s1), (p2, s2))[0]
                x, y = (v.expr.cast(pl.Decimal(DEC_DIGITS, 0)) if v.dtype == pl.Null else v.expr
                        for v in (a, b))  # fmt: skip
                # Exact at the larger scale (polars-decimal-arith).
                w = x + y if name == "add" else x - y
                return fit_decimal(w.to_physical(), p, sc, name, a, b)
            case "multiply", [a, b], [(p1, s1), (p2, s2)]:
                sc = scale(s1 + s2)
                if sc > DEC_DIGITS:
                    raise Unsupported(
                        "a DECIMAL product with more than 38 decimal places is not supported"
                    )
                p = dp if dp is not None else _decimals.mul((p1, s1), (p2, s2))[0]
                return decimal_mul(a, b, p, sc)
            case (("negate" | "subtract"), [a], _):
                return Val(-a.expr, a.dtype, a.issues)
            case "abs", [a], _:
                return Val(a.expr.abs(), a.dtype, a.issues)
            case "sverify_decimal_div", [a, b], [(_, s1), (_, 0)] if b.dtype in (pl.Int64, pl.Null):
                if dp is None or ds is None or ds < s1:
                    raise Unsupported("sverify_decimal_div needs a DECIMAL type of a larger scale")
                return decimal_div(a, b, dp, ds)
            case (("equal" | "lt"), [a, b], _):
                # Polars compares decimals of any scales, and with integers,
                # exactly (polars-decimal-compare).
                x, y = a.expr, b.expr
                return Val(x == y if name == "equal" else x < y, pl.Boolean, issues(a, b))
            case "is_null", [a], _:
                return self.unary(name, a)
        raise Unsupported(f"{name} of DECIMAL is not yet supported on Polars")

    @staticmethod
    def months(j: dict) -> int | None:
        """The months of a compound interval literal (Lean writes month
        intervals only added to a date or timestamp)."""
        c = j.get("literal", {}).get("intervalCompound")
        if c is None:
            return None
        if interval_micros(c.get("intervalDayToSecond", {})) != 0:
            raise Unsupported("an interval of months and days")
        return _plan_read.year_months(c.get("intervalYearToMonth", {}), Unsupported)

    @staticmethod
    def constant(j: dict, what: str) -> Any:
        if "literal" not in j:
            raise Unsupported(f"{what} must be a literal")
        return literal(j["literal"])[0]

    def regex_match(self, j: dict) -> Val:
        """`array_length(regexp_match(s, p))` (`UnFn.regexMatch`): the number
        of entries of the match, NULL if there is none."""
        f = j.get("scalarFunction")
        if f is None or self.function(f.get("functionReference")) != "regexp_match":
            raise Unsupported("array_length is only supported of regexp_match")
        args = [a["value"] for a in f.get("arguments", [])]
        if len(args) != 2:
            raise Unsupported("regexp_match with flags is not supported")
        s, p = self(args[0]), self.constant(args[1], "a regular expression")
        if s.dtype not in (pl.String, pl.Null) or not isinstance(p, str):
            raise Unsupported(f"regexp_match of {s.dtype} and {p!r}")
        groups = regex_groups(p)
        if groups is None:
            # The pattern is compiled whatever the input (`UnFn.issue`).
            bad = issue(pl.lit(True), BadRegex, f"invalid regular expression {p!r}")
            return Val(pl.lit(None, pl.Int64), pl.Int64, (*s.issues, bad))
        found = s.expr.str.contains(p)
        return Val(pl.when(found).then(pl.lit(groups, pl.Int64)), pl.Int64, s.issues)

    def substring(self, s: Val, a: Val, n: int | None, wrap: bool = True) -> Val:
        if s.dtype not in (pl.String, pl.Null) or a.dtype not in (pl.Int64, pl.Null):
            raise Unsupported(f"substring of {s.dtype} from {a.dtype}")
        # `Text.substrInRange` (#336): an offset or length out of range raises.
        bad = (a.expr < -SUBSTR_MAX) | (a.expr >= SUBSTR_MAX)
        if n is not None and n >= SUBSTR_MAX:
            bad = a.expr.is_not_null()
        err = issue(
            bad & s.expr.is_not_null(), DomainError, "substring offset or length out of range"
        )
        if wrap:
            # `Text.substrWrap`: a negative start counts from the end (#209).
            a = Val(shims.substring_wrap(a.expr, s.expr), pl.Int64, a.issues)
        return Val(substr(s, a, n), pl.String, (*issues(s, a), err))

    def cast(self, c: dict) -> Val:
        if c.get("failureBehavior") == "FAILURE_BEHAVIOR_RETURN_NULL":
            raise Unsupported("TRY_CAST is not yet supported on Polars")
        v = self(c["input"])
        target = c.get("type", {})
        if "decimal" in target or is_decimal(v.dtype):
            return self.decimal_cast(v, target)
        if ("fp64" in target or "fp32" in target) and v.dtype in (pl.Int64, pl.Null):
            return Val(v.expr.cast(pl.Float64), pl.Float64, v.issues)
        if "fp64" in target and v.dtype in (pl.Float64, pl.Float32):
            # `UnFn.widen`: a FLOAT as a DOUBLE, exactly (#208).
            return Val(v.expr.cast(pl.Float64), pl.Float64, v.issues)
        if "i64" in target and v.dtype == pl.Float64:
            return ftoi(v)
        if "i64" in target and v.dtype in (pl.Int64, pl.Null):
            # A typed NULL (`CAST(NULL AS BIGINT)`), or an integer as it is.
            return Val(v.expr.cast(pl.Int64), pl.Int64, v.issues)
        if (bits := next((n for n in (8, 16, 32) if f"i{n}" in target), None)) and v.dtype in (
            pl.Int64,
            pl.Null,
        ):
            return narrow_int(v, bits)
        if "string" in target and v.dtype in (pl.Int64, pl.Null):
            return Val(v.expr.cast(pl.String), pl.String, v.issues)
        if "precisionTime" in target and v.dtype == US:
            # `UnFn.timeOfDay`; Polars' times are nanoseconds.
            tod = (wide(v) % US_PER_DAY * 1000).cast(pl.Int64).cast(pl.Time)
            return ts_only(v, tod, pl.Time, "CAST to TIME")
        if "precisionTimestamp" in target and v.dtype in (pl.Int64, pl.Null):
            # `UnFn.asTime`: microseconds since 1970-01-01.
            return Val(v.expr.cast(pl.Int64).cast(US), US, v.issues)
        if "date" in target and v.dtype == US:
            # `UnFn.toDate`: days since 1970-01-01, rounding down.
            days = v.expr.dt.epoch("us") // US_PER_DAY
            return Val(days.cast(pl.Int32).cast(pl.Date), pl.Date, v.issues)
        raise Unsupported(f"unsupported cast from {v.dtype} to {json.dumps(target)}")

    def decimal_cast(self, v: Val, target: dict) -> Val:
        """Casts to and from decimals (#27), as the parser reads them."""
        kind, arg = _plan_read.type_kind(target) or ("other", (0, 0))
        t = v.dtype
        if kind == "decimal":
            p, s = arg
            if s == 0 and p >= 19 and t in (pl.Int64, pl.Null):
                # `Parse.wideIntDecimal`: an integer, kept as one.
                return Val(v.expr.cast(pl.Int64), pl.Int64, v.issues)
            if t == pl.Float64:
                return self.double_to_decimal(v, p, s)
            if t == pl.Null:
                return Val(pl.lit(None, decimal_type(p, s)), decimal_type(p, s), v.issues)
            if t == pl.Int64 or is_decimal(t):
                return decimal_rescale(v, p, s, f"CAST to DECIMAL({p}, {s})")
            raise Unsupported(f"unsupported cast from {t} to DECIMAL({p}, {s})")
        if kind == "float" and "fp64" in target:
            # Correctly rounded, as `FloatCode.ofDecimal` (polars-decimal-casts).
            return Val(v.expr.cast(pl.Float64), pl.Float64, v.issues)
        if kind == "int":
            # Truncated toward zero (`UnFn.dtrunc`), then the integer width.
            bits = next((n for n in (8, 16, 32) if f"i{n}" in target), 64)
            return narrow_int(Val(v.expr.cast(pl.Int128), pl.Int128, v.issues), bits)
        raise Unsupported(f"unsupported cast from {t} to {json.dumps(target)}")

    @staticmethod
    def double_to_decimal(v: Val, p: int, s: int) -> Val:
        """`FloatCode.toDecimal?`: `x · 10ˢ` rounded to a double, then to an
        integer half away from zero; NaN and ±∞ fail (`badCast`). Polars rounds
        the product half to even (polars-decimal-casts). Past `10²²` the double
        `10ˢ` is inexact and Polars's product rounds twice."""
        if s > 22:
            raise Unsupported(
                "a CAST of a double to a DECIMAL of more than 22 decimal places is not "
                "supported on Polars"
            )
        x = v.expr
        y = x * (10.0**s)
        fails = ~y.is_finite()
        r = shims.round_half_away(pl.when(fails).then(0.0).otherwise(y))
        # Past 2¹²⁷ it has more than 38 digits; the cast to `Int128` would fail.
        big = r.abs() >= 2.0**127
        u = pl.when(big).then(0.0).otherwise(r).cast(pl.Int128)
        out = fit_decimal(u, p, s, f"CAST to DECIMAL({p}, {s})", v, bad=big & ~fails)
        bad = issue(fails, BadCast, "cannot cast NaN or infinity to a decimal")
        value = pl.when(fails).then(None).otherwise(out.expr)
        return Val(value, out.dtype, (*out.issues, bad))

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
            dtype = unify(then.dtype, out.dtype, "IF branches")
            value = pl.when(taken).then(then.expr).otherwise(out.expr)
            out = Val(
                value.cast(dtype) if is_decimal(dtype) else value,
                dtype,
                (
                    *c.issues,
                    *(Issue(taken & i.flag, i.kind, i.message) for i in then.issues),
                    *(Issue(~taken & i.flag, i.kind, i.message) for i in out.issues),
                ),
            )
        return out

    def floor_divide(self, name: str, a: Val, b: Val) -> Val:
        """Integer `//` or `%` with `division_type` = `FLOOR`: Polars's own,
        with no shim (`Profile.polars`, `SubstraitLean/PolarsProfile.lean`).
        A zero divisor and `MIN // -1` raise, as under `Profile.polars`; the
        guards check them."""
        if unify(a.dtype, b.dtype, name) not in (pl.Int64, pl.Null):
            raise Unsupported(f"{name} with division_type FLOOR of {a.dtype} and {b.dtype}")
        x, y = a.expr.cast(pl.Int64), b.expr.cast(pl.Int64)
        by_zero = issue(shims.zero_divisor(x, y), DivisionByZero, f"{name} by zero")
        if name == "modulus":
            return Val(x % y, pl.Int64, (*issues(a, b), by_zero))
        wraps = issue(shims.div_overflows(x, y), Overflow, "division leaves 64 bits")
        return Val(x // y, pl.Int64, (*issues(a, b), wraps, by_zero))

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

    def parameter(self, sel: dict) -> Val:
        """A reference in a lambda's body: only to its own parameter, which
        is the list element (`Parse.closeBody`)."""
        ref = sel.get("lambdaParameterReference")
        if ref is None or int(ref.get("stepsOut", 0)) != 0:
            raise Unsupported("a lambda body reads only its own parameter")
        sf = sel["directReference"]["structField"]
        if int(sf.get("field", 0)) != 0:
            raise Unsupported("lambdas have one parameter")
        assert self.param is not None
        element = Val(pl.element(), self.param)
        child = sf.get("child")
        return element if child is None else self.segments(element, child)

    def higher_order(self, name: str, arg_js: list) -> Val:
        """`HoFn.apply`: `any_match`, `all_match` (Kleene OR and AND of the
        predicate over the elements), `transform` and `filter`, with the
        lambda's body run on each element (`list.eval`)."""
        if len(arg_js) != 2 or "lambda" not in arg_js[1]:
            raise Unsupported(f"{name} takes a list and a lambda")
        lst = self(arg_js[0])
        if not isinstance(lst.dtype, pl.List):
            raise Unsupported(f"{name} of a value of type {lst.dtype}")
        inner: Any = lst.dtype.inner
        body = Exprs(self.functions, [], param=inner)(arg_js[1]["lambda"]["body"])
        # The lambda runs on every element (`Expr.issues`): a row fails where
        # one of its elements does.
        lifted = tuple(
            Issue(lst.expr.list.eval(i.flag).list.any().fill_null(False), i.kind, i.message)
            for i in body.issues
        )
        found = (*lst.issues, *lifted)
        each = lst.expr.list.eval(body.expr)
        if name == "transform":
            return Val(each, pl.List(materialize(body.dtype)), found)
        if name == "filter":
            kept = lst.expr.list.eval(pl.element().filter(body.expr.fill_null(False)))
            return Val(kept, lst.dtype, found)
        # Kleene: one decisive element decides; else a NULL makes it NULL.
        decisive = name == "any_match"
        hit = each.list.eval(pl.element().fill_null(not decisive) == decisive).list.any()
        unknown = each.list.eval(pl.element().is_null()).list.any()
        out = (
            pl.when(lst.expr.is_null())
            .then(None)
            .when(hit)
            .then(decisive)
            .when(unknown)
            .then(None)
            .otherwise(not decisive)
        )
        return Val(out, pl.Boolean, found)

    def segments(self, base: Val, seg: dict) -> Val:
        """`base` followed by reference segments (`Parse.segments`): a struct
        field (`UnFn.structField`), or a list element (`UnFn.listElement`:
        zero-based, negative from the end, NULL out of range)."""
        if "structField" in seg:
            sf = seg["structField"]
            k = int(sf.get("field", 0))
            if not isinstance(base.dtype, pl.Struct) or k >= len(base.dtype.fields):
                raise Unsupported(f"field {k} of a value of type {base.dtype}")
            f = base.dtype.fields[k]
            dtype: Any = f.dtype
            out = Val(base.expr.struct.field(f.name), dtype, base.issues)
        elif "listElement" in seg:
            le = seg["listElement"]
            if not isinstance(base.dtype, pl.List):
                raise Unsupported(f"an element of a value of type {base.dtype}")
            off = int(le.get("offset", 0))
            inner: Any = base.dtype.inner
            out = Val(base.expr.list.get(off, null_on_oob=True), inner, base.issues)
        else:
            raise Unsupported(f"unsupported reference segment {json.dumps(seg)}")
        child = seg.get("structField", seg.get("listElement", {})).get("child")
        return self.segments(out, child) if child is not None else out

    def unary(self, name: str, a: Val) -> Val:
        e, t = a.expr, a.dtype
        if name == "cardinality" and isinstance(t, pl.List):
            return Val(e.list.len().cast(pl.Int64), pl.Int64, a.issues)
        if name == "not" and t in (pl.Boolean, pl.Null):
            return Val(~e, pl.Boolean, a.issues)
        if name == "is_null":
            return Val(e.is_null(), pl.Boolean, a.issues)
        if name in ("negate", "subtract"):
            if t == pl.Float64:
                return Val(canon(-e), t, a.issues)  # NaN stays NaN
            if t in (pl.Int64, INTERVAL, pl.Null):
                return narrow(
                    pl.lit(0, pl.Int128) - wide(a), pl.Int64 if t == pl.Null else t, "negation", a
                )
        if t in (pl.String, pl.Null):
            if name == "upper":
                return Val(e.str.to_uppercase(), pl.String, a.issues)
            if name == "lower":
                return Val(e.str.to_lowercase(), pl.String, a.issues)
            if name == "character_length":
                return Val(e.str.len_chars().cast(pl.Int64), pl.Int64, a.issues)
            if name == "reverse":
                return Val(_rows(lambda s: s[::-1], pl.String, a), pl.String, a.issues)
            if name == "ascii":
                return Val(_rows(ascii_code, pl.Int64, a), pl.Int64, a.issues)
        if t == pl.Float64:
            # Exact on doubles; ROUND's halves go away from zero (`roundMag`).
            # A zero result is the one zero, as in `onMag`.
            if name == "floor":
                return Val(canon(e.floor()), t, a.issues)
            if name == "ceil":
                return Val(canon(e.ceil()), t, a.issues)
            if name == "round":
                return Val(canon(shims.round_half_away(e)), t, a.issues)
            # `|x|`, which a split double's partial rows report (#428).
            if name == "abs":
                return Val(canon(e.abs()), t, a.issues)
            if name in FMATH_NATIVE or name in FMATH_ROWS:
                return self.fmath(name, a)
        raise Unsupported(f"unsupported function {name}/1 on {t}")

    def fmath(self, name: str, a: Val) -> Val:
        """`UnFn.fmath`: `NULL` and a `DomainError` outside the domain."""
        e = a.expr
        bad = fmath_domain_error(name, e)
        safe = e if bad is None else pl.when(bad).then(1.0).otherwise(e)
        if name in FMATH_NATIVE:
            y = FMATH_NATIVE[name](safe)
        else:
            y = _rows(FMATH_ROWS[name], pl.Float64, Val(safe, pl.Float64))
        y = canon(y)
        # Only `exp` of a finite double overflows (`UnFn.infIssue`, #575).
        inf = (
            (issue(shims.makes_infinite(y, e), InfiniteResult, f"{name} overflows to infinity"),)
            if name == "exp"
            else ()
        )
        if bad is None:
            return Val(y, pl.Float64, (*a.issues, *inf))
        err = issue(bad, DomainError, f"{name} outside its domain")
        return Val(pl.when(bad).then(None).otherwise(y), pl.Float64, (*a.issues, err, *inf))

    def domain(self, bad: pl.Expr, y: pl.Expr, out: DType, what: str, *vals: Val) -> Val:
        """`y`, or `NULL` and a `DomainError` where `bad`."""
        err = issue(bad, DomainError, f"{what} outside its domain")
        return Val(pl.when(bad).then(None).otherwise(y), out, (*issues(*vals), err))

    def binary(self, name: str, a: Val, b: Val) -> Val:
        ta, tb = a.dtype, b.dtype
        if name in ("atan2", "logb"):
            if unify(ta, tb, name) not in (pl.Float64, pl.Null):
                raise Unsupported(f"{name} of {ta} and {tb}")
            x, y = a.expr.cast(pl.Float64), b.expr.cast(pl.Float64)
            if name == "atan2":
                bad = (x == 0.0) & (y == 0.0)
                return self.domain(bad, canon(pl.arctan2(x, y)), pl.Float64, name, a, b)
            # `ln x / ln b` (`logb?`), with the arguments made safe where it fails.
            bad = (x <= 0.0) | (y <= 0.0) | (y == 1.0)
            sx = pl.when(bad).then(2.0).otherwise(x)
            sy = pl.when(bad).then(2.0).otherwise(y)
            # `logb?` divides once, exactly: no reciprocal (`exact_div`).
            return self.domain(bad, canon(exact_div(sx.log(), sy.log())), pl.Float64, name, a, b)
        if name in BITWISE:
            if unify(ta, tb, name) not in (pl.Int64, pl.Null):
                raise Unsupported(f"{name} of {ta} and {tb}")
            x, y = a.expr.cast(pl.Int64), b.expr.cast(pl.Int64)
            if name in ("bitwise_and", "bitwise_or", "bitwise_xor"):
                out = {"bitwise_and": x & y, "bitwise_or": x | y, "bitwise_xor": x ^ y}[name]
                return Val(out, pl.Int64, issues(a, b))
            # Only a shift of an integer raises (`BinFn.issue`): `NULL >> -1` is NULL.
            bad = x.is_not_null() & ((y < 0) | (y > 63))
            n = pl.when(bad).then(0).otherwise(y)
            if name == "bitwise_shift_right":
                shifted = _rows(lambda v, k: v >> k, pl.Int64, a, Val(n, pl.Int64))
            else:
                shifted = _rows(shift_left, pl.Int64, a, Val(n, pl.Int64))
            return self.domain(bad, shifted, pl.Int64, name, a, b)
        floats = ("add", "subtract", "multiply", "divide", "modulus", "power")
        if name in floats and pl.Float64 in (ta, tb):
            if unify(ta, tb, name) != pl.Float64:
                raise Unsupported(f"{name} of {ta} and {tb}")
            x, y = a.expr, b.expr
            # Polars rewrites `0.0 - x` as `-x` and `x + 0.0` as `x` on the
            # in-memory engine (polars-zero-sign), so a sum or difference can
            # be `-0.0` too.
            ops = {"add": canon(x + y), "subtract": canon(x - y), "multiply": canon(x * y),
                   "divide": canon(fdiv(x, y)), "modulus": canon(fmod(x, y)),
                   "power": canon(x.pow(y))}  # fmt: skip
            nan = issue(nan_case(name, x, y), DomainError, f"{name} would make a NaN")
            # `fmod` is exact: it never overflows (#575).
            inf = () if name == "modulus" else (
                issue(shims.makes_infinite(ops[name], x, y) & y.ne(0.0), InfiniteResult,
                      f"{name} overflows to infinity"),
            )  # fmt: skip
            if name not in ("divide", "modulus"):
                return Val(ops[name], pl.Float64, (*issues(a, b), nan, *inf))
            # `on_division_by_zero` = ERROR (`BinFn.issue`), for `fdiv` and `fmod`;
            # `NULL / 0.0` is NULL.
            zero = issue(x.is_not_null() & y.eq(0.0), DivisionByZero, f"{name} by zero")
            tiny = (
                (issue(x.is_not_null() & subnormal_divisor(y), SubnormalDivisor,
                       "divide by a subnormal double"),)
                if name == "divide" else ()
            )  # fmt: skip
            return Val(ops[name], pl.Float64, (*issues(a, b), zero, *tiny, nan, *inf))
        if name in ("add", "subtract") and ta == pl.Time:
            raise Unsupported("a time of day plus an interval is not yet supported on Polars")
        if name == "add" and ta == pl.Date:
            # `BinFn.dateAdd`: days, as an interval or a count.
            if tb == INTERVAL:
                n = wide(b) // US_PER_DAY
            elif tb in (pl.Int64, pl.Null):
                n = wide(b)
            else:
                raise Unsupported(f"add of {ta} and {tb}")
            return date_range(a, _days(a) + n, DAY_MIN, DAY_MAX, "date + days", b)
        if name == "multiply" and tb == INTERVAL and ta in (pl.Int64, pl.Null):
            # A count of days (`add(d, multiply(n, INTERVAL '1' DAY))`).
            return narrow(wide(a) * wide(b), INTERVAL, name, a, b)
        if name in ("add", "subtract", "multiply"):
            out = arith_type(name, ta, tb)
            if out == pl.Int64:
                # Native: Polars wraps where the reference raises
                # (`Issue.wraps`), which only the guard sees.
                x, y = a.expr.cast(pl.Int64), b.expr.cast(pl.Int64)
                w = {"add": x + y, "subtract": x - y, "multiply": x * y}[name]
                bad = issue(shims.int_overflows(x, y, name), IntegerOverflow,
                            f"{name} leaves 64 bits")  # fmt: skip
                return Val(w, out, (*issues(a, b), bad))
            x, y = wide(a), wide(b)
            w = {"add": x + y, "subtract": x - y, "multiply": x * y}[name]
            return narrow(w, out, name, a, b)
        if name in ("divide", "modulus", "power"):
            if unify(ta, tb, name) not in (pl.Int64, pl.Null):
                raise Unsupported(f"{name} of {ta} and {tb}")
            if name == "power":
                return ipow(a, b)
            # Native `//` and `%` floor; the shims truncate. A zero divisor
            # gives NULL in Polars and `MIN / -1` wraps: the guards raise.
            x, y = a.expr.cast(pl.Int64), b.expr.cast(pl.Int64)
            by_zero = issue(shims.zero_divisor(x, y), DivisionByZero, f"{name} by zero")
            if name == "modulus":
                return Val(shims.int_mod_trunc(x, y), pl.Int64, (*issues(a, b), by_zero))
            wraps = issue(shims.div_overflows(x, y), Overflow, "division leaves 64 bits")
            return Val(shims.int_div_trunc(x, y), pl.Int64, (*issues(a, b), wraps, by_zero))
        strings = ("str_concat", "strpos", "starts_with", "ends_with", "like", "substring",
                   "btrim", "ltrim", "rtrim", "repeat", "levenshtein", "ilike")  # fmt: skip
        if name in strings:
            return self.string(name, a, b)
        if name in _PICKS:
            return self.pick(name, [a, b])
        if name in ("equal", "lt"):
            t = unify(ta, tb, name)
            if name == "lt" and t not in (*INTEGRAL, pl.Date, pl.Time, pl.Float64, pl.Null):
                # `BinFn.lt` is only defined on integers (and the codes of
                # doubles and times); strings would differ from SQL.
                raise Unsupported(f"lt of {t}")
            ka, kb = ordered(a.expr, t), ordered(b.expr, t)
            return Val(ka == kb if name == "equal" else ka < kb, pl.Boolean, issues(a, b))
        raise Unsupported(f"unsupported function {name}/2 on {[ta, tb]}")

    def pick_leaves(self, name: str, arg_js: list) -> list:
        """The values of a chain of `name` calls, in order: `greatest(greatest(a,
        b), c)` is `[a, b, c]`."""
        out = []
        for j in arg_js:
            f = j.get("scalarFunction")
            if f is not None and self.function(f.get("functionReference")) == name:
                out += self.pick_leaves(name, [a["value"] for a in f.get("arguments", [])])
            else:
                out.append(j)
        return out

    def pick(self, name: str, vals: list[Val]) -> Val:
        """`GREATEST`/`LEAST` of `vals` as the pairwise `BinFn.greatest`/`least`
        computes it (`Value.pick`): skipping NULLs, by the order `lt` has (NaN
        above everything, as `ordered` keys it), the first of equal values;
        NULL if all are."""
        t = pl.Null
        for v in vals:
            t = unify(t, v.dtype, name)
        if t not in (*INTEGRAL, pl.Date, pl.Time, pl.Float64, pl.Null) and not is_decimal(t):
            raise Unsupported(f"{name} of {t}")
        if t == pl.Null:
            return Val(pl.lit(None), t, issues(*vals))
        # The first extreme's index in the list of keys: `arg_max` and
        # `arg_min` skip NULLs and NaN, and give the first of equal values;
        # NaN is the greatest double here (polars-min-max-nan). One list, so
        # the expression grows with the arguments, not their square.
        keys = pl.concat_list([ordered(v.expr, t) for v in vals])
        idx = keys.list.arg_max() if name.startswith("greatest") else keys.list.arg_min()
        if t == pl.Float64:
            nans = keys.list.eval(pl.element().is_nan())
            first_nan = pl.when(nans.list.any()).then(nans.list.arg_max())
            if name.startswith("greatest"):
                idx = pl.coalesce(first_nan, idx)
            else:
                idx = pl.coalesce(idx, first_nan)
        e = pl.concat_list([v.expr.cast(t) for v in vals]).list.get(idx, null_on_oob=True)
        return Val(e, t, issues(*vals))

    def string(self, name: str, a: Val, b: Val) -> Val:
        """The binary functions of `SubstraitLean/Text.lean`."""
        if name == "substring":
            return self.substring(a, b, None)
        if name == "repeat":
            if a.dtype not in (pl.String, pl.Null) or b.dtype not in (pl.Int64, pl.Null):
                raise Unsupported(f"repeat of {a.dtype} and {b.dtype}")
            # `Text.repeatFits`, with the count capped so that the product fits.
            cap = REPEAT_MAX + 1
            n = pl.when(b.expr > cap).then(cap).otherwise(b.expr)
            big = issue(n * a.expr.str.len_bytes().cast(pl.Int64) > REPEAT_MAX, Overflow,
                        "repeat beyond 2^31 - 1 bytes")  # fmt: skip
            return Val(_rows(repeat, pl.String, a, b), pl.String, (*issues(a, b), big))
        if unify(a.dtype, b.dtype, name) not in (pl.String, pl.Null):
            raise Unsupported(f"{name} of {a.dtype} and {b.dtype}")
        x, y, found = a.expr, b.expr, issues(a, b)
        if name == "str_concat":
            return Val(pl.concat_str([x, y]), pl.String, found)
        if name in ("starts_with", "ends_with"):
            e = x.str.starts_with(y) if name == "starts_with" else x.str.ends_with(y)
            return Val(e, pl.Boolean, found)
        if name == "strpos":
            return Val(shims.strpos_chars(x, y), pl.Int64, found)
        if name == "levenshtein":
            return Val(_rows(levenshtein, pl.Int64, a, b), pl.Int64, found)
        if name == "ilike":
            return Val(x.str.contains(_rows(ilike_regex, pl.String, b)), pl.Boolean, found)
        if name == "like":
            return Val(_rows(like, pl.Boolean, a, b), pl.Boolean, found)
        # Trimming: Polars strips whitespace for a NULL set, Lean gives NULL.
        strip = {"btrim": x.str.strip_chars, "ltrim": x.str.strip_chars_start,
                 "rtrim": x.str.strip_chars_end}[name]  # fmt: skip
        return Val(pl.when(y.is_not_null()).then(strip(y)), pl.String, found)

    def round_to(self, a: Val, digits: dict) -> Val:
        """`ROUND(x, d)`, as `FloatCode.roundTo` (DuckDB 2.0's, #335): with
        `m = 10^|d|`, `round(x · m) / m` for `d ≥ 0` and `round(x / m) · m`
        for `d < 0`, `x` where that is not finite; 0 for `d < 0` when `m` is
        `±∞`. `±∞` and NaN stay."""
        if "literal" not in digits or literal(digits["literal"])[1] != pl.Int64:
            raise Unsupported("ROUND digits must be an integer literal")
        if a.dtype != pl.Float64:
            raise Unsupported(f"round of {a.dtype}")
        d = int(literal(digits["literal"])[0])
        try:
            m = math.pow(10.0, abs(d))
        except OverflowError:
            m = math.inf
        x, ml = a.expr, pl.lit(m, pl.Float64)
        if d < 0 and math.isinf(m):
            out = pl.when(x.is_null() | ~x.is_finite()).then(x).otherwise(pl.lit(0.0, pl.Float64))
            return Val(canon(out), pl.Float64, a.issues)
        if d >= 0:
            r = exact_div(shims.round_half_away(x * ml), ml)
        else:
            r = shims.round_half_away(exact_div(x, ml)) * ml
        out = pl.when(~x.is_finite() | ~r.is_finite()).then(x).otherwise(r)
        return Val(canon(out), pl.Float64, a.issues)


# --- Relations ---------------------------------------------------------------


_FLAG_IDS = itertools.count()


def _raise_issues(issues: tuple[Issue, ...]):
    def check(s: pl.Series) -> pl.Series:
        for k, i in enumerate(issues):
            hits = s.struct.field(f"i{k}")
            if hits.any():
                raise i.kind(f"{i.message} ({hits.sum()} row(s))")
        return pl.Series([True] * len(s), dtype=pl.Boolean)

    return check


def guard(lf: pl.LazyFrame, vals: list[Val], checks: frozenset[str] = ALL_GUARDS) -> pl.LazyFrame:
    """Raise if any row of `lf` runs into an issue of `vals`, which an operator
    evaluates on exactly these rows. A filter is never pruned, and `collect`
    keeps it in place (no predicate pushdown), so it sees the same rows."""
    found = tuple(i for i in issues(*vals) if i.kind.issue in checks)
    if not found:
        return lf
    # Each flag is a column of its own: one expression holding all of them
    # can outgrow what Polars's plan formatter takes (`fallback_nodes`).
    names = [f"__sv_flag{next(_FLAG_IDS)}" for _ in found]
    lf = lf.with_columns([i.flag.alias(n) for i, n in zip(found, names, strict=True)])
    flags = pl.struct([pl.col(n).alias(f"i{k}") for k, n in enumerate(names)])
    return lf.filter(
        flags.map_batches(_raise_issues(found), return_dtype=pl.Boolean, is_elementwise=True)
    ).drop(names)


Frame = tuple[pl.LazyFrame, list[DType]]


def positional(lf: pl.LazyFrame) -> pl.LazyFrame:
    return lf.rename({c: col(i) for i, c in enumerate(lf.collect_schema().names())})


def type_of(t: dict) -> DType:
    """The engine dtype for a declared column type."""
    match _plan_read.type_kind(t):
        case "int", _:
            return pl.Int64
        case "float", _:
            return pl.Float64
        case "str", _:
            return pl.String
        case "bool", _:
            return pl.Boolean
        case "time", _:
            return US
        case "date", _:
            return pl.Date
        case "tod", _:
            return pl.Time
        case "interval", _:
            return INTERVAL
        case "decimal", (p, s):
            return decimal_type(p, s)
        case "list", elem:
            return pl.List(type_of(elem or {}))
        case "struct", fields:
            return struct_type([type_of(f) for f in fields])
    raise Unsupported(f"unsupported column type {json.dumps(t)}")


def conform(e: pl.Expr, have: DType, want: DType, where: str) -> pl.Expr:
    """Load a table column as the model sees it: integers widened to 64 bits,
    single floats to doubles, `-0.0` as `0.0`. Anything else that would change
    values is refused."""
    if want == pl.Float64 and have in (pl.Float64, pl.Float32):
        return canon(e.cast(pl.Float64))
    if have == want:
        return e
    if want == pl.Int64 and have.is_integer() and have not in (pl.UInt64, pl.Int128):
        return e.cast(pl.Int64)
    if want == pl.String and have == pl.Categorical:
        raise Unsupported(f"{where}: categorical strings are not supported")
    if have == pl.Null:
        return e.cast(want)
    if isinstance(have, pl.Struct) and isinstance(want, pl.Struct):
        hs, ws = have.fields, want.fields
        if len(hs) == len(ws) and all(h.dtype == w.dtype for h, w in zip(hs, ws, strict=True)):
            return e.struct.rename_fields([w.name for w in ws])
    raise Unsupported(f"{where}: column has type {have}, the plan expects {want}")


def materialize(t: DType) -> DType:
    """Untyped NULL columns are `i64`, like the writer's placeholder types."""
    return pl.Int64 if t == pl.Null else t


def _dedup_key(v: Any) -> Any:
    """Values as `Value` equality tells them apart: one zero and one NaN."""
    if isinstance(v, float):
        return "nan" if math.isnan(v) else v + 0.0
    return v


def _int_output(f: dict) -> bool:
    """Does an `avg` declare an integer output type (`AggFn.iavg`)?"""
    return any(k in f.get("outputType", {}) for k in ("i8", "i16", "i32", "i64"))


def _aggregate(fn: str, distinct: bool, vs: list, window: bool = False) -> Any:
    """`Measure.eval` on the values a measure aggregates (NULLs dropped), with
    Polars's profile's choices: doubles added in turn (`SEQUENTIAL`), the
    variance by Polars. A double sum of `+∞` and `-∞` raises (#257), except in
    a window, where the reference still gives NaN."""
    if distinct:
        seen: set = set()
        vs = [v for v in vs if not (_dedup_key(v) in seen or seen.add(_dedup_key(v)))]
    if fn == "count":
        return len(vs)
    if not vs:
        return None
    if fn == "sum":
        total = sum(vs)
        if not I64_MIN <= total <= I64_MAX:
            # DataFusion wraps around; Lean's sum is the true one (`Issue.sumWraps`).
            raise IntegerOverflow("SUM leaves 64 bits")
        return total
    if fn == "collect":
        return list(vs)
    if fn == "iavg":
        # `AggFn.iavg`: the exact mean, truncated toward zero (#209).
        q = abs(sum(vs)) // len(vs)
        return q if sum(vs) >= 0 else -q
    if fn in ("bit_and", "bit_or", "bit_xor"):
        # `AggFn.bit`: the operation folded over the 64-bit values (#53).
        acc = -1 if fn == "bit_and" else 0
        for v in vs:
            acc = acc & v if fn == "bit_and" else acc | v if fn == "bit_or" else acc ^ v
        return acc
    if fn in ("var_samp", "var_pop", "std_samp", "std_pop"):
        # `AggFn.var` (#54), with Polars' own algorithm; an infinity would make
        # a deviation NaN (#257).
        if math.inf in vs or -math.inf in vs:
            raise DomainError(f"{fn} of an infinity would make a NaN")
        if fn.endswith("_samp") and len(vs) == 1:
            return None
        s = pl.Series(vs, dtype=pl.Float64)
        ddof = 1 if fn.endswith("_samp") else 0
        r = float(s.std(ddof=ddof) if fn.startswith("std") else s.var(ddof=ddof))  # pyrefly: ignore
        # D30's clamp shim: at least 0, NaN kept (`Stat.clamp_near`, `FloatMoments.lean`).
        r = r if math.isnan(r) else max(0.0, r)
        if math.isinf(r):
            # Finite values whose variance overflows (`Measure.makesInf`, #575).
            raise InfiniteResult(f"{fn} overflows to infinity")
        return r + 0.0
    if fn in ("fsum", "avg"):
        if not window and math.inf in vs and -math.inf in vs:
            raise DomainError(f"{fn} of +inf and -inf would make a NaN")
        acc = 0.0
        # In list order (`sum_order = SEQUENTIAL`), within the plan's bound of
        # the reference's `floatSumCR` and `floatAvgCR` (D25).
        for v in vs:
            acc = acc + v
        if math.isinf(acc) and all(math.isfinite(v) for v in vs):
            # Finite values whose sum overflows (`Measure.makesInf`, #575).
            raise InfiniteResult(f"{fn} overflows to infinity")
        return acc / len(vs) + 0.0 if fn == "avg" else acc
    if fn in ("fmin", "fmax"):
        # By the codes' order: NaN above every double, and one zero.
        nums = [v for v in vs if not math.isnan(v)]
        if not nums or (fn == "fmax" and len(nums) < len(vs)):
            return math.nan
        return (min(nums) if fn == "fmin" else max(nums)) + 0.0
    # `pickFold` keeps the first extreme; equal values are the same value here.
    return min(vs) if fn == "min" else max(vs)


#: `(descending, nulls_last)` per direction (`shims.null_order`).
SORT_DIRECTIONS = shims.SORT_DIRECTIONS


@dataclass(frozen=True)
class Measure:
    """An aggregate measure: `fn` of `arg` over the rows `filter` keeps."""

    fn: str
    arg: Val
    distinct: bool
    filter: Val | None
    #: `collect`'s order: key, descending, NULLs last.
    sorts: tuple[tuple[Val, bool, bool], ...] = ()

    @property
    def vals(self) -> list[Val]:
        return [self.arg] if self.filter is None else [self.arg, self.filter]

    @property
    def dtype(self) -> DType:
        if self.fn in ("count", "sum", "iavg", "bit_and", "bit_or", "bit_xor"):
            return pl.Int64
        if self.fn == "collect":
            return pl.List(materialize(self.arg.dtype))
        if self.fn in ("var_samp", "var_pop", "std_samp", "std_pop"):
            return pl.Float64
        if self.fn in ("dsum", "davg"):
            p, s = self.arg.dtype.precision, self.arg.dtype.scale  # pyrefly: ignore
            rule = _decimals.sum_of if self.fn == "dsum" else _decimals.avg_of
            return pl.Decimal(*rule((p, s)))
        if self.fn in ("fsum", "avg", "fmin", "fmax"):
            return pl.Float64
        return materialize(self.arg.dtype)

    @property
    def values(self) -> pl.Expr:
        """The argument on the kept rows, NULL elsewhere (times as integers)."""
        a = self.arg.expr.to_physical() if self.arg.dtype in (US, pl.Date) else self.arg.expr
        return a if self.filter is None else pl.when(is_true(self.filter.expr)).then(a)

    def result(self, values: pl.Expr) -> pl.Expr:
        """The measure from the list of each group's values."""
        fn, distinct = self.fn, self.distinct
        t = self.arg.dtype
        physical = pl.Int64 if t == US else pl.Int32 if t == pl.Date else None
        out = physical or self.dtype

        def apply(s: pl.Series) -> pl.Series:
            return pl.Series([_aggregate(fn, distinct, vs) for vs in s.to_list()], dtype=out)

        if fn == "collect":
            # `ARRAY_AGG` of no values is NULL; Polars's list is empty.
            return pl.when(values.list.len() == 0).then(None).otherwise(values)
        r = values.map_batches(apply, return_dtype=out)
        return r.cast(self.arg.dtype) if physical else r

    def native(self, name: str) -> NativeAgg | None:
        """The measure as Polars's own aggregation of the column `name` (the
        argument on the kept rows), with the reference's shims: the
        aggregations of the input `v`, and the result read from the
        aggregated column `r` of the same name. None for `ARRAY_AGG`, whose
        list `result` reads."""
        v = r = pl.col(name)
        if self.fn == "collect":
            return None
        if self.distinct:
            # `dedup` by `Value` equality: one zero and one NaN for doubles.
            # Integers to be summed are widened first: `unique` must be the
            # last step before the reduction for it to stream.
            if self.arg.dtype == pl.Float64:
                v = _float_key(v)
            elif self.fn in ("sum", "iavg"):
                v = v.cast(pl.Int128)
            v = v.unique()
        if self.fn == "sum":
            total = shims.int_sum(v)
            return NativeAgg(
                {name: total},
                pl.when(shims.sum_leaves_i64(r)).then(None).otherwise(r).cast(pl.Int64),
                ((shims.sum_leaves_i64(r), SumOverflow, "SUM leaves 64 bits"),),
            )
        if self.fn == "iavg":
            return NativeAgg({name: shims.avg_int_declared(v)}, r)
        if self.fn in ("dsum", "davg"):
            # Polars's exact sum, a `Decimal(38, s)` (polars-decimal-arith),
            # NULL without values (`sum_empty_null`); the sum's digits are
            # those of `SUM`'s type (`Measure.sumDigits`, #316), for `AVG` too.
            out = self.dtype
            p, s = self.arg.dtype.precision, self.arg.dtype.scale  # pyrefly: ignore
            digits = _decimals.sum_of((p, s))[0]
            total, n = f"{name}_sum", f"{name}_n"
            aggs = {total: shims.sum_empty_null(v.sum(), v), n: v.count().cast(pl.Int64)}
            u = pl.col(total).to_physical()
            leaves = (u.abs() >= i128(10**digits)).fill_null(False)
            flags = ((leaves, SumOverflow, f"SUM leaves DECIMAL({digits}, {s})"),)
            if self.fn == "dsum":
                # NULL past the precision, where the guard raises.
                return NativeAgg(aggs, pl.col(total).cast(out, strict=False), flags)
            # `AVG`: the sum by the count at scale `s + 4`, half away from zero
            # (`decimalAvgs`, `roundDivInt?`); Polars's `mean` is a `Float64`.
            q, _ = shims.decimal_div_half_away(u, pl.col(n), 4)
            avg = of_unscaled(q, s + 4).cast(out)
            return NativeAgg(aggs, pl.when(pl.col(n) == 0).then(None).otherwise(avg), flags)
        if self.fn in ("fsum", "avg"):
            nan, inf = f"{name}_nan", f"{name}_inf"
            agg = shims.float_sum(v) if self.fn == "fsum" else shims.float_avg(v)
            return NativeAgg(
                {name: agg, nan: shims.sum_makes_nan(v),
                 inf: shims.agg_makes_infinite(v.sum(), v)},
                r,
                ((pl.col(nan), DomainError, f"{self.fn} of +inf and -inf would make a NaN"),
                 (pl.col(inf), InfiniteResult, f"{self.fn} overflows to infinity")),
            )  # fmt: skip
        if self.fn == "count":
            return NativeAgg({name: v.count().cast(pl.Int64)}, r)
        if self.fn in ("min", "max"):
            # `pickFold`: equal values are the same value, so which of them
            # is kept does not show. Times aggregate as their integers.
            agg = v.min() if self.fn == "min" else v.max()
            temporal = self.arg.dtype in (US, pl.Date)
            return NativeAgg({name: agg}, r.cast(self.arg.dtype) if temporal else r)
        if self.fn in ("bit_and", "bit_or", "bit_xor"):
            # `AggFn.bit`; NULL for no values, as Polars gives.
            agg = {"bit_and": v.bitwise_and(), "bit_or": v.bitwise_or(),
                   "bit_xor": v.bitwise_xor()}[self.fn]  # fmt: skip
            return NativeAgg({name: shims.sum_empty_null(agg, v)}, r)
        if self.fn == "fmin":
            # NaN is the greatest double and there is one zero; Polars's
            # `min` skips NaN and keeps either zero (polars-min-max-nan,
            # polars-min-max-zero). The shims read the aggregated columns, so
            # `unique` stays the last step before the reduction.
            return NativeAgg({name: v.min()}, shims.min_ignore_nan(r))
        if self.fn == "fmax":
            # Whether the group holds a NaN does not depend on `DISTINCT`.
            nan = f"{name}_nan"
            return NativeAgg(
                {name: v.max(), nan: pl.col(name).is_nan().any()},
                shims.max_nan_greatest(r, pl.col(nan)),
            )
        if self.fn in ("var_samp", "var_pop", "std_samp", "std_pop"):
            # `AggFn.var` (#54) with Polars's algorithm (`stat_algo =
            # WELFORD_CHAN`, polars-var-std-streaming), within the plan's bound
            # of the exact moments rounded once (D30); a sample of one is NULL
            # in both. An infinity makes
            # a deviation NaN (#257); finite values may overflow (#575).
            ddof = 1 if self.fn.endswith("_samp") else 0
            agg = v.std(ddof=ddof) if self.fn.startswith("std") else v.var(ddof=ddof)
            # Aggregated once, and read: D30's clamp shim, at least 0 with NaN
            # kept (`Stat.clamp_near`, `FloatMoments.lean`), and NaN for a
            # group with a NaN (`nan_through`, polars-var-pop-one-nan).
            bad, fin, nan = f"{name}_bad", f"{name}_fin", f"{name}_nan"
            clamped = pl.when(r.is_nan()).then(r).otherwise(r.clip(lower_bound=0.0))
            return NativeAgg(
                {name: agg, bad: v.is_infinite().any(), fin: v.is_finite().all(),
                 nan: v.is_nan().any()},
                canon(shims.nan_through(clamped, pl.col(nan))),
                ((pl.col(bad), DomainError, f"{self.fn} of an infinity would make a NaN"),
                 # `agg_makes_infinite`, its two halves read after the aggregation.
                 (pl.col(fin) & r.is_infinite(), InfiniteResult,
                  f"{self.fn} overflows to infinity")),
            )  # fmt: skip
        return None


@dataclass(frozen=True)
class NativeAgg:
    """A measure Polars aggregates natively: the aggregations (by column), the
    result read from them, and the flags of the issues it may raise, read
    from them too."""

    aggs: dict[str, pl.Expr]
    result: pl.Expr
    flags: tuple[tuple[pl.Expr, type[RuntimeIssue], str], ...] = ()


@dataclass(frozen=True)
class WindowSpec:
    """A window function `python_windows` computes: ranks, NTILE, aggregates
    and FIRST/LAST/NTH_VALUE over a frame (`Window.lean`)."""

    fn: str
    dtype: DType
    n: int = 0
    col: int | None = None
    agg: str = ""
    frame: tuple = (False, ("unbounded", 0), ("unbounded", 0))


def window_frame(w: dict) -> tuple:
    """`(range, lo, hi)` of a window (`Parse.parseFrame`)."""
    bt = w.get("boundsType", "BOUNDS_TYPE_RANGE")
    if bt not in ("BOUNDS_TYPE_ROWS", "BOUNDS_TYPE_RANGE", "BOUNDS_TYPE_UNSPECIFIED"):
        raise Unsupported(f"unsupported window bounds type {bt}")

    def bound(b: dict | None) -> tuple[str, int]:
        if not b or "unbounded" in b:
            return ("unbounded", 0)
        if "currentRow" in b:
            return ("preceding", 0)
        side = "preceding" if "preceding" in b else "following"
        return (side, int(b[side].get("offset", 0)))

    return (bt != "BOUNDS_TYPE_ROWS", bound(w.get("lowerBound")), bound(w.get("upperBound")))


def _key(v: Any) -> Any:
    """A value as `Value.le` and `samePart` see it (one zero, one NaN)."""
    return _dedup_key(v)


def _le(a: Any, b: Any, desc: bool, nulls_first: bool) -> bool:
    """`SortKey.le` on one key's values."""
    if a is None or b is None:
        ra = (0 if nulls_first else 1) if a is None else (1 if nulls_first else 0)
        rb = (0 if nulls_first else 1) if b is None else (1 if nulls_first else 0)
        return ra <= rb
    if isinstance(a, float):
        a, b = _float_rank(a), _float_rank(b)
    return b <= a if desc else a <= b


def _float_rank(x: float) -> tuple:
    return (1, 0.0) if math.isnan(x) else (0, x + 0.0)


def _frame_rows(frame: tuple, sort: list, rows: list, i: int) -> list[int]:
    """`Frame.rows`: the indexes (into the partition `rows`) of row `i`'s frame."""
    rng, lo, hi = frame
    if not rng:
        lo_i = 0 if lo[0] == "unbounded" else i + (lo[1] if lo[0] == "following" else -lo[1])
        hi_i = (
            len(rows) - 1
            if hi[0] == "unbounded"
            else i + (hi[1] if hi[0] == "following" else -hi[1])
        )
        return [j for j in range(len(rows)) if lo_i <= j <= hi_i]
    x = rows[i]

    def sort_le(a: tuple, b: tuple) -> bool:
        for c, desc, nf in sort:
            if not _le(a[c], b[c], desc, nf):
                return False
            if not _le(b[c], a[c], desc, nf):
                return True
        return True

    def ok(y: tuple, b: tuple[str, int], lower: bool) -> bool:
        side, k = b
        if side == "unbounded":
            return True
        if k == 0:
            return sort_le(x, y) if lower else sort_le(y, x)
        d = k if side == "following" else -k
        c, desc, nf = sort[0]
        vx, vy = x[c], y[c]
        if vx is None and vy is None:
            return True
        if vx is None or vy is None:
            # NULLs are at one end: `y` is in the frame only on the unbounded side.
            rx, ry = (
                (0 if nf else 1) if vx is None else (1 if nf else 0),
                (0 if nf else 1) if vy is None else (1 if nf else 0),
            )
            return rx < ry if lower else ry < rx
        if lower:
            return vy <= vx - d if desc else vx + d <= vy
        return vx - d <= vy if desc else vy <= vx + d

    return [j for j, y in enumerate(rows) if ok(y, lo, True) and ok(y, hi, False)]


def python_windows(
    lf: pl.LazyFrame,
    dtypes: list[DType],
    part: list[int],
    sort: list,
    fns: list[tuple[int, WindowSpec]],
    n_in: int,
) -> pl.LazyFrame:
    """Window functions of `fns` (output column, spec) over the sorted frame
    of `n_in` input columns, computed row by row as `WinFn.valueIn` does."""
    schema = {col(i): materialize(t) for i, t in enumerate(dtypes)}

    def compute(df: pl.DataFrame) -> pl.DataFrame:
        cols = [df[col(i)].to_physical().to_list() for i in range(n_in)]
        rows = list(zip(*cols, strict=True)) if cols else [() for _ in range(df.height)]
        groups: dict[tuple, list[int]] = {}
        for r, row in enumerate(rows):
            groups.setdefault(tuple(_key(row[p]) for p in part), []).append(r)
        out: dict[int, list] = {i: [None] * len(rows) for i, _ in fns}
        for idx in groups.values():
            prows = [rows[r] for r in idx]
            keys = [tuple(_key(y[c]) for c, _, _ in sort) for y in prows]
            m = len(prows)
            for i, r in enumerate(idx):
                before = [keys[j] for j in range(i) if keys[j] != keys[i]]
                peers_after = sum(1 for j in range(i + 1, m) if keys[j] == keys[i])
                for o, f in fns:
                    if f.fn == "rank":
                        v: Any = len(before) + 1
                    elif f.fn == "dense_rank":
                        v = len(set(before)) + 1
                    elif f.fn == "percent_rank":
                        v = 0.0 if m <= 1 else len(before) / (m - 1)
                    elif f.fn == "cume_dist":
                        v = (i + 1 + peers_after) / m
                    elif f.fn == "ntile":
                        # The SQL standard's buckets (`ntileOf`): the first
                        # `m % n` hold one row more.
                        size, big = divmod(m, f.n)
                        edge = big * (size + 1)
                        v = i // (size + 1) + 1 if i < edge else (i - edge) // size + big + 1
                    else:
                        frame = [prows[j] for j in _frame_rows(f.frame, sort, prows, i)]
                        vals = [y[f.col] for y in frame] if f.col is not None else [1] * len(frame)
                        if f.fn == "agg" and f.agg == "dsum":
                            # Unscaled values, summed exactly (`Measure.sumDigits`).
                            xs = [x for x in vals if x is not None]
                            v = sum(xs) if xs else None
                            if v is not None and abs(v) >= 10**f.dtype.precision:  # pyrefly: ignore
                                raise SumOverflow(f"SUM leaves {f.dtype}")
                        elif f.fn == "agg":
                            v = _aggregate(
                                f.agg, False, [x for x in vals if x is not None], window=True
                            )
                        elif f.fn == "first_value":
                            v = vals[0] if vals else None
                        elif f.fn == "last_value":
                            v = vals[-1] if vals else None
                        else:
                            v = vals[f.n - 1] if f.n <= len(vals) else None
                    out[o][r] = v
        new = []
        for o, f in fns:
            t = f.dtype
            physical = (
                pl.Int64
                if t == US
                else pl.Int32
                if t == pl.Date
                else pl.Int64
                if t == pl.Time
                else t
            )
            if is_decimal(t):
                # Decimals were read as their unscaled values (`to_physical`).
                sc = t.scale  # pyrefly: ignore
                vs = [None if x is None else Decimal(x).scaleb(-sc) for x in out[o]]
                new.append(pl.Series(col(o), vs, dtype=t))
                continue
            s = pl.Series(col(o), out[o], dtype=physical)
            new.append(s.cast(t) if physical != t else s)
        return df.with_columns(new).select(list(schema))

    for o, f in fns:
        schema[col(o)] = f.dtype
    return lf.map_batches(compute, schema=schema)


#: Which runtime issues to check: True for `ALL_GUARDS`, False for
#: `NO_GUARDS`, or the issues by their `Issue.name` (`RuntimeIssue.issue`).
Guards = bool | Collection[str]


def checks_of(guards: Guards) -> frozenset[str]:
    if guards is True:
        return ALL_GUARDS
    if guards is False:
        return NO_GUARDS
    names = frozenset(guards)
    unknown = names - ALL_GUARDS - {InfiniteResult.issue}
    if unknown:
        raise ValueError(f"unknown issues to guard: {sorted(unknown)}")
    return names


class Translator:
    def __init__(self, plan: dict, tables: Tables, guards: Guards = True):
        _support.check(plan, "Polars", Unsupported)
        self.functions = _plan_read.function_names(plan, Unsupported)
        self.tables = tables
        self.checks = checks_of(guards)

    def guard(self, lf: pl.LazyFrame, vals: list[Val]) -> pl.LazyFrame:
        return guard(lf, vals, self.checks)

    def exprs(self, dtypes: list[DType]) -> Exprs:
        return Exprs(self.functions, dtypes)

    def rel(self, j: dict) -> Frame:
        kinds = [
            "read", "filter", "project", "cross", "join", "fetch", "set", "sort", "aggregate",
            "extensionSingle",
        ]  # fmt: skip
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

    def extensionSingle(self, r: dict) -> Frame:  # noqa: N802 - the relation's name
        """`Rel.unnest`: one row per element of the list in a column, in its
        place; none for an empty list or NULL (Polars' `explode` would give a
        row of NULL for those)."""
        d = r.get("detail", {})
        if d.get("@type") != "type.googleapis.com/sverify.Unnest" or d.get("keepEmpty"):
            raise Unsupported(f"unsupported ExtensionSingleRel {json.dumps(d)[:80]}")
        lf, dtypes = self.rel(r["input"])
        c = int(d.get("column", 0))
        t = dtypes[c] if c < len(dtypes) else None
        if not isinstance(t, pl.List):
            raise Unsupported(f"UNNEST of column {c} of type {t}")
        lf = lf.filter(pl.col(col(c)).list.len() > 0).explode(col(c))
        inner: Any = t.inner
        return lf, [*dtypes[:c], materialize(inner), *dtypes[c + 1 :]]

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
        return self.guard(lf, [cond]).filter(is_true(cond.expr)), dtypes

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
        # An untyped NULL column stays untyped, so that a union can type it
        # (an outer join's padding meets the right side's columns there).
        out = [v.dtype for v in new]
        n = len(dtypes)
        # Every expression is evaluated on every row, used later or not.
        lf = self.guard(lf, new).with_columns(
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
        lf = self.sorted(lf, ex, sorts)
        keys = [ordered(v.expr, v.dtype) for v in (self.column(ex, p) for p in part)]
        n = len(dtypes)
        new, out = [], []
        py: list[tuple[int, WindowSpec]] = []
        for k, w in enumerate(ws):
            name = ex.function(w.get("functionReference"))
            args = [a["value"] for a in w.get("arguments", [])]
            if name == "row_number" and not args:
                # A running count, which streams; a bare `int_range` does not.
                e: pl.Expr = pl.repeat(1, pl.len(), dtype=pl.Int64).cum_sum()
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
                spec = self.window_spec(ex, name, args, w, dtypes, sorts)
                py.append((n + k, spec))
                out.append(spec.dtype)
                continue
            new.append((e.over(keys) if keys else e).cast(materialize(t)).alias(col(n + k)))
            out.append(materialize(t))
        lf = lf.with_columns(new)
        if py:
            part_idx = [ex.field(p["selection"]) for p in part]
            lf = python_windows(lf, dtypes + out, part_idx, self.sort_specs(ex, sorts), py, n)
        return lf, dtypes + out

    def sort_specs(self, ex: Exprs, sorts: list[dict]) -> list[tuple[int, bool, bool]]:
        """`(column, desc, nulls_first)` of each sort key."""
        directions = {
            "SORT_DIRECTION_ASC_NULLS_FIRST": (False, True),
            "SORT_DIRECTION_ASC_NULLS_LAST": (False, False),
            "SORT_DIRECTION_DESC_NULLS_FIRST": (True, True),
            "SORT_DIRECTION_DESC_NULLS_LAST": (True, False),
        }
        out: list[tuple[int, bool, bool]] = []
        for s in sorts:
            d = directions.get(s.get("direction", ""))
            if "selection" not in s["expr"] or d is None:
                raise Unsupported("window sort keys must be columns with a direction")
            out.append((ex.field(s["expr"]["selection"]), d[0], d[1]))
        return out

    def window_spec(
        self, ex: Exprs, name: str, args: list[dict], w: dict, dtypes: list[DType], sorts: list
    ) -> WindowSpec:
        """A window function computed row by row (`WinFn.valueIn`)."""

        def int_arg(j: dict, what: str) -> int:
            if "literal" not in j or literal(j["literal"])[1] != pl.Int64:
                raise Unsupported(f"{what} must be an integer literal")
            v = literal(j["literal"])[0]
            if v <= 0:
                raise Unsupported(f"{what} must be positive")
            return v

        frame = window_frame(w)
        if name in ("rank", "dense_rank", "percent_rank", "cume_dist") and not args:
            t = pl.Float64 if name in ("percent_rank", "cume_dist") else pl.Int64
            return WindowSpec(name, t)
        if name == "ntile" and len(args) == 1:
            return WindowSpec(name, pl.Int64, n=int_arg(args[0], "NTILE's buckets"))
        if name in ("first_value", "last_value", "nth_value"):
            c = self.column(ex, args[0])
            n = int_arg(args[1], "NTH_VALUE's n") if name == "nth_value" else 0
            idx = ex.field(args[0]["selection"])
            return WindowSpec(name, materialize(c.dtype), col=idx, n=n, frame=frame)
        if name in ("count", "sum", "avg", "min", "max") and len(args) <= 1:
            if not args:
                return WindowSpec("agg", pl.Int64, agg="count", col=None, frame=frame)
            a = args[0]
            itof = "cast" in a and "selection" in a["cast"].get("input", {})
            sel = a["cast"]["input"] if itof else a
            if "selection" not in sel and "literal" not in sel:
                raise Unsupported("window aggregates of expressions are not supported")
            if "literal" in sel:
                return WindowSpec("agg", pl.Int64, agg="count", col=None, frame=frame)
            idx = ex.field(sel["selection"])
            t = dtypes[idx]
            fn = {"sum": "fsum" if t == pl.Float64 or itof else "sum"}.get(name, name)
            if name == "avg" and not itof and t == pl.Int64 and _int_output(w):
                fn = "iavg"
            if is_decimal(t) and not itof:
                # A decimal `SUM` has ten more digits (#27); Lean writes a
                # windowed `AVG` as `sverify_decimal_div` of `SUM` and `COUNT`.
                if name == "sum":
                    dsum = pl.Decimal(*_decimals.sum_of((t.precision, t.scale)))  # pyrefly: ignore
                    return WindowSpec("agg", dsum, agg="dsum", col=idx, frame=frame)
                if name not in ("count", "min", "max"):
                    raise Unsupported(f"{name} of a DECIMAL over a window is not supported")
            if name in ("min", "max") and t == pl.Float64 and not itof:
                # By the codes' order: NaN the greatest double, one zero.
                fn = "f" + name
            out = {"count": pl.Int64, "sum": pl.Int64, "fsum": pl.Float64, "avg": pl.Float64,
                   "fmin": pl.Float64, "fmax": pl.Float64, "iavg": pl.Int64,
                   "bit_and": pl.Int64, "bit_or": pl.Int64, "bit_xor": pl.Int64}  # fmt: skip
            return WindowSpec("agg", out.get(fn, materialize(t)), agg=fn, col=idx, frame=frame)
        raise Unsupported(f"unsupported window function {name}/{len(args)}")

    def sorted(
        self, lf: pl.LazyFrame, ex: Exprs, sorts: list[dict], rel: bool = False
    ) -> pl.LazyFrame:
        """`mergeSort (sortLe keys)`: stable, each key with its direction and
        NULL placement, values in `Value.le` order (strings by code point,
        which is UTF-8 byte order, as Polars sorts them)."""
        by, desc, nulls_last = [], [], []
        for s in sorts:
            d = shims.null_order(s.get("direction"))
            # A `SortRel`'s clustered key: a sort realizes it (D6).
            if d is None and rel and s.get("direction") == "SORT_DIRECTION_CLUSTERED":
                d = (False, True)
            if d is None:
                raise Unsupported(f"unsupported sort direction {s.get('direction')}")
            key = self.column(ex, s["expr"])
            by.append(ordered(key.expr, key.dtype))
            desc.append(d[0])
            nulls_last.append(d[1])
        if not by:
            return lf
        return lf.sort(by, descending=desc, nulls_last=nulls_last, **shims.tie_order())

    def sort(self, r: dict) -> Frame:
        """`Rel.orderBy`."""
        lf, dtypes = self.rel(r["input"])
        return self.sorted(lf, self.exprs(dtypes), r.get("sorts", []), rel=True), dtypes

    def aggregate(self, r: dict) -> Frame:
        """`Rel.distinct` (a grouping by every column in order, no measures) or
        `Rel.aggregate` (`aggregateEval`): one row per distinct key, in order
        of first occurrence, or exactly one row without grouping expressions.
        Keys are equal as `Value`s: NULLs equal, doubles by their codes."""
        lf, dtypes = self.rel(r["input"])
        n = len(dtypes)
        ex = self.exprs(dtypes)
        top = r.get("groupingExpressions", [])
        groupings = r.get("groupings", [])
        measures = r.get("measures", [])
        if len(groupings) > 1:
            raise Unsupported("grouping sets are not in Lean's written form")
        if groupings:
            refs = [int(k) for k in groupings[0].get("expressionReferences", [])]
            if any(k >= len(top) for k in refs):
                raise Unsupported("grouping expression out of range")
            group_js = [top[k] for k in refs]
        elif measures:
            group_js = []
        else:
            raise Unsupported("an aggregate without groupings needs measures")
        groups = [ex(g) for g in group_js]
        fields = [ex.field(g["selection"]) if "selection" in g else -1 for g in group_js]
        if not measures and fields == list(range(n)):
            return self.distinct(lf, dtypes)
        ms = [self.measure(m, ex) for m in measures]
        # Grouping expressions and every measure's argument and filter are
        # evaluated on every input row (`Rel.HasIssue`).
        lf = self.guard(lf, [*groups, *(v for m in ms for v in m.vals)])
        keys = [f"__sv_g{k}" for k in range(len(groups))]
        lf = lf.with_columns(
            [ordered(g.expr, g.dtype).alias(k) for g, k in zip(groups, keys, strict=True)]
            + [g.expr.alias(f"__sv_v{k}") for k, g in enumerate(groups)]
            + [m.values.alias(f"__sv_m{j}") for j, m in enumerate(ms)]
            + [
                ordered(key.expr, key.dtype).alias(f"__sv_m{j}_k{i}")
                for j, m in enumerate(ms)
                for i, (key, _, _) in enumerate(m.sorts)
            ]
        )
        # Native aggregations (`Measure.native`), and the lists of values
        # the others compute their measure from (`Measure.result`).
        values, aggs = [], []
        natives = [m.native(f"__sv_m{j}") for j, m in enumerate(ms)]
        for j, m in enumerate(ms):
            if (nat := natives[j]) is not None:
                aggs += [e.alias(k) for k, e in nat.aggs.items()]
                continue
            v = pl.col(f"__sv_m{j}")
            if m.sorts:
                # `Measure.eval`: the group's rows in a stable sort by the keys.
                v = v.sort_by(
                    [pl.col(f"__sv_m{j}_k{i}") for i in range(len(m.sorts))],
                    descending=[d for _, d, _ in m.sorts],
                    nulls_last=[n for _, _, n in m.sorts],
                    maintain_order=True,
                )
            v = v.drop_nulls()
            if m.distinct:
                # The first of equal values, in order (`dedup`).
                key = _float_key(v) if m.arg.dtype == pl.Float64 else v
                v = key.unique(maintain_order=True)
            values.append(v)
        if groups:
            firsts = [pl.col(f"__sv_v{k}").first() for k in range(len(groups))]
            out = lf.group_by(keys, maintain_order=True).agg(firsts + values + aggs)
        else:
            out = lf.select([v.implode() for v in values] + aggs)
        # The issues of whole groups: an integer `SUM` that leaves 64 bits, …
        out = self.guard(out, [
            Val(pl.lit(None), pl.Null, tuple(issue(f, k, msg) for f, k, msg in nat.flags))
            for nat in natives if nat is not None
        ])  # fmt: skip
        out = out.select(
            [pl.col(f"__sv_v{k}").alias(col(k)) for k in range(len(groups))]
            + [
                (m.result(pl.col(f"__sv_m{j}")) if nat is None else nat.result).alias(
                    col(len(groups) + j)
                )
                for j, (m, nat) in enumerate(zip(ms, natives, strict=True))
            ]
        )
        return out, [materialize(g.dtype) for g in groups] + [m.dtype for m in ms]

    @staticmethod
    def distinct(lf: pl.LazyFrame, dtypes: list[DType]) -> Frame:
        """`dedup`: the first of each set of equal rows, in order."""
        n = len(dtypes)
        keys = [f"__sv_key{i}" for i in range(n)]
        return (
            lf.with_columns(
                [
                    ordered(pl.col(col(i)), t).alias(k)
                    for i, (t, k) in enumerate(zip(dtypes, keys, strict=True))
                ]
            )
            .unique(subset=keys, keep="first", maintain_order=True)
            .select([col(i) for i in range(n)]),
            dtypes,
        )

    def measure(self, j: dict, ex: Exprs) -> Measure:
        """A `Measure` as Lean writes it: one argument, `DISTINCT` or `ALL`, and
        an optional `FILTER`."""
        m = j.get("measure", {})
        name = ex.function(m.get("functionReference"))
        if m.get("sorts") and name != "array_agg":
            raise Unsupported(f"ordered aggregates are not supported: {name}")
        invocation = m.get("invocation", "AGGREGATION_INVOCATION_ALL")
        if invocation not in ("AGGREGATION_INVOCATION_ALL", "AGGREGATION_INVOCATION_DISTINCT"):
            raise Unsupported(f"unsupported aggregate invocation {invocation}")
        args = [a["value"] for a in m.get("arguments", [])]
        if len(args) != 1:
            raise Unsupported(f"{name} takes one argument in Lean's written form")
        arg = ex(args[0])
        cond = ex(j["filter"]) if "filter" in j else None
        if cond is not None and cond.dtype not in (pl.Boolean, pl.Null):
            raise Unsupported(f"aggregate filter of type {cond.dtype}")
        t = arg.dtype
        fn: str | None = None
        if name == "count":
            fn = "count"
        elif name == "sum" and t in (pl.Int64, pl.Float64):
            fn = "sum" if t == pl.Int64 else "fsum"
        elif name in ("sum", "avg") and is_decimal(t):
            # `SUM` has ten more digits, `AVG` four more and four more places
            # (`Measure.kind`, `decimalAvgs`, #27).
            if name == "avg" and t.precision + 4 > DEC_DIGITS:  # pyrefly: ignore
                raise Unsupported("AVG of a DECIMAL of more than 34 digits is not supported")
            fn = "dsum" if name == "sum" else "davg"
        elif name == "avg" and t == pl.Float64:
            fn = "avg"
        elif name in ("variance", "std_dev") and t == pl.Float64:
            pop = any(
                o.get("name") == "distribution" and o.get("preference", [None])[0] == "POPULATION"
                for o in m.get("options", [])
            )
            fn = ("var" if name == "variance" else "std") + ("_pop" if pop else "_samp")
        elif name == "avg" and t == pl.Int64 and _int_output(m):
            fn = "iavg"
        elif name in ("min", "max") and (
            t in (pl.Int64, pl.String, pl.Boolean, US, pl.Date) or is_decimal(t)
        ):
            fn = name
        elif name in ("min", "max") and t == pl.Float64:
            fn = "f" + name
        elif name == "array_agg" and t in (pl.Int64, pl.Float64, pl.String, pl.Boolean):
            fn = "collect"
        elif name in ("bit_and", "bit_or", "bit_xor") and t == pl.Int64:
            fn = name
        if fn is None:
            raise Unsupported(f"unsupported aggregate {name} of {t}")
        sorts = []
        for s in m.get("sorts", []):
            d = s.get("direction")
            if d not in SORT_DIRECTIONS:
                raise Unsupported(f"unsupported sort direction {d}")
            sorts.append((self.column(ex, s["expr"]), *SORT_DIRECTIONS[d]))
        distinct = invocation == "AGGREGATION_INVOCATION_DISTINCT"
        return Measure(fn, arg, distinct, cond, tuple(sorts))

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
        """`Rel.join`, and `Rel.semi` for semi and anti joins. Equalities
        between a left and a right column become hash-join keys with NULLs
        never matching (`nulls_equal=False`, as `isTrue (eq NULL _)` is
        false); the rest of the condition filters the matches. Row indices
        restore `Rel.eval`'s order."""
        how = {
            "JOIN_TYPE_INNER": "inner",
            "JOIN_TYPE_LEFT": "left",
            "JOIN_TYPE_LEFT_SEMI": "semi",
            "JOIN_TYPE_LEFT_ANTI": "anti",
        }.get(r.get("type", ""))
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
            matches = self.guard(matches, conds).filter(is_true(on))
        if how in ("semi", "anti"):
            # `Rel.semi`: the left rows with (`anti`: without) a match, in order.
            left_cols = [col(i) for i in range(n)]
            kept = left.join(
                matches.select(_LEFT).unique(), on=_LEFT, how=how, maintain_order="left"
            )
            return kept.sort(_LEFT, maintain_order=True).select(left_cols), dtypes[:n]
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
        lf, dtypes = self.rel(r["input"])

        def constant(key: str) -> int | None:
            """`offsetExpr`/`countExpr` (Lean writes integer literals), or the
            deprecated `offset`/`count`."""
            if key + "Expr" in r:
                lit = r[key + "Expr"].get("literal", {})
                if "null" in lit:
                    return None
                if "i64" not in lit:
                    raise Unsupported(f"FetchRel.{key}Expr must be an integer literal")
                return int(lit["i64"])
            return int(r[key]) if key in r else None

        offset = constant("offset") or 0
        count = constant("count")
        count = -1 if count is None else count
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


def _translate(
    plan: str | dict, tables: Tables, guards: Guards = True
) -> tuple[pl.LazyFrame, list[str]]:
    """The plan's `LazyFrame`, with its columns still positional (`c0`, `c1`,
    …) and cast to their output types, and the root's column names."""
    p = json.loads(plan) if isinstance(plan, str) else plan
    roots = [r["root"] for r in p.get("relations", []) if "root" in r]
    if len(roots) != 1:
        raise Unsupported("plan must have exactly one root relation")
    lf, dtypes = Translator(p, tables, guards).rel(roots[0]["input"])
    names = roots[0].get("names") or [col(i) for i in range(len(dtypes))]
    if len(names) != len(dtypes):
        raise Unsupported(f"root names {names} do not match arity {len(dtypes)}")
    return lf.select([pl.col(col(i)).cast(materialize(t)) for i, t in enumerate(dtypes)]), names


def to_lazy(plan: str | dict, tables: Tables, *, guards: Guards = True) -> pl.LazyFrame:
    """The `LazyFrame` for a plan in Lean's written form, over `tables`
    (by name; columns in schema order). Columns are named by `RelRoot.names`;
    a Polars frame cannot hold two columns of one name, so a plan whose root
    repeats a name (legal in SQL and Substrait) is refused here, and `run`
    names its Arrow result instead.

    `guards=False` leaves out the per-row checks for runtime issues (`guard`);
    only for a plan whose contract report is `guard_free`, on data that meets
    its preconditions (`Rel.guardFree_sound`). Integer `SUM` keeps its check.
    A collection of `Issue.name`s checks exactly those: for a plan verified
    under the reference, the issues its report assumes (`Report.assumed`:
    "SUM overflow", "overflow to infinity", #575)."""
    lf, names = _translate(plan, tables, guards)
    if len(set(names)) != len(names):
        raise Unsupported(f"root names {names} repeat a name; use `run`")
    return lf.rename({col(i): name for i, name in enumerate(names)})


def collect_streaming(lf: pl.LazyFrame, **kwargs: Any) -> pl.DataFrame:
    """`lf.collect` on Polars's streaming engine, named explicitly: with
    `engine="streaming"`, Polars 2.1.0 ignores `pl.Config.set_engine_affinity`,
    `POLARS_ENGINE_AFFINITY`, `POLARS_FORCE_STREAMING` and
    `POLARS_AUTO_STREAMING` (`LazyFrame::collect_with_engine`). Operators the
    streaming engine lacks still run on the in-memory engine inside the
    streaming plan (`fallback_nodes`)."""
    return lf.collect(engine="streaming", **kwargs)


#: The colour Polars's physical plan gives a node the streaming engine runs
#: on the in-memory engine (`polars-stream`'s `NodeStyle::InMemoryFallback`:
#: `InMemoryMap`, `InMemoryJoin`, `ColumnarFunction`, `Recursive`).
_FALLBACK_COLOUR = '"0.0 0.3 1.0"'
_NODE = re.compile(r'^\d+ \[label="(.*)",style=filled,fillcolor=(".*")\];$')
#: The optimizations sverify runs a plan with (`collect`). Predicate pushdown
#: would move `guard`s below the filters before them, onto rows the plan never
#: evaluates there. Common-subexpression elimination hoists an expression two
#: `when/then` branches share into a column computed on every row, so a
#: guarded cast or division would run on the rows its `CASE` excludes and
#: raise (PL-6, polars-exec-cse-hoist).
_OPTIMIZATIONS = pl.QueryOptFlags(predicate_pushdown=False, comm_subexpr_elim=False)


@dataclass(frozen=True)
class Fallback:
    """An allowed node of a streaming plan that runs on the in-memory engine:
    an operation Polars 2.1.0 cannot stream, or sverify does not yet."""

    name: str
    kind: str
    """The node's kind (`in-memory-map`, `columnar-function`, …)."""
    pattern: str
    """A regular expression the node's label matches."""
    reason: str
    fact: str


#: The fallbacks sverify's plans may have; any other one is a regression
#: (`tests/conftest.py` checks every plan the Polars tests run).
ALLOWED_FALLBACKS: tuple[Fallback, ...] = (
    Fallback("ordered list", "in-memory-map", r"\.implode\(",
             "an order-keeping list per group (`ARRAY_AGG`): Polars 2.1.0 has no streaming "
             "reduction for `implode` with `maintain_order` (`lower_group_by.rs`)",
             "polars-exec-streaming-fallback"),
    Fallback("window frames", "in-memory-map", r"OPAQUE_PYTHON",
             "window functions over frames, ranks and NTILE (`python_windows`): sverify "
             "computes them in Python on the whole frame (`LazyFrame.map_batches`)",
             "polars-exec-streaming-fallback"),
)  # fmt: skip


def fallback_nodes(lf: pl.LazyFrame) -> list[str]:
    """The nodes of `lf`'s streaming plan, as `collect` runs it, that run on
    the in-memory engine: each node's kind and label, one line each
    (`in-memory-map: AGGREGATE[…] …`)."""
    try:
        dot = lf.show_graph(
            engine="streaming",
            plan_stage="physical",
            raw_output=True,
            show=False,
            optimizations=_OPTIMIZATIONS,
        )
    except BaseException as e:  # noqa: BLE001 - pyo3's PanicException is not an Exception
        if type(e).__name__ != "PanicException":
            raise
        # Polars's formatter takes expressions of at most 65 535 characters
        # (`polars-stream`'s `fmt.rs`); the nodes are then unknown.
        return [UNINSPECTABLE]
    out = []
    for line in str(dot).splitlines():
        if (m := _NODE.match(line)) and m[2] == _FALLBACK_COLOUR:
            kind, _, label = m[1].replace("\\n", " ").partition(" ")
            out.append(f"{kind}: {label.strip()}")
    return out


#: `fallback_nodes` of a plan Polars cannot describe: no allowed fallback.
UNINSPECTABLE = "unknown: Polars cannot describe the streaming plan (an expression too long)"


def plan_fallbacks(plan: str | dict, tables: Tables, *, guards: Guards = True) -> list[str]:
    """`fallback_nodes` of a plan in Lean's written form, as `run` would run
    it over `tables`."""
    lf, _ = _translate(plan, tables, guards)
    return fallback_nodes(lf)


def disallowed_fallbacks(lf: pl.LazyFrame) -> list[str]:
    """`fallback_nodes` that no entry of `ALLOWED_FALLBACKS` covers."""
    return [
        n
        for n in fallback_nodes(lf)
        if not any(
            n.startswith(f.kind + ":") and re.search(f.pattern, n) for f in ALLOWED_FALLBACKS
        )
    ]


def collect(lf: pl.LazyFrame) -> pl.DataFrame:
    """Run a translated plan on the streaming engine (`collect_streaming`),
    without predicate pushdown and common-subexpression elimination
    (`_OPTIMIZATIONS`)."""
    return collect_streaming(lf, optimizations=_OPTIMIZATIONS)


def run(plan: str | dict, tables: Tables, *, guards: Guards = True) -> pa.Table:
    """Run a plan in Lean's written form on Polars (`guards`: see `to_lazy`).
    The columns are named by `RelRoot.names`, repeats included."""
    lf, names = _translate(plan, tables, guards)
    return collect(lf).to_arrow().rename_columns(names)
