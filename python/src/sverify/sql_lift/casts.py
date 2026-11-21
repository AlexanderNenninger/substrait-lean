"""The lift's rule of CAST."""

from __future__ import annotations

import contextlib
from decimal import ROUND_HALF_UP, Decimal, localcontext
from typing import Any

import ibis.expr.datatypes as dt
import sqlglot.expressions as sge
from ibis.backends.sql.datatypes import DuckDBType

from sverify._decimals import EXACT
from sverify._dialect import REFUSED
from sverify.plan_json import (
    SqlUnsupported,
    Unsupported,
    cast_json,
    literal,
    type_json,
)
from sverify.sql_lift._base import (
    DIALECT,
    DUCKDB,
    Column,
    E,
    Sub,
    _fits,
    _fn,
    _generated,
    _Lift,
    _numeric,
    _same,
    register,
)
from sverify.sql_lift.temporal import _temporal

#: The black box of a cast from VARCHAR to each target (#806), by the
#: target's type: `varchar_<name>`, `try_varchar_<name>` for `TRY_CAST`.
_FROM_VARCHAR = (
    (lambda t: t.is_integer(), "bigint", dt.int64),
    (lambda t: t.is_float64(), "double", dt.float64),
    (lambda t: t.is_boolean(), "boolean", dt.boolean),
    (lambda t: t.is_date(), "date", dt.date),
    (lambda t: t.is_timestamp(), "timestamp", dt.timestamp(scale=6)),
)


def _from_varchar(lf: _Lift, a: E, t: Any, try_: bool) -> E | None:
    """`CAST(s AS t)` or `TRY_CAST(s AS t)` of a string: the black box of the
    target (`black_box.py`), DuckDB's rules. An integer narrower than a
    BIGINT is the BIGINT cast down, as DuckDB fails (or, trying, is NULL)
    where either does."""
    if t.is_decimal():
        raise Unsupported(f"a cast of a string to {t} is not supported yet (#27)", construct="CAST")
    if t.is_timestamp() and t.timezone is not None:
        raise Unsupported(
            "a cast of a string to a timestamp with a time zone is not supported yet (#1725): "
            "conversions and literals of instants follow",
            construct="CAST",
        )
    for accepts, name, via in _FROM_VARCHAR:
        if accepts(t):
            row = f"{'try_' if try_ else ''}varchar_{name}"
            e = E(_fn(row, [a.json], via), via)
            if _same(via, t):
                return e
            return E(cast_json(e.json, t, or_null=try_), t)
    return None  # other targets: the casts the model had before


def _in_filtered_aggregate(node: sge.Expression) -> bool:
    """Is `node` in the argument of an aggregate with `FILTER (WHERE …)`?"""
    child, parent = node, node.parent
    while parent is not None:
        if isinstance(parent, sge.Filter):
            return child.arg_key == "this"
        child, parent = parent, parent.parent
    return False


#: The roundings whose `CAST(... AS BIGINT)` of a double lifts as one function
#: of the generated table (#1655), by sqlglot's node.
_ROUNDED: dict[type[sge.Expression], str] = {
    sge.Round: "round",
    sge.Floor: "floor",
    sge.Ceil: "ceil",
}


def _rounding(node: sge.Cast) -> sge.Expression | None:
    """The `round`, `floor` or `ceil` (no digit count) that `node` casts, through
    any parentheses: its operand is integral, so both readings of the cast agree.
    `round(x, 2)` is not: it leaves a fraction."""
    inner = node.this
    while isinstance(inner, sge.Paren):
        inner = inner.this
    rounds = type(inner) in _ROUNDED and inner.args.get("decimals") is None
    return inner if rounds else None


def _rounded_to_bigint(lf: _Lift, node: sge.Cast, a: E, t: Any, sub: Sub) -> E | None:
    """`CAST(round(x) AS BIGINT)`, and of `floor(x)` and `ceil(x)`, of a double
    under DuckDB's semantics: the argument is integral, so DuckDB's half-to-even
    cast is the model's truncating one (the generated table's
    `CAST(round(DOUBLE) AS BIGINT)`, #1655). None for any other cast."""
    r = _rounding(node)
    if r is None or not (a.type.is_float64() and _same(t, dt.int64)):
        return None
    return _generated(lf, f"CAST({_ROUNDED[type(r)]}(DOUBLE) AS BIGINT)", [sub(r.this)])


def _cast(lf: _Lift, node: sge.Cast, sub: Sub, scope: list[Column]) -> E:
    try_ = isinstance(node, sge.TryCast) or bool(node.args.get("safe"))
    if node.args.get("format"):
        raise SqlUnsupported("CAST … FORMAT is not supported", construct="CAST FORMAT")
    try:
        t: Any = DuckDBType.to_ibis(node.to).copy(nullable=True)
    except Exception as e:  # noqa: BLE001 - Ibis raises a variety
        raise SqlUnsupported(
            f"CAST to {node.to.sql(DIALECT)} is not supported", construct="CAST"
        ) from e
    if node.to.this == sge.DataType.Type.NULL:
        raise SqlUnsupported(f"CAST to {node.to.sql(DIALECT)} is not supported", construct="CAST")
    if node.to.is_type(*sge.DataType.TEMPORAL_TYPES) and [
        p.sql(DIALECT) for p in node.to.expressions
    ] not in ([], ["4"], ["5"], ["6"]):
        # DuckDB reads `TIMESTAMP(p)` as seconds for p = 0, milliseconds for
        # 1 to 3 and nanoseconds for 7 to 9; the model's timestamps are
        # microseconds, DuckDB's for 4 to 6 (#626, #323).
        raise SqlUnsupported(
            f"CAST to {node.to.sql(DIALECT)}: a precision is not supported", construct="CAST"
        )
    if node.to.this in (sge.DataType.Type.INT128, sge.DataType.Type.UINT128):
        raise SqlUnsupported(
            f"CAST to {node.to.sql(DIALECT)} (HUGEINT) is not supported",
            issue=350,
            construct="CAST",
        )
    if t.is_array() and getattr(t, "length", None) is not None:
        raise SqlUnsupported(
            f"CAST to the fixed-size array {node.to.sql(DIALECT)} is not supported",
            construct="CAST",
        )
    if isinstance(t, dt.Timestamp) and t.scale in (0, 3):
        # DuckDB's cast to TIMESTAMP_S or TIMESTAMP_MS truncates toward zero
        # (`duckdb-ts-narrow-toward-zero`); the model's narrowing floors (D61).
        raise SqlUnsupported(
            f"CAST to {node.to.sql(DIALECT)} truncates toward zero in DuckDB; "
            "write date_trunc to the unit instead",
            issue=323,
            construct="CAST",
        )
    type_json(t)  # refuses the types outside the model
    a = sub(node.this)
    if t.is_string() and a.type.is_decimal() and a.type.precision == a.type.scale:
        # DuckDB prints a DECIMAL(p, p) without its integer part (`.500`), the reference with
        # it (`0.500`): neither reading is the SQL's, so the lift refuses it (D72, ruling 245).
        p, s = a.type.precision, a.type.scale
        wide = f"DECIMAL({p + 1}, {s})" if p < 38 else f"DECIMAL(38, {s - 1})"
        raise SqlUnsupported(
            f"{node.sql(DIALECT)} is a DECIMAL({p}, {s}) as text: DuckDB prints it without its "
            f"integer part (.500) and the reference with it (0.500)",
            hint=f"cast it to {wide} first",
            construct="CAST",
        )
    # DuckDB casts to and from a timestamp with a time zone in the session's zone (D53).
    in_tz = a.type.is_timestamp() and a.type.timezone is not None
    to_tz = t.is_timestamp() and t.timezone is not None
    if (in_tz and not to_tz) or (to_tz and not in_tz and not (a.type.is_string() and a.constant)):
        raise SqlUnsupported(
            f"{node.sql(DIALECT)} follows the session time zone in DuckDB; write "
            "x AT TIME ZONE 'UTC' to convert between a timestamp and a timestamp with a "
            "time zone at UTC (#1725)",
            construct="CAST",
        )
    from_string = a.type.is_string() and not t.is_string() and (try_ or not a.constant)
    if from_string and not try_ and _in_filtered_aggregate(node):
        raise Unsupported(
            f"{node.sql(DIALECT)} in an aggregate with FILTER: DuckDB casts every row's "
            "argument before the FILTER, and raises on a row it filters out; use TRY_CAST",
            construct="CAST",
        )
    if from_string and (lifted := _from_varchar(lf, a, t, try_)) is not None:
        return lifted
    if try_:
        raise Unsupported("TRY_CAST is only supported of strings yet", construct="TRY CAST")
    if a.constant and a.type.is_string() and (t.is_date() or t.is_timestamp() or t.is_time()):
        return _temporal(a, t)
    if a.constant and a.type.is_string() and t.is_decimal():
        text = a.value.strip()
        try:
            v = Decimal(text)
        except ArithmeticError as e:
            raise SqlUnsupported(
                f"CAST of {text!r} to {t} is not supported", construct="CAST"
            ) from e
        # Python reads digit separators and exponents DuckDB raises on
        # (`'_12.12'`, `'1e-9999999999'`; `'1e-9999'` DuckDB reads).
        exponent = v.as_tuple().exponent
        if "_" in text or (isinstance(exponent, int) and abs(exponent) > 10**6):
            raise SqlUnsupported(f"CAST of {text!r} to {t} is not supported", construct="CAST")
        if v.is_finite():
            # DuckDB rounds the digits past the scale half away from zero.
            with localcontext(EXACT):
                v = v.quantize(Decimal(1).scaleb(-t.scale), rounding=ROUND_HALF_UP)
        if not (v.is_finite() and _fits(v, t)):
            raise SqlUnsupported(
                f"CAST of {text!r} to {t}: DuckDB raises, the value does not fit",
                hint="write a value that fits the type, or a wider type",
                construct="CAST",
            )
        return E(literal(v, t), t, v)
    if not a.constant and (rounded := _rounded_to_bigint(lf, node, a, t, sub)) is not None:
        return rounded
    if not a.constant:
        for src, to, sql in (
            (dt.float64, dt.int64, "DOUBLE AS BIGINT"),
            (dt.int64, dt.float64, "BIGINT AS DOUBLE"),
        ):
            if _same(a.type, src) and _same(t, to) and (g := _generated(lf, f"CAST({sql})", [a])):
                return g
    if t.is_integer() and a.type.is_decimal():
        # DuckDB rounds a decimal half away from zero, as the reference's rescale to
        # scale 0 does (`decimal_rescale`); the exact cast of that is the value (#322). One digit
        # more than the integer part holds the carry (99.5 to 100).
        whole = dt.Decimal(min(a.type.precision - a.type.scale + 1, 38), 0, nullable=True)
        return lf.to(lf.to(E(a.json, a.type), whole), t)
    # Other casts: pending generation (#268).
    if t.is_integer() and a.type.is_floating():
        hint = REFUSED["float_to_int"]
        if a.type.is_float32():
            # `round` of a REAL lifts once it is a DOUBLE, which holds it exactly (#2152).
            hint += "; for a FLOAT x, write CAST(x AS DOUBLE) in place of x"
        if lf.profile.float_to_int != "TRUNCATE":
            raise SqlUnsupported(
                f"CAST of a {a.type} to {t} rounds ({lf.profile.float_to_int}) in DuckDB, which "
                f"the model's casts (they truncate) cannot state yet (#322); {hint}",
                construct="CAST",
            )
        # `round`, `floor` and `ceil` leave an integral double: both readings agree.
        if _rounding(node) is None:
            raise SqlUnsupported(
                f"CAST of a {a.type} to {t} is DuckDB's cast, which rounds "
                f"({DUCKDB.float_to_int}); sverify's reference truncates (R9); {hint}",
                construct="CAST",
            )
    # A numeric constant becomes a literal of the type, where that is exact
    # (not a double or decimal made an integer, nor one that doesn't fit).
    exact = not (t.is_integer() and not a.type.is_integer())
    if a.constant and a.value is not None and _numeric(a.type) and _numeric(t) and exact:
        with contextlib.suppress(Unsupported):
            return lf.to(a, t)
    if a.constant and a.type.is_date() and t.is_timestamp():
        return lf.to(a, t)  # the timestamp at the date's midnight
    return lf.to(E(a.json, a.type), t)


register(
    {
        sge.Cast: _cast,
        sge.TryCast: _cast,
    }
)
