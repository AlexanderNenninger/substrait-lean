"""The lift's rule of CAST."""

from __future__ import annotations

import contextlib
from decimal import ROUND_HALF_UP, Decimal, localcontext
from typing import Any

import ibis.expr.datatypes as dt
import sqlglot.expressions as sge
from ibis.backends.sql.datatypes import DuckDBType

from sverify.plan_json import Unsupported, cast_json, literal, type_json
from sverify.sql_lift._base import (
    DIALECT,
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
        raise Unsupported(f"a cast of a string to {t} is not supported yet (#27)")
    if t.is_timestamp() and t.timezone is not None:
        raise Unsupported("timestamps with a time zone are not supported")
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


def _cast(lf: _Lift, node: sge.Cast, sub: Sub, scope: list[Column]) -> E:
    try_ = isinstance(node, sge.TryCast) or bool(node.args.get("safe"))
    if node.args.get("format"):
        raise Unsupported("CAST … FORMAT is not supported")
    try:
        t: Any = DuckDBType.to_ibis(node.to).copy(nullable=True)
    except Exception as e:  # noqa: BLE001 - Ibis raises a variety
        raise Unsupported(f"CAST to {node.to.sql(DIALECT)} is not supported") from e
    if node.to.this == sge.DataType.Type.NULL:
        raise Unsupported(f"CAST to {node.to.sql(DIALECT)} is not supported")
    if node.to.is_type(*sge.DataType.TEMPORAL_TYPES) and [
        p.sql(DIALECT) for p in node.to.expressions
    ] not in ([], ["4"], ["5"], ["6"]):
        # DuckDB reads `TIMESTAMP(p)` as seconds for p = 0, milliseconds for
        # 1 to 3 and nanoseconds for 7 to 9; the model's timestamps are
        # microseconds, DuckDB's for 4 to 6 (#626, #323).
        raise Unsupported(f"CAST to {node.to.sql(DIALECT)}: a precision is not supported")
    if node.to.this in (sge.DataType.Type.INT128, sge.DataType.Type.UINT128):
        raise Unsupported(f"CAST to {node.to.sql(DIALECT)} (HUGEINT) is not supported")
    if t.is_array() and getattr(t, "length", None) is not None:
        raise Unsupported(f"CAST to the fixed-size array {node.to.sql(DIALECT)} is not supported")
    type_json(t)  # refuses the types outside the model
    a = sub(node.this)
    from_string = a.type.is_string() and not t.is_string() and (try_ or not a.constant)
    if from_string and not try_ and _in_filtered_aggregate(node):
        raise Unsupported(
            f"{node.sql(DIALECT)} in an aggregate with FILTER: DuckDB casts every row's "
            "argument before the FILTER, and raises on a row it filters out; use TRY_CAST"
        )
    if from_string and (lifted := _from_varchar(lf, a, t, try_)) is not None:
        return lifted
    if try_:
        raise Unsupported("TRY_CAST is only supported of strings yet")
    if a.constant and a.type.is_string() and (t.is_date() or t.is_timestamp() or t.is_time()):
        return _temporal(a, t)
    if a.constant and a.type.is_string() and t.is_decimal():
        text = a.value.strip()
        try:
            v = Decimal(text)
        except ArithmeticError as e:
            raise Unsupported(f"CAST of {text!r} to {t} is not supported") from e
        # Python reads digit separators and exponents DuckDB raises on
        # (`'_12.12'`, `'1e-9999999999'`; `'1e-9999'` DuckDB reads).
        exponent = v.as_tuple().exponent
        if "_" in text or (isinstance(exponent, int) and abs(exponent) > 10**6):
            raise Unsupported(f"CAST of {text!r} to {t} is not supported")
        if v.is_finite():
            # DuckDB rounds the digits past the scale half away from zero.
            with localcontext() as ctx:
                ctx.prec = 100
                v = v.quantize(Decimal(1).scaleb(-t.scale), rounding=ROUND_HALF_UP)
        if not (v.is_finite() and _fits(v, t)):
            raise Unsupported(f"CAST of {text!r} to {t}: DuckDB raises, the value does not fit")
        return E(literal(v, t), t, v)
    if not a.constant:
        for src, to, sql in (
            (dt.float64, dt.int64, "DOUBLE AS BIGINT"),
            (dt.int64, dt.float64, "BIGINT AS DOUBLE"),
        ):
            if _same(a.type, src) and _same(t, to) and (g := _generated(lf, f"CAST({sql})", [a])):
                return g
    # Other casts: pending generation (#268).
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


register(
    {
        sge.Cast: _cast,
        sge.TryCast: _cast,
    }
)
