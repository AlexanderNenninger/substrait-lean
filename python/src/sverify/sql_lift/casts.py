"""The lift's rule of CAST."""

from __future__ import annotations

import contextlib
from decimal import ROUND_HALF_UP, Decimal, localcontext
from typing import Any

import ibis.expr.datatypes as dt
import sqlglot.expressions as sge
from ibis.backends.sql.datatypes import DuckDBType

from sverify.plan_json import Unsupported, literal, type_json
from sverify.sql_lift._base import (
    DIALECT,
    Column,
    E,
    Sub,
    _fits,
    _generated,
    _Lift,
    _numeric,
    _same,
    register,
)
from sverify.sql_lift.temporal import _temporal


def _cast(lf: _Lift, node: sge.Cast, sub: Sub, scope: list[Column]) -> E:
    if isinstance(node, sge.TryCast) or node.args.get("safe"):
        raise Unsupported("TRY_CAST is not supported yet")
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
    if a.constant and a.type.is_string() and (t.is_date() or t.is_timestamp() or t.is_time()):
        return _temporal(a, t)
    if a.constant and a.type.is_string() and t.is_decimal():
        text = a.value.strip()
        try:
            v = Decimal(text)
        except ArithmeticError as e:
            raise Unsupported(f"CAST of {text!r} to {t} is not supported") from e
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
    }
)
