"""Cast rules of the Ibis producer: `CAST`, `TRY_CAST` and `typeof`.

Part of the Ibis producer (`sverify.ibis_substrait`), derived from
ibis-substrait (Apache License 2.0); `__init__.py` notes the changes.
"""

from __future__ import annotations

from typing import Any, cast

import ibis.expr.datatypes as dt
import ibis.expr.operations as ops

from sverify.ibis_substrait._base import Exprs, register, same_type
from sverify.plan_json import Json, Unsupported, cast_json, literal


def _cast(x: Exprs, op: Any) -> Json:
    if same_type(op.arg.dtype, op.to):
        return x(op.arg)
    return cast_json(x(op.arg), op.to)


def _try_cast(x: Exprs, op: Any) -> Json:
    """`TRY_CAST`: NULL where the cast fails (#58)."""
    if same_type(op.arg.dtype, op.to):
        return x(op.arg)
    return cast_json(x(op.arg), op.to, or_null=True)


#: DuckDB's names of the types of `typeof` (`duckdb-typeof-names`).
_DUCKDB_NAMES: dict[type, str] = {
    dt.Int8: "TINYINT", dt.Int16: "SMALLINT", dt.Int32: "INTEGER", dt.Int64: "BIGINT",
    dt.UInt8: "UTINYINT", dt.UInt16: "USMALLINT", dt.UInt32: "UINTEGER", dt.UInt64: "UBIGINT",
    dt.Float32: "FLOAT", dt.Float64: "DOUBLE", dt.String: "VARCHAR", dt.Boolean: "BOOLEAN",
    dt.Date: "DATE", dt.Time: "TIME", dt.Binary: "BLOB", dt.UUID: "UUID", dt.Interval: "INTERVAL",
}  # fmt: skip
_TIMESTAMPS = {None: "TIMESTAMP", 6: "TIMESTAMP", 0: "TIMESTAMP_S", 3: "TIMESTAMP_MS",
               9: "TIMESTAMP_NS"}  # fmt: skip


def duckdb_type_name(t: dt.DataType) -> str | None:
    """DuckDB's `typeof` of a column of type `t`, or None where it is not known."""
    if type(t) in _DUCKDB_NAMES:
        return _DUCKDB_NAMES[type(t)]
    match t:
        case dt.Decimal(precision=int(p), scale=int(s)):
            return f"DECIMAL({p},{s})"
        case dt.Timestamp(timezone=None, scale=sc) if sc in _TIMESTAMPS:
            return _TIMESTAMPS[sc]
        case dt.Timestamp(scale=None | 6):
            return "TIMESTAMP WITH TIME ZONE"
        case dt.Array(value_type=v):
            name = duckdb_type_name(v)
            return None if name is None else f"{name}[]"
    return None


def _typeof(x: Exprs, op: Any) -> Json:
    """`typeof(column)`: the engine's name of the column's type, a constant
    once the plan is checked (#508). DuckDB's names (`duckdb-typeof-names`).
    An expression's type is the engine's own inference (DuckDB types `1` as
    INTEGER), so only a column's is folded."""
    column: Any = op.arg
    if not isinstance(column, ops.Field):
        raise Unsupported("typeof is only supported of a column")
    t = cast("dt.DataType", column.dtype)
    name = duckdb_type_name(t)
    if name is None:
        raise Unsupported(f"typeof of a {t} column is not supported")
    return literal(name, dt.string)


register(
    {
        ops.Cast: _cast,
        ops.TryCast: _try_cast,
        ops.TypeOf: _typeof,
    }
)
