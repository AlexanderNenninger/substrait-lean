"""Cast rules of the Ibis producer: `CAST`, `TRY_CAST` and `typeof`.

Part of the Ibis producer (`sverify.ibis_substrait`), derived from
ibis-substrait (Apache License 2.0); `__init__.py` notes the changes.
"""

from __future__ import annotations

from typing import Any, cast

import ibis.expr.datatypes as dt
import ibis.expr.operations as ops

from sverify.ibis_substrait._base import Exprs, register, same_type
from sverify.plan_json import Json, Unsupported, call, cast_json, literal


def _from_varchar(x: Exprs, op: Any, try_: bool, to: dt.DataType) -> Json | None:
    """A cast of a string (#806): the black box of its target, DuckDB's
    rules, as the SQL lift reads one (`sql_lift/casts.py`); a narrower
    integer is the BIGINT cast down. None for the other targets."""
    if not op.arg.dtype.is_string():
        return None
    if isinstance(op.arg, ops.Literal) and not try_:
        # A constant: Lean folds it, as it did (`DATE '1998-12-01'` in TPC-H).
        return None
    if to.is_decimal():
        raise Unsupported(
            f"a cast of a string to {to} is not supported yet (#27)", construct="CAST"
        )
    for accepts, name, via in (
        (to.is_integer, "bigint", dt.int64),
        (to.is_float64, "double", dt.float64),
        (to.is_boolean, "boolean", dt.boolean),
        (to.is_date, "date", dt.date),
        (lambda: isinstance(to, dt.Timestamp) and to.timezone is None, "timestamp", dt.timestamp),
    ):
        if accepts():
            j = call(f"{'try_' if try_ else ''}varchar_{name}", [x(op.arg)])
            return j if same_type(via, to) else cast_json(j, to, or_null=try_)
    return None


def _from_seconds(x: Exprs, op: Any, try_: bool, to: dt.DataType) -> Json | None:
    """A cast of an integer to a timestamp: Ibis reads the integer as seconds
    since the epoch (`pd.to_datetime(unit="s")` in its tests, DuckDB's
    `to_timestamp`), where Substrait's cast reads microseconds. So it is
    `as_timestamp("s")` (#860). None for the other casts."""
    if not (op.arg.dtype.is_integer() and isinstance(to, dt.Timestamp)):
        return None
    if try_ or to.timezone is not None or to.scale not in (None, 6):
        raise Unsupported(
            f"a {'try_' if try_ else ''}cast of an integer to {op.to} is not supported; "
            'write .as_timestamp("s") for seconds since the epoch',
            construct="TRY_CAST" if try_ else "CAST",
        )
    return cast_json(call("multiply", [x(op.arg, dt.int64), literal(10**6, dt.int64)]), to)


def _cast_to(x: Exprs, op: Any, try_: bool) -> Json:
    """A cast. To a second or millisecond timestamp it converts to the target's
    microsecond type first (a time zone included, D53) and then floors with
    `date_trunc`, whatever the source: the reference's timestamps count
    microseconds (D61)."""
    to, narrow = op.to, None
    if isinstance(to, dt.Timestamp) and to.scale in (0, 3):
        narrow = "second" if to.scale == 0 else "millisecond"
        to = to.copy(scale=6)
    if same_type(op.arg.dtype, to):
        j = x(op.arg)
    elif from_string := _from_varchar(x, op, try_, to):
        j = from_string
    elif from_seconds := _from_seconds(x, op, try_, to):
        j = from_seconds
    else:
        j = cast_json(x(op.arg), to, or_null=try_)
    return j if narrow is None else call("date_trunc", [literal(narrow, dt.string), j])


def _cast(x: Exprs, op: Any) -> Json:
    return _cast_to(x, op, False)


def _try_cast(x: Exprs, op: Any) -> Json:
    """`TRY_CAST`: NULL where the cast fails (#58)."""
    return _cast_to(x, op, True)


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
        raise Unsupported(
            "typeof is only supported of a column; select the expression as a column first",
            construct="function typeof",
        )
    t = cast("dt.DataType", column.dtype)
    # A second or millisecond column is read as microseconds (D61): its type
    # in the run is TIMESTAMP, which the declared type's name does not say.
    name = None if isinstance(t, dt.Timestamp) and t.scale in (0, 3) else duckdb_type_name(t)
    if name is None:
        raise Unsupported(
            f"typeof of a {t} column is not supported; write the type's name as a constant",
            construct="function typeof",
        )
    return literal(name, dt.string)


register(
    {
        ops.Cast: _cast,
        ops.TryCast: _try_cast,
        ops.TypeOf: _typeof,
    }
)
