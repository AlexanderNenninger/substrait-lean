"""The schema a plan was verified for, checked against the tables of a run
(#1540).

Internal: not part of sverify's public API.

The checker proved the plan over the schema in each `baseSchema`: its types
and its nullability. A run on a table that differs is a run of something
else, so `Report.check_inputs` refuses it before an engine reads a row. One
check serves every engine; an engine's reader then only converts.

What is compared:

* a missing column, and a type the reader would change (`schema_mismatches`);
* a NULL in a column the plan reads as non-null. The data decides
  (`null_count`), not the table's `nullable` flag: `Connection.put` tables
  are nullable by default;
* an integer column whose physical type is wider than the declared one (D46):
  its values must lie in the declared range, checked once, as a condition
  the engine counts (`int_range`).
"""

from __future__ import annotations

from collections.abc import Mapping
from dataclasses import dataclass

import pyarrow as pa
import pyarrow.compute as pc

from sverify._plan_read import type_kind
from sverify._scan import schema_mismatches

_BITS = {"i8": 8, "i16": 16, "i32": 32, "i64": 64}
_FLOATS = {"fp32": pa.float32(), "fp64": pa.float64()}


@dataclass(frozen=True)
class Declared:
    """A column of a plan's `baseSchema`."""

    name: str
    kind: tuple[str, object] | None
    non_null: bool

    @property
    def int_key(self) -> str | None:
        """`i8` to `i64` for an integer column."""
        return str(self.kind[1]) if self.kind and self.kind[0] == "int" else None

    def arrow(self, actual: pa.DataType) -> pa.DataType:
        """The Arrow type the plan reads. An integer, or a type that is not
        compared, is `actual` (ranges are `int_range`'s)."""
        if self.kind is None:
            return actual
        kind, payload = self.kind
        if kind == "int":
            return actual if pa.types.is_integer(actual) else pa.int64()
        if kind == "float":
            return _FLOATS[str(payload)]
        if kind == "str":
            return pa.string()
        if kind == "bool":
            return pa.bool_()
        if kind == "date":
            return pa.date32()
        if kind == "decimal" and isinstance(payload, tuple):
            return pa.decimal128(*payload)
        return actual


def declared_columns(plan: object) -> dict[str, list[list[Declared]]]:
    """Each named table of a plan with the columns each distinct `baseSchema`
    of its reads declares (top-level columns): a table read twice with two
    declarations is checked against both."""
    found: dict[str, list[list[Declared]]] = {}

    def walk(node: object) -> None:
        if isinstance(node, dict):
            if "namedTable" in node and isinstance(node.get("baseSchema"), dict):
                cols = _columns(node["baseSchema"])
                seen = found.setdefault(".".join(node["namedTable"]["names"]), [])
                if cols not in seen:
                    seen.append(cols)
            for v in node.values():
                walk(v)
        elif isinstance(node, list):
            for v in node:
                walk(v)

    walk(plan)
    return found


def _columns(base: dict) -> list[Declared]:
    names = base.get("names", [])
    types = base.get("struct", {}).get("types", [])
    out, i = [], 0
    for t in types:
        if i >= len(names):
            break
        body = next(iter(t.values()), {}) if isinstance(t, dict) and t else {}
        required = isinstance(body, dict) and body.get("nullability") == "NULLABILITY_REQUIRED"
        out.append(Declared(names[i], type_kind(t), required))
        i += 1 + _nested_names(t)
    return out


def _nested_names(t: object) -> int:
    """The field names a type adds to `names` after its own (depth first)."""
    match type_kind(t):
        case ("struct", types):
            return sum(1 + _nested_names(c) for c in types)
        case ("list", elem):
            return _nested_names(elem)
    return 0


def int_range(key: str) -> tuple[int, int]:
    """The values of the integer type `key` (`i8` to `i64`)."""
    n = _BITS[key]
    return -(2 ** (n - 1)), 2 ** (n - 1) - 1


def int_name(key: str) -> str:
    """The Arrow name of the integer type `key` (`i32`: `int32`)."""
    return f"int{_BITS[key]}"


def _fits(actual: pa.DataType, key: str) -> bool:
    """Whether every value of the integer type `actual` is of type `key`."""
    n = actual.bit_width
    lo, hi = (
        (0, 2**n - 1)
        if pa.types.is_unsigned_integer(actual)
        else (-(2 ** (n - 1)), 2 ** (n - 1) - 1)
    )
    d_lo, d_hi = int_range(key)
    return d_lo <= lo and hi <= d_hi


def problems(
    declared: list[Declared], schema: pa.Schema, data: pa.Table | None
) -> tuple[list[str], list[tuple[str, str | None]]]:
    """How a table fails the schema the plan was verified for, as messages
    (missing columns, types, NULLs in a non-null column, values outside a
    declared integer width), and the columns the caller must check on the
    engine, as `(column, declared integer type)` for a range and `(column,
    None)` for a NULL count. `data` is None for a table the engine reads where
    it is: every non-null column and every column of a wider physical type is
    returned for the engine to check; on an Arrow table both are checked here,
    in one pass."""
    expected = pa.schema(
        [
            pa.field(d.name, d.arrow(schema.field(i).type if i >= 0 else pa.null()))
            for d in declared
            for i in [schema.get_field_index(d.name)]
        ]
    )
    out = [str(m) for m in schema_mismatches(expected, schema)]
    on_engine: list[tuple[str, str | None]] = []
    for d in declared:
        i = schema.get_field_index(d.name)
        if i < 0:
            continue
        actual = schema.field(i).type
        if d.int_key and pa.types.is_integer(actual) and not _fits(actual, d.int_key):
            if data is None:
                on_engine.append((d.name, d.int_key))
            elif found := outside(data.column(i), *int_range(d.int_key)):
                n, example = found
                out.append(range_message(d.name, d.int_key, n, example))
        if d.non_null:
            if data is None and schema.field(i).nullable:
                on_engine.append((d.name, None))
            elif data is not None and (n := data.column(i).null_count):
                out.append(null_message(d.name, n))
    return out, on_engine


def null_message(column: str, count: int) -> str:
    """The refusal for `count` NULLs in a column the plan reads as non-null."""
    return f"column {column!r} holds {count} NULL(s), the plan reads it as non-null"


def range_message(column: str, key: str, count: int, example: object) -> str:
    """The refusal for `count` values of an integer column outside its declared
    type, `example` one of them."""
    lo, hi = int_range(key)
    return (
        f"column {column!r} is declared {int_name(key)} ({lo} to {hi}) and "
        f"{count} value(s) lie outside it, e.g. {example}"
    )


def outside(column: pa.ChunkedArray, lo: int, hi: int) -> tuple[int, object] | None:
    """The count of values of an integer column outside `[lo, hi]` and one of
    them, or None if all lie inside (NULLs do). One native pass for the
    minimum and maximum, a second only on a failure."""
    mm = pc.call_function("min_max", [column]).as_py()
    if mm["min"] is None or (lo <= mm["min"] and mm["max"] <= hi):
        return None
    high = pc.call_function("greater", [column, pa.scalar(hi, column.type)])
    if pa.types.is_unsigned_integer(column.type):
        bad = high
    else:
        bad = pc.call_function(
            "or", [pc.call_function("less", [column, pa.scalar(lo, column.type)]), high]
        )
    count = pc.call_function("sum", [bad]).as_py()
    return count, column.filter(bad)[0].as_py()


def table_problems(plan: object, tables: Mapping[str, pa.Table]) -> list[str]:
    """How the Arrow `tables` fail the schemas `plan` was verified for, one
    message per table (`table t differs from the schema the plan was verified
    for: ...`), for the callers that run a plan over tables they hold:
    shards, a pipeline's batches."""
    out = []
    for t, schemas in declared_columns(plan).items():
        if t not in tables:
            continue
        found = [
            m for declared in schemas for m in problems(declared, tables[t].schema, tables[t])[0]
        ]
        if found:
            out.append(
                f"table {t} differs from the schema the plan was verified for: " + "; ".join(found)
            )
    return out
