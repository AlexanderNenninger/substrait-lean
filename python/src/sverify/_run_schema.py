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

from dataclasses import dataclass

import pyarrow as pa

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


def declared_columns(plan: object) -> dict[str, list[Declared]]:
    """Each named table of a plan with the columns its `baseSchema` declares
    (top-level columns; a table read twice has one schema)."""
    found: dict[str, list[Declared]] = {}

    def walk(node: object) -> None:
        if isinstance(node, dict):
            if "namedTable" in node and isinstance(node.get("baseSchema"), dict):
                found.setdefault(
                    ".".join(node["namedTable"]["names"]), _columns(node["baseSchema"])
                )
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
) -> tuple[list[str], list[tuple[str, str]]]:
    """How a table fails the schema the plan was verified for, as messages
    (missing columns, types, NULLs in a non-null column), and the integer
    columns, as `(column, declared type)`, whose physical type is wider than
    declared and whose values still have to be range-checked. `data` is None
    for a table the engine reads where it is: its NULLs and values are then
    not counted."""
    expected = pa.schema(
        [
            pa.field(d.name, d.arrow(schema.field(i).type if i >= 0 else pa.null()))
            for d in declared
            for i in [schema.get_field_index(d.name)]
        ]
    )
    out = [str(m) for m in schema_mismatches(expected, schema)]
    wide = []
    for d in declared:
        i = schema.get_field_index(d.name)
        if i < 0:
            continue
        actual = schema.field(i).type
        if d.int_key and pa.types.is_integer(actual) and not _fits(actual, d.int_key):
            wide.append((d.name, d.int_key))
        if data is not None and d.non_null and (n := data.column(i).null_count):
            out.append(f"column {d.name!r} holds {n} NULL(s), the plan reads it as non-null")
    return out, wide
