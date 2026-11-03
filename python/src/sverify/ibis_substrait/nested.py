"""Nested-value rules of the Ibis producer: lists, structs, lambdas and UNNEST.

Part of the Ibis producer (`sverify.ibis_substrait`), derived from
ibis-substrait (Apache License 2.0); `__init__.py` notes the changes.
"""

from __future__ import annotations

from collections.abc import Callable
from typing import Any

import ibis.expr.operations as ops

from sverify.ibis_substrait._base import (
    Exprs,
    _common,
    _unary,
    register,
    register_rels,
    rel,
    same_type,
)
from sverify.plan_json import Json, Unsupported, call, cast_json, literal, type_json


def reference(segment: Json, expr: Json) -> Json:
    """A reference with `segment` into the value of `expr` (#94)."""
    return {"selection": {"directReference": segment, "expression": expr}}


#: The parameter of the innermost lambda.
PARAM = {
    "selection": {"directReference": {"structField": {"field": 0}}, "lambdaParameterReference": {}}
}


class _Body(Exprs):
    """A lambda's body. The model's lambdas are closed (#94): the body reads
    its parameter and constants, not the table's columns or an outer lambda's
    parameter."""

    def __init__(self, param: Any):
        super().__init__({})
        self.param = param

    def translate(self, op: Any) -> Json:
        if isinstance(op, ops.Argument):
            if op != self.param:
                raise Unsupported(
                    "a lambda body that reads an outer lambda's parameter is not supported yet"
                )
            return PARAM
        if isinstance(op, ops.Field):
            raise Unsupported("a lambda body that reads the table's columns is not supported yet")
        return super().translate(op)


def lambda_json(param_type: Any, body: Json) -> Json:
    """A lambda of one parameter of type `param_type`."""
    params = {"types": [type_json(param_type)], "nullability": "NULLABILITY_REQUIRED"}
    return {"lambda": {"parameters": params, "body": body}}


def _higher_order(name: str) -> Callable[[Exprs, Any], Json]:
    """`array.map(f)` and `array.filter(f)`: `transform` and `filter` with
    `f` as a lambda (#94)."""

    def rule(x: Exprs, op: Any) -> Json:
        if op.index is not None:
            raise Unsupported("lambdas that take the element's index are not supported")
        body = _Body(op.param)(op.body)
        return call(name, [x(op.arg), lambda_json(op.arg.dtype.value_type, body)])

    return rule


def _array_contains(x: Exprs, op: Any) -> Json:
    # Ibis's `contains` is true where an element IS NOT DISTINCT FROM the
    # value, as Polars has it: `any_match` with that predicate (#94). The
    # lambda is closed, so the value is a constant.
    if not isinstance(op.other, ops.Literal):
        raise Unsupported(
            "contains needs a constant value (a lambda reading a column is not supported yet)"
        )
    elem = op.arg.dtype.value_type
    t = _common(elem, op.other.dtype)
    param = PARAM if same_type(elem, t) or elem.is_null() else cast_json(PARAM, t)
    body = call("is_not_distinct_from", [param, literal(op.other.value, t)])
    return call("any_match", [x(op.arg), lambda_json(elem, body)])


def _struct_field(x: Exprs, op: Any) -> Json:
    # A struct is positional in the model: the field by its ordinal.
    i = list(op.arg.dtype.names).index(op.field)
    return reference({"structField": {"field": i}}, x(op.arg))


def _array_index(x: Exprs, op: Any) -> Json:
    # Ibis's `a[i]` is zero-based, negative from the end and NULL out of
    # range, as Substrait's `ListElement` is; its offset is a constant.
    if not isinstance(op.index, ops.Literal) or op.index.value is None:
        raise Unsupported("a list element needs a constant index")
    return reference({"listElement": {"offset": int(op.index.value)}}, x(op.arg))


def _table_unnest(op: Any) -> Json:
    # No standard Substrait relation: an `ExtensionSingleRel` with our own
    # detail (`docs/nested-values.md`). The column keeps its place.
    if op.offset is not None:
        raise Unsupported("unnest(offset=) is not supported")
    if op.keep_empty:
        raise Unsupported("unnest(keep_empty=True) is not supported")
    if op.column_name != op.column.name or not isinstance(op.column, ops.Field):
        raise Unsupported("unnest must unnest a column in place")
    col = list(op.parent.schema.names).index(op.column.name)
    detail = {"@type": "type.googleapis.com/sverify.Unnest", "column": col}
    return {"extensionSingle": {"input": rel(op.parent), "detail": detail}}


register(
    {
        ops.StructField: _struct_field,
        ops.ArrayIndex: _array_index,
        ops.ArrayLength: _unary("cardinality"),
        ops.ArrayContains: _array_contains,
        ops.ArrayMap: _higher_order("transform"),
        ops.ArrayFilter: _higher_order("filter"),
    }
)


register_rels(
    {
        ops.TableUnnest: _table_unnest,
    }
)
