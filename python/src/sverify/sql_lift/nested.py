"""The lift's rules of lists: list literals and indexing."""

from __future__ import annotations

import json
from typing import Any

import ibis.expr.datatypes as dt
import sqlglot.expressions as sge

from sverify.plan_json import Unsupported, literal
from sverify.plan_json import same_type as _same
from sverify.sql_lift._base import (
    _KNOWN,
    PARSE_REWRITES,
    Column,
    E,
    Sub,
    _fn,
    _Lift,
    _shown,
    register,
)


def _array(lf: _Lift, node: sge.Array, sub: Sub, scope: list[Column]) -> E:
    """A list `[a, b, …]` (#348) at its elements' common type as DuckDB types
    it (`[1, 2.5]` is a `DECIMAL(11,1)[]`): a literal of constants, else
    (#812) `list_prepend(a, list_prepend(b, []))`."""
    es = [sub(e) for e in node.expressions]
    if not es:
        raise Unsupported("an empty list literal has no element type; cast it, e.g. []::INT[]")
    t = lf.common(es, "a list literal")
    if t.is_decimal():
        # The model holds a decimal unscaled; inside a list nothing rescales it.
        raise Unsupported(f"a list of {t} is not supported yet")
    lt = dt.Array(value_type=t)
    if all(e.constant for e in es):
        values = [lf.to(e, t).value for e in es]
        return E(literal(values, lt), lt, values)
    if t.is_floating() and not any("selection" in json.dumps(e.json) for e in es):
        # Lean reads a double constant as its code, of no kind of its own: the
        # list's elements would be integers to it (`Expr.kind`), as a cast
        # `'nan'::DOUBLE` the lift does not fold is (`types/float/nested_nan`).
        raise Unsupported(
            f"{_shown(node)}: a list of DOUBLE constants that are not literals is not "
            "supported yet; write them as numbers"
        )
    out = literal([], lt)
    for e in reversed(es):
        out = _fn("list_prepend", [lf.to(e, t).json, out], lt)
    return E(out, lt)


def _list(lf: _Lift, x: E, what: str) -> Any:
    """The list type of `x`, which `what` needs."""
    if not x.type.is_array():
        raise Unsupported(f"{what} of a {x.type} is not supported")
    return x.type


def _len(lf: _Lift, node: sge.ArraySize, sub: Sub, scope: list[Column]) -> E:
    """`len(l)`, `array_length(l)`: the number of elements, NULL ones
    included (`UnFn.cardinality`, #812)."""
    if node.expression is not None:
        raise Unsupported(f"{_shown(node)}: array_length of a dimension is not supported")
    x = sub(node.this)
    _list(lf, x, "array_length")
    return E(_fn("cardinality", [x.json], dt.int64), dt.int64)


def _needle(lf: _Lift, node: sge.Expression, lst: E, x: E, name: str) -> tuple[E, Any]:
    """The value looked for in a list, at the list's element type. Doubles
    and nested values compare otherwise in DuckDB (`-0.0 = 0.0`, NaN = NaN),
    so they are refused."""
    elem = _list(lf, lst, name).value_type
    if elem.is_floating() or elem.is_nested() or elem.is_decimal():
        raise Unsupported(f"{_shown(node)}: {name} of a list of {elem} is not supported yet")
    if x.type.is_null():
        return E(literal(None, elem), elem, None), elem
    t = lf.common([E(lst.json, elem), x], name)
    if not _same(t, elem):
        raise Unsupported(f"{_shown(node)}: {name} of a {x.type} in a list of {elem}")
    return lf.to(x, elem), elem


def _contains(lf: _Lift, node: sge.ArrayContains, sub: Sub, scope: list[Column]) -> E:
    """`list_contains(l, x)` (`list_has`, `array_contains`): whether an
    element equals `x`; NULL for a NULL list or `x` (`BinFn.listContains`,
    #812)."""
    lst = sub(node.this)
    x, _ = _needle(lf, node, lst, sub(node.expression), "list_contains")
    return E(_fn("list_contains", [lst.json, x.json], dt.boolean), dt.boolean)


def _concat(lf: _Lift, node: sge.ArrayConcat, sub: Sub, scope: list[Column]) -> E:
    """`list_concat(l, m, …)` (`array_cat`, `||` of lists): a NULL list is
    empty (`BinFn.listConcat`, #812)."""
    es = [sub(e) for e in [node.this, *node.expressions]]
    for e in es:
        if not (e.type.is_array() or e.type.is_null()):
            raise Unsupported(f"{_shown(node)}: list_concat of a {e.type} is not supported")
    lists = [e for e in es if e.type.is_array()]
    if not lists:
        raise Unsupported(f"{_shown(node)} of NULLs has no element type; cast them")
    t = lf.common([E(e.json, e.type.value_type) for e in lists], "list_concat")
    if t.is_decimal():
        raise Unsupported(f"a list of {t} is not supported yet")
    lt = dt.Array(value_type=t)
    out = lf.to(es[0], lt).json if es[0].type.is_array() else literal(None, lt)
    for e in es[1:]:
        right = lf.to(e, lt).json if e.type.is_array() else literal(None, lt)
        out = _fn("list_concat", [out, right], lt)
    return E(out, lt)


class ListPosition(sge.Expression, sge.Func):
    """DuckDB's `list_position(l, x)`, which SQLGlot reads as an unknown
    function (`_rewrite` gives it this node)."""

    arg_types = {"this": True, "expression": True}
    _sql_names = ["LIST_POSITION"]


def _position(
    lf: _Lift, node: ListPosition | sge.ArrayPosition, sub: Sub, scope: list[Column]
) -> E:
    """`list_position(l, x)` (`list_indexof`, `array_position`): the
    position from 1 of the first element equal to `x`, a NULL `x` finding a
    NULL element; NULL when none is (`BinFn.listPosition`, #812). DuckDB
    types it an INTEGER."""
    lst = sub(node.this)
    x, _ = _needle(lf, node, lst, sub(node.expression), "list_position")
    return E(_fn("list_position", [lst.json, x.json], dt.int32), dt.int32)


def _bracket(lf: _Lift, node: sge.Bracket, sub: Sub, scope: list[Column]) -> E:
    """`l[i]` of a list (#348): DuckDB counts from 1, and from the end for a
    negative `i`; `l[0]` and an index out of range are NULL. SQLGlot has
    already subtracted 1 from a constant index (`l[-1]` reads as -2), which is
    added back here. Slices are not supported yet."""
    x = sub(node.this)
    if not x.type.is_array():
        raise Unsupported(f"{_shown(node)}: indexing a {x.type} is not supported yet")
    if len(node.expressions) != 1 or isinstance(node.expressions[0], sge.Slice):
        raise Unsupported(f"{_shown(node)}: list slices are not supported yet")
    k = sub(node.expressions[0])
    if not (k.constant and isinstance(k.value, int) and not isinstance(k.value, bool)):
        raise Unsupported(f"{_shown(node)}: a list element needs a constant index")
    d = k.value + 1
    elem = x.type.value_type
    if d == 0:
        return E(literal(None, elem), elem, None)
    offset = d - 1 if d > 0 else d
    ref = {
        "selection": {"directReference": {"listElement": {"offset": offset}}, "expression": x.json}
    }
    return E(ref, elem)


def _index(k: sge.Expression) -> sge.Expression:
    """A constant index as SQLGlot reads one inside brackets: less 1."""
    if isinstance(k, sge.Literal) and not k.is_string and k.this.lstrip("-").isdigit():
        return sge.Literal.number(int(k.this) - 1)
    if isinstance(k, sge.Neg) and isinstance(k.this, sge.Literal) and k.this.this.isdigit():
        return sge.Literal.number(-int(k.this.this) - 1)
    return k


def _rewrite(tree: sge.Expr) -> sge.Expr:
    """DuckDB's other names of indexing and of list literals (#327):
    `list_extract(l, i)`, `list_element` and `array_extract` are `l[i]`, and
    `array_value(a, …)` is `[a, …]`."""

    def node(n: sge.Expr) -> sge.Expr:
        if type(n) is not sge.Anonymous:
            return n
        name = n.name.lower()
        if name in ("list_extract", "list_element", "array_extract") and len(n.expressions) == 2:
            lst, k = (e.transform(node, copy=False) for e in n.expressions)
            return sge.Bracket(this=lst, expressions=[_index(k)])
        if name in ("list_position", "list_indexof", "array_indexof"):
            if len(n.expressions) != 2:
                raise Unsupported(f"{_shown(n)} takes a list and a value")
            lst, x = (e.transform(node, copy=False) for e in n.expressions)
            return ListPosition(this=lst, expression=x)
        if name == "array_value":
            if any(
                isinstance(e, sge.Anonymous) and e.name.lower() == "array_value"
                for e in n.expressions
            ):
                # Fixed-size arrays, which raise where their sizes differ; the
                # model's lists do not.
                raise Unsupported(
                    "array_value of arrays is not supported: DuckDB's fixed-size arrays must "
                    "agree in size, which the model's lists do not (#327)"
                )
            return sge.Array(expressions=[e.transform(node, copy=False) for e in n.expressions])
        return n

    return tree.transform(node, copy=False)


_KNOWN.update({"list_extract", "list_element", "array_extract", "array_value"})
PARSE_REWRITES.append(_rewrite)

register(
    {
        sge.Array: _array,
        sge.Bracket: _bracket,
        sge.ArraySize: _len,
        sge.ArrayContains: _contains,
        sge.ArrayConcat: _concat,
        ListPosition: _position,
        sge.ArrayPosition: _position,
    }
)
