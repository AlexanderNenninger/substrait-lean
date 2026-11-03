"""The lift's rules of lists: list literals and indexing."""

from __future__ import annotations

import ibis.expr.datatypes as dt
import sqlglot.expressions as sge

from sverify.plan_json import Unsupported, literal
from sverify.sql_lift._base import Column, E, Sub, _Lift, _shown, register


def _array(lf: _Lift, node: sge.Array, sub: Sub, scope: list[Column]) -> E:
    """A list literal `[a, b, …]` (#348) of constants, at their common type as
    DuckDB types it (`[1, 2.5]` is a `DECIMAL(11,1)[]`). The model has no list
    of computed elements."""
    es = [sub(e) for e in node.expressions]
    if not es:
        raise Unsupported("an empty list literal has no element type; cast it, e.g. []::INT[]")
    if not all(e.constant for e in es):
        raise Unsupported("a list of computed elements is not supported yet; only constants")
    t = lf.common(es, "a list literal")
    if t.is_decimal():
        # The model holds a decimal unscaled; inside a list nothing rescales it.
        raise Unsupported(f"a list of {t} is not supported yet")
    values = [lf.to(e, t).value for e in es]
    lt = dt.Array(value_type=t)
    return E(literal(values, lt), lt, values)


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


register(
    {
        sge.Array: _array,
        sge.Bracket: _bracket,
    }
)
