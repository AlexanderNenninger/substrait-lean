"""The lift's rules of subqueries in expressions: scalar and EXISTS."""

from __future__ import annotations

import ibis.expr.datatypes as dt
import sqlglot.expressions as sge

from sverify.plan_json import Unsupported
from sverify.sql_lift._base import Column, E, Sub, _Lift, register


def _scalar_subquery(lf: _Lift, node: sge.Subquery, sub: Sub, scope: list[Column]) -> E:
    # At most one row, which the checker must prove (an aggregate without
    # groups, LIMIT 1); no row is NULL.
    rel, cols = lf.nested(node.this, scope)
    if len(cols) != 1:
        raise Unsupported("a scalar subquery must return one column")
    return E({"subquery": {"scalar": {"input": rel}}}, cols[0].type.copy(nullable=True))


def _exists(lf: _Lift, node: sge.Exists, sub: Sub, scope: list[Column]) -> E:
    rel, _ = lf.nested(node.this, scope)
    exists_ = {"predicateOp": "PREDICATE_OP_EXISTS", "tuples": rel}
    return E({"subquery": {"setPredicate": exists_}}, dt.boolean)


register(
    {
        sge.Subquery: _scalar_subquery,
        sge.Exists: _exists,
    }
)
