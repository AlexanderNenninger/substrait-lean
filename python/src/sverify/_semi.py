"""Delta rules for semi and anti joins (#248, stage 2).

Internal: not part of sverify's public API.

A semi join keeps the left rows that have a match on the right, an anti
join those without. For an equi-join (`a.k == b.k AND …`), whether a left
row has a match depends only on its key, through the number of right rows
with that key. So a view that ends in such a join keeps that count per key
beside its rows (`__key0, …, __count`; right rows with a NULL key match
nothing and are not counted), and a batch

1. adds the right side's change to the counts of the keys it touches
   (`contrib`, `merge`), and finds the keys whose count leaves or returns
   to 0;
2. keeps the left side's change where the new counts keep it (`kept`);
3. emits the old left rows whose key's count left 0 and retracts those
   whose count returned to 0, the other way round for an anti join
   (`flipped`: the only read of the left input, for the flipped keys);
4. passes these weighted rows through the filters and projections above
   the join, with their weights (`finish`).

Lean proves that the old output plus this change has the weights of the
new output, for any join condition (`SemiDelta.semi_maintained` in
`SubstraitLean/IncrementalSemi.lean`), and that for an equi-join the count
only depends on the key (`SemiDelta.matchCount_by_key`). This module is
trusted glue: it recognises the shape on the Ibis expression and builds the
plans, which Lean checks as it checks any plan.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any

import ibis
import ibis.expr.operations as ops
import ibis.expr.types as ir

from sverify._linear import WEIGHT_IN
from sverify._retention import _own_tree, _row_local, _under

COUNT = "__count"


@dataclass(frozen=True)
class Semi:
    """The plans that maintain a view that ends in a semi or anti join."""

    anti: bool
    keys: list[str]
    """The state's key columns `__key0, __key1, …`."""
    left_deltas: list[str]
    """The delta plans of the join's left input."""
    right_deltas: list[str]
    """The delta plans of the join's right input."""
    left_names: list[str]
    right_names: list[str]
    init: str
    """The count per key, from the whole right input."""
    contrib: str
    """Each row of `<view>$rin` (the right input's columns, then `__weight`)
    as its key and weight; rows with a NULL key are left out."""
    merge: str
    """The rows of `<view>$old` (counts) and `<view>$contrib`, added up per
    key."""
    kept: str
    """The rows of `<view>$lin` (the left input's columns, then `__weight`)
    the counts in `<view>$state` keep."""
    flipped: str
    """The left input's rows whose key is in `<view>$flip` (the keys, then
    `__weight`), with that weight."""
    finish: str
    """The view's rows of `<view>$rows` (the left input's columns, then
    `__weight`), then their weights."""


def plan(name: str, query: ir.Table | str) -> Semi | str:
    """How to maintain the view `name` of `query` from a count per key, or
    why it cannot be."""
    from sverify.engine import plan_json, written_plan
    from sverify.incremental import NotIncrementalError, delta_plans

    if isinstance(query, str):
        return "the view is SQL"
    found = _split(query.op())
    if isinstance(found, str):
        return found
    node, left, right, lkeys, rkeys, anti = found
    try:
        left_deltas = delta_plans(plan_json(None, left.to_expr()))  # type: ignore[arg-type]
        right_deltas = delta_plans(plan_json(None, right.to_expr()))  # type: ignore[arg-type]
    except NotIncrementalError as e:
        return f"an input of the join has no delta rules ({e})"

    def write(expr: ir.Table) -> str:
        return written_plan(plan_json(None, expr))  # type: ignore[arg-type]

    keys = [f"__key{i}" for i in range(len(lkeys))]

    def on(rel: ops.Relation, exprs: list[ops.Value], rows: ir.Table) -> list[ir.Value]:
        return [e.replace({rel: rows.op()}).to_expr() for e in exprs]  # type: ignore[attr-defined]

    def counted(rows: ir.Table, weight: Any) -> ir.Table:
        ks = on(right, rkeys, rows)
        cols: dict[str, Any] = dict(zip(keys, ks, strict=True))
        cols[COUNT] = weight
        return rows.filter([k.notnull() for k in ks]).select(**cols)

    def added(rows: ir.Table) -> ir.Table:
        return rows.group_by(keys).aggregate(**{COUNT: rows[COUNT].sum()})

    r = right.to_expr()
    init = added(counted(r, ibis.literal(1, "int64")))
    rin = ibis.table({**r.schema(), WEIGHT_IN: "int64"}, name=f"{name}$rin")
    contrib = counted(rin, rin[WEIGHT_IN])
    old = ibis.table(init.schema(), name=f"{name}$old")
    new = ibis.table(init.schema(), name=f"{name}$contrib")
    merge = added(old.union(new, distinct=False))
    state = ibis.table(init.schema(), name=f"{name}$state")
    live = state.filter(state[COUNT] > 0)
    lt = left.to_expr()
    lin = ibis.table({**lt.schema(), WEIGHT_IN: "int64"}, name=f"{name}$lin")
    match = [a == live[k] for a, k in zip(on(left, lkeys, lin), keys, strict=True)]
    kept = lin.anti_join(live, match) if anti else lin.semi_join(live, match)
    flip = ibis.table(
        {**{k: init.schema()[k] for k in keys}, WEIGHT_IN: "int64"}, name=f"{name}$flip"
    )
    pairs = [a == flip[k] for a, k in zip(on(left, lkeys, lt), keys, strict=True)]
    joined = lt.inner_join(flip, pairs)
    flipped = joined.select(*lt.columns, **{WEIGHT_IN: joined[WEIGHT_IN]})
    rows = ibis.table(lin.schema(), name=f"{name}$rows")
    finish = _carry(query.op(), node, rows.op())  # type: ignore[arg-type]
    return Semi(
        anti=anti,
        keys=keys,
        left_deltas=left_deltas,
        right_deltas=right_deltas,
        left_names=list(lt.columns),
        right_names=list(r.columns),
        init=write(init),
        contrib=write(contrib),
        merge=write(merge),
        kept=write(kept),
        flipped=write(flipped),
        finish=write(finish.to_expr()),  # type: ignore[attr-defined]
    )


def _carry(op: ops.Relation, node: ops.Relation, rows: ops.Relation) -> ops.Relation:
    """`op` with `node` replaced by `rows`, whose last column `__weight` the
    filters, sorts and projections between them pass on to the end."""
    if op == node:
        return rows
    parent: Any = op.parent  # type: ignore[attr-defined]
    new = _carry(parent, node, rows)
    sub = {parent: new}
    match op:
        case ops.Filter():
            return op.copy(parent=new, predicates=tuple(p.replace(sub) for p in op.predicates))
        case ops.Sort():
            return op.copy(parent=new, keys=tuple(k.replace(sub) for k in op.keys))
        case ops.Project():
            values = {n: v.replace(sub) for n, v in op.values.items()}
            values[WEIGHT_IN] = ops.Field(new, WEIGHT_IN)
            return ops.Project(new, values)
    raise AssertionError(f"not a filter, sort or projection: {type(op).__name__}")


def _split(
    op: ops.Relation,
) -> tuple[ops.Relation, ops.Relation, ops.Relation, list[ops.Value], list[ops.Value], bool] | str:
    """The semi or anti join a view ends in (under filters, projections and
    sorts of its rows): the join, its left and right inputs, the left and
    right keys it compares, and whether it is an anti join; or why the view
    has none with delta rules."""

    def is_semi(o: ops.Relation) -> bool:
        return (
            isinstance(o, ops.JoinChain) and len(o.rest) == 1 and o.rest[0].how in ("semi", "anti")
        )

    found = _under(op, is_semi)
    if found is None:
        return "not a semi or anti join under filters and projections of its rows"
    node: Any = found[0]
    if WEIGHT_IN in node.schema.names:
        return f"a column is named {WEIGHT_IN}"
    first, link = node.first, node.rest[0]
    if any(not (isinstance(v, ops.Field) and v.rel == first) for v in node.values.values()):
        return "the join's output is not its left input's columns"
    lkeys, rkeys = [], []
    for p in link.predicates:
        if not isinstance(p, ops.Equals):
            return "the join's condition is not equalities of keys"
        a, b = p.left, p.right
        if _row_local([a], first) and _row_local([b], link.table):
            pass
        elif _row_local([b], first) and _row_local([a], link.table):
            a, b = b, a
        else:
            return "the join's condition is not equalities of a left and a right key"
        if any(k.find(ops.Reduction, filter=_own_tree) for k in (a, b)):
            return "a key of the join reads other rows"
        if a.dtype.is_floating() or b.dtype.is_floating():
            return "a key of the join is a double"
        lkeys.append(a)
        rkeys.append(b)
    if not lkeys:
        return "the join has no condition"
    left, right = first.parent, link.table.parent
    lk = [k.replace({first: left}) for k in lkeys]
    rk = [k.replace({link.table: right}) for k in rkeys]
    return node, left, right, lk, rk, link.how == "anti"
