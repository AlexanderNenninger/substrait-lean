"""Delta rules for `COUNT`, `SUM` and `DISTINCT` (#248, stage 1).

Internal: not part of sverify's public API.

`COUNT` and integer `SUM` per group are linear over Z-sets, so a view that
ends in such an aggregate keeps a state beside its rows, one row per group:
the group's keys `k0, k1, …`, its number of input rows (`__count`), and for
each measure the number of values it adds up (`__n0`, …: rows that pass its
`FILTER`, with a non-NULL argument) and their sum (`__s0`, …). `DISTINCT` is
the same with every column a key and no measures: a count per row.

A batch updates the state at the cost of the change, without reading the
view's input:

1. the input's change, from the input's delta plans (`deltas`);
2. each changed row's contribution to its group, its weight times its
   values (`contrib`);
3. the touched groups' old state plus the contributions, added up per group
   (`merge`): the new state of those groups;
4. the view's rows of the touched groups that still have rows, from the new
   state (`finish`). These replace the view's rows of the same keys.

Lean proves that the state of the old input plus the state of the change
finishes to the aggregate (or `DISTINCT`) of the new input, groups appearing
and disappearing included (`LinearAgg.aggregate_maintained` and
`LinearAgg.distinct_maintained` in `SubstraitLean/IncrementalAgg.lean`).
This module is trusted glue: it recognises the shape on the Ibis expression
and builds the plans, which Lean checks as it checks any plan.

The maintained sum is the exact sum of the group's values, and `merge` adds
it up with the engine's `SUM`, which raises when a group's sum leaves 64
bits: the same check a full recompute makes on the data
(`Report.assumed`). `contrib` multiplies each value by its row's weight,
which raises if that product leaves 64 bits.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any

import ibis
import ibis.expr.operations as ops
import ibis.expr.types as ir

from sverify._retention import _aggregate, _own_tree, _row_local, _under

COUNT = "__count"
WEIGHT_IN = "__weight"
"""The weight column of the input's change, as `contrib` reads it."""


@dataclass(frozen=True)
class Linear:
    """The plans that maintain a view from its group state."""

    what: str
    """"aggregate" or "distinct"."""
    keys: list[str]
    """The state's key columns `k0, k1, …`."""
    columns: list[str]
    """The view's columns that hold the keys, in key order."""
    deltas: list[str]
    """The delta plans of the aggregate's (or `DISTINCT`'s) input."""
    input_names: list[str]
    """The input's columns."""
    init: str
    """The state, from the whole input."""
    contrib: str
    """Each row of `<view>$in` (the input's columns, then `__weight`) as its
    contribution to its group's state."""
    merge: str
    """The rows of `<view>$old` (state rows) and `<view>$contrib`
    (contributions), added up per group."""
    finish: str
    """The view's rows of the groups in `<view>$state` with rows."""


def plan(name: str, query: ir.Table | str) -> Linear | str:
    """How to maintain the view `name` of `query` from a group state, or why
    it cannot be."""
    from sverify.engine import plan_json, written_plan
    from sverify.incremental import NotIncremental, delta_plans

    if isinstance(query, str):
        return "the view is SQL"
    found = _split(query.op())
    if isinstance(found, str):
        return found
    node, groups, measures, names, what = found
    if missing := [g for g in groups if g not in names]:
        return f"the view does not output the key {missing[0]} unchanged"
    parent = node.parent.to_expr()
    try:
        deltas = delta_plans(plan_json(None, parent))  # type: ignore[arg-type]
    except NotIncremental as e:
        return f"the {what}'s input has no delta rules ({e})"

    def write(expr: ir.Table) -> str:
        return written_plan(plan_json(None, expr))  # type: ignore[arg-type]

    keys = [f"k{i}" for i in range(len(groups))]
    sums = [COUNT] + [c for i in range(len(measures)) for c in (f"__n{i}", f"__s{i}")]

    def contributions(rows: ir.Table, weight: Any) -> ir.Table:
        def own(v: ops.Value) -> ir.Value:
            return v.replace({node.parent: rows.op()}).to_expr()  # type: ignore[attr-defined]

        cols: dict[str, Any] = {k: own(g) for k, g in zip(keys, groups.values(), strict=True)}
        cols[COUNT] = weight
        for i, (arg, where, is_sum) in enumerate(measures):
            cond: Any = ibis.literal(True) if arg is None else own(arg).notnull()
            if where is not None:
                passes: Any = own(where)
                cond = cond & passes.fill_null(False)
            zero = ibis.literal(0, "int64")
            cols[f"__n{i}"] = ibis.ifelse(cond, weight, zero)
            value = own(arg).cast("int64") * weight if is_sum else zero
            cols[f"__s{i}"] = ibis.ifelse(cond, value, zero)
        return rows.select(**cols)

    def added(rows: ir.Table) -> ir.Table:
        return rows.group_by(keys).aggregate(**{c: rows[c].sum() for c in sums})

    one = ibis.literal(1, "int64")
    init = write(added(contributions(parent, one)))
    changed = ibis.table({**parent.schema(), WEIGHT_IN: "int64"}, name=f"{name}$in")
    contrib = contributions(changed, changed[WEIGHT_IN])
    old = ibis.table(contrib.schema(), name=f"{name}$old")
    new = ibis.table(contrib.schema(), name=f"{name}$contrib")
    merge = write(added(old.union(new, distinct=False)))
    state = ibis.table(contrib.schema(), name=f"{name}$state")
    live = state.filter(state[COUNT] > 0)
    schema = node.schema  # type: ignore[attr-defined]
    out: dict[str, Any] = {}
    for k, g in zip(keys, groups, strict=True):
        out[g] = live[k]
    for i, ((m, fn), _) in enumerate(zip(_metrics(node), measures, strict=True)):
        n = live[f"__n{i}"]
        out[m] = n if fn == "count" else ibis.ifelse(n == 0, ibis.null("int64"), live[f"__s{i}"])
    rel = live.select(**{c: out[c].cast(schema[c]) for c in schema.names})
    hole = ibis.table(schema, name=f"{name}$hole").op()
    view = query.op().replace({node: hole}).replace({hole: rel.op()}).to_expr()  # type: ignore[attr-defined]
    return Linear(
        what=what,
        keys=keys,
        columns=[names[g] for g in groups],
        deltas=deltas,
        input_names=list(parent.columns),
        init=init,
        contrib=write(contrib),
        merge=merge,
        finish=write(view),
    )


def _metrics(node: Any) -> list[tuple[str, str]]:
    """Each measure's column and whether it is a "count" or a "sum"."""
    if isinstance(node, ops.Distinct):
        return []
    return [(m, "sum" if isinstance(v, ops.Sum) else "count") for m, v in node.metrics.items()]


def _split(op: ops.Relation) -> tuple[Any, dict[str, ops.Value], list, dict[str, str], str] | str:
    """The aggregate or `DISTINCT` a view ends in (under filters,
    projections and sorts of its rows), its keys by name, each measure's
    argument (None for `COUNT(*)`) and filter, the view's column for each of
    its columns, and what it is; or why the view has none with delta rules."""
    found = _aggregate(op)
    if found is not None:
        agg, names = found
        if not agg.groups:
            return "the aggregate has no GROUP BY"
        parent = agg.parent
        if not _row_local(list(agg.groups.values()), parent):
            return "a grouping key reads other rows"
        measures = []
        for m, v in agg.metrics.items():
            match v:
                case ops.CountStar(where=where):
                    arg = None
                case ops.Count(arg=arg, where=where):
                    pass
                case ops.Sum(arg=arg, where=where) if arg.dtype.is_integer():
                    pass
                case _:
                    return f"{m} is not COUNT or an integer SUM"
            parts = [p for p in (arg, where) if p is not None]
            if not _row_local(parts, parent) or any(
                p.find(ops.Reduction, filter=_own_tree) for p in parts
            ):
                return f"{m} reads other rows"
            measures.append((arg, where, isinstance(v, ops.Sum)))
        return agg, dict(agg.groups), measures, names, "aggregate"
    found = _under(op, lambda o: isinstance(o, ops.Distinct))
    if found is None:
        return "not an aggregate or DISTINCT under filters and projections of its rows"
    node, names = found
    parent = node.parent  # type: ignore[attr-defined]
    groups = {c: ops.Field(parent, c) for c in parent.schema.names}
    return node, groups, [], names, "distinct"  # type: ignore[return-value]
