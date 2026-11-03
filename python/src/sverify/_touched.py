"""Touched-group recompute: an aggregate without delta rules, maintained at
the cost of the groups a batch touches.

Internal: not part of sverify's public API.

A view that ends in an aggregate (under filters, projections and sorts of
its output rows that read only their own row, and keep the group keys) and
whose input has delta rules is maintained in three steps per batch:

1. the input's change, from the input's delta plans;
2. the group keys of the rows it inserts or deletes (`keys`);
3. the view over the new input rows with those keys, a semi-join on the
   keys with NULLs equal (`recompute`). These rows replace the view's rows
   of the same keys.

Groups are independent, so this is the full recomputation for any measure
(`TouchedGroups.touched_sound` and `TouchedGroups.touched_eval` in
`SubstraitLean/TouchedGroups.lean`). Filters and projections over the
aggregate act on each output row, and keep the group keys, so they keep the
split. This module is trusted glue: it recognises the shape on the Ibis
expression and builds the three plans, which Lean checks as it checks any
plan.
"""

from __future__ import annotations

from dataclasses import dataclass

import ibis
import ibis.expr.types as ir

from sverify._retention import _aggregate, _row_local


@dataclass(frozen=True)
class Touched:
    """The plans that maintain a view by touched groups."""

    columns: list[str]
    """The view's columns that hold the group keys, in key order."""
    deltas: list[str]
    """The delta plans of the aggregate's input."""
    input_names: list[str]
    """The input's columns."""
    keys: str
    """The distinct group keys `k0, k1, …` of the rows of table `<view>$in`
    (the input's columns)."""
    recompute: str
    """The view over the input rows whose keys are rows of `<view>$keys`."""


def plan(name: str, query: ir.Table | str) -> Touched | str:
    """How to maintain the view `name` of `query` by touched groups, or why
    it cannot be."""
    from sverify.engine import plan_json, written_plan
    from sverify.incremental import NotIncremental, delta_plans

    if isinstance(query, str):
        return "the view is SQL; touched groups need an Ibis expression"
    found = _aggregate(query.op())
    if found is None:
        return "not an aggregate under filters and projections of its rows"
    agg, names = found
    if not agg.groups:
        return "the aggregate has no GROUP BY"
    if not _row_local(list(agg.groups.values()), agg.parent):
        return "a grouping key reads other rows"
    if missing := [g for g in agg.groups if g not in names]:
        return f"the view does not output the group key {missing[0]} unchanged"
    parent = agg.parent.to_expr()
    try:
        deltas = delta_plans(plan_json(None, parent))  # type: ignore[arg-type]
    except NotIncremental as e:
        return f"the aggregate's input has no delta rules ({e})"
    groups = list(agg.groups.values())
    rows = ibis.table(parent.schema(), name=f"{name}$in")
    keys = rows.select(
        **{f"k{i}": g.replace({agg.parent: rows.op()}).to_expr() for i, g in enumerate(groups)}
    ).distinct()
    touched = ibis.table(keys.schema(), name=f"{name}$keys")
    on = [g.to_expr().identical_to(touched[f"k{i}"]) for i, g in enumerate(groups)]  # type: ignore[union-attr]
    narrowed = parent.semi_join(touched, on)
    # Through a placeholder: `narrowed` holds the input itself.
    hole = ibis.table(parent.schema(), name=f"{name}$hole").op()
    recompute = query.op().replace({agg.parent: hole}).replace({hole: narrowed.op()})
    return Touched(
        columns=[names[g] for g in agg.groups],
        deltas=deltas,
        input_names=list(parent.columns),
        keys=written_plan(plan_json(None, keys)),  # type: ignore[arg-type]
        recompute=written_plan(plan_json(None, recompute.to_expr())),  # type: ignore[arg-type,attr-defined]
    )
