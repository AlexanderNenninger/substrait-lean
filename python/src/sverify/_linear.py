"""Delta rules for `COUNT`, `SUM`, `AVG`, `MIN`, `MAX` and `DISTINCT`
(#248, stages 1 and 2).

Internal: not part of sverify's public API.

`COUNT` and exact `SUM` per group are linear over Z-sets, so a view that
ends in such an aggregate keeps a state beside its rows, one row per group:
the group's keys `k0, k1, …`, its number of input rows (`__count`), and for
each measure the number of values it adds up (`__n0`, …: rows that pass its
`FILTER`, with a non-NULL argument) and their sum (`__s0`, …). `DISTINCT` is
the same with every column a key and no measures: a count per row. A
`DECIMAL` `AVG` keeps the sum and the count of its values, and divides them
when it finishes, as the model computes it (`Parse.decimalAvgs`). A `MIN`
or `MAX` keeps the extreme of its values in `__s`. A `SUM`, `AVG`, `VAR`,
`STDDEV`, `COVAR` or `CORR` of doubles keeps its exact moments beside the
state (`sverify._exact_sum`, `LinearAgg.no_drift`): `contrib` gives each
changed row's value (a pair's second in `__t`), and `__s` is the value
finished from them.

A batch updates the state at the cost of the change, without reading the
view's input:

1. the input's change, from the input's delta plans (`deltas`);
2. each changed row's contribution to its group, its weight times its
   values, or for `MIN` and `MAX` the value itself (`contrib`);
3. the touched groups' old state plus the contributions, added up per group
   (`merge`; `MIN` and `MAX` take the extreme): the new state of those
   groups;
4. with a `MIN` or `MAX`, the groups the change deletes from are recomputed
   on the new input instead (`regroup`): a deleted extreme leaves no trace
   of the next one in the state;
5. the view's rows of the touched groups that still have rows, from the new
   state (`finish`). These replace the view's rows of the same keys.

Lean proves that the state of the old input plus the state of the change
finishes to the aggregate (or `DISTINCT`) of the new input, groups appearing
and disappearing included (`LinearAgg.aggregate_maintained` and
`LinearAgg.distinct_maintained` in `SubstraitLean/IncrementalAgg.lean`), and
with `MIN` and `MAX`, that merging the groups a batch only inserts into and
recomputing the others gives the aggregate too
(`ExtremeAgg.extreme_maintained` in `SubstraitLean/IncrementalMinMax.lean`).
A projection that finishes an `AVG` keeps that (`ExtremeAgg.map_maintained`).
This module is trusted glue: it recognises the shape on the Ibis expression
and builds the plans, which Lean checks as it checks any plan.

The maintained sum is the exact sum of the group's values, and `merge` adds
it up with the engine's `SUM`, which raises when a group's sum leaves 64
bits (38 digits for decimals): the same check a full recompute makes on the
data (`Report.assumed`). `contrib` multiplies each value by its row's
weight, which raises if that product leaves 64 bits.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any

import ibis
import ibis.expr.datatypes as dt
import ibis.expr.operations as ops
import ibis.expr.types as ir

from sverify import _decimals, _exact_sum
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
    regroup: str | None = None
    """With a `MIN` or `MAX`: the state of the groups in `<view>$keys`, from
    the whole (new) input. A batch that deletes from a group recomputes its
    state with it; the others merge."""
    exact: tuple[_exact_sum.Exact, ...] = ()
    """The `SUM`s, `AVG`s and statistical aggregates of doubles: their exact
    moments are kept beside the state (`sverify._exact_sum`), and their
    `__s` is the finished value."""
    values: str | None = None
    """With an exact measure: each input row's contribution, unaggregated,
    which `sverify._exact_sum.fold` adds up into the initial state."""


#: Why a view has no state per group when it is not one this module keeps:
#: the checker's refusal of its delta rules says more (`IncrementalView`).
SQL = "the view is SQL"
NOT_AGGREGATE = "not an aggregate or DISTINCT under filters and projections of its rows"


def plan(name: str, query: ir.Table | str) -> Linear | str:
    """How to maintain the view `name` of `query` from a group state, or why
    it cannot be."""
    from sverify.engine import NotIncrementalError, delta_plans, plan_json, written_plan
    from sverify.ibis_substrait.core import DecimalDiv

    if isinstance(query, str):
        return SQL
    found = _split(query.op())
    if isinstance(found, str):
        return found
    node, groups, measures, names, what = found
    if missing := [g for g in groups if g not in names]:
        return f"the view does not output the key {missing[0]} unchanged"
    parent = node.parent.to_expr()
    try:
        deltas = delta_plans(plan_json(None, parent))  # type: ignore[arg-type]
    except NotIncrementalError as e:
        return f"the {what}'s input has no delta rules ({e})"

    def write(expr: ir.Table) -> str:
        return written_plan(plan_json(None, expr))  # type: ignore[arg-type]

    keys = [f"k{i}" for i in range(len(groups))]

    def contributions(rows: ir.Table, weight: Any = None) -> ir.Table:
        """Each row's contribution, times its `weight` (None: 1)."""

        def own(v: ops.Value) -> ir.Value:
            return v.replace({node.parent: rows.op()}).to_expr()  # type: ignore[attr-defined]

        cols: dict[str, Any] = {k: own(g) for k, g in zip(keys, groups.values(), strict=True)}
        one = ibis.literal(1, "int64")
        cols[COUNT] = one if weight is None else weight
        for i, m in enumerate(measures):
            cond: Any = ibis.literal(True) if m.arg is None else own(m.arg).notnull()
            if m.arg2 is not None:
                cond = cond & own(m.arg2).notnull()
            if m.where is not None:
                passes: Any = own(m.where)
                cond = cond & passes.fill_null(False)
            zero = ibis.literal(0, "int64")
            cols[f"__n{i}"] = ibis.ifelse(cond, cols[COUNT], zero)
            if m.kind == "count" or m.arg is None:
                value = zero
            elif m.kind in ("min", "max"):
                # The extreme of the values; a delete recomputes the group.
                value = ibis.ifelse(cond, own(m.arg), ibis.null(m.state))
            elif m.kind in EXACT_KINDS:
                # The value itself (a pair's second in `__t`): the weight is in
                # `__n`, and the exact moments are added up outside the engine
                # (`sverify._exact_sum`).
                value = ibis.ifelse(cond, own(m.arg).cast(m.state), ibis.null(m.state))
                if m.arg2 is not None:
                    second = ibis.ifelse(cond, own(m.arg2).cast(m.state), ibis.null(m.state))
                    cols[f"__t{i}"] = second
            else:
                v = own(m.arg).cast(m.state)
                v = v if weight is None else v * weight
                value = ibis.ifelse(cond, v, ibis.literal(0, m.state))
            cols[f"__s{i}"] = value
            if m.arg2 is not None:
                # `__t` after `__s`, as the state's columns are.
                cols[f"__t{i}"] = cols.pop(f"__t{i}")
        return rows.select(**cols)

    def added(rows: ir.Table) -> ir.Table:
        sums: dict[str, Any] = {COUNT: rows[COUNT].sum()}
        for i, m in enumerate(measures):
            s = rows[f"__s{i}"]
            sums[f"__n{i}"] = rows[f"__n{i}"].sum()
            # An exact measure's `__s` is replaced by its finished value.
            sums[f"__s{i}"] = (
                s.min()
                if m.kind == "min"
                else s.max()
                if m.kind in ("max", *EXACT_KINDS)
                else s.sum()
            )
            if m.arg2 is not None:
                sums[f"__t{i}"] = rows[f"__t{i}"].max()
        return rows.group_by(keys).aggregate(**sums)

    exact = tuple(
        _exact_sum.Exact(i, m.kind, m.sample, m.sqrt)
        for i, m in enumerate(measures)
        if m.kind in EXACT_KINDS
    )
    if exact and any(m.kind in ("min", "max") for m in measures):
        return (
            "a SUM, AVG or statistical aggregate of doubles beside a MIN or MAX: the touched "
            "groups are recomputed"
        )
    init = added(contributions(parent))
    changed = ibis.table({**parent.schema(), WEIGHT_IN: "int64"}, name=f"{name}$in")
    contrib = contributions(changed, changed[WEIGHT_IN])
    old = ibis.table(contrib.schema(), name=f"{name}$old")
    new = ibis.table(contrib.schema(), name=f"{name}$contrib")
    merge = write(added(old.union(new, distinct=False)))
    regroup = None
    if any(m.kind in ("min", "max") for m in measures):
        # The groups a batch deletes from, recomputed on the new input.
        touched = ibis.table({k: contrib.schema()[k] for k in keys}, name=f"{name}$keys")
        whole = contributions(parent)
        # NULL equals NULL. (`identical_to` next to decimal arithmetic does
        # not write back yet.)
        on = [(whole[k] == touched[k]) | (whole[k].isnull() & touched[k].isnull()) for k in keys]
        regroup = write(added(whole.semi_join(touched, on)))
    state = ibis.table(contrib.schema(), name=f"{name}$state")
    live = state.filter(state[COUNT] > 0)
    schema = node.schema  # type: ignore[attr-defined]
    out: dict[str, Any] = {}
    for k, g in zip(keys, groups, strict=True):
        out[g] = live[k]
    for i, m in enumerate(measures):
        n, s = live[f"__n{i}"], live[f"__s{i}"]
        if m.kind == "count":
            out[m.name] = n
        elif m.kind in ("min", "max"):
            out[m.name] = s
        elif m.kind in EXACT_KINDS:
            # Finished from the exact moments, NULL where Lean's is
            # (`sverify._exact_sum.finish`).
            out[m.name] = s
        elif m.kind == "avg":
            mean = DecimalDiv(s.op(), n.op(), m.to).to_expr()  # type: ignore[abstract]
            out[m.name] = ibis.ifelse(n == 0, ibis.null(m.to), mean)
        else:
            out[m.name] = ibis.ifelse(n == 0, ibis.null(m.state), s)
    # A decimal AVG keeps its exact type (Ibis's is the argument's).
    avgs = {m.name for m in measures if m.kind == "avg"}
    rel = live.select(**{c: out[c] if c in avgs else out[c].cast(schema[c]) for c in schema.names})
    hole = ibis.table(schema, name=f"{name}$hole").op()
    view = query.op().replace({node: hole}).replace({hole: rel.op()}).to_expr()  # type: ignore[attr-defined]
    return Linear(
        what=what,
        keys=keys,
        columns=[names[g] for g in groups],
        deltas=deltas,
        input_names=list(parent.columns),
        init=write(init),
        contrib=write(contrib),
        merge=merge,
        finish=write(view),
        regroup=regroup,
        exact=exact,
        values=write(contributions(parent)) if exact else None,
    )


@dataclass(frozen=True)
class _Measure:
    name: str
    kind: str
    """"count", "sum", "avg", "min", "max", or one of `EXACT_KINDS` for a
    `SUM`, an `AVG`, a `VAR`/`STDDEV`, a `COVAR` or a `CORR` of doubles."""
    arg: ops.Value | None
    """None for `COUNT(*)`."""
    where: ops.Value | None
    state: Any = None
    """The type of the state's `__s` column: the sum's (64-bit integers, or
    for decimals ten more digits at the argument's scale, as `SUM` has), or
    the argument's for `MIN` and `MAX`; None for `COUNT`."""
    to: Any = None
    """A decimal `AVG`'s type: four more digits and decimal places."""
    arg2: ops.Value | None = None
    """A `COVAR`'s or `CORR`'s second argument."""
    sample: bool = False
    """A sample's `VAR`, `STDDEV` or `COVAR` (else the population's)."""
    sqrt: bool = False
    """`STDDEV` (the root of `VAR`)."""


EXACT_KINDS = ("fsum", "favg", "var", "cov", "corr")
"""The measures kept from exact moments (`sverify._exact_sum`)."""


def _measure(name: str, v: ops.Value) -> _Measure | str:
    """The measure `v` as the state keeps it, or why it cannot."""
    from sverify.ibis_substrait._base import exact

    match v:
        case ops.CountStar(where=where):
            return _Measure(name, "count", None, where)
        case ops.Count(arg=arg, where=where):
            return _Measure(name, "count", arg, where)
        case ops.Sum(arg=arg, where=where) | ops.Mean(arg=arg, where=where):
            t = exact(arg)
            mean = isinstance(v, ops.Mean)
            if t.is_integer() and not mean:
                return _Measure(name, "sum", arg, where, dt.int64)
            if t.is_decimal():
                # The type of the decimal's SUM: ten more digits.
                state = dt.Decimal(*_decimals.sum_of((t.precision, t.scale)))
                if not mean:
                    return _Measure(name, "sum", arg, where, state)
                to = dt.Decimal(*_decimals.avg_of((t.precision, t.scale)))
                return _Measure(name, "avg", arg, where, state, to)
            if t.is_float64():
                # D25: the exact sum rounded once, kept exactly (#918).
                return _Measure(name, "favg" if mean else "fsum", arg, where, dt.float64)
            what = "AVG" if mean else "SUM"
            return (
                f"{name} is a {what} of {t}: only integer SUMs and DECIMAL and DOUBLE SUMs "
                "and AVGs are kept"
            )
        case ops.Min(arg=arg, where=where) | ops.Max(arg=arg, where=where):
            kind = "min" if isinstance(v, ops.Min) else "max"
            return _Measure(name, kind, arg, where, arg.dtype)
        case (
            ops.Variance(arg=arg, how=how, where=where)
            | ops.StandardDev(arg=arg, how=how, where=where)
        ):
            # D30: the exact moments rounded once, kept exactly (#918).
            if not exact(arg).is_float64():
                return f"{name} is a variance of {exact(arg)}: only DOUBLE variances are kept"
            sqrt = isinstance(v, ops.StandardDev)
            return _Measure(name, "var", arg, where, dt.float64, sample=how != "pop", sqrt=sqrt)
        case (
            ops.Covariance(left=x, right=y, how=how, where=where)
            | ops.Correlation(left=x, right=y, how=how, where=where)
        ):
            kind = "corr" if isinstance(v, ops.Correlation) else "cov"
            return _Measure(name, kind, x, where, dt.float64, arg2=y, sample=how != "pop")
    return f"{name} is not COUNT, SUM, AVG, MIN, MAX or a statistical aggregate"


def _split(
    op: ops.Relation,
) -> tuple[Any, dict[str, ops.Value], list[_Measure], dict[str, str], str] | str:
    """The aggregate or `DISTINCT` a view ends in (under filters,
    projections and sorts of its rows), its keys by name, its measures, the
    view's column for each of its columns, and what it is; or why the view
    has none with delta rules."""
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
            got = _measure(m, v)
            if isinstance(got, str):
                return got
            parts = [p for p in (got.arg, got.arg2, got.where) if p is not None]
            if not _row_local(parts, parent) or any(
                p.find(ops.Reduction, filter=_own_tree) for p in parts
            ):
                return f"{m} reads other rows"
            measures.append(got)
        return agg, dict(agg.groups), measures, names, "aggregate"
    found = _under(op, lambda o: isinstance(o, ops.Distinct))
    if found is None:
        return NOT_AGGREGATE
    node, names = found
    parent = node.parent  # type: ignore[attr-defined]
    groups = {c: ops.Field(parent, c) for c in parent.schema.names}
    return node, groups, [], names, "distinct"  # type: ignore[return-value]
