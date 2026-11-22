# `Rel.refines_of_perm`

A rewrite to a plan with no open choices, whose rows are the original's in some order, refines the original.

Lean: `Substrait.Rel.refines_of_perm`, in
[`analysis/Sverify/Analysis/AllowedAnalysis.lean`](../../analysis/Sverify/Analysis/AllowedAnalysis.lean).
Layer: `RefinesBag`, every result the original allows is matched by the rewrite's, up to the order of rows. Axioms: `propext`, `Classical.choice`, `Quot.sound`
([trusted-base.md](../trusted-base.md)).

## What it says

Some plans leave a choice open: a `LIMIT 1` over tied rows takes any one of
them, and a window over tied rows numbers them in any order. A rewrite, or an
engine's own plan, may fix one of those choices. This theorem says when that
is allowed: if the original plan has no open choice (its result is the same
rows in every order the reference allows), then any plan that returns those
rows in some order refines it. The optimizer's gate and a sink's
`reproducible=` rest on it.

## The statement, line by line

```lean
theorem Rel.refines_of_perm {cat : Catalog} (hcat : cat.WF) {A : String → List AVal}
    {F : String → List Fact}
    (hA : ∀ t, ∀ row ∈ (cat t).rows, EnvMem (A t) row)
    (hF : ∀ t, ∀ row ∈ (cat t).rows, FactsHold (F t) row) {K : TableCond}
    (hK : K.Hold cat) {q r : Rel} (hwf : q.WF cat)
    (hd : q.detPlan cat A F K = true) (h : (q.eval cat).Perm (r.eval cat)) : q.RefinesBag cat r
```

- `cat`, `hcat`: the data, a catalog of tables, and the assumption that it
  is well formed.
- `A`, `hA`: what the checker knows of the values of each table's columns,
  as a set per column, and the assumption that every row of the data lies in
  those sets.
- `F`, `hF`: the facts between columns or about a whole row that follow from
  the preconditions, and the assumption that every row satisfies them.
- `K`, `hK`: the table conditions you stated, keys and non-overlapping
  ranges, and the assumption that the data meets them.
- `q`, `hwf`: the original plan, and the assumption that it is well formed.
- `r`: the rewrite.
- `hd`: the checker's own computation (`Rel.detPlan`) that the original has
  no open choice: its windows have keys that close their ties, and its
  aggregates are order-free or sort.
- `h`: the rewrite's rows are a permutation of the original's.
- The conclusion: the rewrite refines the original as a bag
  (`Rel.RefinesBag`): every result the original allows is one the rewrite
  allows, up to the order of the rows.

## What it rules out

- A rewrite that drops or repeats a row, for a plan Sverify proved
  determined: `h` fails.
- Fixing a choice the original leaves open and calling it a refinement
  without a key that closes it: `hd` fails, and the checker names the window
  or `LIMIT` where ties stay open.

## What it does not cover

- The order of the rows. The conclusion is up to the order, so an `ORDER BY`'s
  order is not preserved by this theorem; the exact refinement
  (`Rel.Refines`) needs the rewrite's allowed results, not only its rows.
- Plans with open choices. `hd` is false for them, and a rewrite of such a
  plan needs a different argument.

## Its side conditions

`hcat` is a fact about the data, which the run's schema check covers. `hwf` and
`hd` are the checker's computations on the plan. `hA`, `hF` and `hK` are the
contract's schemas, preconditions and table conditions, checked on the data on
each run. `h` is proved for each rewrite the optimizer applies
([`Rel.optimize_refines`](optimize_refines.md)).

## Example

A plan with a key that closes its ties is determined, so a run may ask for a
reproducible result:

```python
import ibis
import pyarrow as pa
import sverify as sv

orders = ibis.table({"id": "int64", "amount": "float64"}, name="orders")
numbered = orders.mutate(rn=ibis.row_number().over(ibis.window(order_by=orders.id)))
con = sv.connect()
con.put("orders", pa.table({"id": [1, 2, 3], "amount": [5.0, 6.0, 7.0]}))

keyed = sv.verify(numbered.select("id", "rn"), requires={"orders": [sv.unique("id")]})
print(keyed.verdict)
# proved
print(len(keyed.run(con, "duckdb", reproducible=sv.equivalent())))
# 3
```

Without the key, `ROW_NUMBER` over rows that tie has an open choice, `hd`
does not hold, and the run refuses to promise a reproducible result:

```python
unkeyed = sv.verify(numbered.select("id", "rn"))
try:
    unkeyed.run(con, "duckdb", reproducible=sv.equivalent())
except sv.errors.RouteError as e:
    print(str(e)[:60])
# refused on duckdb: a rerun must give the same result: ...
```
