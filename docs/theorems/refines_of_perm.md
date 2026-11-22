# `Rel.refines_of_perm`

A plan with no open choices refines any plan that has its rows in some order.

Lean: `Substrait.Rel.refines_of_perm`, in
[`analysis/Sverify/Analysis/AllowedAnalysis.lean`](../../analysis/Sverify/Analysis/AllowedAnalysis.lean).
Layer: `RefinesBag`, every result `q` allows is one `r` allows, up to the order of rows. Axioms: `propext`, `Classical.choice`, `Quot.sound`
([trusted-base.md](../trusted-base.md)).

## What it says

Some plans leave a choice open: a `LIMIT 1` over tied rows takes any one of
them, and a window over tied rows numbers them in any order. A plan `q` with
no open choice has one result, up to the order of its rows. If another plan
`r` returns those rows in some order, then `q` refines `r`: the one result
`q` gives is among those `r` allows. The optimizer's gate uses it with `q`
the rewrite and `r` the original, which is how a rewrite that fixes a choice
of the original, say the order of ties, is still a refinement
([`Rel.optimize_refines`](optimize_refines.md)).

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
- `q`, `hwf`: the plan with no open choice, and the assumption that it is
  well formed.
- `r`: the other plan.
- `hd`: the checker's own computation (`Rel.detPlan`) that `q` has no open
  choice. A `FETCH` counts only over an `ORDER BY` whose columns hold a key
  and none clustered; windows are closed by keys that break their ties;
  `DISTINCT`, and windowed `MIN`, `MAX` and `QUANTILE_DISC`, count only
  without doubles; and an aggregate counts when its measures are order-free
  (`COUNT`, `SUM`, `AVG`, `MIN`, `MAX`) or when it sorts its rows so as to
  fix its inputs.
- `h`: the rows of `q` are a permutation of the rows of `r`.
- The conclusion: `q` refines `r` as a bag (`Rel.RefinesBag`): every result
  `q` allows is one `r` allows, up to the order of the rows.

## What it rules out

- A rewrite that drops or repeats a row, for a plan Sverify proved
  determined: `h` fails.
- Calling a plan a refinement while it leaves a choice open, such as a
  `LIMIT` over tied rows or a window without a key that closes its ties:
  `hd` fails, and the checker names the place where ties stay open.

## What it does not cover

- The order of the rows. The conclusion is up to the order, so an `ORDER BY`'s
  order is not preserved by this theorem; the exact refinement
  (`Rel.Refines`) needs the rewrite's allowed results, not only its rows.
- A plan `q` that leaves a choice open: `hd` is false for it, and its
  refinement needs the exact one (`Rel.Refines`).

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
