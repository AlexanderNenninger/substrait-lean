# `Rel.optimize_refines`

The plan `optimize` gives refines the original, up to the order of rows, when it has no open choices.

Lean: `Substrait.Rel.optimize_refines`, in
[`analysis/Sverify/Analysis/Semantic.lean`](../../analysis/Sverify/Analysis/Semantic.lean).
Layer: `RefinesBag`, every result the original allows is matched by the optimized plan's, up to the order of rows. Axioms: not yet listed;
`#print axioms Substrait.Rel.optimize_refines` is the check ([trusted-base.md](../trusted-base.md)).

## What it says

Sverify rewrites a plan before an engine runs it where a rewrite is proved:
`COUNT(DISTINCT id)` becomes `COUNT(id)` when `id` is a key, an outer join
becomes an inner join when a filter above it never accepts a padded row, and
so on. [`Rel.optimize_sound`](../optimizations.md) says the optimized plan has
the same rows in the same order; this theorem says the optimized plan refines
the original, so any result the optimized plan gives is one the original
allows, up to the order of rows. It is the statement an engine's run of the
optimized plan rests on.

## The statement, line by line

```lean
theorem Rel.optimize_refines {cat : Catalog} (hcat : cat.WF) {A : String → List AVal}
    {F : String → List Fact}
    (hA : ∀ t, ∀ row ∈ (cat t).rows, EnvMem (A t) row)
    (hF : ∀ t, ∀ row ∈ (cat t).rows, FactsHold (F t) row) {K : TableCond}
    (hK : K.Hold cat) {R : ForeignKeys} (hR : R.Hold cat) {use : Rule → Bool} {r : Rel}
    (hwf : r.WF cat) (hd : (r.optimize cat A F K R use).1.detPlan cat A F K = true) :
    (r.optimize cat A F K R use).1.RefinesBag cat r
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
- `R`, `hR`: the foreign keys you stated (`sv.references`), and the
  assumption that the data meets them.
- `use`: which rewrite rules are on.
- `r`, `hwf`: the plan, and the assumption that it is well formed.
- `hd`: the checker's own computation that the optimized plan has no open
  choice.
- The conclusion: the optimized plan refines `r` as a bag.

## What it rules out

- An optimization that changes a row: `Rel.optimize_sound` gives the same
  rows, and this theorem carries them over to the refinement.
- Running an optimized plan whose result the original does not allow.

## What it does not cover

- Plans with open choices: `hd` is false, and the engine runs the plan as
  written.
- The order of rows, as in [`Rel.refines_of_perm`](refines_of_perm.md): under
  an `ORDER BY` the run's gate asks for the exact refinement.
- That an engine computes the optimized plan the way the reference does. That
  is [`Rel.polars_sound`](polars_sound.md) and its siblings, for the plan the
  engine gets.

## Its side conditions

`hcat` is a fact about the data, which the run's schema check covers. `hwf` and
`hd` are the checker's computations on the plan. `hA`, `hF`, `hK` and `hR` are
the contract's schemas, preconditions, table conditions and foreign keys,
checked on the data on each run.

## Example

A key lets the optimizer turn `COUNT(DISTINCT id)` into `COUNT(id)`. A run
with the optimizer on and off returns the same rows:

```python
import ibis
import pyarrow as pa
import sverify as sv

orders = ibis.table({"id": "int64", "total": "int64"}, name="orders")
report = sv.verify(
    orders.aggregate(n=orders.id.nunique()), requires={"orders": [sv.unique("id")]}
)
print(report.verdict)
# proved
con = sv.connect()
con.put("orders", pa.table({"id": [1, 2, 3], "total": [5, 6, 7]}))
print(report.run(con, "duckdb").to_pylist())
# [{'n': 3}]
print(report.run(con, "duckdb", optimize=False).to_pylist())
# [{'n': 3}]
```
