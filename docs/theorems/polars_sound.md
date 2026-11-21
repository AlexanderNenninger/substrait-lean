# `Rel.polars_sound`

A plan Sverify has proved returns the reference's rows when it runs on Polars as the translation writes it.

Lean: `Substrait.Rel.polars_sound`, in
[`engines/polars/Sverify/Polars/Shims.lean`](../../engines/polars/Sverify/Polars/Shims.lean).
Layer: `eval`, the reference's result for the plan. Axioms: not yet listed;
`#print axioms Substrait.Rel.polars_sound` is the check ([trusted-base.md](../trusted-base.md)).

## What it says

Sverify does not run the reference's plan on Polars as it stands: it writes
it with a shim for each place where Polars's value differs from the
reference's, and this theorem says that the result is the reference's rows. The shims have lemmas of their own
(`Polars.int_div_trunc` for the division), and the theorem uses them. A plan
whose proof holds on the reference therefore holds on Polars for any data
that meets the preconditions.

## The statement, line by line

```lean
theorem Rel.polars_sound {cat : Catalog} (hcat : cat.WF) {A : String → List AVal}
    {F : String → List Fact}
    (hA : ∀ t, ∀ row ∈ (cat t).rows, EnvMem (A t) row)
    (hF : ∀ t, ∀ row ∈ (cat t).rows, FactsHold (F t) row) {T : WindowKeys} (hT : T.SoundAll cat)
    {r : Rel} (hwf : r.WF cat) (hsmall : r.Small cat) (hs : r.looseSub = true)
    (hm : (r.mayIssues cat A F T false).all (·.1.assumed) = true) :
    r.eval cat Polars.written = r.eval cat
```

- `cat`, `hcat`: the data, a catalog of tables, and the assumption that it
  is well formed.
- `A`, `hA`: what the checker knows of the values of each table's columns,
  as a set per column, and the assumption that every row of the data lies in
  those sets.
- `F`, `hF`: the facts between columns or about a whole row that follow from
  the preconditions, and the assumption that every row satisfies them.
- `T`, `hT`: what the analysis assumes about the order of tied window rows
  (the keys that close the ties).
- `r`, `hwf`: the plan, and the assumption that it is well formed.
- `hsmall`: the size hypothesis (`Rel.Small`): a window reads fewer than
  2⁶² rows and an aggregate fewer than 2⁶³. An engine's memory guarantees it.
- `hs`: the plan keeps all rows where it must: no left join's right side
  loses a filter (`Rel.looseSub`).
- `hm`: the checker's list of issues the plan may raise (`Rel.mayIssues`)
  holds nothing but issues assumed on the data, which the run checks first.
- The conclusion: evaluating the plan with Polars's functions as the translation writes them (`Polars.written`) gives the same rows as the reference's `Rel.eval`.

## What it rules out

- A Polars result that differs from the reference's on data that meets the
  preconditions, for a plan Sverify proved: a quotient of a negative
  number, say, that differs by one.
- A plan that may raise on the data being run unless the run checks that it
  does not: `hm` allows only the issues the run checks first.

## What it does not cover

- What Polars does outside the model of its functions. The theorem is about
  `Polars.written`, the model of Polars's scalar functions (probed, in
  [`engines/polars/facts/`](../../engines/polars/facts/)); that the model
  matches Polars rests on tests ([trusted-base.md](../trusted-base.md)).
- A double `SUM` or `AVG`, whose order Polars does not fix: the reference
  leaves it open, and [`contract_sound_allowed`](contract_sound_allowed.md)
  covers it.

## Its side conditions

`hcat` is a fact about the data, which the run's schema check covers.
`hwf`, `hsmall`, `hs` and `hm` are the checker's own computations on the
plan. `hA`, `hF` and `hT` are the contract's schemas, preconditions and the
tie keys, checked on the data on each run. The route that rests on this
theorem names it: `routes.choose(report, "polars").theorems`.

## Example

```python
import ibis
import pyarrow as pa
import sverify as sv
from ibis import _
from sverify import routes

lines = ibis.table({"id": "int64", "n": "int64", "total": "int64"}, name="lines")
per_line = lines.select(lines.id, per=lines.total // lines.n)
report = sv.verify(
    per_line,
    requires={"lines": [_.n != 0, _.total > -1000, _.total < 1000]},
)
print(report.verdict)
# proved
```

Polars takes the plan through a translation with a shim for the division,
and the route names the theorem and the shim's lemma:

```python
route = routes.choose(report, "polars")
print(route.kind, route.cls)
# translated shim
print(route.theorems)
# ('Rel.polars_sound', 'Polars.int_div_trunc')
con = sv.connect()
con.put("lines", pa.table({"id": [1, 2], "n": [4, -4], "total": [100, 250]}))
print(report.run(con, "polars", route="auto").to_pylist())
# [{'id': 1, 'per': 25}, {'id': 2, 'per': -63}]
```

The second row is `250 // -4`, which is -63 in the reference, and Polars
gives -63 too, through the shim.

Take the precondition `n != 0` away and Sverify does not prove the plan, so
no route carries it:

```python
unguarded = sv.verify(per_line, requires={"lines": [_.total > -1000, _.total < 1000]}, on_inferred="off")
print(unguarded.verdict)
# unproved
print(routes.choose(unguarded, "polars").refused)
# True
```
