# `Rel.polars_sound`

A plan Sverify has proved returns the reference's rows when it runs on Polars, lowered by Polars's generated table.

Lean: `Substrait.Rel.polars_sound`, in
[`engines/polars/Sverify/Polars/Engine.lean`](../../engines/polars/Sverify/Polars/Engine.lean).
Layer: `eval`, the reference's result for the plan. Axioms: `propext`, `Classical.choice`, `Quot.sound` and
`Substrait.FloatCode.exp_fin`, a float fact that [trusted-base.md](../trusted-base.md)
lists as trusted.

## What it says

Sverify lowers the plan for Polars with a generated table: each function Polars computes its own way
gets a template proved to give the reference's value under Polars's profile (`Lowering.polars_exact`,
the truncating `//` from Polars's floored one, for the division). This theorem says that the lowered
plan, run with Polars's functions, gives the reference's rows. A plan whose proof holds on the
reference therefore holds on Polars for any data that meets the preconditions.

## The statement, line by line

```lean
theorem Rel.polars_sound {cat : Catalog} (hcat : cat.WF) {A : String → List AVal}
    {F : String → List Fact}
    (hA : ∀ t, ∀ row ∈ (cat t).rows, EnvMem (A t) row)
    (hF : ∀ t, ∀ row ∈ (cat t).rows, FactsHold (F t) row) {T : WindowKeys} (hT : T.SoundAll cat)
    {r r' : Rel} (hr : Lowering.polars.lowerRel? r = .ok r') (hwf : r.WF cat)
    (hsmall : r.Small cat) (hs : r.looseSub = true)
    (hm : (r.mayIssues cat A F T false).all (·.1.assumed) = true) :
    r'.eval cat Polars.impl = r.eval cat
```

- `cat`, `hcat`: the data, a catalog of tables, and the assumption that it
  is well formed.
- `A`, `hA`: what the checker knows of the values of each table's columns,
  as a set per column, and the assumption that every row of the data lies in
  those sets.
- `F`, `hF`: the facts between columns or about a whole row that follow from
  the preconditions, and the assumption that every row satisfies them.
- `T`, `hT`: what the analysis assumes about the order of tied window rows
  (the keys that close the ties, from [`Rel.keys_sound`](keys_sound.md)).
- `r`, `hwf`: the plan, and the assumption that it is well formed.
- `r'`, `hr`: the plan Polars's generated table lowers it to (`Lowering.lowerRel?`,
  which refuses a plan with a function the table has no entry for, `%` of doubles).
- `hsmall`: the size hypothesis (`Rel.Small`): a window reads fewer than
  2⁶² rows and an aggregate fewer than 2⁶³. An engine's memory guarantees it.
- `hs`: the plan keeps all rows where it must: no left join's right side
  loses a filter and no `UNNEST` sits below the guards (`Rel.looseSub`).
- `hm`: the checker's list of issues the plan may raise (`Rel.mayIssues`)
  holds nothing but issues assumed on the data, which the run checks first.
- The conclusion: evaluating the lowered plan with Polars's functions (`Polars.impl`: its profile's
  values, and its own where the profile raises) gives the same rows as the reference's `Rel.eval`.

## What it rules out

- A Polars result that differs from the reference's on data that meets the
  preconditions, for a plan Sverify proved: a quotient of a negative
  number, say, that differs by one.
- A plan that may raise on the data being run unless the run checks that it
  does not: `hm` allows only the issues the run checks first.

## What it does not cover

- What Polars does outside the model of its functions. The theorem is about
  `Polars.impl`, the model of Polars's scalar functions (`Profile.polars` and
  its error side, probed, in [`engines/polars/facts/`](../../engines/polars/facts/));
  that the model matches Polars rests on tests ([trusted-base.md](../trusted-base.md)).
- A double `SUM` or `AVG`, whose order Polars does not fix: the reference
  leaves it open, and [`contract_sound_allowed`](contract_sound_allowed.md)
  covers it.

## Its side conditions

`hcat` is a fact about the data, which the run's schema check covers.
`hwf`, `hs` and `hm` are the checker's own computations on the plan.
`hsmall` is about the data, the row counts of what windows and aggregates
read, and it is trusted: an engine's memory guarantees it
([trusted-base.md](../trusted-base.md)). `hA` and `hF` are the contract's schemas and preconditions, checked on the
data on each run; `hT` follows from the key analysis
([`Rel.keys_sound`](keys_sound.md)) and the table conditions the run checks. The route that rests on this
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

Polars takes the plan through its generated lowering, whose template for the
division truncates, and the route names the theorem and the lowering's:

```python
route = routes.choose(report, "polars")
print(route.taken, route.cls)
# translated shim
print(route.theorems)
# ('Rel.polars_sound', 'Lowering.polars_exact')
con = sv.connect()
con.put("lines", pa.table({"id": [1, 2], "n": [4, -4], "total": [100, 250]}))
print(report.run(con, "polars", route="auto").to_pylist())
# [{'id': 1, 'per': 25}, {'id': 2, 'per': -63}]
```

The second row is `250 // -4`, which is -63 in the reference, and Polars
gives -63 too, through the template.

Take the precondition `n != 0` away and Sverify does not prove the plan, so
no route carries it:

```python
unguarded = sv.verify(per_line, requires={"lines": [_.total > -1000, _.total < 1000]}, on_inferred="off")
print(unguarded.verdict)
# unproved
print(routes.choose(unguarded, "polars").refused)
# True
```
