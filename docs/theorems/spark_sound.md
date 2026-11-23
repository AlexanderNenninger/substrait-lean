# `Rel.spark_sound`

A plan Sverify has proved returns the reference's rows when it runs on Spark under ANSI, lowered by Spark's generated table.

Lean: `Substrait.Rel.spark_sound`, in
[`engines/spark/Sverify/Spark/Engine.lean`](../../engines/spark/Sverify/Spark/Engine.lean).
Layer: `eval`, the reference's result for the plan. Axioms: `propext`, `Classical.choice`, `Quot.sound` and
`Substrait.FloatCode.exp_fin`, a float fact that [trusted-base.md](../trusted-base.md)
lists as trusted.

## What it says

Spark under ANSI raises where the reference raises. Sverify lowers the plan
for Spark with a generated table (`Lowering.spark`): each function Spark
computes its own way gets a template proved to give the reference's value
under Spark's profile, on doubles (`floor` and `ceil`, which return a
`BIGINT` on Spark). This theorem says that the lowered plan, run with Spark's
functions where they do not raise (`Spark.impl`), gives the reference's rows.
The plan in the example needs no shim, and its route class is `exact`.

It covers a plan whose every function the table lowers exactly, which is every
plan but one with IEEE division. That one's entry raises at a zero divisor,
where IEEE gives `±∞`, as Spark does under ANSI. Such a plan keeps every guard,
and its theorem is `Rel.spark_sound_or_raises`: the reference's rows wherever
Spark does not raise. `Engine.spark_sound` joins the two (`Engine.SparkSide`,
ruling 277).

## The statement, line by line

```lean
theorem Rel.spark_sound {cat : Catalog} (hcat : cat.WF) (hdbl : cat.Dbl) {A : String → List AVal}
    {F : String → List Fact}
    (hA : ∀ t, ∀ row ∈ (cat t).rows, EnvMem (A t) row)
    (hF : ∀ t, ∀ row ∈ (cat t).rows, FactsHold (F t) row) {T : WindowKeys} (hT : T.SoundAll cat)
    {r : Rel} (hwf : r.WF cat) (hsmall : r.Small cat) (hs : r.looseSub = true)
    (hm : (r.mayIssues cat A F T false).all (·.1.assumed) = true) (hc : r.ConstsDbl)
    (hx : r.ExactOnB Lowering.spark = true) {r' : Rel} (hr : Lowering.spark.lowerRel? r = .ok r') :
    r'.eval cat Spark.impl = r.eval cat
```

- `cat`, `hcat`: the data, a catalog of tables, and the assumption that it
  is well formed.
- `hdbl`: every double in the data is a double's code (`Catalog.Dbl`): a
  fact of every Arrow `float64` column (ruling 248).
- `A`, `hA`: what the checker knows of the values of each table's columns,
  as a set per column, and the assumption that every row of the data lies in
  those sets.
- `F`, `hF`: the facts between columns or about a whole row that follow from
  the preconditions, and the assumption that every row satisfies them.
- `T`, `hT`: what the analysis assumes about the order of tied window rows
  (the keys that close the ties, from [`Rel.keys_sound`](keys_sound.md)).
- `r`, `hwf`: the plan, and the assumption that it is well formed.
- `hsmall`: the size hypothesis (`Rel.Small`): a window reads fewer than
  2⁶² rows and an aggregate fewer than 2⁶³. An engine's memory guarantees it.
- `hs`: the plan keeps all rows where it must: no left join's right side
  loses a filter and no `UNNEST` sits below the guards (`Rel.looseSub`).
- `hm`: the checker's list of issues the plan may raise (`Rel.mayIssues`)
  holds nothing but issues assumed on the data, which the run checks first.
- `hc`: the plan's constants are doubles' codes (`Rel.ConstsDbl`), which the
  checker checks on every plan (`Rel.constsDblB`).
- `hx`: Spark's table lowers every expression of the plan exactly
  (`Rel.ExactOnB`): the plan calls no IEEE division.
- `r'`, `hr`: the plan Spark's table lowers it to.
- The conclusion: evaluating the lowered plan with Spark's functions where they do not raise (`Spark.impl`) gives the same rows as the reference's `Rel.eval`.

## What it rules out

- A Spark result that differs from the reference's on data that meets the
  preconditions, for a plan Sverify proved.
- A plan that may raise unchecked: `hm` allows only the issues the run
  checks first.

## What it does not cover

- What Spark does outside the model of its functions. The theorem is about
  `Profile.spark`, built from Spark's facts
  ([`engines/spark/facts/`](../../engines/spark/facts/)); that the model
  matches Spark rests on tests ([trusted-base.md](../trusted-base.md)).
- A plan with IEEE division: `Rel.spark_sound_or_raises`, the reference's
  rows where Spark does not raise.
- A plan whose ties stay open or whose doubles Spark adds in another order:
  [`contract_sound_all`](contract_sound_all.md) and
  [`contract_sound_allowed`](contract_sound_allowed.md).

## Its side conditions

`hcat` and `hdbl` are facts about the data, which the run's schema check covers.
`hwf`, `hs`, `hm`, `hc` and `hx` are the checker's own computations on the plan.
`hsmall` is about the data, the row counts of what windows and aggregates
read, and it is trusted: an engine's memory guarantees it
([trusted-base.md](../trusted-base.md)). `hA` and `hF` are the contract's schemas and preconditions, checked on the
data on each run; `hT` follows from the key analysis
([`Rel.keys_sound`](keys_sound.md)) and the table conditions the run checks. The route that rests on this
theorem names it: `routes.choose(report, "spark").theorems`.

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

The route to Spark is exact, and names the theorem:

```python
route = routes.choose(report, "spark")
print(route.taken, route.cls)
# translated exact
print(route.theorems)
# ('Rel.spark_sound',)
```

Without the precondition `n != 0` the plan is not proved, and the route is
refused:

```python
unguarded = sv.verify(per_line, requires={"lines": [_.total > -1000, _.total < 1000]}, on_inferred="off")
print(routes.choose(unguarded, "spark").refused)
# True
```
