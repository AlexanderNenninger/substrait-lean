# `contract_sound_allowed`

A proved postcondition holds on every result the reference allows,
including doubles summed in any order.

Lean: `Substrait.contract_sound_allowed`, in
[`analysis/Sverify/Analysis/AllowedAnalysis.lean`](../../analysis/Sverify/Analysis/AllowedAnalysis.lean).
Layer: `Allowed`, every result `Rel.Allowed` allows. Axioms: `propext`,
`Classical.choice`, `Quot.sound` ([trusted-base.md](../trusted-base.md)).

## What it says

Addition of doubles isn't associative, so two engines that add the same
numbers in another order give sums that differ in the last digits. The
reference allows each of those sums. A postcondition proved by this theorem
holds on all of them, as long as it doesn't depend on digits the observation
ignores.

## The statement, line by line

```lean
theorem contract_sound_allowed {cat : Catalog} (hcat : cat.WF)
    {S : String → List AVal} {pre : String → List Expr}
    {T : Rel} {es : List Expr} {mp : List Nat}
    (hS : …) (hpre : …) (hT : T.WF cat)
    {q : Obs} {ctx : ObsCtx} (hq : q.rows = .multiset)
    (hsafe : T.FloatOpenSafe q ctx cat) {sh : Nat → Option Shift}
    (hsh : ∀ i s, sh i = some s → s.Sound q ctx i)
    (hrob : ∀ j ∈ mp, (postExpr (T.arity cat) es j).robustB q ctx sh = true)
    (hQ : (Rel.emit (.project T (es.map (·.narrow sh))) mp).WF cat)
    {W : WindowKeys} (hW : W.SoundAll cat)
    (hproved : (… .aeval …).all AVal.certainlyTrue = true) :
    ∀ {out : Relation}, (Rel.emit (.project T es) mp).Allowed cat out →
      ∀ row ∈ out, ∀ v ∈ row, v = .bool true
```

- `T`, `es`, `mp`: the transformation, its postconditions and the columns
  of them that are selected.
- `q`, `ctx`, `hq`: the observation the result is read under. Here the
  rows are a multiset, so their order doesn't matter.
- `hsafe`: the plan is `FloatOpenSafe` under `q`: every choice the
  reference leaves open, a double sum's order, gives a result equal to
  one of the reference's up to the observation. [`contract_sound_allowed_closed`](contract_sound_allowed_closed.md)
  replaces it with a check.
- `sh`, `hsh`: a shift per column, how far the observation lets its value
  move, and the assumption that each shift is sound for `q`.
- `hrob`: each postcondition is robust: it holds of every value within its
  column's shift (`Expr.robustB`). A threshold at 100 on a mean that is only
  known within 1e-4 isn't robust, and this is where it is refused.
- `hQ`, `hW`, `hproved`: as for [`contract_sound_all`](contract_sound_all.md),
  over the postconditions narrowed by the shifts (`Expr.narrow`).
- The conclusion: every value of every row of every result in `Allowed`
  is `TRUE`.

## What it rules out

- A sum of doubles that is `≥ 0` in the reference and `-1e-17` on an engine
  that adds in another order, for a postcondition that reads the sum with
  no margin.
- A postcondition that holds on the reference's sum and fails on an
  allowed one, because the checker narrowed it by how far the sum may move.

## What it does not cover

- A postcondition that isn't robust. It isn't proved, and the report says
  which column's tolerance it needs (`sv.approx`, `sv.equivalent(floats=...)`).
- A value outside what the observation allows: an engine whose double sum
  leaves the plan's bound isn't an allowed result.
- What an engine computes: the engine theorems
  (`Engine.contract_sound`, [proofs.md](../proofs.md)) carry this one to
  each engine.

## Its side conditions

The checker decides `hrob` (`robustB`), `hQ` and `hproved`. `hsafe` is
decided by `Rel.closedB` for a plan whose measures are not `VAR_*`,
`STDDEV_*`, `COVAR_*`, `CORR` or `QUANTILE_CONT`
([`contract_sound_allowed_closed`](contract_sound_allowed_closed.md)), and
by the engine's table otherwise.

## Example

A sum of doubles per key, promised to be non-negative:

```python
import ibis
import sverify as sv
from ibis import _

m = ibis.table({"k": "int64", "x": "float64"}, name="m")
totals = m.group_by("k").aggregate(total=m.x.sum())

report = sv.verify(
    totals,
    requires={"m": [_.x.between(0, 1000), sv.max_rows(1000)]},
    ensures=[_.total >= 0],
)
print(report.verdict)
# proved
print(report.observation.floats)
# plan
```

The observation is the plan's own bound: `report.observation` prints the
tolerance (`≤ abs=1.1e-07, rel=2.2e-13`) within which every allowed sum
lies of the reference's.
