# `contract_sound`

A postcondition Sverify proves is TRUE on every row the plan outputs.

Lean: `Substrait.contract_sound`, in
[`analysis/Sverify/Analysis/Contracts/Sound.lean`](../../analysis/Sverify/Analysis/Contracts/Sound.lean).
Layer: `eval`, the reference's result for the plan. Axioms: `propext`,
`Classical.choice`, `Quot.sound`
([trusted-base.md](../trusted-base.md)).

## What it says

You write a rule and a promise about its output, say that `doubled` is never
negative. Sverify proves the promise from what the rule's inputs are known
to be. If the proof goes through, no row of the output breaks the promise,
for any data that meets the preconditions.

## The statement, line by line

```lean
theorem contract_sound {cat : Catalog} (hcat : cat.WF)
    {S : String → List AVal} {pre : String → List Expr} {Q : Rel}
    (hS : ∀ t, ∀ row ∈ (cat t).rows, EnvMem (S t) row)
    (hpre : ∀ t, ∀ row ∈ (cat t).rows, ∀ e ∈ pre t, (e.eval row).isTrue = true)
    (hQ : Q.WF cat) {T : WindowKeys} (hT : T.SoundAll cat)
    (hproved : (Q.aeval cat (fun t => tableEnv (S t) (pre t))
      (fun t => (pre t).flatMap Expr.factsOf) T).all AVal.certainlyTrue = true) :
    ∀ row ∈ Q.eval cat, ∀ v ∈ row, v = .bool true
```

- `cat`, `hcat`: the data, a catalog of tables, and the assumption that it
  is well formed (each row has its table's arity).
- `S`, `hS`: each table's schema as the checker knows it, and the
  assumption that every row of the data fits it (an integer column holds
  integers or NULL).
- `pre`, `hpre`: the preconditions of each table, and the assumption that
  every row of the data makes each of them TRUE. This is the `requires` you
  wrote, checked on the data when the plan runs.
- `Q`, `hQ`: the plan followed by a select of the postconditions, and the
  assumption that it is well formed.
- `T`, `hT`: what the analysis assumes about the order of tied window rows
  (the keys that close the ties).
- `hproved`: the checker's own computation. It evaluates `Q` over
  descriptions of values instead of values (`aeval`), starting from the
  schemas refined by the preconditions and the facts they imply, and finds
  that every output column is certainly TRUE. The computation is a Boolean
  function, so `hproved` is checked by running it.
- The conclusion: every value of every row of `Q`'s result is `TRUE`.

## What it rules out

- A row with `doubled < 0` in the output of a plan proved to keep
  `doubled ≥ 0`.
- A row where the postcondition is NULL. A comparison with a NULL is not
  TRUE, so the checker doesn't prove it.

## What it does not cover

- Data that breaks a precondition. The theorem assumes them; the run
  checks them before it starts.
- What an engine computes. This theorem is about the reference.
  [`check_proved_on`](../proofs.md) and the engine theorems carry it to each
  engine.
- A plan whose ties stay open, or whose doubles an engine adds in another
  order: [`contract_sound_all`](contract_sound_all.md) and
  [`contract_sound_allowed`](contract_sound_allowed.md).

## Its side conditions

`hcat` and `hQ` are decided by `Rel.checkWF_iff`'s check. `hS` and `hpre`
are the schemas and `requires` of the contract, checked on the data on each
run. `hT` holds for the keys the checker derives (`Rel.keyedWindows_soundAll`).
`hproved` is what the checker's report says: `proved`.

## Example

A rule that doubles an amount, with the amount bounded:

```python
import ibis
import sverify as sv
from ibis import _

orders = ibis.table({"id": "int64", "amount": "int64"}, name="orders")
doubled = orders.select(orders.id, doubled=orders.amount * 2)

report = sv.verify(
    doubled,
    requires={"orders": [_.amount >= 0, _.amount <= 1_000_000]},
    ensures=[_.doubled >= 0],
)
print(report.verdict)
# proved
```

Without the preconditions, `amount` may be NULL, and `NULL * 2` is NULL, so
the promise isn't proved, and the report names a row that breaks it:

```python
unbounded = sv.verify(doubled, ensures=[_.doubled >= 0])
print(unbounded.verdict)
# unproved
```
