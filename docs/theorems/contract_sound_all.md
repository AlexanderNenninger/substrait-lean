# `contract_sound_all`

A proved postcondition holds on every row, in every order the reference
allows the plan to return its rows.

Lean: `Substrait.contract_sound_all`, in
[`analysis/Sverify/Analysis/Contracts/Sound.lean`](../../analysis/Sverify/Analysis/Contracts/Sound.lean).
Layer: `OrderAllowed`, every row order the reference allows. Axioms:
`propext`, `Classical.choice`, `Quot.sound`
([trusted-base.md](../trusted-base.md)).

## What it says

Some plans leave a choice open. A `LIMIT 1` over rows that tie in the
`ORDER BY` takes any one of them, and a window over tied rows numbers them
in any order. Two engines, or two runs of one, may pick differently. A
postcondition proved by this theorem holds whichever way the choice falls.

## The statement, line by line

```lean
theorem contract_sound_all {cat : Catalog} (hcat : cat.WF)
    {S : String → List AVal} {pre : String → List Expr} {Q : Rel}
    (hS : ∀ t, ∀ row ∈ (cat t).rows, EnvMem (S t) row)
    (hpre : ∀ t, ∀ row ∈ (cat t).rows, ∀ e ∈ pre t, (e.eval row).isTrue = true)
    (hQ : Q.WF cat) {T : WindowKeys} (hT : T.SoundAll cat)
    (hproved : (Q.aeval cat (fun t => tableEnv (S t) (pre t))
      (fun t => (pre t).flatMap Expr.factsOf) T).all AVal.certainlyTrue = true) :
    ∀ {out : Relation}, Q.OrderAllowed cat out →
      ∀ row ∈ out, ∀ v ∈ row, v = .bool true
```

The hypotheses are [`contract_sound`](contract_sound.md)'s, `hT` included:
`T.SoundAll` says the analysis's window keys are sound on every order the
reference allows. Only the conclusion changes: it is about any `out` with
`Q.OrderAllowed cat out`: every result that differs from the reference's
only in how it breaks ties, takes the rows of a `FETCH`, or orders the rows
of `FIRST`, `STRING_AGG` or a window. `contract_sound` follows from this
theorem, since the reference's own result is one of them
(`Rel.eval_orderAllowed`).

## What it rules out

- A postcondition that holds on the rows one engine returns and fails on
  the rows another engine returns for the same plan, because the two broke a
  tie differently.
- A `LIMIT 1` that takes a row with a NULL amount, when the postcondition
  says the amount is not NULL: every row it may take is one the proof covers.

## What it does not cover

- That the result is the same on every run. A plan may be proved and still
  have open ties: the rows can differ, and each of them meets the promise.
  `report.deterministic` says whether the rows are determined, and
  `Rel.window_deterministic` proves it where the keys close the ties.
- Doubles added in another order, which change the values themselves:
  [`contract_sound_allowed`](contract_sound_allowed.md).

## Its side conditions

As for [`contract_sound`](contract_sound.md). The checker's report is the
statement `check_proved_sound`
([`ContractCheck.lean`](../../SubstraitLean/ContractCheck.lean)) turns into
this theorem's hypotheses, so `proved` in the report means the conclusion
holds on every allowed order.

## Example

The smallest amount, taken with `LIMIT 1`. Orders with equal amounts tie,
so the row the plan returns is open, and the promise holds for each of
them:

```python
import ibis
import sverify as sv
from ibis import _

orders = ibis.table({"id": "int64", "amount": "int64"}, name="orders")
smallest = orders.order_by("amount").limit(1)

report = sv.verify(
    smallest,
    requires={"orders": [_.amount >= 0]},
    ensures=[_.amount >= 0],
)
print(report.verdict, report.deterministic)
# proved False
```

With a unique `amount`, no two rows tie, and the result is determined as well:

```python
keyed = sv.verify(
    smallest,
    requires={"orders": [_.amount >= 0, sv.unique("amount")]},
    ensures=[_.amount >= 0],
)
print(keyed.verdict, keyed.deterministic)
# proved True
```
