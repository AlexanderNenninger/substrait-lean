# `contract_sound_allowed_closed`

[`contract_sound_allowed`](contract_sound_allowed.md) with its float-safety
side condition replaced by a check the checker runs.

Lean: `Substrait.contract_sound_allowed_closed`, in
[`analysis/Sverify/Analysis/AllowedAnalysis.lean`](../../analysis/Sverify/Analysis/AllowedAnalysis.lean).
Layer: `Allowed`. Axioms: `propext`, `Classical.choice`, `Quot.sound`
([trusted-base.md](../trusted-base.md)).

## What it says

`contract_sound_allowed` asks for `FloatOpenSafe`, a property of the plan
that is a statement about every allowed result. This theorem swaps it for
`Rel.closedB`, a Boolean the checker computes on the plan's syntax: a plan
is closed when none of its measures is `VAR_*`, `STDDEV_*`, `COVAR_*`,
`CORR` or `QUANTILE_CONT`. A double `SUM` or `AVG` is closed, since the
reference rounds their exact value once and every order an engine adds in
stays within the plan's bound.

## The statement, line by line

It is `contract_sound_allowed` with two changes:

```lean
(hq : q.rows = .multiset) (hc : ctx.ReflAt q)
(hclosed : T.closedB = true)
```

- `hc`: the observation's context treats a value as equal to itself up to
  `q`, so comparing a result with itself finds no difference.
- `hclosed`: the plan is closed. The proof is
  `Rel.floatOpenSafe_of_closed hc hclosed`, which gives
  `contract_sound_allowed`'s `hsafe`.

The conclusion is the same: every value of every row of every result
`Rel.Allowed` allows is `TRUE`.

## What it rules out

- A proof that depends on the engine's order of addition, for a plan with a
  double sum. The check is purely syntactic, so a plan can't pass it by luck.
- A plan with an open `STDDEV` being called closed: it fails `closedB`
  and goes the longer way through `FloatOpenSafe`.

## What it does not cover

- A plan that isn't closed. It may still be proved, through the engine's
  table and `Rel.FloatOpenSafeP`, or it isn't.
- The postcondition's own robustness (`hrob`), as for
  `contract_sound_allowed`.

## Its side conditions

`hclosed` is `T.closedB = true`, decided on the plan. `hc` holds of every
observation Sverify builds. The rest are `contract_sound_allowed`'s.

## Example

The same sum as for `contract_sound_allowed`; the plan is closed, so the
checker needs no engine's table to prove it:

```python
import ibis
import sverify as sv
from ibis import _

m = ibis.table({"k": "int64", "x": "float64"}, name="m")
totals = m.group_by("k").aggregate(total=m.x.sum(), n=m.x.count())

report = sv.verify(
    totals,
    requires={"m": [_.x.between(0, 1000), sv.max_rows(1000)]},
    ensures=[_.total >= 0, _.n >= 0],
)
print(report.verdict)
# proved
```
