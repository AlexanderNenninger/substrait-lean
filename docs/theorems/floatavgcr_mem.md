# `floatAvgCR_mem`

The `AVG` of doubles lies between the bounds of its values, widened by the checker's tolerance.

Lean: `Substrait.floatAvgCR_mem`, in
[`core/Sverify/Core/FloatExact.lean`](../../core/Sverify/Core/FloatExact.lean).
Layer: `eval`, the reference's value of the aggregate. Axioms: `propext`, `Classical.choice`, `Quot.sound`
([trusted-base.md](../trusted-base.md)).

## What it says

The reference's `AVG` of doubles is the exact sum divided by the count,
rounded once (D25). A mean of values in `[lo, hi]` lies in `[lo, hi]`, and the
rounded mean lies within the tolerance `avgTolScaled N` of that range. The
range does not move with the count, and the checker's own bound for an `AVG`
(`floatBound`, with `crBound`, D25) needs no row cap: it is the range rounded
once. This theorem is #85's statement of a tolerance around the exact result,
and that tolerance does grow with `N`: the theorem takes a count `N ≤ 2³²`
(`_h32`, unused in the proof but in the statement), which a row cap or the
plan's shape supplies. Where the bounds are finite the checker's bound
already contains it.

## The statement, line by line

```lean
theorem floatAvgCR_mem {cs : List Int} {N : Nat} {lo hi : Int} (hne : cs ≠ []) (hN : cs.length ≤ N)
    (_h32 : N ≤ 2 ^ 32) (hlo : lo.natAbs ≤ 2 ^ 1474) (hhi : hi.natAbs ≤ 2 ^ 1474)
    (hb : ∀ c ∈ cs, lo ≤ scaled (canon c) ∧ scaled (canon c) ≤ hi) :
    lo - avgTolScaled N (max lo.natAbs hi.natAbs) ≤ scaled (floatAvgCR (cs.map .float)) ∧
      scaled (floatAvgCR (cs.map .float)) ≤ hi + avgTolScaled N (max lo.natAbs hi.natAbs)
```

A double is a code, an integer; `scaled c` is the double's value times 2¹⁰⁷⁴
with its sign, so a bound on doubles becomes a bound on integers the checker
can compute with. 
- `cs`, `hne`: the codes of the doubles averaged, and the assumption that
  there is at least one.
- `N`, `hN`, `_h32`: a count of at most 2³² that bounds the rows, which the
  tolerance `avgTolScaled N` grows with. It comes from `sv.max_rows` or from
  the plan's shape (a `LIMIT`, `VALUES`). The checker's bound for an `AVG`
  uses no count, so a plan with neither is still proved.
- `lo`, `hi`, `hlo`, `hhi`: bounds in scaled units, finite doubles'.
- `hb`: every value lies between them, in canonical form.
- The conclusion: the scaled mean, `floatAvgCR`, lies between `lo` and `hi`
  widened by the tolerance.

## What it rules out

- A mean that lands outside `[lo, hi]` by more than the tolerance, for values
  in `[lo, hi]`.
- A postcondition on the mean above `hi`: not proved, and one at `hi`, with
  the tolerance stated, is proved.

## What it does not cover

- An average of an empty group: `hne` assumes a value, and the mean of no
  rows is NULL.
- The tolerance in the postcondition. A mean the plan proves at `hi` is
  within the checker's tolerance of it, and a postcondition on the exact
  bound states that with `sv.approx` ([`float-bounds.md`](../float-bounds.md)).
- The order of the sum, as for [`floatSumCR_mem`](floatsumcr_mem.md).

## Its side conditions

`hne` is the group being non-empty (the mean of no rows is NULL). `hN` is a
row count the tolerance is stated for, from `sv.max_rows` or the plan's
shape; the checker's bound for a mean uses none. `hlo`, `hhi` and `hb` are
the column's range, a precondition checked on the data on each run.

## Example

```python
import ibis
import sverify as sv
from ibis import _

metrics = ibis.table({"host": "string", "cpu": "float64"}, name="metrics")
CPU = [_.cpu >= 0.0, _.cpu <= 100.0, _.cpu.notnull()]
```

A mean of values in `[0, 100]` is proved to stay within the range, with no
row cap and the tolerance stated by `sv.approx`:

```python
per_host = metrics.group_by("host").aggregate(mean=metrics.cpu.mean())
report = sv.verify(
    per_host,
    requires={"metrics": CPU},
    ensures=[_.mean >= 0.0, sv.approx(_.mean <= 100.0)],
)
print(report.verdict)
# proved
```
