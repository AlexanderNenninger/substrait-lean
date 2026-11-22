# `comomentNum_nonneg`

A variance's numerator is never negative.

Lean: `Substrait.comomentNum_nonneg`, in
[`core/Sverify/Core/FloatMoments.lean`](../../core/Sverify/Core/FloatMoments.lean).
Layer: `eval`, the reference's value of the aggregate. Axioms: `propext`, `Classical.choice`, `Quot.sound`
([trusted-base.md](../trusted-base.md)).

## What it says

The reference computes `VAR_POP`, `STDDEV_POP` and the other moments of
doubles exactly (D30), as integers: `n · Σx² − (Σx)²` is `n²` times the
population variance's numerator, with no rounding. This theorem says that
number is not negative, by Lagrange's identity: it is a sum of squares.
Rounded once at the end, a variance is therefore not negative, and a
postcondition `var >= 0.0` is proved.

## The statement, line by line

```lean
theorem comomentNum_nonneg : ∀ cs : List Int, 0 ≤ comomentNum cs
```

- `cs`: the codes of the doubles. There is no hypothesis: the theorem holds
  for every list, the empty one included.
- `comomentNum cs`: `n · Σx² − (Σx)²`, exact, in units of 2⁻²¹⁴⁸
  (`FloatMoments.lean`).
- The conclusion: it is at least 0.

## What it rules out

- A negative variance or standard deviation in the reference, from
  cancellation: the numerator is an exact integer, so there is none.

## What it does not cover

- What an engine gives. DuckDB, Polars and Spark compute variances by their
  own algorithms, recorded in their facts; the route says how a proof reaches
  them ([`float-bounds.md`](../float-bounds.md)).
- A variance of fewer than two rows, which is NULL for the sample variance.
  The postcondition states `var.isnull() | var >= 0.0` where a group can have
  one row.

## Its side conditions

None: the theorem has no hypotheses. The checker's postcondition `var >= 0`
rests on the exact numerator being non-negative and on the rounding of a
non-negative number being non-negative.

## Example

```python
import ibis
import sverify as sv
from ibis import _

metrics = ibis.table({"host": "string", "cpu": "float64"}, name="metrics")
CPU = [_.cpu >= 0.0, _.cpu <= 100.0, _.cpu.notnull()]
```

A variance is not negative, for any data; it is NULL for a group of one row
under the sample variance, so the postcondition allows NULL:

```python
per_host = metrics.group_by("host").aggregate(var=metrics.cpu.var(how="sample"))
report = sv.verify(
    per_host,
    requires={"metrics": [*CPU, sv.max_rows(1000)]},
    ensures=[(_.var >= 0.0) | _.var.isnull()],
)
print(report.verdict)
# proved_with_checks
```

The verdict is `proved_with_checks` because the run checks that the variance
stays finite. Without allowing NULL the postcondition is not proved:

```python
report = sv.verify(per_host, requires={"metrics": [*CPU, sv.max_rows(1000)]}, ensures=[_.var >= 0.0])
print(report.verdict)
# unproved
```
