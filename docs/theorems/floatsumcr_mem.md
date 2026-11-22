# `floatSumCR_mem`

The `SUM` of doubles lies between the bounds the checker computes from the values' range and the row cap.

Lean: `Substrait.floatSumCR_mem`, in
[`core/Sverify/Core/FloatExact.lean`](../../core/Sverify/Core/FloatExact.lean).
Layer: `eval`, the reference's value of the aggregate. Axioms: `propext`, `Classical.choice`, `Quot.sound`
([trusted-base.md](../trusted-base.md)).

## What it says

The reference's `SUM` of doubles is the exact sum, rounded once to the
nearest double (D25). If every value lies in `[lo, hi]` and there are at most
`N` of them, the exact sum lies in `[min(lo, N·lo), max(hi, N·hi)]`, and the
rounded sum is within half an ulp of it. The theorem states the rounded
sum's bounds, widened by the checker's tolerance `sumTolScaled`. That is how a
postcondition such as `total <= 100_000.0` is proved for a bounded column with
a row cap, and why it is not proved without the cap.

## The statement, line by line

```lean
theorem floatSumCR_mem {cs : List Int} {N : Nat} {lo hi : Int} (hne : cs ≠ []) (hN : cs.length ≤ N)
    (h32 : N ≤ 2 ^ 32) (hlo : lo.natAbs ≤ 2 ^ 1474) (hhi : hi.natAbs ≤ 2 ^ 1474)
    (hb : ∀ c ∈ cs, lo ≤ scaled (canon c) ∧ scaled (canon c) ≤ hi) :
    min lo (N * lo) - sumTolScaled N (max lo.natAbs hi.natAbs)
        ≤ scaled (floatSumCR (cs.map .float)) ∧
      scaled (floatSumCR (cs.map .float))
        ≤ max hi (N * hi) + sumTolScaled N (max lo.natAbs hi.natAbs)
```

A double is a code, an integer; `scaled c` is the double's value times 2¹⁰⁷⁴
with its sign, so a bound on doubles becomes a bound on integers the checker
can compute with. 
- `cs`, `hne`: the codes of the doubles summed, and the assumption that there
  is at least one.
- `N`, `hN`, `h32`: a count of at most 2³² that bounds the rows, from
  `sv.max_rows` or the plan's shape (a `LIMIT`, `VALUES`).
- `lo`, `hi`, `hlo`, `hhi`: bounds in scaled units, finite doubles' (below
  2¹⁴⁷⁴).
- `hb`: every value lies between them, after the canonical form of its code
  (`-0.0` is `0.0`).
- The conclusion: the scaled sum, `floatSumCR`, lies between
  `min lo (N·lo)` less the tolerance and `max hi (N·hi)` plus it.

## What it rules out

- A `SUM` that lands above `max hi (N·hi)` plus the tolerance, for values in
  `[lo, hi]` and at most `N` rows: a postcondition `total <= X` is proved
  where `X` is at or above the bound, and not proved where `X` is below it.
- A sum that is not finite, for finite bounded values: `hlo` and `hhi` keep
  the bound far below the largest double.

## What it does not cover

- A sum with no row count: `N` is the count, and with none the tolerance
  bound is not there, though the sign bound is. The report names the cap to
  declare.
- The order of the sum. The reference's `SUM` is order-free; an engine that
  adds in another order is within the plan's bound of it, which
  [`float-bounds.md`](../float-bounds.md) proves over the reals.
- Which tolerance a postcondition states: that is `sv.approx` and
  `sv.equivalent(floats=...)`.

## Its side conditions

`hne` is the group being non-empty (the `SUM` of no rows is NULL). `hN` and
`h32` are the row count the contract states or the plan's shape gives, which the checker checks on the
data on each run. `hlo`, `hhi` and `hb` are the column's
range, a precondition checked on the data. The checker computes `sumTolScaled`
from `N` and the bound.

## Example

```python
import ibis
import sverify as sv
from ibis import _

metrics = ibis.table({"host": "string", "cpu": "float64"}, name="metrics")
CPU = [_.cpu >= 0.0, _.cpu <= 100.0, _.cpu.notnull()]
```

With the range and a row cap, the sum of a group is proved to stay within the
bound, for any data that meets the preconditions:

```python
per_host = metrics.group_by("host").aggregate(total=metrics.cpu.sum())
report = sv.verify(
    per_host,
    requires={"metrics": [*CPU, sv.max_rows(1000)]},
    ensures=[_.total >= 0.0, _.total <= 100_000.0],
)
print(report.verdict)
# proved
```

Without the row cap there is no `N`, and the same postcondition is not
proved:

```python
report = sv.verify(per_host, requires={"metrics": CPU}, ensures=[_.total <= 100_000.0])
print(report.verdict)
# unproved
```
