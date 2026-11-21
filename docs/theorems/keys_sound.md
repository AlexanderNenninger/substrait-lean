# `Rel.keys_sound`

A key that Sverify derives for a plan's output holds: no two output rows
agree on those columns.

Lean: `Substrait.Rel.keys_sound`, in
[`analysis/Sverify/Analysis/Keys.lean`](../../analysis/Sverify/Analysis/Keys.lean).
Layer: `eval`, the reference's result for the plan; `Rel.keys_sound_all` is
the same statement for every row order the reference allows. Axioms:
`propext`, `Classical.choice`, `Quot.sound`
([trusted-base.md](../trusted-base.md)).

## What it says

You state a key on an input, say that `id` is unique in `orders`, and a
promise that the output has one too. Sverify follows the key through the
plan: a filter keeps it, a projection keeps it while the columns stay, and a
join keeps the left side's key when each left row has at most one partner.
If the plan loses the key, Sverify does not prove the promise and names
where it went. Every key it does derive holds on the output, for any data
that meets the preconditions.

## The statement, line by line

```lean
theorem Rel.keys_sound {cat : Catalog} (hcat : cat.WF) {A : String → List AVal}
    {F : String → List Fact}
    (hA : ∀ t, ∀ row ∈ (cat t).rows, EnvMem (A t) row)
    (hF : ∀ t, ∀ row ∈ (cat t).rows, FactsHold (F t) row) {K : TableCond}
    (hK : K.Hold cat) {r : Rel} (hwf : r.WF cat) :
    ∀ k ∈ r.keys cat A F K, KeyOn k (r.eval cat)
```

- `cat`, `hcat`: the data, a catalog of tables, and the assumption that it
  is well formed.
- `A`, `hA`: what the checker knows of each table's columns (their types),
  and the assumption that every row of the data fits.
- `F`, `hF`: the facts that follow from the preconditions (a range, a
  column that is never NULL), and the assumption that every row satisfies
  them.
- `K`, `hK`: the table conditions you stated, such as `sv.unique("id")`,
  and the assumption that the data meets them. This is the key the
  derivation starts from.
- `r`, `hwf`: the plan, and the assumption that it is well formed.
- The conclusion: every key `k` in the list `r.keys` the checker derives is
  a key of the plan's result, `KeyOn k (r.eval cat)`: no two rows have the
  same values in the columns of `k`.

## What it rules out

- An output with two rows that share an `id`, in a plan proved to keep
  `unique(id)`.
- A join that repeats a left row, in a plan whose key was kept through the
  join: Sverify keeps it only where the join condition fixes a key of the
  right side.

## What it does not cover

- Equality of values in the sense of SQL `UNIQUE`. Here two NULLs count as
  equal, so a key proved here is stronger than SQL's.
- Data that breaks a stated key. The theorem assumes `hK`; the run checks
  the key on each batch.
- Keys Sverify does not derive. The list is sound and not complete, so a
  plan that is unique for a reason the analysis does not see reports the
  promise as not proved.

## Its side conditions

`hcat` and `hwf` are decided by the checker's well-formedness check.
`hA`, `hF` and `hK` are the contract's schemas, preconditions and table
conditions, checked on the data on each run. The conclusion is what the
report says when it lists a key under "The output guarantees".

## Example

A filter keeps the key of its input:

```python
import ibis
import sverify as sv

orders = ibis.table({"id": "int64", "customer": "string", "amount": "int64"}, name="orders")
customers = ibis.table({"name": "string", "city": "string"}, name="customers")
events = ibis.table({"customer": "string", "kind": "string"}, name="events")

kept = orders.filter(orders.amount > 0)
report = sv.verify(kept, requires={"orders": [sv.unique("id")]}, ensures=[sv.unique("id")])
print(report.verdict)
# proved
```

A join to a table that is unique on the join column keeps it too, because
each order has at most one customer row:

```python
joined = orders.join(customers, orders.customer == customers.name).select(orders.id, customers.city)
report = sv.verify(
    joined,
    requires={"orders": [sv.unique("id")], "customers": [sv.unique("name")]},
    ensures=[sv.unique("id")],
)
print(report.verdict)
# proved
```

A join to a table with no key can repeat an order, so the promise is not
proved, and the report gives rows that break it:

```python
repeated = orders.join(events, orders.customer == events.customer).select(orders.id, events.kind)
report = sv.verify(repeated, requires={"orders": [sv.unique("id")]}, ensures=[sv.unique("id")])
print(report.verdict)
# unproved
print(report)
# NOT proved: 1 of 1 postcondition not proved
# ...
#   no two rows share id: the preconditions do not make it a key: ... a join, a union or an UNNEST can repeat a value
#     counterexample: ...
```
