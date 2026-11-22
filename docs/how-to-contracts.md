# Contracts

The examples on this page run in order (`python/tests/test_readme.py`), from this setup:

```python
import ibis
import pyarrow as pa
import sverify as sv
from ibis import _
from sverify.io import Changes, StaticSource

orders = StaticSource(
    pa.table({"id": [1, 2], "customer": ["ada", "bob"], "amount": [30, 5]}), name="orders"
)
orders.apply(Changes(inserts=[(3, "cy", 50)], deletes=[(1, "ada", 30)]))  # now orders holds bob and cy
```

`@sv.transform` decorates a function from Ibis tables to an Ibis table.
Called on a source or another node, it builds a node (and on Ibis tables, an
Ibis expression). Each call proves the postconditions before it returns:

```python
@sv.transform(
    requires={"orders": [_.amount >= 0, _.amount < 1_000_000_000, _.id.notnull()]},
    ensures=[_.doubled >= 0, _.doubled.notnull(), "id IS NOT NULL"],
)
def doubled(orders):
    return orders.filter(orders.amount > 10).select(orders.id, doubled=orders.amount * 2)

expr = doubled(orders)
print(doubled.report)
# proved
# The output guarantees:
#   doubled ≥ 0
#   doubled is never NULL
#   id IS NOT NULL
# Each run checks on the data:
#   orders: amount ≥ 0
#   orders: amount < 1000000000
#   orders: id is never NULL
# Known about the output:
#   id: any integer
#   doubled: an integer in [22, 1999999998]
```

Lean worked out that `doubled` is at least 22: the filter keeps only
`amount > 10`, and doubling preserves that. The bound on `amount` keeps
`amount * 2` within 64 bits, and caps `doubled`; without a bound, the
report names the one the plan needs ([Inferred bounds](how-to-bounds.md#inferred-bounds)). A
postcondition that doesn't follow is refused, with what *is* known:

```python
@sv.transform(requires={"orders": [_.amount >= 0]}, ensures=[_.total > 5])
def plus_one(orders):
    return orders.select(orders.id, total=orders.amount + 1)

from sverify.errors import CompositionError, NotIncrementalError, VerificationError

try:
    plus_one(orders)
except VerificationError as e:
    print(e)
# 1 of 1 postcondition not proved, 1 precondition needed (e.report has the details)
#   ...
#   not proved: (_.total > 5): it may be FALSE on some rows ...
#     would hold with `(_.amount >= 5)` in the requires of 'orders'
```

* Conditions are Ibis expressions (`_.amount >= 0`) or SQL snippets
  (`"amount >= 0"`), whichever language the transformation is in. SQL
  transformations are checked with
  `sv.verify(sql, tables=..., requires=..., ensures=...)`, which returns the
  report; an Ibis condition there reads the query's output, or in `requires`
  its input table.
* `report.run(con)` runs the plan the report checked over the tables of an
  `sv.connect()` connection, on its engine or the one you name
  (`report.run(con, "polars")`). The result is the one the report is about,
  `params` and `semantics` included.
  It first checks the report's preconditions on the tables, the inferred
  ones included, and refuses a batch that breaks one with a
  `PreconditionError` that names it, before anything runs.
  `check_requires=False` skips the check for a caller that has made it
  already; the report's guarantee then holds only on data that meets them:

  ```python
  # skip: a fragment: query and con are the reader's
  report = sv.verify(query, tables={"t": con.table("t")}, ensures=[sv.unique("host")])
  if report.verdict == sv.Verdict.PROVED:
      result = report.run(con)
  ```
* `requires` maps each input to its conditions. A transformation with one
  input also takes a plain list, `requires=[_.amount >= 0]`. A key that
  names no input raises a `ValueError` that lists the inputs.
* Preconditions describe data that comes from outside. On a source, they
  are checked on the data when the node is first refreshed and then on each
  batch (`PreconditionError`), or proved from the table's metadata; on Ibis
  tables bound to data (`sv.connect()`), at call time. The error carries
  the table (`e.source`), the condition as stated or inferred
  (`e.condition`) and up to ten of the rows that break it, as an Arrow
  table (`e.rows`; None for `max_rows` and `rows_per`):

  ```python
  # skip: a fragment: node, log and quarantine are the reader's
  try:
      node.refresh()
  except PreconditionError as e:
      log.error("%s breaks %s", e.source, e.condition)
      quarantine.write(e.rows)
  ```
* Unproved postconditions raise `VerificationError`. With
  `on_unproved="check"` they are checked on the output data instead
  (`PostconditionError`): on bound tables at call time, on a node at every
  refresh (see [Nodes](how-to-nodes.md#nodes-composing-storing-refreshing)). With
  `on_unproved="warn"` you get a warning.
* Every exception sverify raises on purpose derives from
  `sverify.errors.SverifyError`, and keeps its built-in base (`ValueError`,
  `RuntimeError`); import the exceptions from `sverify.errors`.
* What Lean tracks per column: whether it can be NULL, integer, double
  and timestamp ranges, which booleans it can be, and whether it can be a
  string. Filters (`amount > 10`, `x IN (1, 2, 3)`, `x IS NOT NULL`) refine
  those facts; arithmetic, `CASE`, `COALESCE`, joins and `UNION ALL` carry
  them through. Schemas count: a non-nullable column is never NULL.
  `x IN (0, 1)`, and `isin([0, 1])`, of integers that fill a range is
  read as `x BETWEEN 0 AND 1`, so a column known to lie in `[0, 1]` meets
  it.
  `report.output` types the output columns the checker shows are never NULL
  as not nullable (`count(*)` is `!int64`).
* Relations between columns: join and filter conditions such as
  `w1.ts = w0.ts + 60`, `a.ts = b.ts`, `t0 < t1` or `value != -9999` become
  facts about each row, so postconditions like `t1 - t0 == 60` or
  `first_txn < duplicate_txn` follow.
* Conditions kept whole: each precondition and filter condition, of
  any shape, is also a fact about each row, as stated. A postcondition that
  restates one is proved where the plan keeps it: through projections that
  keep its columns (renamed or not), filters, sorts, limits, joins and
  `UNION ALL`s whose inputs all have it. The right side of a left join loses
  it, since its padded rows are NULL. Under a filter or in a `CASE` branch,
  a disjunct that cannot be TRUE drops out, and the rest narrows the columns:
  with `(_.a <= 0) | (_.b < 0)` in `requires`, `t.filter(_.a > 0)` gives
  `b <= -1`, and so does the branch `ifelse(_.a > 0, ..., ...)`. A NULL
  disjunct is not TRUE either, so the columns need not be NOT NULL.
  Implications written `ifelse(_.a > 0, _.b < 0, True)` work the same way.
  Comparisons between columns other than `x - y` against a constant,
  products and facts through aggregates are not facts yet, tracked in
  [an issue](https://github.com/AlexanderNenninger/substrait-lean/issues/597) ([tests](../python/tests/test_relational_preconditions.py)).
* Keys: `sv.unique("user_id", "ts")` says there is at most one row per
  key. In `requires` it is checked on the data; in `ensures` it is proved
  (keys survive filters, projections, aggregates and joins whose condition
  pins down the other side's key). Every Arrow column is nullable, so
  `sv.unique("id")` leaves `id` able to be NULL. `sv.key("id")` is a
  primary key: `sv.unique("id")` and `'"id" IS NOT NULL'`, which the report
  lists in its place.
* Foreign keys: `sv.references("cust", to=customers.id)` in `requires`
  says every non-NULL `cust` occurs in `customers.id` (checked on the data,
  like `unique`). `to` also takes a pair of names, `("customers", "id")`. Nothing proves it in `ensures`, so it stays an assumption.
* Windows: `LAG`, `LEAD` and `ROW_NUMBER` over `PARTITION BY … ORDER BY`.
  If rows can tie in the order, the engine decides which comes first:
  `verify` proves the postconditions that hold for every order of the ties,
  `report.deterministic` is `False`, `str(report)` names the window and
  `report.ties` the key that would close it ([tie order](reference-semantics.md#tie-order-and-determinism)).
  A key on the partition and order columns makes the order total, which
  facts such as `prev_ts < ts` and a rerun that must give the same rows
  need.
* ASOF joins: `sv.asof_join(left, right, on="ts", by="device",
  tolerance=...)` matches each row with the latest earlier row of the other
  table, built from a range join and `ROW_NUMBER` that Lean checks like any
  plan.
* Doubles and time: comparisons with constants are exact, including
  sentinels like `-9999.0`, `isnan()` and intervals; doubles compare as SQL
  engines compare them, with one zero and one NaN above every number.
* Sums and means of doubles round once. Their signs are exact, a mean
  of values in `[0, 100]` is in `[0, 100]`, and with a row cap in
  `requires`, `sv.max_rows(10_000_000)` (checked on the data), a sum of
  values in `[0, 100]` is in `[0, 10⁹]` ([float bounds](float-bounds.md)).
  `sv.approx(_.total <= 1e9)` states a postcondition up to rounding; the
  report suggests it when an exact claim misses only by rounding.
* Strings: a column's strings while they are few (up to 64), from constants,
  `IN` lists, `=` and `<>` filters, `CASE`, `COALESCE` and `UNION ALL`. That
  proves dbt's `accepted_values` and keys over `UNION ALL` branches tagged by
  a constant.
* Not tracked yet: what is inside a string (`LIKE`, lengths), relations beyond
  "column plus constant" (`a < 2 * b`), and counts across rows (so
  `COUNT(*) >= 1` in a group is not known).
