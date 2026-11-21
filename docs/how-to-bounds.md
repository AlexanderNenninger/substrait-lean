# Bounds, row caps and suggested preconditions

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
from sverify.errors import VerificationError
```

## Inferred bounds

An overflow at the declared width is an error, so `amount * 2` on a
`BIGINT` needs a bound on `amount`. Sverify infers it: for each `+`,
`-`, `*` by a constant, negation, `abs` and timestamp truncation that may
leave its range, it works out the range each input column must stay in. By
default the plan is not proved until you declare it, and the report says
where it came from and how to fix it
([why inferred preconditions are errors](reference-semantics.md#errors)):

```python
@sv.transform(requires={"orders": [_.amount >= 0]}, ensures=[_.twice >= 0])
def twice(orders):
    return orders.select(orders.id, twice=orders.amount * 2)

try:
    twice(orders)
except VerificationError as e:
    print(e)
# 1 precondition needed (e.report has the details)
#   needs: (_.amount < 2**62) on orders, inferred from `amount * 2` (overflow otherwise): declare it in requires ...
```

Declare `_.amount < 2**62`, or a tighter bound your data keeps, or filter
the rows out first. A tool that phrases the fix in its own terms (a dbt
test, an editor's quick fix) reads `Report.needs`: one `Needed` per
precondition, with its table, column, comparison, bound, SQL and the
runtime error it rules out. Each postcondition's
`CheckedCondition.reason` says the same of an unproved postcondition, as a
code (`"not_a_key"`, `"may_be_false"`, `"may_be_null"`, …).

`on_inferred` takes four values: `"error"` (the default) needs the bound in
`requires`, `"warn"` assumes it with an `InferredWarning`,
`"ignore"` assumes it without one, and `"off"` infers nothing:

```python
@sv.transform(requires={"orders": [_.amount >= 0]}, ensures=[_.twice >= 0], on_inferred="ignore")
def twice_assumed(orders):
    return orders.select(orders.id, twice=orders.amount * 2)

twice_assumed(orders)
print(twice_assumed.report)
# proved
# The output guarantees:
#   twice ≥ 0
# Each run checks on the data:
#   orders: amount ≥ 0
#   orders: amount < 2**62 (inferred from amount * 2)
# ...
```

An assumed bound is a precondition like the rest. It is checked on the
data at call time and on every refresh, or proved from Delta and Iceberg
file statistics, and refresh reports list it as
`orders: (_.amount < 2**62) (inferred, checked on data)`. Downstream nodes
build on it like on any other precondition of a source.

* The inference is untrusted: Lean proves the contract again with the
  inferred bounds added, so a wrong bound makes the proof fail
  ([analysis/Sverify/Analysis/Infer.lean](../analysis/Sverify/Analysis/Infer.lean)).
* Bounds are rounded inward to round numbers (`3 * 10**18`, `2**62`) and
  timestamps to whole years (`(ts + ibis.interval(days=1)).truncate("M")`
  needs `_.ts < datetime(9999, 1, 1)`). A DATE or TIMESTAMP column lies in
  0001-01-01 to 9999-12-31 by its type, and reading one outside fails
  ([calendar functions](reference-semantics.md#temporal)),
  so a column read needs no bound.
* Other runtime errors get preconditions the same way:

  | Operation | Inferred precondition |
  |---|---|
  | `a // b`, `a % b` | `(_.b != 0)`, `(_.b != 1)` for `a % (b - 1)` |
  | `x.sqrt()`, `x ** 0.5` | `(_.x >= 0.0)` |
  | `x.ln()`, `x.log10()`, `x.log2()` | `(_.x > 0)` |
  | `x.asin()`, `x.acos()` | `(_.x >= -1.0)`, `(_.x <= 1.0)` |
  | `x.cast("int64")` of a double | `(_.x >= -2**63)`, `(_.x < 2**63)` |
  | `a.cast("int32")` | `(_.a >= -2**31)`, `(_.a < 2**31)` |
  | `ibis.literal("ab").repeat(n)` | `(_.n < 2**30)` |
  | `big * 2` of a `DECIMAL(38, 2)` | `(_.big >= -4 * 10**35)`, `(_.big < 5 * 10**35)` |
  | `d + ibis.interval(days=10)` | `(_.d < date(9999, 1, 1))` |

  [test_infer_errors.py](../python/tests/test_infer_errors.py) has these
  cases.
* A product or sum of two unbounded columns has no single weakest bound,
  the value of an aggregate (`SUM`) or window function has none on a
  column, and a value from another contracted transformation is bounded by
  its `ensures`. For these the report's hint suggests a bound
  (`Issue.hint`), and sverify assumes none.
* `on_inferred="off"`, on `@sv.transform` and `sv.verify`, infers and
  assumes nothing: each overflow, a `SUM`'s included, fails the proof, and
  its hint names the bound to state.

For what it does not infer, the report's `hint:` lines name
the bound to add. An integer `SUM` gets the range Lean knows for the column it
adds up and the largest group whose sum then fits 64 bits, or a bound to add
when the column has none:

```python
samples = ibis.table({"host": "string", "ts": "timestamp", "cpu": "int64"}, name="samples")
per_minute = samples.group_by(["host", samples.ts.truncate("m").name("minute")]).aggregate(
    cpu=samples.cpu.sum()
)
print(sv.verify(per_minute))
# ...
# Notes:
#   SUM of `cpu`: the job checks the sum as it runs. To prove it, bound it in `requires` of samples, for example `_.cpu <= 1_000_000_000` and `_.cpu >= -1_000_000_000`; then a row cap in `requires` of samples proves it: ...
```

## Row caps

`sv.max_rows(n)` in `requires` states that an input has at most `n` rows.
Lean carries the caps through the plan
([Rows.lean](../analysis/Sverify/Analysis/Rows.lean)), and an integer `SUM` of values in
`[-m, m]` over at most `n` rows, with `n · m < 2⁶³`, is proved to fit, with
nothing to check on the data:

```python
per_host = samples.group_by("host").aggregate(cpu=samples.cpu.sum())
report = sv.verify(
    per_host, requires={"samples": [_.cpu >= 0, _.cpu <= 100, sv.max_rows(10**12)]}
)
print(report.details())
# requires samples: (_.cpu >= 0)
# requires samples: (_.cpu <= 100)
# requires samples: max_rows(1000000000000)
# semantics: reference
# evidence: duckdb exact, tested at 2.0.0 (facts duckdb-R6; #1985)
# evidence: polars exact, proved by Polars.sum_leaves_i64 on polars's model (facts polars-sum-int)
# evidence: spark shim, proved by Shim.sum_empty_null on spark's model (facts spark-sum-int, spark-exec-parallel)
# known about the output:
#   rows: at most 1,000,000,000,000
# ...
```

* Filters, semi-joins and `DISTINCT` keep at most their input's rows,
  `LIMIT` at most its count, `UNION ALL` adds, and an aggregate without
  `GROUP BY` has one row. A join multiplies, or keeps the left side's rows
  when its condition matches a `unique` key of the right side.
* A cap is checked on the data at call time and on every batch of an
  incremental view, or proved from the record counts of the Delta or Iceberg
  files a source reads.
* In `ensures`, `sv.max_rows(n)` is proved from the inputs' caps.
  `Report.rows` is the cap on the output, under "known about the output".
* The SUM hint names the cap that proves a sum fits.
* A cap also bounds the magnitude of an integer or decimal `SUM`: at most
  `n` values in `[lo, hi]` add up to within `[min(0, n·lo), max(0, n·hi)]`,
  so arithmetic on the sum can be proved to fit.

## Non-overlapping ranges

A point-in-time join to a type-2 dimension keeps the fact table's key only if
the dimension's validity ranges do not overlap. `sv.non_overlapping("valid_from",
"valid_to", by="customer_id")` in `requires` states that: every row has a start,
the end is NULL (an open end, at most one per customer) or not before it, and two
rows of a customer end where or before the other begins. The data check is one
query over the ranges ordered by start; its count is the rows that break it.

```python
facts = ibis.table({"order_id": "!int64", "customer_id": "!int64", "ts": "!int64"}, name="facts")
versions = ibis.table(
    {"customer_id": "!int64", "valid_from": "!int64", "valid_to": "int64", "city": "string"},
    name="versions",
)
during = (
    (facts.customer_id == versions.customer_id)
    & (versions.valid_from <= facts.ts)
    & (versions.valid_to.isnull() | (facts.ts < versions.valid_to))
)
city_of = facts.left_join(versions, during).select(facts.order_id, versions.city)
report = sv.verify(
    city_of,
    requires={
        "facts": [sv.unique("order_id")],
        "versions": [sv.non_overlapping("valid_from", "valid_to", by="customer_id")],
    },
    ensures=[sv.unique("order_id")],
)
assert report.verdict == sv.Verdict.PROVED
```

Lean gives each order at most one version when the join condition equates the
`by` columns, tests `valid_from <= x` and `x < valid_to` (or `valid_to IS NULL OR
x < valid_to`) for one expression `x` of the order's columns; the join keeps the
orders' keys. A closed end (`x <= valid_to`) matches two versions at a
boundary and has no rule. `dbt_utils.mutually_exclusive_ranges` is the same test
in dbt.

## Rows per key

`sv.rows_per("customer", at_most=n)` in `requires` states that at most
`n` rows of an input agree on the columns. A cap on the whole table
bounds every group at once; this bounds each group alone, so a table may
grow without limit while each customer's rows stay few:

```python
sales = ibis.table({"customer": "string", "amount": "int64"}, name="sales")
per_customer = sales.group_by("customer").aggregate(total=sales.amount.sum())
report = sv.verify(
    per_customer,
    requires={"sales": [_.amount >= 0, _.amount <= 10**6, sv.rows_per("customer", at_most=10**12)]},
)
assert not report.assumed and not report.errors
# Each group's sum is at most 10¹² · 10⁶, which fits 64 bits.
```

* Filters, sorts, `LIMIT`, `DISTINCT`, semi-joins, projections and
  `UNION ALL` keep the bounds, and so does a join on a `unique`
  key of its right side. A `unique` key is a bound of 1.
* An aggregate grouping by all of a bound's columns has groups of at most
  that many rows, which bounds its integer and
  decimal `SUM`s.
* `Report.rows` is the bound on the result's rows.
* It is checked on the data at call time (a `GROUP BY` of the columns, with
  NULLs as one key), or proved from a row count of a Delta or Iceberg table
  of at most `n` rows. Incremental views refuse it until batches are checked
  against it.

## Suggested preconditions

An unproved postcondition that compares a value with a constant gets a
suggestion: the precondition on the inputs under which Lean proves it. It
is never assumed, since it changes what the transformation accepts:

```python
items = ibis.table({"id": "int64", "qty": "!int64"}, name="items")
report = sv.verify(
    items.select(items.id, doubled=items.qty * 2),
    requires={"items": [_.qty >= 0]},
    ensures=[_.doubled <= 100],
)
print(report)
# ...
# Not proved:
#   doubled ≤ 100: it may be FALSE on some rows
#     would hold with `(_.qty < 51)` in the requires of 'items'
# ...
```

Sverify proves each suggestion before showing it, by proving the
postcondition again with it added. Each postcondition's `needs` has them as
`Needed` records, for editors and language servers
([test_suggestions.py](../python/tests/test_suggestions.py)).
