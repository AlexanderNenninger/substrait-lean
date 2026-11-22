# Runtime errors and guards

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

## Runtime errors

The report lists every runtime error that may happen on some input that
meets the preconditions, and `@sv.transform` refuses the transformation
while there is one:

```python
@sv.transform(requires={"orders": [_.amount >= 0]}, on_inferred="off")
def share(orders):
    return orders.select(orders.id, per_unit=orders.amount // (orders.amount - 30))

try:
    share(orders)
except VerificationError as e:
    print(e)
# 1 possible runtime error (e.report has the details)
#   may fail: division by zero: amount // (amount - 30)
#     hint: state `(_.amount != 30)` in the requires of 'orders'
```

Without `on_inferred="off"`, the report names the precondition the plan needs,
`(_.amount != 30)`; declare it in `requires`, and `share` is proved
([Inferred bounds](how-to-bounds.md#inferred-bounds)).

Errors are what an engine fails on: integer division or remainder by zero,
`MIN / -1`, bad `POWER`s, out-of-range casts, regular expressions that may
not compile, and `+`, `-`, `*` leaving their declared width (Polars's own
arithmetic wraps around there; the reference raises). An integer `SUM` leaving 64 bits,
or a decimal `SUM` leaving its precision,
is ruled out where the plan bounds a group's rows (a `VALUES` list, a `FETCH`
count, or a row cap `sv.max_rows(n)` on an input: [Row caps](how-to-bounds.md#row-caps)) and
`requires` bounds the column. Elsewhere sverify assumes the sum fits, and
the job checks it at run time, on the data before the run
(`Report.assumed`; an error with `on_inferred="off"`). The same holds for an
operation on finite doubles that may overflow to `±∞`, which the reference
raises on.

## Guards

Guards are understood where the engine respects them: in a `CASE` branch
or `NULLIF(n, 0)`, and in a filter below a projection. Filter first, then
compute, and the division is proved safe with no precondition:

```python
gcon = sv.connect()
gcon.put("lines", pa.table({"id": [1, 2, 3], "n": [4, 0, 2], "total": [100, 250, 30]}))
lines = gcon.table("lines")
kept = lines.filter(lines.n != 0)
per_line = sv.verify(kept.select(kept.id, per=kept.total // kept.n), requires={"lines": [_.total >= 0]})
print(per_line.run(gcon).to_pylist())
# [{'id': 1, 'per': 25}, {'id': 3, 'per': 15}]
```

A guard inside an `AND` or `OR` protects nothing, since DuckDB and Polars
evaluate both operands ([`AND` and `OR` raise eagerly](reference-semantics.md#null)), and
neither does a guard in one column of a `SELECT` for a division in another.
The report then needs the precondition `n != 0`, and says where the error
sits:

```python
mixed = sv.verify(
    lines.select(lines.id, ok=(lines.n != 0) & (lines.total // lines.n > 1), per=lines.total // lines.n)
)
print(mixed)
# Not proved:
#   (_.total >= -9 * 10**18) and (_.n != 0) on lines, inferred from `total // n` ...
# Notes:
#   `total // n` is inside an AND or OR you wrote (`&` or `|`), and DuckDB and Polars evaluate both operands ...
```

Declared in `requires`, `n != 0` is checked on each batch before the run,
and `run` refuses this batch, whose second row has `n = 0`, with a
`PreconditionError`. Guard the operation itself,
`ibis.cases((_.n != 0, _.total // _.n))`, and no precondition is needed.
A constant subexpression that raises, such as `1 // 0 = 1` in a later
`WHEN`, makes the whole plan raise on any data, since DuckDB evaluates it
while it plans the query.
