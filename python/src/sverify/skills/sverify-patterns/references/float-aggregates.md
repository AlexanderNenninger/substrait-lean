# Floating point aggregates across engines

Use it when a `SUM` or `AVG` of doubles must give the same answer on DuckDB,
Polars and Spark. Engines add in different orders, so the totals differ in the
last digits.

## The rule

State the tolerance in the contract. A bound on the values and a row cap give
sverify the rounding error it has to allow.

```python
import ibis
from ibis import _

import sverify as sv

m = ibis.table({"sensor": "string", "v": "float64"}, name="m")
totals = m.group_by("sensor").aggregate(total=m.v.sum(), n=m.v.count())
```

In SQL:

```sql
SELECT sensor, sum(v) AS total, count(v) AS n FROM m GROUP BY sensor
```

## The contract

`sv.approx` relaxes a comparison of a column with a number by the
tolerance of the engines' summation orders.

```python
requires = {"m": [_.v.notnull(), _.v.between(-1e6, 1e6), sv.max_rows(10**6)]}
ensures = [_.n >= 0, sv.approx((_.total >= -1e12) & (_.total <= 1e12))]
assert sv.verify(totals, requires=requires, ensures=ensures).verdict == sv.Verdict.PROVED

sql = sv.sql("SELECT sensor, sum(v) AS total, count(v) AS n FROM m GROUP BY sensor", m=m)
assert sv.verify(sql, requires=requires, ensures=ensures).verdict == sv.Verdict.PROVED
```

## Refusals and suggestions

Without a bound on `v` the sum may overflow or be NaN (`+inf` and `-inf`), and
the report lists a domain error:

```python
loose = sv.verify(totals, requires={"m": [_.v.notnull()]}, ensures=[_.n >= 0])
print(loose.verdict)  # unproved
assert loose.verdict != sv.Verdict.PROVED
```

State the bound the hint names (`_.v.between(-1e300, 1e300)`) or tighter.
An exact bound on a total (`_.total >= 0`) holds on one engine and not on another;
write it with `sv.approx`.
