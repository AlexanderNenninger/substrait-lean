# Gap filling: the last observation carried forward

Use it to fill the NULLs of a series with the last value before them.

## The rule

`last_value(... IGNORE NULLS)` is not in the plan language. The same result takes
two steps: the time of the latest reading up to each row, then a join back to
that reading.

```python
import ibis
from ibis import _

import sverify as sv

readings = ibis.table({"sensor": "string", "ts": "int64", "v": "int64"}, name="readings")
upto = ibis.window(group_by=readings.sensor, order_by=readings.ts, rows=(None, 0))
marked = readings.mutate(src=ibis.ifelse(readings.v.notnull(), readings.ts, None).max().over(upto))
values = readings.select("sensor", src="ts", got="v")
filled = marked.join(values, ["sensor", "src"], how="left").select("sensor", "ts", filled="got")
```

## The contract

A filled value is NULL (no reading yet) or in the range of the readings.

```python
requires = {
    "readings": [
        _.sensor.notnull(),
        _.ts.notnull(),
        _.v.between(0, 10**6),
        sv.unique("sensor", "ts"),
    ]
}
ensures = [_.filled.isnull() | _.filled.between(0, 10**6)]
assert sv.verify(filled, requires=requires, ensures=ensures).verdict == sv.Verdict.PROVED
assert (
    sv.verify(filled, requires=requires, ensures=[sv.unique("sensor", "ts")]).verdict
    == sv.Verdict.PROVED
)
```

## Refusals and suggestions

- `readings.v.last(include_null=False)` plans a value the proof reads as any
  type. Use the two-step form.
- A series with missing timestamps needs the missing rows first: join a calendar
  of the expected timestamps to the readings, then fill.
