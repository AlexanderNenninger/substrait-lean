# Counters and time-weighted averages

Use it for the increase of a counter that resets (bytes, requests), and for
the mean of a value that holds between readings.

## The rule

A counter's increase is the difference to the previous reading, or the reading
itself after a reset.

```python
import ibis
from ibis import _

import sverify as sv

counters = ibis.table({"sensor": "string", "ts": "int64", "c": "int64"}, name="counters")
w = ibis.window(group_by=counters.sensor, order_by=counters.ts)
p = counters.mutate(prev=counters.c.lag().over(w))
p = p.mutate(reset=p.c < p.prev)
increase = p.mutate(inc=ibis.ifelse(p.prev.isnull(), 0, ibis.ifelse(p.reset, p.c, p.c - p.prev)))
```

A time-weighted mean weights each value by the time until the next reading.

```python
g = ibis.table({"sensor": "string", "ts": "int64", "v": "float64"}, name="g")
gw = ibis.window(group_by=g.sensor, order_by=g.ts)
t = g.mutate(dt=g.ts.lead().over(gw) - g.ts)
t = t.filter(t.dt.notnull())
twa = t.group_by("sensor").aggregate(num=(t.v * t.dt).sum(), den=t.dt.sum())
```

## The contract

The increase is bounded, with no overflow. Its sign is unproved: the proof does
not narrow `c - prev` by the branch condition `c >= prev`.

```python
requires = {
    "counters": [
        _.sensor.notnull(),
        _.ts.notnull(),
        _.c.notnull(),
        _.c >= 0,
        _.c < 2**40,
        sv.unique("sensor", "ts"),
    ]
}
report = sv.verify(increase, requires=requires, ensures=[_.inc.between(-(2**41), 2**41)])
assert report.verdict == sv.Verdict.PROVED
```

The weights of the mean are positive where there are any, so the division by
`den` needs the guard:

```python
requires = {
    "g": [
        _.sensor.notnull(),
        _.ts.notnull(),
        _.v.notnull(),
        _.v.between(-1e6, 1e6),
        _.ts >= 0,
        _.ts < 2**40,
        sv.unique("sensor", "ts"),
        sv.max_rows(10**6),
    ]
}
report = sv.verify(twa, requires=requires, ensures=[_.den.isnull() | (_.den > 0)])
assert report.verdict == sv.Verdict.PROVED
```

## Refusals and suggestions

- `inc >= 0` is unproved. Check it on the data, or clip the difference when a
  negative one is a data error.
- The mean is `num / den`. Divide only where `den > 0`, or sverify lists a division
  by zero.
