# Time buckets: bounded state

A node that aggregates by a time bucket keeps a row per bucket and group, so
its state grows with every hour it has seen. A bound on how late rows arrive
lets sverify drop the buckets no later batch can change:

```python
from datetime import datetime, timedelta

import pyarrow as pa
import sverify as sv
from deltalake import write_deltalake
from ibis import _
from sverify.io import DeltaSink, DeltaSource

start = datetime(2026, 11, 3)
write_deltalake(
    "lake/samples",
    pa.table({
        "host": ["a", "b"] * 30,
        "ts": [start + timedelta(minutes=10 * (k // 2)) for k in range(60)],
        "cpu": list(range(60)),
    }),
    configuration={"delta.enableChangeDataFeed": "true"},
)


@sv.transform(
    requires={"samples": [
        sv.arrives_within("ts", "PT2H"),
        _.ts >= datetime(2000, 1, 1), _.ts < datetime(2100, 1, 1),
    ]}
)
def hourly(samples):
    return samples.group_by(["host", samples.ts.truncate("h").name("hour")]).aggregate(
        n=samples.count(), peak=samples.cpu.max()
    )


rollup = DeltaSource("lake/samples").pipe(hourly).write(DeltaSink("lake/hourly"))
print(rollup.refresh())  # samples until 4:50, so the hours before 2:00 are final
# hourly:
# ...
#   retention hourly.hour: 3 bucket(s) open (bound 3), 2 retired, 6 state row(s); watermark 2026-11-03 02:50:00
```

- `arrives_within("ts", "PT2H")` says every row a batch inserts has `ts` at
  or after the watermark: the largest `ts` seen before the batch, minus two
  hours. The first refresh checks that `ts` has no NULLs; every later batch
  is checked at refresh, and a late row rejects the batch with
  `PreconditionError`, so nothing is applied.
- A delete before the watermark is an expiry, the source's own retention (a
  `FlightSource` floor, a Delta `VACUUM` of old partitions), when its row is
  in a final bucket of every view that drops buckets of `ts`. The views and
  their sinks keep those buckets as they were, and the report counts the
  expired rows. Lean proves that the final buckets in the sink and the open
  ones in the state are then a full recompute over every row the source
  received, less the deletes at or after the watermark (see [proved-theorems.md](proved-theorems.md)).
  A delete before the watermark in a bucket that
  is still open rejects the batch. With no view that drops buckets of `ts`,
  every delete is applied as it is.
- A bucket that ends at or before the watermark is final. Lean proves that
  no admissible batch changes a final bucket, for every measure, so the
  final buckets kept in the sink and the open ones in the state add up to a
  full recompute (see [proved-theorems.md](proved-theorems.md)).
- After the sink has written a refresh, the node drops the final buckets
  from its state. At most `⌈lateness / width⌉ + 1` buckets stay open,
  so the state holds that many rows per group.
  The refresh report gives the open and retired buckets, the bound and the
  watermark (`RetentionReport`).
- The bucket is `ts.truncate(unit)` to a second, minute, hour or day, or
  `ts.bucket(...)` with a constant interval of days or less, of a timestamp
  column of the source, under filters and projections that read only their
  own row. Calendar units (weeks, months) and time zones other than UTC for
  hours and days keep every bucket, and the report says why.
- Retention needs a sink that keeps what the state drops: `DeltaSink` does.
  A custom sink that does sets `keeps_retired = True`. With a sink that may rewrite its whole table, such
  as `sink_from`, the node keeps every bucket. A node without a sink holds
  only its open buckets.
- A restarted job resumes from the sink with every bucket, takes the
  watermark from the source's largest `ts`, and drops the final buckets at
  the end of its first refresh.

The refresh still recomputes the aggregate from the source and keeps the
buckets after the last one retired. Windows over time with bounded frames
and interval joins keep every bucket; bounded state for them is tracked in
[an issue](https://github.com/AlexanderNenninger/substrait-lean/issues/294).
