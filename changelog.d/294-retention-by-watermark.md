### Bounded state for time buckets: `arrives_within` and retention by watermark

`sv.arrives_within("ts", hours=2)` in `requires` bounds how late a source's
rows arrive. It is checked on every batch at refresh: a row before the
watermark (the largest `ts` seen minus the lateness), or a NULL, rejects the
batch. A node that aggregates by `ts.truncate(...)` or `ts.bucket(...)` then
drops the buckets that end at or before the watermark from its state once its
sink has written them, and keeps at most `⌈lateness / width⌉ + 1` open. Lean
proves that a final bucket's delta is empty for every admissible batch and the
bound (`SubstraitLean/Retention.lean`). The refresh report gives the open and
retired buckets and the bound. `DeltaSink` keeps the retired buckets
(`Sink.keeps_retired`); with other sinks the node keeps every bucket (#294).
