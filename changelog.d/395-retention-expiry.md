### `arrives_within` lets a source's own retention through

A delete before the watermark no longer rejects the batch when its row is in
a bucket every retiring view has made final: it is the source's own
retention, such as a `FlightSource` floor or a Delta `VACUUM`. The views and
their sinks keep those buckets, and the report counts the expired rows. Lean
proves the result is the full recompute over the rows the source received
(`Retention.expiry_sound`). A delete before the watermark in a bucket that is
still open rejects the batch (#395).
