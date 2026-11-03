### Touched groups read only the touched time range

When one of an aggregate's group keys is a fixed-width time bucket
(`ts.truncate("m")`, `ts.bucket(...)`), recomputing the touched groups reads
the input through the range those buckets cover, so the engine skips the
other rows while it scans. The semi-join on the keys still picks the exact
rows, and a touched NULL bucket reads the whole input.
