### Casts of rounded aggregates keep their bounds

With a row cap (`sv.max_rows`), a cast of a `SUM` or `AVG` of doubles keeps
the aggregate's proved error bound (#85, #223). `CAST(AVG(cpu) AS BIGINT)` of
`cpu` in `[0, 100]` is in `[0, 100]`, and `verify` no longer reports that the
cast may fail, nor a cast to a decimal that the bound keeps within its
precision. A `SUM` of integers cast to doubles carries each conversion's
rounding in its bounds.
