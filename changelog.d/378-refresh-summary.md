### One-line refresh summaries

`Refresh.summary()` gives one line per node for the log of a job that
refreshes often, such as "paid: orders@v1→v2, Δ trusted (change feed),
requires checked on 1 row(s) (3 proved from metadata), merge v3: +1 −0"
(#378). `str(refresh)` keeps the full report. A node's line becomes its full
entry when the refresh did something notable (`StageRefresh.notable`): its
first refresh, a source recomputed without a change feed, a schema change
(`SourceRefresh.schema`), or a sink overwriting its table.
