### `Report.needs` is the one name; result and IO dataclasses are keyword-only

Breaking. `Report.needed`, `Report.needed_text` and `Report.needed_conditions`
are removed: read `Report.needs` (`Needed.label`, `.text`, `.condition`). The
old names of `Report`'s internal fields (`depends`, `epsilon`, `transfer` and
the 28 others) and `Report.plan` (`Report.internal_plan`) no longer read with
a `DeprecationWarning`; 1.0 keeps no alias
([#2081](https://github.com/AlexanderNenninger/substrait-lean/issues/2081)).

`Report`, `Contract`, `Batch`, `Snapshot`, `SourceBatch` and `SinkWrite` take
keyword arguments only, so a field added in 1.x breaks no caller. sverify
builds `Report` and `Contract`; a source or sink of your own builds the other
four, by keyword: `Batch(table=rows, cursor=n)`.

`sverify.odcs.UnreadRuleWarning` and `sverify.openlineage.LineageWarning`
derive from `SverifyWarning`, so `warnings.simplefilter("error",
SverifyWarning)` covers every warning sverify gives.

A precondition checked on data with `check_engine=` counts the rows that
break it inside the engine: 8 ms on 5 million rows on DuckDB, where it took
187 ms
([#881](https://github.com/AlexanderNenninger/substrait-lean/issues/881)).
