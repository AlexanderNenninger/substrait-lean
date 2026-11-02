### Incremental views keep their state in DuckDB

On DuckDB, an incremental view's state no longer lives in Python: DuckDB
holds it between refreshes, and the view's rows are a DuckDB view of it. On
every engine, states and changes are added up by one plan Lean checks (a
union, grouped by every column, with the weights summed), so they group rows
as the model compares them: one NaN, `-0.0` equal to `0.0`, lists by their
elements. Sinks compute their change with the same plan (#173).
