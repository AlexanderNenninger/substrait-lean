### `inf - inf` and `0 * inf` are NaN under `semantics="duckdb"`

With DuckDB's semantics, `+`, `-` and `*` of doubles now lift to what DuckDB
computes: NaN for `inf - inf`, `-inf + inf` and `0 * inf`, as `/` already
gave for `inf / inf` and `0 / 0`. Lean's generated lift table states them
exactly (`DuckFn.addDouble`, `subDouble`, `mulDouble`), so the plan Lean writes
back runs on DuckDB and gives NaN too, where it used to raise "domain error".
The reference semantics still raises there (#257).
