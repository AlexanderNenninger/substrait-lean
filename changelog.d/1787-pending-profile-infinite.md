### A pending engine profile keeps the reference's ±∞ precondition

`verify(semantics="polars")` (or Spark's), whose report is the reference's
until the engine has a report of its own, dropped the reference's
precondition that no double overflows to ±∞ while labelling the report
`"reference"`. It now keeps it, as the reference's report does. Only
`semantics="duckdb"`, DuckDB's SQL lift, treats ±∞ as the value (#575).
