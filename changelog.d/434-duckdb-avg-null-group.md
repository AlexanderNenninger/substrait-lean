### Fixed: `avg` of a nullable integer under `semantics="duckdb"`

An `avg` of an integer column that may be NULL failed its proof with
"division by zero", because DuckDB's `avg` is lifted as the sum divided by
the count, and the count of a group whose values are all NULL is 0. The lift
now states that such a group's average is NULL, as DuckDB returns it, so
nothing can fail (#434).
