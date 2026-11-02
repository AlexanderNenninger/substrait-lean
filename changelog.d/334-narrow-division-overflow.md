### Integer division overflow at narrow widths

`MIN // -1` at TINYINT, SMALLINT and INTEGER (`-128 // -1` is 128, which a
TINYINT cannot hold) is now reported as an overflow, as it already was for
BIGINT, and the plans sverify writes raise there, as DuckDB does (#334).
Integer division at a narrow width is now checked at that width, like `+`,
`-`, `*` and negation. The sqllogictest replay also sees `verify`'s warnings
for queries that read no table, such as `SELECT 7 // 0` (#333): `verify`
reported those all along, but the replay's check went through
`sverify.sql`, which refuses such queries.
