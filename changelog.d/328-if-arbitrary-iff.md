### The SQL lift refuses what DuckDB refuses for `if` and `iff`

DuckDB SQL with a two-argument `if(condition, value)` is refused, as DuckDB's binder does; the lift had read it as a `CASE` without `ELSE` (part of [#328](https://github.com/AlexanderNenninger/substrait-lean/issues/328)). `iff`, which DuckDB 2.0 does not have, stays refused as an unknown function. Tests check `if` (also schema-qualified) and `arbitrary` against DuckDB.
