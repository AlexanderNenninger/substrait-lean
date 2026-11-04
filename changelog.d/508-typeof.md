### typeof of a column is a constant

`t.qty.typeof()` now verifies: the Ibis producer folds `typeof` of a column to
DuckDB's name of its type (`BIGINT`, `DECIMAL(10,2)`, `VARCHAR[]`), a string
constant in the plan. `typeof` of an expression, a struct or a map is refused,
since the engine infers that type its own way
([#508](https://github.com/AlexanderNenninger/substrait-lean/issues/508)).
