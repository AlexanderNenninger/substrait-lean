### Struct fields, list elements and lambdas

Ibis's struct fields (`t.s.a`), list elements (`t.l[0]`, a constant index,
negative from the end), `length()` of a list, and `map`, `filter` and
`contains` on lists are verified (#94). A lambda may read only its element
and constants, so `contains(v)` needs a constant `v`. A NULL element matches
only NULL in `contains`. `verify` reports an error in a lambda's body on any
element as the row's. Polars runs them; for DuckDB, see "Lists run on
DuckDB". This also fixes the Ibis producer reading `t.select(a=t.s.a)`
as the table's first column.
