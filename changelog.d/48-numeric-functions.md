### Numeric functions: `sqrt`, logarithms, trigonometry, `sign`, bitwise operations

Ibis's `sqrt`, `exp`, `ln`, `log`, `log2`, `log10`, `sin`, `cos`, `tan`,
`asin`, `acos`, `atan`, `atan2`, `cot`, `degrees`, `radians`, `sign`,
`isinf`, `e` and `pi`, and the bitwise `&`, `|`, `^`, `~` and shifts, are
verified (#48). The functions compute as C's libm does, and contracts treat
their results as doubles. Outside a function's domain (`sqrt` of a negative,
the logarithm of 0, `asin(2)`, `atan2(0, 0)`, a shift by more than 63) the
reference raises a domain error, which `verify` reports unless a filter or
`requires` rules it out: `t.filter(_.x > 0).select(_.x.ln())` is proved.
DuckDB and Polars run them all; Spark runs `sqrt` and the bitwise operations,
Snowflake `&`, `|` and `^`, and both refuse the rest.
