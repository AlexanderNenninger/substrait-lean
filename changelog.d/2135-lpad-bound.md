### The SQL lift refuses `lpad` and `rpad` past 2^20 characters

`lpad(s, n, p)` and `rpad(s, n, p)` with a constant `n` over 1,048,576 characters are refused, with the reason. The lift writes the fill as a constant of `n` characters, and `lpad('', 1100000000, '😀')` built 4.4 GB of it before DuckDB refused the query at its string limit ([#2135](https://github.com/AlexanderNenninger/substrait-lean/issues/2135)).
