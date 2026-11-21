### A FLOAT cast to an integer in DuckDB SQL is refused

A DuckDB SQL `CAST(x AS INTEGER)` of a `FLOAT` (REAL) is refused as the cast
of a `DOUBLE` is: DuckDB rounds it to the nearest integer, and the model's cast
truncates. Sverify used to prove the truncated value, 0 for `0.55::FLOAT`
where DuckDB gives 1. The message names spellings that lift, with
`CAST(x AS DOUBLE)` in place of the `FLOAT`
([#2152](https://github.com/AlexanderNenninger/substrait-lean/issues/2152)).
