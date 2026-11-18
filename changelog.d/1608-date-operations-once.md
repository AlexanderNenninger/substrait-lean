### Date and time operations compute their operand once

The range guards of a date or timestamp operation (`day + INTERVAL 7 DAY`,
`date_trunc('month', day)`, `date_part`) repeated the operand's SQL, and the
`DATE` as `TIMESTAMP` guard nested them. A projection of date and time
operations over columns now computes each operand once in a layer below it:
`day + INTERVAL 7 DAY` writes 1,326 characters instead of 3,227 and
`date_trunc('month', day)` 1,366 instead of 3,387, and on 10 million days in DuckDB they run in 0.08 s
instead of 0.12 s and 0.41 s instead of 0.69 s
([#1608](https://github.com/AlexanderNenninger/substrait-lean/issues/1608)).
