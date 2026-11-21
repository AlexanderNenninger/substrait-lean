### Shorter, faster range checks in written date SQL

The SQL Sverify writes for `date_trunc` of a date and for a date plus a constant number of days now checks the reference's date range once, on the input: a truncation stays in range, and a constant shift moves the range. On DuckDB, `date_trunc('month', day)` over 5 million rows runs 2.4× faster (0.085 to 0.035 s), and `day + INTERVAL 7 DAY` matches the hand-written query. The results and the errors are the same ([#1608](https://github.com/AlexanderNenninger/substrait-lean/issues/1608)).
