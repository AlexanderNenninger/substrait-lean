### Polars computes `replace`, `reverse`, `ascii`, `repeat` and `LIKE` natively

On Polars, `replace` with a literal pattern, `reverse`, `ascii`, `repeat`,
and `LIKE`/`ILIKE` with a literal pattern run as Polars expressions where they
called Python per row ([#1270](https://github.com/AlexanderNenninger/substrait-lean/issues/1270)).
The values are the same. On a million rows they take 1 to 29 ms, down from
97 to 184 ms. A pattern per row still takes the old path.
