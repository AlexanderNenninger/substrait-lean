### Casts of booleans to numbers, and of lists

- `CAST(b AS INT)` and `CAST(b AS DOUBLE)` of a boolean are 1, 0 or NULL, so
  `b.cast("int64").sum()` counts the trues
  ([#1911](https://github.com/AlexanderNenninger/substrait-lean/issues/1911)).
- A list casts element by element, `transform(l, x -> CAST(x AS t))`. Polars runs it;
  the SQL engines refuse the lambda until
  [#348](https://github.com/AlexanderNenninger/substrait-lean/issues/348). A cast of a
  struct is refused by design: sverify cannot build a struct
  ([#1919](https://github.com/AlexanderNenninger/substrait-lean/issues/1919), ruling 186).
