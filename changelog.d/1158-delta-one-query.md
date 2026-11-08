### One delta query per batch

- An incrementally maintained view runs its delta plan as one query per
  batch on every engine. The checker used to split it into union-free terms,
  one query each, for DataFusion's Substrait consumer: a 2-table join ran 3
  queries a batch and a 3-table join 7. Batches of the 3-table join now take
  about half the time on DuckDB and Polars.
  `sverify.engines.delta_plans` returns a one-item list.
