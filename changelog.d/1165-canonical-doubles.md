### Leaner plans and copy-free tables

- Written plans no longer wrap each double operation in `nanvl(x + 0.0, NaN)`
  for DataFusion. Plans of double arithmetic are about a fifth smaller, and
  Polars runs them up to 5 times faster.
  `Report.to_substrait` still gives other Substrait consumers canonical
  doubles (ST-4).
- `Connection.put` stores a table as given, without copying it.
