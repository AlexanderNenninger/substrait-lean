### Tied windows, `first` and `string_agg` take their keys alone

Under `rows="multiset"` a window node with two or more functions that read
how ties are ordered numbers its rows once, so every function sees one
arrangement (`Rel.Allowed`'s). `first`, `last`, `string_agg` and `collect` sort
by their own keys, without the row ordinal. Spark and Snowflake write plans with
tied windows and `LIMIT`s that they refused, and `rows="sequence"` is the only
observation they still refuse. Where an engine's runner leaves ties open (`ProfilePlugin.rows`, Spark and
Snowflake), a margin check above a `LIMIT` or a window that reads the order of
ties is refused before the run, since the check and the run would each pick
their own rows; `reproducible=`, a total sort key or `on_inferred="warn"` lift
it. DuckDB writes both statements with the row ordinal and is not affected
([#1608](https://github.com/AlexanderNenninger/substrait-lean/issues/1608)).
