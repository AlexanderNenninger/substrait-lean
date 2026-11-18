### Tied windows, `first` and `string_agg` take their keys alone

Under `rows="multiset"` a window node with two or more functions that read
how ties are ordered numbers its rows once, so every function sees one
arrangement (`Rel.Allowed`'s). `first`, `last`, `string_agg` and `collect` sort
by their own keys, without the row ordinal. Spark and Snowflake write plans with
tied windows and `LIMIT`s that they refused, and `rows="sequence"` is the only
observation they still refuse. A report that has a margin check above a `LIMIT`
or a window with open rows warns, as it does for an unpinned table
([#1608](https://github.com/AlexanderNenninger/substrait-lean/issues/1608)).
