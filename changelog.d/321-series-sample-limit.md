### Refused: a sample of a series, and a percent limit

`TABLESAMPLE` on `range()` or `generate_series()` is refused. `LIMIT n PERCENT` and `LIMIT … WITH TIES` are refused on every source, tables included: the lift read a percent limit as a row count, a wrong result that tables accepted until now (#321).
