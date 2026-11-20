### Refused: a sample of a series, and a percent limit

`TABLESAMPLE` on `range()` or `generate_series()` and `LIMIT n PERCENT` or `WITH TIES` are refused; the percent limit was read as a row count (#321).
