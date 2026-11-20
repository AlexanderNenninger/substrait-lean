### Dates and times: more Ibis constructs

Ibis `date_bin`/`delta` of literal timestamps (#1924), a date part such as
`iso_year` of a constant date (#1927), a date or timestamp moved by a column's
count of months or years (#1925, the day cut to the month's length, as DuckDB
does) and `ibis.timestamp(y, m, d, h, mi, s)` of integer columns (#1928, with
DuckDB's ranges for the time) are read.

### Ibis `unnest(keep_empty=True)`

An empty or NULL list gives one row with a NULL element (#1917), as DuckDB,
Polars and Spark's `explode_outer` do. `unnest(offset=)` stays refused.

### SQL lift: GROUP BY ALL, QUALIFY and strftime

`GROUP BY ALL` groups by the select items without an aggregate, `QUALIFY`
filters a window column, and `strftime(ts, fmt)` with a constant format of
`%Y %m %d %H %M %S %j %%` is read (#1991, #319). `current_date` and `now()`
stay refused, naming the function; pass the date in as a column or a constant.
