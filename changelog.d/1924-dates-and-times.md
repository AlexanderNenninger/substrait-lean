### Dates and times: more Ibis constructs

Ibis `date_bin`/`delta` of literal timestamps (#1924), a date part such as
`iso_year` of a constant date (#1927), a date or timestamp moved by a column's
count of months or years (#1925, the day cut to the month's length, as DuckDB
does) and `ibis.timestamp(y, m, d, h, mi, s)` of integer columns (#1928, with
DuckDB's ranges for the time) are read.
