### The SQL lift reads dates and timestamps

The SQL lift now reads dates and timestamps (#240): `EXTRACT`, `date_part`,
`year()` and its kin, `DATE - DATE`, `datediff('day', …)`, `date_trunc` of
a date, and a date or timestamp plus or minus a constant interval. Adding
months clamps to the month's last day, as in DuckDB. DuckDB types
`DATE ± INTERVAL` and `date_trunc` of a date as TIMESTAMPs. They compare
exactly with dates, but as an output column or next to a timestamp column
they need a cast of a date column to a timestamp the model lacks yet, and
are refused.
