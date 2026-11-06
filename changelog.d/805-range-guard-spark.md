### Spark runs the lift's guards

The guards the SQL lift writes (`sverify_raise`) run on Spark as well as
DuckDB: a `RANGE` frame with offsets over an integer key, whose bounds DuckDB
computes in the key's type
([#805](https://github.com/AlexanderNenninger/substrait-lean/issues/805)),
and a date from columns (`make_date`, Ibis `ibis.date`,
[#809](https://github.com/AlexanderNenninger/substrait-lean/issues/809)).
Snowflake refuses them with why: its SQL of the date guards grows to 208 MB.
Polars and DataFusion refuse them too.
