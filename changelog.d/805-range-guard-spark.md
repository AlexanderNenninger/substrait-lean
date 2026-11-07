### Spark and Snowflake run the RANGE frame guard

The guard the SQL lift writes on a `RANGE` frame with offsets over an integer
key, whose bounds DuckDB computes in the key's type
([#805](https://github.com/AlexanderNenninger/substrait-lean/issues/805)),
runs on Spark and Snowflake as well as DuckDB. Every such frame was refused
there. The date guards of `make_date` of columns
([#809](https://github.com/AlexanderNenninger/substrait-lean/issues/809))
stay DuckDB's, and their refusal says why: Spark's SQL of them exhausts its
JVM's heap, Snowflake's grows to 208 MB.
