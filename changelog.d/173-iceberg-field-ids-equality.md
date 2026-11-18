### DuckDB reads renamed Iceberg columns and equality deletes natively

An Iceberg table's Parquet files are read by field id, so a column renamed since a file was written is found without passing the table through Python. Equality deletes (which pyiceberg cannot read) apply to the data files written before them, NULL matching NULL, for local Parquet files of tables without partition fields ([#173](https://github.com/AlexanderNenninger/substrait-lean/issues/173)).
