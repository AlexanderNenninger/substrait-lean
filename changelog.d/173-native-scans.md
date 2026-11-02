### Delta and Iceberg tables read natively by DuckDB

On DuckDB, a `DeltaSource` or `IcebergSource` is no longer loaded into
Python. The pipeline holds the Parquet files of the table's version, chosen
by sverify's own pruning (#81, #108), with the rows that deletion vectors or
position delete files remove, and DuckDB reads them with `read_parquet`.
Refreshes keep the table as the files of the new version. Partitioned tables,
Delta column mapping, renamed Iceberg columns, equality deletes, object
stores and the other engines read through Arrow as before.
`scripts/bench_io.py` measures reading, refreshing and writing at scale (#173).
