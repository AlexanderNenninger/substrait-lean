### Spark reads Delta and Iceberg tables from their files

A plan run on Spark reads a local Delta or Iceberg source as the Parquet files of its version, with the session's own reader, instead of receiving an Arrow copy of the table through `createDataFrame`. Deletion vectors, position and equality deletes and renamed Iceberg columns are applied as on DuckDB and Polars, and classic and Spark Connect sessions both work ([#173](https://github.com/AlexanderNenninger/substrait-lean/issues/173)).
