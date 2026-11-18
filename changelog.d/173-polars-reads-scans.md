### Polars reads Delta and Iceberg tables from their files

A pipeline on Polars holds a local Delta or Iceberg source as the Parquet files of its version, and Polars scans them lazily on its streaming engine instead of receiving an Arrow copy of the table. Deletion vectors, position and equality deletes and renamed Iceberg columns are applied as on DuckDB, and a file column whose type does not widen to the table's raises ([#173](https://github.com/AlexanderNenninger/substrait-lean/issues/173)).
