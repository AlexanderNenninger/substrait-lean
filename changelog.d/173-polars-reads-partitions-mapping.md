### Polars reads partitioned and column-mapped Delta tables from their files

A Delta table with partition columns or column mapping (by name or by id) on Polars is scanned lazily on its streaming engine, as on DuckDB, instead of reaching Polars as an Arrow copy: the partition values from the log are joined on the file path and the files are read by their physical names ([#173](https://github.com/AlexanderNenninger/substrait-lean/issues/173)).
