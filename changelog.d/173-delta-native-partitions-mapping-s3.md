### DuckDB reads partitioned and column-mapped Delta tables, and Delta tables on S3, where they are

A Delta table's partition values come from its log, and its column mapping (by name or by id) is followed, so DuckDB scans these tables without loading them into Python (#173). Delta tables on S3 are read through DuckDB's `httpfs` with a temporary secret made from the `Storage`; with no explicit key the scan needs DuckDB's `aws` extension, and without it the table reads through Arrow as before.

Also fixed: the Arrow route returned NULL for every column of a column-mapped Delta table, because delta-rs's Arrow reader ignores the mapping. It now reads those tables through delta-rs's DataFusion reader, and their file statistics reach the logical columns.
