### No more hangs when DuckDB frees a resident table

A refresh could hang for good in `sverify._duckdb.cursor`: opening a cursor
holds the module's lock, and when the garbage collector ran then, a
resident table's finalizer (`forget`) waited on the same lock. The lock is
now reentrant, and `collect` keeps what a finalizer queues while it runs
(`tests/test_duckdb_lock.py`).
