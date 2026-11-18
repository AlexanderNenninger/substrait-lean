"""The engines the engine tests run on.

The engine tests (`test_reference.py`, `test_retention.py`,
`test_touched.py`, `test_sort_directions.py`, `test_usability_655.py`) run on
every engine with a profile: DuckDB, Polars and Spark (#740). A Spark table
has no row order; the written SQL leaves ties and the rows of a `FETCH` open,
as the reference does, so the tests run there too (#1608).
"""

#: The engines with a profile.
PROFILED = ("duckdb", "polars", "spark")
