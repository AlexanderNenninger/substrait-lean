"""The engines the engine tests run on, and what Spark cannot run yet.

The engine tests (`test_reference.py`, `test_retention.py`,
`test_touched.py`, `test_sort_directions.py`, `test_usability_655.py`) run on
every engine with a profile: DuckDB, Polars and Spark (#740). A Spark table
has no row order, so `sverify_spark.dialect` refuses what follows the
reference's list order over a named table: a sort with ties left open, a
window, a `FETCH`. (A `SUM` or `AVG` of doubles runs natively since D25,
#917.) Those tests are expected to fail on Spark, strictly, so the day the
writer runs them they fail until their mark is dropped.
"""

import pytest

#: Spark refuses a plan that follows the list order over a named table.
NO_ROW_ORDER = pytest.mark.xfail(
    strict=True,
    reason="Spark tables have no row order: sorts with open ties, windows and FETCH over a "
    "named table are refused (sverify_spark.dialect.row_ordinal)",
)

#: The engines with a profile, Spark's runs expected to work.
PROFILED = ("duckdb", "polars", "spark")

#: The same, with Spark expected to refuse for want of a row order.
PROFILED_ORDERED = ("duckdb", "polars", pytest.param("spark", marks=NO_ROW_ORDER))
