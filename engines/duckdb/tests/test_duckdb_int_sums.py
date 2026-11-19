"""DuckDB's `SUM` and `AVG` of integer-valued doubles are exact (D35,
amended 2026-11-19): with one thread and four, over constant runs and
lengths around the vector size (`_int_sums.py`)."""

import duckdb
import pyarrow as pa
import pytest

from _int_sums import cases, check

CASES = cases()


@pytest.mark.parametrize("threads", [1, 4])
@pytest.mark.parametrize(("name", "values"), CASES, ids=[n for n, _ in CASES])
def test_sum_and_mean_are_exact(name, values, threads):
    con = duckdb.connect()
    con.execute(f"SET threads={threads}")
    con.register("src", pa.table({"x": pa.array([float(v) for v in values], pa.float64())}))
    con.execute("CREATE TABLE t AS SELECT x FROM src")
    total, mean = con.sql("SELECT sum(x), avg(x) FROM t").fetchall()[0]
    check(values, total, mean)
    # A constant run stored as one value: DuckDB's `fl(k · x)` (SCALED_CONSTANT).
    if name.startswith("constant"):
        n = len(values)
        total, mean = con.sql(
            f"SELECT sum(7.0::DOUBLE), avg(7.0::DOUBLE) FROM range({n})"
        ).fetchall()[0]
        check(values, total, mean)
