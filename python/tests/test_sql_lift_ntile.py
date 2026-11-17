"""SQL `NTILE(k)` through sverify's own lift (#1509): the lift writes the
model's `ntile`, the SQL standard's buckets, as the Ibis producer does. A plan
with it is proved, and it runs on DuckDB and Polars as DuckDB's own `NTILE`."""

import duckdb
import ibis
import pyarrow as pa
import pytest

import sverify as sv

pytestmark = pytest.mark.backend("duckdb")

#: Distinct sort keys, so the buckets are determined: ten rows in two partitions
#: of unequal sizes, a partition of one row, `n % k != 0` and `n < k`.
ROWS = [(i, "a" if i < 7 else "b" if i < 10 else "c") for i in range(11)]
SCHEMA = ibis.schema({"o": "!int64", "p": "!string"})
QUERIES = [
    f"SELECT o, ntile({k}) OVER ({part} ORDER BY o) AS n FROM t"
    for k in (1, 2, 3, 4, 20)
    for part in ("", "PARTITION BY p")
]


def _table() -> pa.Table:
    return pa.table({"o": pa.array([r[0] for r in ROWS]), "p": pa.array([r[1] for r in ROWS])})


@pytest.mark.parametrize("query", QUERIES)
def test_ntile_is_proved_and_runs_as_duckdbs_on_duckdb_and_polars(query):
    report = sv.verify(query, tables={"t": SCHEMA})
    assert report.proved, report
    arrow = _table()
    own = duckdb.connect()
    own.register("t", arrow)
    expected = own.sql(f"{query} ORDER BY o").fetchall()
    for engine in ("duckdb", "polars"):
        con = sv.connect()
        con.put("t", arrow)
        out = report.run(con, engine)
        got = zip(out.column("o").to_pylist(), out.column("n").to_pylist(), strict=True)
        assert sorted(got) == expected
