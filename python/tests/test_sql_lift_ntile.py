"""SQL `NTILE(k)` through sverify's own lift (#1509): the lift writes the
model's `ntile`, the SQL standard's buckets, as the Ibis producer does. A plan
with it is proved, and it runs on DuckDB and Polars as DuckDB's own `NTILE`."""

import duckdb
import ibis
import pyarrow as pa
import pytest

import sverify as sv
from sverify.routes import RouteError

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
@pytest.mark.parametrize("semantics", [None, "duckdb"])
def test_ntile_is_proved_and_runs_as_duckdbs_on_duckdb_and_polars(query, semantics):
    report = sv.verify(query, tables={"t": SCHEMA}, semantics=semantics)
    assert report.verdict == sv.Verdict.PROVED, report
    arrow = _table()
    own = duckdb.connect()
    own.register("t", arrow)
    expected = own.sql(f"{query} ORDER BY o").fetchall()
    # A partitioned plan verified under DuckDB's semantics does not transfer to
    # Polars: `rel.keys`'s zero_sign is ONE_ZERO on DuckDB and IEEE on Polars.
    for engine in ("duckdb", "polars"):
        con = sv.connect()
        con.put("t", arrow)
        if semantics == "duckdb" and engine == "polars" and "PARTITION" in query:
            with pytest.raises(RouteError, match="zero_sign"):
                report.run(con, engine)
            continue
        out = report.run(con, engine)
        got = zip(out.column("o").to_pylist(), out.column("n").to_pylist(), strict=True)
        assert sorted(got) == expected
