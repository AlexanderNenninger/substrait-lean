"""`replace(s, '', r)` (#1508, D44): an empty pattern matches nowhere, so the
result is `s` (NULL for a NULL `r`), as DuckDB's. Both frontends accept it
under both semantics, and every route gives what DuckDB's own SQL gives."""

import duckdb
import ibis
import pyarrow as pa
import pytest

import sverify as sv

pytestmark = pytest.mark.backend("duckdb")

SCHEMA = ibis.schema({"s": "string"})
ROWS = pa.table({"s": pa.array(["ab", "b", "", None])})
SQL = "SELECT replace(s, '', {r}) AS r FROM t"


def _duckdbs_own(query: str) -> list:
    own = duckdb.connect()
    own.register("t", ROWS)
    return [row[0] for row in own.sql(query).fetchall()]


@pytest.mark.parametrize("r", ["'x'", "''", "NULL"])
@pytest.mark.parametrize("semantics", ["duckdb", "reference"])
@pytest.mark.parametrize("engine", ["duckdb", "polars"])
def test_sql_gives_duckdbs_value_on_every_route(r, semantics, engine):
    query = SQL.format(r=r)
    report = sv.verify(query, tables={"t": SCHEMA}, semantics=semantics)
    assert report.proved, report
    con = sv.connect()
    con.put("t", ROWS)
    expected = _duckdbs_own(query)
    assert report.run(con, engine).column("r").to_pylist() == expected
    assert expected == ([None] * 4 if r == "NULL" else ["ab", "b", "", None])


@pytest.mark.parametrize("engine", ["duckdb", "polars"])
def test_ibis_gives_duckdbs_value_on_every_route(engine):
    con = sv.connect()
    con.put("t", ROWS)
    t = con.table("t")
    report = sv.verify(t.select(r=t.s.replace("", "x")))
    assert report.proved, report
    assert report.run(con, engine).column("r").to_pylist() == ["ab", "b", "", None]
