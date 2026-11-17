"""`replace(s, '', r)` (#1508): the model's `replace` puts `r` around every
character (Rust, Polars), DuckDB's returns `s` (duckdb-replace-empty-pattern).
The reference refuses a constant empty pattern; `semantics="duckdb"` lifts it
to DuckDB's value, so every route gives what DuckDB's own SQL gives."""

import duckdb
import ibis
import pyarrow as pa
import pytest

import sverify as sv
from sverify.errors import UnsupportedError
from sverify.sql_lift import lift

pytestmark = pytest.mark.backend("duckdb")

SCHEMA = ibis.schema({"s": "string"})
ROWS = pa.table({"s": pa.array(["ab", "b", "", None])})
SQL = "SELECT replace(s, '', {r}) AS r FROM t"


def test_the_reference_refuses_a_constant_empty_pattern_and_names_the_values():
    shown = "empty pattern.*DuckDB returns the string unchanged"
    with pytest.raises(UnsupportedError, match=shown):
        lift(SQL.format(r="'x'"), {"t": SCHEMA}, "reference")
    with pytest.raises(UnsupportedError, match="empty pattern"):
        sv.verify(SQL.format(r="'x'"), tables={"t": SCHEMA}, semantics="reference")


def test_the_ibis_producer_refuses_a_constant_empty_pattern():
    t = ibis.table(SCHEMA, name="t")
    with pytest.raises(UnsupportedError, match="empty pattern"):
        sv.verify(t.select(r=t.s.replace("", "x")))


@pytest.mark.parametrize("r", ["'x'", "NULL"])
@pytest.mark.parametrize("engine", ["duckdb", "polars"])
def test_duckdb_semantics_gives_duckdbs_value_on_every_route(r, engine):
    query = SQL.format(r=r)
    report = sv.verify(query, tables={"t": SCHEMA}, semantics="duckdb")
    assert report.proved, report
    con = sv.connect()
    con.put("t", ROWS)
    own = duckdb.connect()
    own.register("t", ROWS)
    expected = [row[0] for row in own.sql(query).fetchall()]
    assert report.run(con, engine).column("r").to_pylist() == expected
    assert expected == ([None] * 4 if r == "NULL" else ["ab", "b", "", None])
