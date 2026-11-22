"""A struct cast pairs fields by name on DuckDB (#2376, fact
`duckdb-struct-cast-by-name`). A verified plan must not give DuckDB a value
other than DuckDB's own: it is refused, or it runs to DuckDB's result.

A list of structs reaches the cast through the list's element-wise branch;
the core's struct kind carries no field names, so a target with the same field
kinds in another order was read as the identity."""

import duckdb
import pyarrow as pa
import pytest

import sverify as sv

TY = pa.list_(pa.struct([("a", pa.int32()), ("b", pa.int16())]))
DATA = pa.table({"l": pa.array([[{"a": 100000, "b": 1}]], type=TY)})
COLS = {"l": "array<struct<a: int32, b: int16>>"}


@pytest.mark.parametrize(
    "target",
    [
        "STRUCT(b SMALLINT, a INTEGER)[]",  # the names swapped, the kinds the same
        "STRUCT(b INTEGER, a SMALLINT)[]",  # 100000 into SMALLINT by name: an error
    ],
)
def test_a_list_of_structs_cast_is_refused_or_duckdbs(target):
    sql = f"SELECT CAST(l AS {target}) AS x FROM t"
    native = duckdb.connect()
    native.register("t", DATA)
    try:
        expected = native.execute(sql).fetchall()
    except duckdb.Error:
        expected = None
    try:
        report = sv.verify(sql, tables={"t": COLS})
    except Exception as e:  # a refusal, naming why
        assert "struct" in str(e)
        return
    if report.issues:
        return
    con = sv.connect()
    con.put("t", DATA)
    if expected is None:
        with pytest.raises(Exception):
            report.run(con, "duckdb")
    else:
        got = report.run(con, "duckdb").column("x").to_pylist()
        assert got == [row[0] for row in expected]
