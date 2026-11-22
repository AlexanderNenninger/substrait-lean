"""A struct cast pairs fields by name on DuckDB (#2376, fact
`duckdb-struct-cast-by-name`). A verified plan must not give DuckDB a value
other than DuckDB's own: until the model pairs the fields (ruling 269), the cast is refused.

A list of structs reaches the cast through the list's element-wise branch;
the core's struct kind carries no field names, so a target with the same field
kinds in another order was read as the identity."""

import pyarrow as pa
import pytest

import sverify as sv

TY = pa.list_(pa.struct([("a", pa.int32()), ("b", pa.int16())]))
COLS = {"l": "array<struct<a: int32, b: int16>>"}


@pytest.mark.parametrize(
    "target",
    [
        "STRUCT(b SMALLINT, a INTEGER)[]",  # the names swapped, the kinds the same
        "STRUCT(b INTEGER, a SMALLINT)[]",  # 100000 into SMALLINT by name: an error in DuckDB
    ],
)
def test_a_cast_of_a_list_of_structs_is_refused(target):
    with pytest.raises(Exception, match="casts of structs"):
        sv.verify(f"SELECT CAST(l AS {target}) AS x FROM t", tables={"t": COLS})
