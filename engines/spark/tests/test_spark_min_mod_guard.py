"""The lens's `MIN % -1` guard runs on Spark (#2058): the lifted `a % b` under
`semantics="duckdb"` stops at `(MIN, -1)` with the guard's message, as DuckDB
does, and `(5, 0)` still raises the division by zero."""

import pyarrow as pa
import pytest

from sverify.engine import connect, put_table, substrait_json, written_plan
from sverify.sql import to_sql
from sverify_spark.dialect import SPARK

pytestmark = pytest.mark.backend("spark")


@pytest.mark.parametrize("width", [pa.int64(), pa.int32()], ids=str)
def test_the_lens_remainder_guard_raises_on_spark(width):
    import json

    from spark_session import put_tables, query

    low = -(2 ** (width.bit_width - 1))

    def run(rows):
        table = pa.table({k: pa.array([r[i] for r in rows], width) for i, k in enumerate("ab")})
        con = connect()
        put_table(con, "r", table)
        put_tables({"r": table})
        plan = json.loads(written_plan(substrait_json(con, "SELECT a % b AS m FROM r", "duckdb")))
        return query(to_sql(plan, SPARK))

    with pytest.raises(Exception, match=r"MIN % -1"):
        run([(5, 2), (low, -1), (7, 2)])
    with pytest.raises(Exception, match=r"(?i)zero|divide"):
        run([(5, 0), (7, 2)])
    assert run([(5, 2), (-7, 2), (low + 1, -1), (None, 3), (4, None)]) == [
        (1,),
        (-1,),
        (0,),
        (None,),
        (None,),
    ]
