"""#322: a decimal cast to an integer or a coarser scale rounds half away from
zero in the DuckDB SQL lift, and the verified plan gives that value on every
engine with a profile (DuckDB natively, Polars by its shim, Spark natively)."""

from decimal import Decimal

import pyarrow as pa
import pytest

import sverify as sv
from _engines import PROFILED
from sverify.engine import connect, put_table

#: Values on and around .5 at scale 3, both signs.
VALUES = ["2.500", "-2.500", "0.500", "-0.500", "2.499", "-2.499", "3.501", "0.000", "999.500"]
QUERY = (
    "SELECT d, CAST(d AS BIGINT) AS i, CAST(d AS DECIMAL(10, 0)) AS w, "
    "CAST(d AS DECIMAL(10, 2)) AS c FROM t"
)


def half_away(v: Decimal, places: int) -> Decimal:
    return v.quantize(Decimal(1).scaleb(-places), rounding="ROUND_HALF_UP")


@pytest.mark.parametrize("engine", PROFILED)
def test_the_rescale_gives_duckdbs_value_on_each_engine(engine):
    # The analysis bounds no rounding yet, so the overflow of a carry (999.5 to 1000) stays
    # possible and the run is unverified: the route itself is not refused.
    report = sv.verify(QUERY, tables={"t": {"d": "DECIMAL(10,3)"}}, on_inferred="ignore")
    assert {i.kind for i in report.errors} == {"overflow"}
    con = connect()
    column = pa.array([Decimal(v) for v in VALUES], type=pa.decimal128(10, 3))
    put_table(con, "t", pa.table({"d": column}))
    got = report.run(con, engine, unverified=True).to_pydict()
    want = [Decimal(v) for v in VALUES]
    assert got["i"] == [int(half_away(v, 0)) for v in want]
    assert got["w"] == [half_away(v, 0) for v in want]
    assert got["c"] == [half_away(v, 2) for v in want]
