"""Windows partitioned by every column are deterministic (`window_allColumns`).

`ROW_NUMBER() OVER (PARTITION BY` every column`)` numbers the copies of each
row; rows tied in such a partition are equal, so the engine's tie-breaking
cannot change the result. The SQL lift writes `INTERSECT ALL` and
`EXCEPT ALL` with such a window (#344), so they are reported as determined
without keys on their inputs. A window over some columns only is not.
"""

import ibis
import pytest

import sverify as sv

S = ibis.schema({"x": "int64", "s": "string"})
TABLES = {"a": S, "b": S}


@pytest.mark.parametrize("op", ["INTERSECT ALL", "EXCEPT ALL", "INTERSECT", "EXCEPT"])
def test_set_operations_are_determined_without_keys(op):
    report = sv.verify(f"SELECT x, s FROM a {op} SELECT x, s FROM b", tables=TABLES)
    assert report.deterministic, str(report)


def test_a_window_over_every_column_is_determined():
    t = ibis.table(S, name="a")
    every = t.mutate(n=ibis.row_number().over(group_by=["x", "s"]))
    assert sv.verify(every).deterministic


@pytest.mark.parametrize(
    "build",
    [
        lambda t: t.mutate(n=ibis.row_number().over(group_by="x")),
        lambda t: t.mutate(n=ibis.row_number().over(group_by="x", order_by="s")),
    ],
    ids=["some columns", "some columns, ordered"],
)
def test_a_window_over_some_columns_is_not(build):
    assert not sv.verify(build(ibis.table(S, name="a"))).deterministic
