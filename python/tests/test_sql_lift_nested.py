"""Lists, structs and UNNEST in DuckDB SQL through sverify's own lift
(`sverify.sql_lift`)."""

import json

import ibis
import pyarrow as pa
import pytest

from sverify.plan_json import Unsupported as Refused
from sverify.sql_lift import lift

pytestmark = pytest.mark.backend("duckdb")


def test_nested_values_have_no_order_yet():
    # DuckDB orders structs field by field; the model's order differs.
    schema = {"t": ibis.schema({"s": "struct<p: int64, q: int64>"})}
    with pytest.raises(Refused, match="ordering comparisons"):
        lift("SELECT a.s < b.s AS c FROM t AS a, t AS b", schema)


# #348: list literals, indexing and UNNEST in DuckDB's SQL. Lean's rows match
# DuckDB's (oracle A), and so do DuckDB's running the plan Lean writes (oracle
# C, #94).
LISTS = ibis.schema({"a": "int64", "l": "array<int64>"})
LIST_ROWS = [(1, [1, 2, 3]), (2, []), (3, None), (4, [5, None]), (None, [7])]
LIST_QUERIES = [
    "SELECT [1, 2, 3] AS x",
    "SELECT [[1], [2, 3]] AS x",
    "SELECT [1, NULL] AS x",
    "SELECT [10, 20, 30][2] AS x",
    "SELECT a, l[1] AS f, l[-1] AS z, l[0] AS n, l[3] AS t3, l[-3] AS m FROM t",
    "SELECT a, UNNEST(l) AS e FROM t",
    "SELECT UNNEST([1, 2, 3]) AS e",
    "SELECT a, UNNEST(l) + 1 AS e FROM t WHERE a > 1",
    # The same UNNEST twice is one (DuckDB zips equal lists).
    "SELECT UNNEST(l) AS x, UNNEST(l) * 10 AS y FROM t",
    # #812: lengths, membership, positions, concatenation and lists of
    # computed elements, NULLs as DuckDB has them.
    "SELECT a, len(l) AS n, array_length(l) AS m, list_contains(l, 5) AS c,"
    " list_contains(l, a) AS ca, list_has(l, NULL) AS h, list_position(l, 2) AS p,"
    " list_position(l, NULL) AS pn, array_position(l, a + 1) AS pa FROM t",
    "SELECT a, [a, 1] AS x, [a, NULL, a + 1] AS y, list_concat(l, [a]) AS z,"
    " list_concat(l, NULL) AS w, array_cat(NULL, l) AS v FROM t",
    "SELECT a FROM t WHERE list_contains(l, 2) OR len(l) > 1",
]


@pytest.mark.parametrize("sql", LIST_QUERIES)
def test_lists_lift_as_duckdb_reads_them(sql):
    from sverify.engine import connect, put_table, run_plan, written_plan
    from sverify.testing import duckdb_sql, inline_tables, lean_values

    con = connect()
    put_table(
        con,
        "t",
        pa.table(
            {
                "a": pa.array([r[0] for r in LIST_ROWS], pa.int64()),
                "l": pa.array([r[1] for r in LIST_ROWS], pa.list_(pa.int64())),
            }
        ),
    )
    plan = json.dumps(lift(sql, {"t": LISTS}, "duckdb").plan)
    lean = lean_values(json.dumps(inline_tables(json.loads(plan), {"t": LIST_ROWS})))
    want = [tuple(r.values()) for r in duckdb_sql(con, sql).to_pylist()]
    assert sorted(map(repr, lean)) == sorted(map(repr, want))
    got = [tuple(r.values()) for r in run_plan(con, written_plan(plan), "duckdb").to_pylist()]
    assert sorted(map(repr, got)) == sorted(map(repr, want))


@pytest.mark.parametrize(
    ("sql", "why"),
    [
        ("SELECT [] AS x", "empty list literal"),
        ("SELECT list_contains([1.5::DOUBLE], 1.5::DOUBLE) AS x", "list of float64"),
        ("SELECT list_contains(l, 'x') AS x FROM t", "list_contains of"),
        ("SELECT array_length(l, 1) AS x FROM t", "dimension"),
        ("SELECT l[1:2] AS x FROM t", "slices"),
        ("SELECT l[a] AS x FROM t", "constant index"),
        ("SELECT [1, 2.5] AS x", "decimal"),
        ("SELECT UNNEST(l) AS x, UNNEST([1, 2]) AS y FROM t", "more than one UNNEST"),
        ("SELECT 'abc'[1] AS x", "indexing a string"),
    ],
)
def test_list_refusals_say_why(sql, why):
    with pytest.raises(Refused, match=why):
        lift(sql, {"t": LISTS}, "duckdb")


def test_decimals_in_lists_and_structs_keep_their_scale():
    """Lean prints a decimal inside a list or struct with its scale; it
    printed the unscaled integer (`[10, 25]` for `[1.0, 2.5]`), which reached
    the replay's rows and counterexamples (#628)."""
    from decimal import Decimal

    from sverify.testing import inline_tables, lean_values

    schemas = {
        "t": ibis.schema({"l": "array<decimal(4, 1)>", "s": "struct<a: string, b: decimal(9, 3)>"})
    }
    row = ([Decimal("1.0"), None, Decimal("-2.5")], {"a": "x", "b": Decimal("1.500")})
    plan = lift("SELECT l, s FROM t", schemas).plan
    got = lean_values(json.dumps(inline_tables(plan, {"t": [row]})))
    assert got == [([Decimal("1.0"), None, Decimal("-2.5")], ["x", Decimal("1.500")])]
