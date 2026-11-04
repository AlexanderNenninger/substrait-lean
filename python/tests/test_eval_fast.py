"""`Rel.evalFast` (`SubstraitLean/EvalFast.lean`, #357) against `Rel.eval`.

`Rel.evalFast_eq` proves the two equal; these tests check the wiring:
`substrait-check` evaluates with `Rel.evalFast`, and `--eval-spec` with
`Rel.eval`, and both print the same rows in the same order on random plans
and data. The data has few distinct keys, so joins match many rows, keys
repeat, and NULL keys occur. The last test is the query that made #357.
"""

import json
import time

import pyarrow as pa
import pytest
from hypothesis import HealthCheck, given, settings
from hypothesis import strategies as st

from sverify.engine import connect, create_table, run_checker, substrait_json
from sverify.testing import inline_tables, lean_values

T = pa.schema([("i", pa.int64()), ("j", pa.int64()), ("s", pa.string())])
U = pa.schema([("k", pa.int64()), ("v", pa.string())])

keys = st.one_of(st.none(), st.integers(0, 3))
names = st.one_of(st.none(), st.sampled_from(["a", "b", "c"]))
tables = st.fixed_dictionaries(
    {
        "t": st.lists(st.tuples(keys, keys, names), max_size=12),
        "u": st.lists(st.tuples(keys, names), max_size=12),
    }
)

ONS = [
    "t.i = u.k",
    "u.k = t.i",
    "t.i = u.k AND t.s = u.v",
    "t.i = u.k AND t.j < u.k",
    "t.i + 1 = u.k",
    "t.i = u.k OR t.j = u.k",
    "t.i < u.k",
    "t.s = u.v AND t.j = u.k AND t.i IS NOT NULL",
]
JOINS = ["JOIN", "LEFT JOIN", "RIGHT JOIN", "FULL JOIN"]


@st.composite
def queries(draw: st.DrawFn) -> str:
    on = draw(st.sampled_from(ONS))
    join = f"t {draw(st.sampled_from(JOINS))} u ON {on}"
    return draw(
        st.sampled_from(
            [
                f"SELECT t.i, t.s, u.k, u.v FROM {join}",
                f"SELECT DISTINCT t.s, u.v FROM {join}",
                f"SELECT u.v, count(*), count(DISTINCT t.s), sum(t.j) FROM {join} GROUP BY u.v",
                f"SELECT count(*), count(DISTINCT t.i), count(DISTINCT u.v) FROM {join}",
                "SELECT t.i, t.s FROM t WHERE t.i IN (SELECT k FROM u)",
                "SELECT t.i, t.s FROM t WHERE t.j IN (SELECT k FROM u WHERE v IS NOT NULL)",
                "SELECT t.i, t.s FROM t WHERE t.i NOT IN (SELECT k FROM u WHERE k IS NOT NULL)",
                "SELECT DISTINCT i, s FROM t",
                "SELECT i, s FROM t EXCEPT SELECT k, v FROM u",
                "SELECT j, s FROM t INTERSECT SELECT k, v FROM u",
                "SELECT i, s FROM t EXCEPT ALL SELECT k, v FROM u",
                "SELECT s, i, count(DISTINCT j), min(j) FROM t GROUP BY s, i",
                "SELECT a.i, b.k, c.v FROM t a JOIN u b ON a.i = b.k "
                "LEFT JOIN u c ON b.k = c.k AND a.s = c.v",
            ]
        )
    )


def both(plan: str) -> tuple[tuple[int, str, str], tuple[int, str, str]]:
    return run_checker((), plan), run_checker(("--eval-spec",), plan)


@settings(
    max_examples=200,
    derandomize=True,
    deadline=None,
    suppress_health_check=[HealthCheck.too_slow],
)
@given(sql=queries(), rows=tables)
def test_fast_evaluator_agrees_with_spec(sql, rows):
    con = connect()
    create_table(con, "t", T)
    create_table(con, "u", U)
    try:
        plan = substrait_json(con, sql)
    except Exception:  # noqa: BLE001 - outside the lift
        return
    inlined = json.dumps(inline_tables(json.loads(plan), rows))
    fast, spec = both(inlined)
    assert fast == spec, sql


# DuckDB's `test/sql/join/hash_join/hash_join_dict_surviving_outer_build.test`:
# 8.4 s with `Rel.eval` on a laptop (#357).
SLOW_TABLES = {
    "nation": [(i, f"NATION_{i % 5}") for i in range(25)],
    "customer": [(i * 1000, i % 25) for i in range(2000)],
    "returns": [(i * 2000, i % 7) for i in range(1500)],
    "dates": [(i, f"day_{i}") for i in range(7)],
}
SLOW_SCHEMAS = {
    "nation": pa.schema([("nk", pa.int64()), ("n_name", pa.string())]),
    "customer": pa.schema([("ck", pa.int64()), ("nk", pa.int64())]),
    "returns": pa.schema([("ck", pa.int64()), ("dk", pa.int64())]),
    "dates": pa.schema([("dk", pa.int64()), ("d_name", pa.string())]),
}
SLOW_SQL = """
SELECT count(*), count(DISTINCT n_name), count(DISTINCT d_name)
FROM dates d RIGHT JOIN (
    SELECT c.ck, n.n_name, r.dk
    FROM customer c JOIN nation n ON c.nk = n.nk
    FULL OUTER JOIN returns r ON c.ck = r.ck
) b ON d.dk = b.dk
"""


@pytest.mark.slow
def test_hash_join_on_thousands_of_rows():
    con = connect()
    for name, schema in SLOW_SCHEMAS.items():
        create_table(con, name, schema)
    plan = inline_tables(json.loads(substrait_json(con, SLOW_SQL)), SLOW_TABLES)
    start = time.perf_counter()
    rows = lean_values(json.dumps(plan))
    took = time.perf_counter() - start
    assert rows == [(2500, 5, 7)]
    # Under a second on a laptop; `Rel.eval` takes over 8.
    assert took < 4, f"{took:.1f} s"
