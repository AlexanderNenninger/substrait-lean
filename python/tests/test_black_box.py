"""Black-box functions (#325): DuckDB functions the checker treats as opaque,
with the laws their row declares (`SubstraitLean/BlackBox.lean`,
`sverify.black_box`).

Each example, `base64` (a scalar) and `entropy` (an aggregate), is lifted,
verified with its laws, written back by Lean, and run on DuckDB against
DuckDB on the SQL (oracle C). The laws are checked on random data, and the
Python table against Lean's."""

import base64
import json
import math
import subprocess

import ibis
import pyarrow as pa
import pytest
from hypothesis import HealthCheck, given, settings
from hypothesis import strategies as st

import sverify as sv
from _sql_lift import SCHEMAS, TABLES
from sverify import black_box, duckdb_engine
from sverify.engine import checker_path, connect, create_table, run_checker, run_plan, written_plan
from sverify.plan_json import Unsupported as Refused
from sverify.sql import Unsupported, to_sql
from sverify.sql.snowflake import SNOWFLAKE
from sverify.sql.spark import SPARK
from sverify.sql_lift import lift
from sverify_dev.lift import check, duckdb_result

pytestmark = pytest.mark.backend("duckdb")

#: The examples' queries: oracle C for all, oracle A (Lean's evaluator) for
#: `base64`, which Lean evaluates.
SCALAR = (
    "SELECT id, base64(encode(customer)) AS b, to_base64(encode(customer || 'é')) AS c FROM orders"
)
AGGREGATES = [
    "SELECT customer, entropy(amount) AS e, entropy(DISTINCT price) AS f FROM orders"
    " GROUP BY customer",
    "SELECT entropy(customer) AS e, entropy(price) FILTER (WHERE price > 1) AS f,"
    " entropy(day) AS g FROM orders",
    # No values: the row's `empty`, 0.0.
    "SELECT entropy(placed) AS e FROM orders WHERE id > 100",
    "SELECT base64(encode(customer)) AS b, entropy(qty) AS e FROM orders GROUP BY customer",
]


def _rows(t: pa.Table) -> list:
    return sorted((tuple(r.values()) for r in t.to_pylist()), key=repr)


def test_the_table_is_leans():
    out = subprocess.run(
        [str(checker_path()), "--black-boxes"], capture_output=True, text=True, check=True
    ).stdout
    lean = json.loads(out)
    assert [r["name"] for r in lean] == [b.name for b in black_box.TABLE]
    for i, (r, b) in enumerate(zip(lean, black_box.TABLE, strict=True)):
        assert r["anchor"] == 700 + i
        assert r["kind"] == b.kind
        assert tuple(r["args"]) == b.args
        assert r["result"] == b.result
        assert tuple(tuple(law) for law in r["laws"]) == b.laws
        if b.kind == "scalar":
            assert (r["strict"], r["raises"]) == (b.strict, b.raises)
        else:
            # A double's code: `0` is `+0.0`.
            assert r["empty"] == ({"i64": "0"} if b.empty == 0.0 else {"null": {"i64": {}}})


def test_a_black_box_is_under_sverifys_urn():
    plan = lift(SCALAR, SCHEMAS).plan
    assert plan["extensionUrns"] == [{"extensionUrnAnchor": 1, "urn": black_box.URN}]
    exts = {e["extensionFunction"]["name"]: e["extensionFunction"] for e in plan["extensions"]}
    assert exts["base64"]["extensionUrnReference"] == 1
    assert "extensionUrnReference" not in exts["str_concat"]
    written = json.loads(written_plan(json.dumps(plan)))
    ref = {e["extensionFunction"]["name"]: e["extensionFunction"] for e in written["extensions"]}
    assert ref["base64"]["functionAnchor"] == 700 and ref["entropy"]["functionAnchor"] == 701
    assert ref["entropy"]["extensionUrnReference"] == 1
    assert "extensionUrnReference" not in ref["add"]


def test_a_scalar_black_box_through_oracles_a_and_c():
    result = check(SCALAR, TABLES)
    assert result.ok, f"{result.stage}: {result.detail}"


@pytest.mark.parametrize("semantics", ["duckdb", "reference"])
@pytest.mark.parametrize("query", AGGREGATES)
def test_written_back_it_is_duckdbs_function(query, semantics):
    # Oracle C: DuckDB on the SQL, and DuckDB on the plan Lean writes back.
    plan = json.dumps(lift(query, SCHEMAS, semantics).plan)
    code, out, err = run_checker((), plan)
    assert code == 0, err or out
    got = duckdb_engine.run(written_plan(plan), TABLES)
    assert _rows(got) == _rows(duckdb_result(query, TABLES))


def test_lean_does_not_evaluate_entropy():
    # No evaluator: the checker refuses to print rows rather than print wrong ones.
    result = check(AGGREGATES[0], TABLES)
    assert result.stage == "oracle A" and "black box Lean does not evaluate" in result.detail


@pytest.mark.parametrize("semantics", ["duckdb", "reference"])
@pytest.mark.parametrize(
    ("query", "ensures"),
    [
        ("SELECT customer, entropy(amount) AS e FROM orders GROUP BY customer",
         ["e >= 0", "e IS NOT NULL"]),
        ("SELECT entropy(price) FILTER (WHERE price > 100) AS e FROM orders",
         ["e >= 0.0", "e IS NOT NULL"]),
        ("SELECT base64(encode(customer)) AS b FROM orders WHERE customer IS NOT NULL",
         ["b IS NOT NULL"]),
    ],
)  # fmt: skip
def test_the_laws_prove_contracts(query, ensures, semantics):
    report = sv.verify(
        query, tables=SCHEMAS, ensures=ensures, counterexamples=0, semantics=semantics
    )
    assert report.proved, report
    assert not report.errors


def test_what_the_laws_do_not_say_stays_unproved():
    # `base64` of a NULL is NULL (strict); `entropy` has no upper bound.
    for query, ensures in [
        ("SELECT base64(encode(customer)) AS b FROM orders", ["b IS NOT NULL"]),
        ("SELECT entropy(amount) AS e FROM orders", ["e <= 100.0"]),
    ]:
        report = sv.verify(query, tables=SCHEMAS, ensures=ensures, counterexamples=0)
        assert not report.proved


@pytest.mark.parametrize(
    ("query", "message"),
    [
        ("SELECT base64(customer) FROM orders", "BLOB"),
        ("SELECT base64(encode(amount)) FROM orders", "base64 of a !?int64"),
        ("SELECT entropy(amount, id) FROM orders", "takes one argument"),
        ("SELECT entropy(amount) OVER () FROM orders", "over a window"),
    ],
)
def test_refusals_say_what(query, message):
    with pytest.raises(Refused, match=message):
        lift(query, SCHEMAS)


@pytest.mark.parametrize("dialect", [SPARK, SNOWFLAKE])
@pytest.mark.parametrize("query", [SCALAR, AGGREGATES[0]])
def test_other_dialects_refuse(query, dialect):
    plan = json.loads(written_plan(json.dumps(lift(query, SCHEMAS).plan)))
    with pytest.raises(Unsupported, match="see #271"):
        to_sql(plan, dialect)


@pytest.mark.parametrize("engine", ["polars", "datafusion"])
@pytest.mark.parametrize(
    "query", ["SELECT base64(encode(s)) AS b FROM t", "SELECT s, entropy(x) AS e FROM t GROUP BY s"]
)
def test_other_engines_refuse(query, engine):
    con = connect(engine)
    schema = ibis.schema({"s": "string", "x": "int64"})
    create_table(con, "t", schema, [("a", 1), (None, 2)])
    plan = written_plan(json.dumps(lift(query, {"t": schema}).plan))
    # Each engine's own `Unsupported`, a `ValueError`.
    with pytest.raises(ValueError, match="see #271"):
        run_plan(con, plan, engine)


# -- the laws on random data ---------------------------------------------------

_values = st.one_of(
    st.lists(st.one_of(st.none(), st.integers(-3, 3)), max_size=12).map(
        lambda vs: (pa.int64(), vs)
    ),
    st.lists(
        st.one_of(st.none(), st.sampled_from([0.0, -0.0, 1.5, math.inf, math.nan])), max_size=12
    ).map(lambda vs: (pa.float64(), vs)),  # fmt: skip
    st.lists(st.one_of(st.none(), st.text(max_size=3)), max_size=12).map(
        lambda vs: (pa.string(), vs)
    ),
)


def _table(ty: pa.DataType, vs: list, groups: list[int]) -> pa.Table:
    return pa.table(
        {
            "g": pa.array(groups[: len(vs)] + [0] * (len(vs) - len(groups)), pa.int64()),
            "x": pa.array(vs, ty),
        }  # fmt: skip
    )


@settings(max_examples=60, deadline=None, suppress_health_check=[HealthCheck.too_slow])
@given(col=_values, groups=st.lists(st.integers(0, 2), max_size=12))
def test_entropy_keeps_its_laws_on_random_data(col, groups):
    # `nonNull` and `atLeast 0` (a double ≥ +0.0), grouped and over no values.
    ty, vs = col
    t = _table(ty, vs, groups)
    queries = [
        "SELECT g, entropy(x) AS e FROM t GROUP BY g",
        "SELECT entropy(x) AS e FROM t",
        "SELECT entropy(DISTINCT x) AS e FROM t",
    ]
    for q in queries:
        for *_, e in (tuple(r.values()) for r in duckdb_result(q, {"t": t}).to_pylist()):
            assert e is not None and e >= 0.0 and math.copysign(1.0, e) == 1.0
    schemas = {"t": ibis.Schema.from_pyarrow(t.schema)}
    plan = json.dumps(lift(queries[0], schemas).plan)
    # Oracle C on the random data too.
    got = duckdb_engine.run(written_plan(plan), {"t": t})
    assert _rows(got) == _rows(duckdb_result(queries[0], {"t": t}))


@settings(max_examples=40, deadline=None)
@given(vs=st.lists(st.one_of(st.none(), st.text(max_size=6)), max_size=8))
def test_base64_keeps_its_laws_on_random_data(vs):
    # `nonNull` where the argument is not NULL, NULL where it is (strict):
    # the UTF-8 bytes in base64. Lean evaluates it, so oracles A and C both.
    t = pa.table({"s": pa.array(vs, pa.string())})
    query = "SELECT s, base64(encode(s)) AS b FROM t"
    for r in duckdb_result(query, {"t": t}).to_pylist():
        if r["s"] is None:
            assert r["b"] is None
        else:
            assert r["b"] == base64.b64encode(r["s"].encode()).decode()
    result = check(query, {"t": t})
    assert result.ok, f"{result.stage}: {result.detail}"
