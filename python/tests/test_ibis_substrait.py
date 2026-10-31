"""The vendored Ibis → Substrait producer (`sverify.ibis_substrait`).

* Every Ibis operation the coverage table verifies compiles to a plan the
  checker accepts and writes back unchanged.
* Lean's semantics of that plan agrees with DataFusion running Ibis's own
  SQL for the same expression, on random tables: the producer means what
  Ibis means.
* Upstream ibis-substrait's mistakes stay fixed.
"""

import datetime as dt
import decimal
import json
import math
from typing import cast

import ibis
import ibis.expr.datatypes as idt
import pytest
from hypothesis import HealthCheck, given, settings
from hypothesis import strategies as st

from sverify.contracts import decode_double
from sverify.coverage import (
    CASES,
    DATAFUSION_SQL,
    MEMTABLES,
    NO_DATAFUSION_SQL,
    UNORDERED_LISTS,
    L,
    T,
    U,
)
from sverify.engine import connect, create_table, put_table, run_sql, to_sql
from sverify.ibis_substrait import Unsupported, to_substrait
from sverify.testing import EPOCH, canonical, inline_tables, lean_values

VERIFIED = [c for c in CASES if c.expected == "verified"]
#: Known gaps between Lean and DataFusion, fixed elsewhere.
KNOWN_GAPS = {
    "non-equi join": "string < is undefined in Lean (#17)",
}
#: Regular expressions are black boxes in Lean's semantics: not evaluated.
OPAQUE = {"re_search"}
#: LIMIT without a total order keeps whichever rows come first.
UNORDERED = {"limit", "limit with offset", "order_by + limit"}

names = st.sampled_from(["ada", "bob", "cy", None])
amounts = st.one_of(st.none(), st.sampled_from([0.5, -1.5, 2.25, 3.0, 10.0]))
small = st.one_of(st.none(), st.integers(-3, 6))


@st.composite
def t_rows(draw: st.DrawFn) -> list[tuple]:
    n = draw(st.integers(0, 6))
    # Distinct timestamps: LAG and ROW_NUMBER over ties depend on the engine.
    stamps = draw(st.lists(st.integers(-(10**12), 10**12), min_size=n, max_size=n, unique=True))
    return [
        (
            draw(small),
            draw(names),
            draw(amounts),
            draw(small),
            EPOCH + dt.timedelta(microseconds=s),
            draw(st.one_of(st.none(), st.booleans())),
        )
        for s in stamps
    ]


u_rows = st.lists(st.tuples(names, st.sampled_from(["north", "south", None])), max_size=4)
l_rows = st.lists(st.tuples(small, st.one_of(st.none(), st.lists(small, max_size=3))), max_size=4)


def normalize(rows: list[tuple], schema: ibis.Schema, lean: bool) -> list[tuple]:
    """Values as Python values of the expression's Ibis types, doubles rounded
    (Lean prints six decimals). Lean writes small doubles, timestamps and
    dates as integer codes; DataFusion may return other types than Ibis
    declares (an integer `POW`, a timestamp for `ts.date()`, decimals)."""

    def value(v: object, t: idt.DataType) -> object:
        if v is None:
            return None
        if isinstance(v, decimal.Decimal):
            v = int(v) if v == v.to_integral_value() else float(v)
        if t.is_floating():
            x = decode_double(v) if lean and isinstance(v, int) else float(cast(float, v))
            return "nan" if math.isnan(x) else round(x, 4) + 0.0
        if t.is_timestamp() and isinstance(v, int):
            return EPOCH + dt.timedelta(microseconds=v)
        if t.is_time() and isinstance(v, int):
            return (EPOCH + dt.timedelta(microseconds=v)).time()
        if t.is_date():
            if isinstance(v, int):
                return EPOCH.date() + dt.timedelta(days=v)
            if isinstance(v, dt.datetime):
                return v.date()
        if isinstance(v, dt.datetime):
            return v.replace(tzinfo=None)
        if isinstance(t, idt.Array) and isinstance(v, list):
            return [value(x, t.value_type) for x in v]
        return v

    types: list[idt.DataType] = [schema[name] for name in schema]
    return [tuple(value(v, t) for v, t in zip(r, types, strict=True)) for r in rows]


@pytest.mark.parametrize(
    "case",
    [
        pytest.param(c, marks=pytest.mark.xfail(reason=KNOWN_GAPS[c.label], strict=True))
        if c.label in KNOWN_GAPS
        else c
        for c in VERIFIED
        if c.label not in OPAQUE and c.label not in NO_DATAFUSION_SQL
    ],
    ids=lambda c: c.label,
)
@settings(
    max_examples=25, deadline=None, suppress_health_check=[HealthCheck.function_scoped_fixture]
)
@given(t=t_rows(), u=u_rows, lr=l_rows)
def test_plans_mean_what_ibis_means(case, t, u, lr):
    expr = case.build()
    con = connect()
    create_table(con, "t", T.schema(), t)
    create_table(con, "u", U.schema(), u)
    create_table(con, "l", L.schema(), lr)
    for name, table in MEMTABLES.items():
        put_table(con, name, table)
    if case.label in DATAFUSION_SQL:
        # DataFusion means something else: SQL's meaning, as DuckDB computes it.
        out = con.ibis.con.sql(ibis.to_sql(expr, dialect="duckdb")).to_arrow_table()
    else:
        out = run_sql(con, to_sql(expr))
    schema = expr.schema()
    rows = list(zip(*(c.to_pylist() for c in out.columns), strict=True))
    expected = normalize(rows, schema, lean=False)
    plan = inline_tables(to_substrait(expr), {"t": t, "u": u, "l": lr})
    got = normalize(lean_values(json.dumps(plan)), schema, lean=True)
    if case.label in UNORDERED_LISTS:
        # The order inside each list is the engine's: compare them as bags.
        def bags(rs: list[tuple]) -> list[tuple]:
            return [tuple(sorted(v, key=repr) if isinstance(v, list) else v for v in r) for r in rs]

        got, expected = bags(got), bags(expected)
    if case.label in UNORDERED:
        assert len(got) == len(expected)
    else:
        assert canonical(got) == canonical(expected)


# --------------------------------------------------------------------------
# Upstream ibis-substrait's mistakes stay fixed


def functions(plan: dict) -> dict[int, str]:
    return {
        e["extensionFunction"]["functionAnchor"]: e["extensionFunction"]["name"]
        for e in plan["extensions"]
    }


def root(expr: ibis.Table) -> dict:
    return to_substrait(expr)["relations"][0]["root"]["input"]


t = T


def test_integer_division_is_division_of_doubles():
    plan = to_substrait(t.select(x=t.qty / 2))
    (call,) = plan["relations"][0]["root"]["input"]["project"]["expressions"]
    assert functions(plan)[call["scalarFunction"]["functionReference"]] == "divide"
    for arg in call["scalarFunction"]["arguments"]:
        assert arg["value"]["cast"]["type"] == {"fp64": {"nullability": "NULLABILITY_NULLABLE"}}


def test_where_filters_the_measure():
    (m,) = root(t.group_by("name").aggregate(s=t.qty.sum(where=t.flag)))["aggregate"]["measures"]
    assert "filter" in m


def test_sort_keys_keep_their_null_placement():
    def direction(key: ibis.Deferred | str) -> str:
        return root(t.order_by(key))["sort"]["sorts"][0]["direction"]

    assert direction("qty") == "SORT_DIRECTION_ASC_NULLS_LAST"
    assert direction(ibis.desc("qty", nulls_first=True)) == "SORT_DIRECTION_DESC_NULLS_FIRST"


@settings(max_examples=25, deadline=None)
@given(t=t_rows())
def test_mixed_comparisons_promote_the_integer(t):
    """`qty > amount` compares as doubles (the DataFusion-produced plan of
    Ibis's SQL compared an integer with a double's code: #16)."""
    expr = T.filter(T.qty > T.amount).select("id", "qty", "amount")
    cond = root(expr)["project"]["input"]["filter"]["condition"]
    left = cond["scalarFunction"]["arguments"][0]["value"]
    assert left["cast"]["type"] == {"fp64": {"nullability": "NULLABILITY_NULLABLE"}}
    con = connect()
    create_table(con, "t", T.schema(), t)
    out = run_sql(con, to_sql(expr))
    rows = list(zip(*(c.to_pylist() for c in out.columns), strict=True))
    plan = inline_tables(to_substrait(expr), {"t": t})
    got = lean_values(json.dumps(plan))
    schema = expr.schema()
    assert canonical(normalize(got, schema, lean=True)) == canonical(
        normalize(rows, schema, lean=False)
    )


def test_timestamp_literals_are_not_local_time():
    expr = t.filter(t.ts > ibis.timestamp("2024-01-01 00:00:00"))
    cond = root(expr)["filter"]["condition"]
    lit = cond["scalarFunction"]["arguments"][1]["value"]["literal"]
    assert lit["precisionTimestamp"]["value"] == str(1_704_067_200 * 10**6)


@pytest.mark.parametrize(
    ("build", "message"),
    [
        (lambda: t.select(x=t.qty.cast("uint8")), "unsigned"),
        (lambda: t.select(x=t.amount.cast("float32")), "float32"),
        (lambda: t.sample(0.5), "Sample"),
        (lambda: t.mutate(c=(t.qty + 1).cumsum(order_by="ts")), "window aggregates"),
    ],
)
def test_what_lean_does_not_model_is_refused(build, message):
    with pytest.raises(Unsupported, match=message):
        to_substrait(build())
