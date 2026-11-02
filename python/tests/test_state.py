"""Views' state kept by a store and added up by a checked plan (#173).

The merge plan (`sverify._state.Merger`) must group rows as the model
compares them on every engine: these tests run it on each engine and compare
with `_weighted.consolidated`, the Arrow grouping it replaces. Then views on
DuckDB keep their state in DuckDB, views on other engines in Arrow, and both
give the rows a recomputation gives."""

import gc
from datetime import datetime
from decimal import Decimal

import pyarrow as pa
import pytest

import sverify as sv
from sverify import _duckdb
from sverify._scan import Resident
from sverify._state import ArrowStore, DuckDBStore, Merger, arrow_of
from sverify._weighted import WEIGHT, consolidated, negated
from sverify.engine import put_table, run_plan
from sverify.incremental import Pipeline
from sverify.testing import installed_engines

NAN = float("nan")


def weighted_table(columns: dict, weights: list[int]) -> pa.Table:
    return pa.table({**columns, WEIGHT: pa.array(weights, pa.int64())})


CASES = {
    "doubles": weighted_table(
        {"x": [0.0, -0.0, NAN, NAN, None, None, 1.5, 1.5]}, [1, 1, 1, -1, 2, -1, 3, -3]
    ),
    "lists": weighted_table({"x": [[1, 2], [1, 2], None, [None], []]}, [1, 1, 1, 1, -1]),
    "mixed": weighted_table(
        {
            "s": ["a", "a", None, "b", "b"],
            "i": [1, 1, None, 2, 2],
            "d": [Decimal("1.50")] * 5,
            "t": [datetime(2024, 1, 1)] * 5,
        },
        [1, -1, 1, 4, 1],
    ),
    "empty": weighted_table({"x": pa.array([], pa.int64())}, []),
}


def same(got: pa.Table, want: pa.Table) -> bool:
    """The same weighted table, as the model compares rows."""
    return consolidated(got.cast(want.schema), negated(want)).num_rows == 0


@pytest.mark.parametrize("case", CASES)
def test_the_merge_plan_groups_as_the_model_on_every_engine(case):
    z = CASES[case]
    a, b = z.slice(0, z.num_rows // 2), z.slice(z.num_rows // 2)
    con = sv.connect()
    merge = Merger(con, z.schema)
    want = consolidated(a, b)
    assert merge.refused is None and merge.plan() is not None
    assert same(merge(a, b), want)
    kept = merge(a, b, keep=True)
    assert isinstance(kept, Resident) and same(kept.to_arrow(), want)
    # The same plan on the other engines.
    put_table(con, "$merge_a", a)
    put_table(con, "$merge_b", b)
    for engine in installed_engines():
        try:
            out = run_plan(con, merge.plan(), engine)
        except ValueError as e:
            # An engine may refuse a type (Polars: decimals), never differ.
            assert type(e).__name__ == "Unsupported", e
            continue
        assert same(out.rename_columns(z.schema.names), want), engine


def test_a_refused_merge_plan_adds_up_in_arrow():
    """Struct columns have no SQL form on DuckDB yet (#94)."""
    z = weighted_table({"p": [{"a": 1}, {"a": 1}, {"a": 2}]}, [1, 1, -1])
    merge = Merger(sv.connect(), z.schema)
    assert same(merge(z), consolidated(z))
    assert merge.refused is not None


def test_stores_negate_and_expand_alike():
    z = CASES["mixed"]
    duck = DuckDBStore()
    kept = duck.keep_table(z)
    for got, want in [
        (duck.negated(kept), ArrowStore().negated(z)),
        (
            duck.weighted(duck.keep_table(z.drop_columns([WEIGHT])), 3),
            ArrowStore().weighted(z.drop_columns([WEIGHT]), 3),
        ),
    ]:
        assert same(arrow_of(got), want)
    positive = z.filter(pa.compute.greater(z.column(WEIGHT), 0))
    expanded = arrow_of(duck.expanded(duck.keep_table(positive)))
    assert expanded.num_rows == 1 + 1 + 4 + 1
    assert duck.has_negative(kept) and not duck.has_negative(duck.keep_table(positive))


def orders(n=0):
    return [(i, f"c{i % 3}", float(i % 4) if i % 5 else NAN) for i in range(n, n + 10)]


def pipeline(engine):
    con = sv.connect(engine)
    schema = pa.schema([("id", pa.int64()), ("c", pa.string()), ("x", pa.float64())])
    put_table(
        con, "o", pa.Table.from_pylist([dict(zip(schema.names, r)) for r in orders()], schema)
    )
    pipe = Pipeline(con)
    o = con.table("o")
    big = pipe.view("big", o.filter(o.x >= 1.0).select(o.c, o.x))
    by_c = pipe.view("by_c", big.table.group_by("c").aggregate(n=big.table.c.count()))
    return pipe, [big, by_c]


@pytest.mark.parametrize("engine", installed_engines())
def test_views_keep_their_state_where_their_engine_reads_it(engine):
    pipe, views = pipeline(engine)
    held = Resident if engine == "duckdb" else pa.Table
    for step in range(3):
        deletes = orders()[2 * step : 2 * step + 2]
        pipe.apply({"o": sv.Changes(inserts=orders(100 + 10 * step), deletes=deletes)})
        for v in views:
            assert isinstance(v.state, held)
            assert repr(v.rows()) == repr(v.recompute())


def test_old_states_are_dropped():
    pipe, views = pipeline("duckdb")
    for step in range(5):
        pipe.apply({"o": sv.Changes(inserts=orders(100 + 10 * step))})
    gc.collect()
    db = _duckdb.cursor()
    _duckdb.collect(db)
    held = {
        r[0]
        for r in db.sql(
            "SELECT table_name FROM duckdb_tables() UNION ALL SELECT view_name FROM duckdb_views()"
        ).fetchall()
        if r[0].startswith("__sverify_resident")
    }
    # Each view: its state, and the view of its rows; other tests' may linger.
    live = {v.state.name for v in pipe.views.values()} | {
        pipe.con.get(name).name for name in pipe.views
    }
    assert live <= held
    del pipe, views
    gc.collect()
    _duckdb.collect(db)
    gone = {
        r[0] for r in db.sql("SELECT table_name FROM duckdb_tables()").fetchall() if r[0] in live
    }
    assert not gone
