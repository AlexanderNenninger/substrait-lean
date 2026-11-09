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
import pyarrow.compute as pc
import pytest

import sverify as sv
from sverify import _duckdb
from sverify._arrow_state import ArrowOps as ArrowStore
from sverify._scan import Resident
from sverify._state import Merger, arrow_of
from sverify._weighted import WEIGHT, consolidated, negated
from sverify.engine import put_table, run_plan
from sverify.incremental import Pipeline
from sverify.io import Changes
from sverify.testing import installed_engines
from sverify_duckdb import DuckDBStore

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
    plan = merge.plan()
    assert merge.refused is None and plan is not None
    assert same(merge(a, b), want)
    kept = merge(a, b, keep=True)
    assert isinstance(kept, Resident) and same(kept.to_arrow(), want)
    # The same plan on the other engines.
    put_table(con, "$merge_a", a)
    put_table(con, "$merge_b", b)
    for engine in installed_engines():
        try:
            out = run_plan(con, plan, engine)
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
    positive = z.filter(pc.call_function("greater", [z.column(WEIGHT), 0]))
    expanded = arrow_of(duck.expanded(duck.keep_table(positive)))
    assert expanded.num_rows == 1 + 1 + 4 + 1
    assert duck.has_negative(kept) and not duck.has_negative(duck.keep_table(positive))


def orders(n=0):
    return [(i, f"c{i % 3}", float(i % 4) if i % 5 else NAN) for i in range(n, n + 10)]


def pipeline(engine):
    con = sv.connect(engine)
    schema = pa.schema([("id", pa.int64()), ("c", pa.string()), ("x", pa.float64())])
    put_table(
        con,
        "o",
        pa.Table.from_pylist([dict(zip(schema.names, r, strict=True)) for r in orders()], schema),
    )
    pipe = Pipeline(con)
    o = con.table("o")
    big = pipe.view("big", o.filter(o.x >= 1.0).select(o.c, o.x))
    by_c = pipe.view("by_c", big.table.group_by("c").aggregate(n=big.table.c.count()))
    small = pipe.view("small", o.filter(o.x < 1.0).select(o.id, o.x))
    return pipe, [big, by_c, small]


@pytest.mark.parametrize("engine", installed_engines())
def test_views_keep_their_state_where_their_engine_reads_it(engine):
    pipe, views = pipeline(engine)
    held = Resident if engine == "duckdb" else pa.Table
    for step in range(3):
        deletes = orders()[2 * step : 2 * step + 2]
        pipe.apply({"o": Changes(inserts=orders(100 + 10 * step), deletes=deletes)})
        for v in views:
            assert isinstance(v.state, held)
            assert repr(v.rows()) == repr(v.recompute())


def resident_names(db) -> set[str]:
    sql = "SELECT table_name FROM duckdb_tables() UNION ALL SELECT view_name FROM duckdb_views()"
    return {r[0] for r in db.sql(sql).fetchall() if r[0].startswith("__sverify_resident")}


def held(pipe) -> set[str]:
    """Each view's state and the DuckDB view of its rows."""
    tables = [v.state for v in pipe.views.values()] + [pipe.con.get(n) for n in pipe.views]
    return {r.name for r in tables if isinstance(r, Resident)}


def test_states_change_in_place_and_old_views_are_dropped():
    pipe, _ = pipeline("duckdb")
    db = _duckdb.cursor()
    views = list(pipe.views.values())
    # A view with no delta rules is recomputed on the new tables, so the
    # views it reads are merged in full; every other view changes in place.
    recomputed = [v for v in views if v.fallback is not None]
    read_new = {t for v in recomputed for t in v.tables}
    in_place = [v for v in views if v.name not in read_new]
    assert in_place, "the pipeline has a view that changes in place"

    def states():
        return {v.state.name for v in in_place if isinstance(v.state, Resident)}

    before = states()
    first = held(pipe)
    assert len(before) == len(in_place) and first <= resident_names(db)
    for step in range(5):
        pipe.apply({"o": Changes(inserts=orders(100 + 10 * step))})
    gc.collect()
    _duckdb.collect(db)
    now = resident_names(db)
    # The same state tables, updated in place; the views of their rows are new.
    assert states() == before
    assert held(pipe) <= now
    assert not (first - before) & now


def tricky_pipeline(engine):
    con = sv.connect(engine)
    schema = pa.schema([("k", pa.int64()), ("x", pa.float64()), ("tags", pa.list_(pa.int64()))])
    rows = [(1, NAN, [1]), (1, NAN, [1]), (2, -0.0, None), (3, None, []), (3, None, [])]
    put_table(
        con,
        "t",
        pa.Table.from_pylist([dict(zip(schema.names, r, strict=True)) for r in rows], schema),
    )
    pipe = Pipeline(con)
    t = con.table("t")
    v = pipe.view("v", t.select(t.x, t.tags))
    return pipe, v


BATCHES = [
    Changes(inserts=[(4, NAN, [1]), (5, 0.0, None)], deletes=[(1, NAN, [1])]),
    Changes(deletes=[(3, None, []), (2, -0.0, None)]),
    Changes(inserts=[(6, None, [])], deletes=[(1, NAN, [1]), (4, NAN, [1])]),
]


def test_in_place_merges_match_recomputation_and_the_arrow_store():
    duck, v = tricky_pipeline("duckdb")
    arrow, w = tricky_pipeline("polars")
    for batch in BATCHES:
        duck.apply({"t": batch})
        arrow.apply({"t": batch})
        assert isinstance(v.state, Resident)
        assert repr(v.rows()) == repr(v.recompute()) == repr(w.rows())
    # The state holds each row once, with its weight.
    rows = [tuple(r[c] for c in ("x", "tags")) for r in v.state.to_arrow().to_pylist()]
    assert len({repr(r) for r in rows}) == len(rows)


def test_a_sink_writes_the_changes_it_missed():
    """A sink that skips a refresh writes the sum of the view's changes since
    the state it wrote."""
    from sverify.io import Sink

    class Recording(Sink):
        def __init__(self):
            super().__init__("rec")
            self.changes = []

        def write(self, change):
            self.changes.append(None if change.replace else change.change)

    pipe, v = tricky_pipeline("duckdb")
    sink = Recording()
    sink._attach(v)
    pipe.versions["t"] = 0  # a sink records the source versions it wrote
    sink._commit()
    pipe.apply({"t": BATCHES[0]})
    pipe.apply({"t": BATCHES[1]})
    assert v.serial == 2
    sink._last = None  # commit again, as a new epoch would
    sink._commit()
    first, total = sink.changes
    assert first is None  # the first write replaces
    want = consolidated(
        *[
            pa.Table.from_pylist(
                [{"x": r[1], "tags": r[2], WEIGHT: s} for r in rows],
                schema=total.schema,
            )
            for rows, s in [
                (BATCHES[0].inserts, 1),
                (BATCHES[0].deletes, -1),
                (BATCHES[1].inserts, 1),
                (BATCHES[1].deletes, -1),
            ]
            if rows
        ]
    )
    assert same(total, want)
