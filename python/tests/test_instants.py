"""A UTC-zoned timestamp is an instant (D53, #1725): read, compared, ordered, grouped and
aggregated as the Lean kind `timeTz`, and written back as an instant; every conversion,
calendar function, other zone and literal is refused naming the issue."""

import datetime as dt
import json
import os
import time
from collections.abc import Iterator
from typing import Any

import ibis
import pyarrow as pa
from ibis import _
import pytest
from deltalake import DeltaTable, write_deltalake

import sverify as sv
from sverify import _duckdb
from sverify.engines import ENGINES
from sverify.ibis_substrait import to_substrait_json
from sverify.io import DeltaSink, DeltaSource
from sverify.testing import inline_tables, lean_values

U = lambda *a: dt.datetime(*a, tzinfo=dt.UTC)  # noqa: E731
NTZ = pa.timestamp("us")
UTC = pa.timestamp("us", tz="UTC")

ROWS = [
    (1, U(2024, 1, 2), U(2024, 1, 3), dt.datetime(2024, 1, 2)),
    (2, U(2024, 1, 1), U(2024, 1, 1), dt.datetime(2024, 1, 1)),
    (3, None, U(2024, 1, 1), None),
    (4, U(2024, 1, 2), None, dt.datetime(2024, 1, 2)),
    (5, U(2024, 1, 2), U(2024, 1, 2), dt.datetime(2024, 1, 2)),
]
TABLE = pa.table(
    {
        "id": [r[0] for r in ROWS],
        "ts": pa.array([r[1] for r in ROWS], UTC),
        "ts2": pa.array([r[2] for r in ROWS], UTC),
        "naive": pa.array([r[3] for r in ROWS], NTZ),
    }
)


def instant_table() -> ibis.Table:
    return ibis.table(
        {
            "id": "int64",
            "ts": "timestamp('UTC', 6)",
            "ts2": "timestamp('UTC', 6)",
            "naive": "timestamp",
        },
        name="t",
    )


def _self_join(t):
    other = t.view()
    return t.join(other, t.ts == other.ts).select(t.id, other.id.name("id2"))


QUERIES = {
    "filter": lambda t: t.filter(t.ts <= t.ts2).select(t.id),
    "coalesce": lambda t: t.select(t.id, c=ibis.coalesce(t.ts, t.ts2)),
    "case": lambda t: t.select(t.id, c=ibis.ifelse(t.ts < t.ts2, t.ts, t.ts2)),
    "order": lambda t: t.order_by(t.ts, t.id).select(t.id, t.ts),
    "group": lambda t: t.group_by("ts").aggregate(n=t.count(), lo=t.ts2.min(), hi=t.ts2.max()),
    "distinct": lambda t: t.select(t.ts).distinct(),
    "self_join": lambda t: _self_join(t),
}


def con_with(engine: str = "duckdb") -> Any:
    con = sv.connect(engine)
    con.put("t", TABLE)
    return con


def canon(table: pa.Table) -> list[tuple]:
    rows = [tuple(r.values()) for r in table.to_pylist()]
    return sorted(rows, key=repr)


@pytest.mark.parametrize("engine", ENGINES)
@pytest.mark.parametrize("name", QUERIES)
def test_the_zone_free_operations_run_and_return_instants(name, engine):
    if engine == "spark":
        pytest.skip("Spark has no map for an instant yet (#1725)")
    t = instant_table()
    report = sv.verify(QUERIES[name](t), counterexamples=0)
    out = report.run(con_with(engine), engine, unverified=True)
    for f in out.schema:
        if pa.types.is_timestamp(f.type):
            assert f.type == UTC, (name, f)


@pytest.mark.parametrize("name", QUERIES)
def test_the_zone_free_operations_agree_with_the_lean_evaluator(name):
    t = instant_table()
    query = QUERIES[name](t)
    plan = json.loads(to_substrait_json(query))
    rows = {"t": [(r[0], _us(r[1]), _us(r[2]), _us(r[3])) for r in ROWS]}
    lean = lean_values(json.dumps(inline_tables(plan, rows)))
    got = sv.verify(query, counterexamples=0).run(con_with(), "duckdb", unverified=True)
    want = (
        canon(pa.table({f"c{i}": [r[i] for r in lean] for i in range(len(lean[0]))}))
        if lean
        else []
    )
    have = [tuple(_us(v) for v in r) for r in canon(got)]
    assert sorted(map(repr, have)) == sorted(map(repr, [tuple(r) for r in want])), name


def _us(v):
    """A datetime as its microseconds since 1970 (the code Lean reads)."""
    if v is None or isinstance(v, int):
        return v
    epoch = dt.datetime(1970, 1, 1, tzinfo=v.tzinfo)
    return (v - epoch) // dt.timedelta(microseconds=1)


@pytest.fixture
def duckdb_zone() -> Iterator:
    cursor = _duckdb.cursor()
    cursor.execute("SET GLOBAL TimeZone = 'UTC'").fetchall()

    def set_zone(zone: str) -> None:
        cursor.execute(f"SET GLOBAL TimeZone = '{zone}'").fetchall()

    yield set_zone
    cursor.execute("RESET GLOBAL TimeZone").fetchall()


@pytest.fixture
def host_zone() -> Iterator:
    old = os.environ.get("TZ")

    def set_zone(zone: str) -> None:
        os.environ["TZ"] = zone
        time.tzset()

    yield set_zone
    if old is None:
        os.environ.pop("TZ", None)
    else:
        os.environ["TZ"] = old
    time.tzset()


@pytest.mark.parametrize("name", ["filter", "coalesce", "order", "group", "self_join"])
def test_a_plan_gives_the_same_rows_and_schema_under_any_session_or_host_zone(
    name, duckdb_zone, host_zone
):
    t = instant_table()
    report = sv.verify(QUERIES[name](t), counterexamples=0)
    results = []
    for session, host in [
        ("UTC", "UTC"),
        ("America/New_York", "Asia/Kolkata"),
        ("Asia/Tokyo", "UTC"),
    ]:
        duckdb_zone(session)
        host_zone(host)
        out = report.run(con_with(), "duckdb", unverified=True)
        results.append((out.schema, canon(out)))
    assert all(r == results[0] for r in results[1:])
    assert all(f.type == UTC for f in results[0][0] if pa.types.is_timestamp(f.type))


def test_a_delta_table_of_instants_and_naive_timestamps_round_trips_through_a_sink(tmp_path):
    write_deltalake(tmp_path / "src", TABLE)

    @sv.transform()
    def keep(t):
        return t.filter(t.id > 0)

    for engine in ("duckdb", "polars"):
        node = keep(DeltaSource(str(tmp_path / "src"))).write(DeltaSink(str(tmp_path / engine)))
        node.refresh(engine=engine)
        schema = DeltaTable(str(tmp_path / engine)).to_pyarrow_table().schema
        assert schema.field("ts").type == UTC and schema.field("naive").type == NTZ, engine


def _naive_other(t):
    return ibis.table({"id": "int64", "naive": "timestamp"}, name="o")


REFUSED = {
    "a naive column compared with an instant": lambda t: t.filter(t.ts <= t.naive),
    "a naive literal compared with an instant": lambda t: t.filter(
        t.ts > ibis.literal(dt.datetime(2024, 1, 1), "timestamp")
    ),
    "IN with a naive literal": lambda t: t.filter(
        t.ts.isin([ibis.literal(dt.datetime(2024, 1, 1), "timestamp")])
    ),
    "IN with a naive column": lambda t: t.filter(t.ts.isin([t.naive])),
    "an instant plus an interval": lambda t: t.select(x=t.ts + ibis.interval(hours=1)),
    "the difference of two instants": lambda t: t.select(x=t.ts - t.ts2),
    "date_trunc of an instant": lambda t: t.select(x=t.ts.truncate("D")),
    "extract from an instant": lambda t: t.select(x=t.ts.year()),
    "an instant cast to a date": lambda t: t.select(x=t.ts.cast("date")),
    "an instant cast to a string": lambda t: t.select(x=t.ts.cast("string")),
    "least of an instant": lambda t: t.select(x=ibis.least(t.ts, t.ts2)),
    "lag of an instant": lambda t: t.select(x=t.ts.lag().over(ibis.window(order_by=t.id))),
    "an instant literal in a comparison": lambda t: t.filter(
        t.ts > ibis.literal(U(2024, 1, 1), "timestamp('UTC', 6)")
    ),
    "an instant literal in a projection": lambda t: t.select(
        x=ibis.literal(U(2024, 1, 1), "timestamp('UTC', 6)")
    ),
    "a naive timestamp cast to an instant": lambda t: t.select(
        x=t.naive.cast("timestamp('UTC', 6)")
    ),
    "a CASE with a NULL branch": lambda t: t.select(x=ibis.cases((t.ts < t.ts2, t.ts))),
    "NULLIF of instants": lambda t: t.select(x=t.ts.nullif(t.ts2)),
    "COALESCE of an instant and a naive column": lambda t: t.select(x=ibis.coalesce(t.ts, t.naive)),
    "SUM, AVG and FIRST of an instant": lambda t: t.aggregate(x=t.ts.first()),
    "date_trunc over COALESCE of instants, one level up": lambda t: t.select(
        c=ibis.coalesce(t.ts, t.ts2)
    ).select(x=_.c.truncate("D")),
}


@pytest.mark.parametrize("what", REFUSED)
def test_what_reads_a_calendar_or_mixes_kinds_is_refused_and_names_the_issue(what):
    with pytest.raises(Exception, match="1725") as err:
        sv.verify(REFUSED[what](instant_table()), counterexamples=0)
    assert "1725" in str(err.value), what


def test_a_zone_other_than_utc_is_refused_and_names_the_issue():
    t = ibis.table({"ts": "timestamp('Europe/Berlin', 6)"}, name="t")
    with pytest.raises(Exception, match="1725"):
        sv.verify(t.select(t.ts))


def test_ibis_itself_refuses_a_list_of_instants_and_a_union_with_a_naive_column():
    t = instant_table()
    with pytest.raises(Exception):  # noqa: B017 - Ibis (a list) and the producer (#60) refuse
        sv.verify(t.select(x=ibis.array([t.ts, t.ts2])))
    with pytest.raises(Exception, match="schemas must be equal"):
        sv.verify(ibis.union(t.select(x=t.ts), t.select(x=t.naive), distinct=False))


def test_a_set_operation_over_an_instant_and_a_naive_column_is_refused_by_the_checker():
    """The parser's gate, past Ibis: the second input's column is retyped naive."""
    from sverify.engine import run_checker

    t = ibis.table({"ts": "timestamp('UTC', 6)"}, name="t")
    u = ibis.table({"ts": "timestamp('UTC', 6)"}, name="u")
    plan = to_substrait_json(ibis.union(t.select(x=t.ts), u.select(x=u.ts), distinct=False))
    tz = '"precisionTimestampTz"'
    first = plan.index(tz) + 1
    second = plan.index(tz, first)
    # The second `precisionTimestampTz` after the first table's read is table `u`'s `ts`.
    patched = plan[:second] + '"precisionTimestamp"' + plan[second + len(tz) :]
    code, _, err = run_checker((), patched)
    assert code != 0 and "1725" in err
