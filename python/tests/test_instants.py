"""A UTC-zoned timestamp is an instant (D53, #1725): read, compared, ordered, grouped and
aggregated as the Lean kind `timeTz`, and written back as an instant; every conversion,
interval arithmetic, other zone and literal is refused naming the issue; the calendar functions
of an instant at UTC are those of its UTC wall clock (D69, `test_instant_calendar.py`)."""

import datetime as dt
import json
import os
import sys
import time
from collections.abc import Iterator
from typing import Any

import ibis
import pyarrow as pa
import pyarrow.compute as pc
import pytest
from deltalake import DeltaTable, write_deltalake
from ibis import _

import sverify as sv
from sverify import _duckdb
from sverify.engines import ENGINES
from sverify.ibis_substrait import to_substrait_json
from sverify.io import DeltaSink, DeltaSource, from_query
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
    if not hasattr(time, "tzset"):
        pytest.skip("the host zone is set with time.tzset, which Windows lacks")
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


def test_a_delta_table_of_instants_and_naive_timestamps_round_trips_through_a_sink(
    tmp_path, monkeypatch
):
    # DuckDB fetches a TIMESTAMPTZ as a Python value only with `pytz`, which sverify does
    # not need: the file statistics read the epoch instead.
    monkeypatch.setitem(sys.modules, "pytz", None)
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
    "COALESCE of an instant and a naive column": lambda t: t.select(x=ibis.coalesce(t.ts, t.naive)),
    "an instant plus an interval": lambda t: t.select(x=t.ts + ibis.interval(hours=1)),
    "the difference of two instants": lambda t: t.select(x=t.ts - t.ts2),
    "an instant cast to a string": lambda t: t.select(x=t.ts.cast("string")),
    "least of an instant": lambda t: t.select(x=ibis.least(t.ts, t.ts2)),
    "lag of an instant": lambda t: t.select(x=t.ts.lag().over(ibis.window(order_by=t.id))),
    "a CASE with a NULL branch": lambda t: t.select(x=ibis.cases((t.ts < t.ts2, t.ts))),
    "NULLIF of instants": lambda t: t.select(x=t.ts.nullif(t.ts2)),
    "SUM, AVG and FIRST of an instant": lambda t: t.aggregate(x=t.ts.first()),
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


# -- Step 2: the conversion and the literals (D53, #1725) -----------------------------

LIT0 = U(2000, 1, 1)
LIT1 = U(2100, 1, 1)
LIT = ibis.literal(U(2024, 1, 1, 12), "timestamp('UTC', 6)")

CONVERT = {
    "filter by an instant literal": lambda t: t.filter(t.ts > LIT).select(t.id),
    "IN with instant literals": lambda t: t.filter(
        t.ts.isin([LIT, ibis.literal(U(2024, 1, 2), "timestamp('UTC', 6)")])
    ).select(t.id),
    "an instant literal in a projection": lambda t: t.select(t.id, x=LIT),
    "COALESCE with an instant literal": lambda t: t.select(t.id, x=ibis.coalesce(t.ts, LIT)),
    "an instant as a timestamp": lambda t: t.select(t.id, x=t.ts.cast("timestamp")),
    "a timestamp as an instant": lambda t: t.select(t.id, x=t.naive.cast("timestamp('UTC', 6)")),
    "date_trunc of the timestamp of an instant": lambda t: t.select(
        t.id, x=t.ts.cast("timestamp").truncate("D")
    ),
}


@pytest.mark.parametrize("name", CONVERT)
def test_the_conversion_and_the_literals_agree_with_the_lean_evaluator(name):
    t = instant_table()
    query = CONVERT[name](t)
    plan = json.loads(to_substrait_json(query))
    rows = {"t": [(r[0], _us(r[1]), _us(r[2]), _us(r[3])) for r in ROWS]}
    lean = lean_values(json.dumps(inline_tables(plan, rows)))
    got = sv.verify(query, counterexamples=0).run(con_with(), "duckdb", unverified=True)
    have = [tuple(_us(v) for v in r) for r in canon(got)]
    assert sorted(map(repr, have)) == sorted(map(repr, [tuple(r) for r in lean])), name


@pytest.mark.parametrize("engine", ["duckdb", "polars"])
@pytest.mark.parametrize("name", CONVERT)
def test_the_conversion_gives_the_same_rows_on_each_engine_and_zone(
    name, engine, duckdb_zone, host_zone
):
    t = instant_table()
    report = sv.verify(CONVERT[name](t), counterexamples=0)
    results = []
    for session, host in [("UTC", "UTC"), ("America/New_York", "Asia/Kolkata")]:
        duckdb_zone(session)
        host_zone(host)
        out = report.run(con_with(engine), engine, unverified=True)
        results.append((out.schema, canon(out)))
    assert results[0] == results[1]


def test_date_trunc_of_an_instant_at_utc_agrees_on_every_engine_under_any_session_zone(
    duckdb_zone,
):
    """T5: `date_trunc('day', ts AT TIME ZONE 'UTC')`, from SQL, on DuckDB under a non-UTC
    session and on Polars."""
    decl = {"t": instant_table()}
    sql = "SELECT id, date_trunc('day', ts AT TIME ZONE 'UTC') AS d FROM t"
    report = sv.verify(sv.sql(sql, dialect="duckdb", **decl), counterexamples=0)
    duckdb_zone("Asia/Tokyo")
    duck = canon(report.run(con_with(), "duckdb", unverified=True))
    pol = canon(report.run(con_with("polars"), "polars", unverified=True))
    assert duck == pol
    assert dict(duck) == {
        1: dt.datetime(2024, 1, 2),
        2: dt.datetime(2024, 1, 1),
        3: None,
        4: dt.datetime(2024, 1, 2),
        5: dt.datetime(2024, 1, 2),
    }


@pytest.mark.parametrize(
    ("sql", "message"),
    [
        ("SELECT CAST(ts AS TIMESTAMP) AS x FROM t", "AT TIME ZONE 'UTC'"),
        ("SELECT ts::DATE AS x FROM t", "AT TIME ZONE 'UTC'"),
        ("SELECT CAST(naive AS TIMESTAMPTZ) AS x FROM t", "AT TIME ZONE 'UTC'"),
        ("SELECT id FROM t WHERE ts > TIMESTAMPTZ '2024-01-01 12:00:00'", "offset"),
        ("SELECT ts AT TIME ZONE 'Europe/Berlin' AS x FROM t", "'UTC'"),
    ],
)
def test_the_lift_refuses_what_follows_the_session_zone_and_names_the_exit(sql, message):
    with pytest.raises(Exception, match="1725") as err:
        sv.verify(sv.sql(sql, dialect="duckdb", t=instant_table()), counterexamples=0)
    assert message in str(err.value)


def test_a_timestamptz_literal_with_an_offset_is_an_instant():
    sql = "SELECT id FROM t WHERE ts > TIMESTAMPTZ '2024-01-01 14:00:00+02'"
    report = sv.verify(sv.sql(sql, dialect="duckdb", t=instant_table()), counterexamples=0)
    # 14:00+02 is 12:00 UTC: ids 1 (Jan 2) and 5 pass, id 2 (Jan 1 00:00) does not.
    assert [r[0] for r in canon(report.run(con_with(), "duckdb", unverified=True))] == [1, 4, 5]


def test_a_delta_filter_on_an_instant_skips_the_files_its_naive_twin_skips(tmp_path):
    """T3."""

    def table(day):
        ts = [dt.datetime(2024, 1, day), dt.datetime(2024, 1, day + 1)]
        return pa.table(
            {
                "id": [day, day + 1],
                "ts": pa.array([x.replace(tzinfo=dt.UTC) for x in ts], UTC),
                "naive": pa.array(ts, NTZ),
            }
        )

    write_deltalake(tmp_path / "t", table(1))
    write_deltalake(tmp_path / "t", table(10), mode="append")
    zoned = DeltaSource(str(tmp_path / "t"), where="ts > TIMESTAMPTZ '2024-01-05 00:00:00+00'")
    naive = DeltaSource(str(tmp_path / "t"), where="naive > TIMESTAMP '2024-01-05 00:00:00'")
    zoned.snapshot(), naive.snapshot()
    assert len(zoned.skipped) == len(naive.skipped) == 1


def test_a_precondition_and_a_bound_on_an_instant_column():
    """T7: a precondition on an instant column is checked on the data, and proves the
    postcondition of the same bound."""
    t = instant_table()
    report = sv.verify(
        t.filter(t.id > 0), requires=[_.ts >= LIT], ensures=[_.ts >= LIT], counterexamples=0
    )
    assert report.verdict == sv.Verdict.PROVED
    con = sv.connect()
    con.put(
        "t", TABLE.filter(pa.array([r[1] is not None and r[1] >= U(2024, 1, 1, 12) for r in ROWS]))
    )
    assert report.run(con, "duckdb").num_rows == 3
    with pytest.raises(sv.errors.PreconditionError):
        report.run(con_with(), "duckdb")


def test_an_incremental_cursor_on_an_instant_column(tmp_path):
    """T7: a restarted job resumes from the instant its sink recorded."""
    rows = [{"id": 1, "ts": U(2026, 11, 3, 12), "amount": 30}]

    class Feed:
        def since(self, ts):
            table = pa.Table.from_pylist(rows)
            return (
                table
                if ts is None
                else table.filter(pc.call_function("greater", [table["ts"], ts]))
            )

    f = Feed()

    @sv.transform(requires={"payments": [_.amount >= 0]}, ensures=[_.amount.notnull()])
    def big(payments):
        return payments.filter(payments.amount > 10)

    def job():
        return big(from_query(f.since, cursor_on="ts", name="payments")).write(
            DeltaSink(str(tmp_path / "big"))
        )

    job().refresh()
    recorded = DeltaSource(str(tmp_path / "big")).contract()
    assert recorded is not None and "payments" in recorded.cursors
    rows.append({"id": 2, "ts": U(2026, 11, 3, 12, 1), "amount": 40})
    w = job().refresh().writes[0]
    assert (w.mode, w.inserted) == ("merge", 1)


@pytest.mark.parametrize(
    "sql",
    [
        "SELECT id FROM t WHERE ts <= naive",
        "SELECT id FROM t WHERE ts IN (naive)",
        "SELECT COALESCE(ts, naive) AS x FROM t",
        "SELECT CASE WHEN id > 1 THEN ts ELSE naive END AS x FROM t",
        "SELECT ts AS x FROM t UNION ALL SELECT naive FROM t",
        "SELECT id FROM t WHERE ts > TIMESTAMP '2024-01-01 00:00:00'",
    ],
)
def test_the_lift_refuses_a_mix_of_instants_and_naive_timestamps(sql):
    """DuckDB brings the naive side to the session's zone: the lift does not guess it."""
    with pytest.raises(Exception, match="1725"):
        sv.verify(sv.sql(sql, dialect="duckdb", t=instant_table()), counterexamples=0)


def test_the_checker_refuses_a_comparison_of_an_instant_with_a_naive_column():
    """The parser's gate, past the frontends: the second column of the plan is retyped naive."""
    from sverify.engine import run_checker

    t = ibis.table({"a": "timestamp('UTC', 6)", "b": "timestamp('UTC', 6)"}, name="t")
    plan = to_substrait_json(t.filter(t.a <= t.b))
    tz = '"precisionTimestampTz"'
    first = plan.index(tz) + 1
    second = plan.index(tz, first)
    patched = plan[:second] + '"precisionTimestamp"' + plan[second + len(tz) :]
    code, _, err = run_checker((), patched)
    assert code != 0 and "1725" in err


def test_a_retention_cutoff_on_an_instant_column():
    """T7: buckets of an instant's UTC wall clock retire as a naive column's do."""
    from datetime import timedelta

    from sverify.errors import PreconditionError  # noqa: F401
    from sverify.io import Changes, StaticSource

    t0 = dt.datetime(2026, 11, 3, tzinfo=dt.UTC)
    schema = pa.schema([("host", pa.string()), ("ts", UTC), ("cpu", pa.int64())])

    def samples(rows):
        return pa.table(
            {
                "host": [h for h, _, _ in rows],
                "ts": [t0 + timedelta(minutes=m) for _, m, _ in rows],
                "cpu": [c for _, _, c in rows],
            },
            schema=schema,
        )

    @sv.transform(
        requires={
            "samples": [
                sv.arrives_within("ts", timedelta(hours=2)),
                _.ts >= LIT0,
                _.ts < LIT1,
                _.cpu.notnull(),
            ]
        }
    )
    def hourly(samples):
        bucket = samples.ts.cast("timestamp").truncate("h").name("bucket")
        return samples.group_by(["host", bucket]).aggregate(n=samples.count())

    src = StaticSource(samples([("a", m, 1) for m in range(0, 60, 10)]), name="samples")
    node = src.pipe(hourly)
    node.refresh()
    for minute in range(60, 60 * 12, 10):
        src.apply(Changes(inserts=samples([("a", minute, 1)])))
        entry = node.refresh()["hourly"]
        (report,) = entry.retention
        assert report.open <= report.bound
    assert node._stage is not None
    # The latest sample is at 11:50: buckets up to 08:50 are final.
    assert node._stage.view.retired_through == dt.datetime(2026, 11, 3, 8, 50)
