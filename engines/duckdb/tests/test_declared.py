"""DuckDB column types sverify refuses by their declared type (#1253).

Arrow exports a UUID as `string`, an ENUM as `dictionary<string>` and a BIT as
`binary`; DuckDB compares and orders them by its own rules. The refusal names
the exit, a cast to text in the source query, and after the cast DuckDB agrees
with the text model (duckdb-uuid-text-order, duckdb-uuid-string-cast,
duckdb-enum-order)."""

import duckdb
import pytest

from sverify.errors import UnsupportedError
from sverify_dev.slt import Replay  # noqa: F401  (the replay's check is this one)
from sverify_duckdb.declared import refuse_unmodelled

pytestmark = pytest.mark.backend("duckdb")

UUIDS = [
    "ffffffff-0000-0000-0000-000000000000",
    "00000000-0000-0000-0000-000000000001",
    "7fffffff-ffff-ffff-ffff-ffffffffffff",
    "80000000-0000-0000-0000-000000000000",
    "0a000000-0000-0000-0000-000000000000",
]


def _db() -> duckdb.DuckDBPyConnection:
    db = duckdb.connect()
    db.execute("CREATE TYPE mood AS ENUM ('sad', 'ok', 'happy')")
    db.execute("CREATE TABLE u(id UUID)")
    db.executemany("INSERT INTO u VALUES (?)", [(u,) for u in UUIDS])
    db.execute("CREATE TABLE e(m mood)")
    db.execute("INSERT INTO e VALUES ('happy'), ('sad'), ('ok')")
    return db


def _refuse(db: duckdb.DuckDBPyConnection, ddl_type: str) -> None:
    rel = db.sql(f"SELECT CAST(NULL AS {ddl_type}) AS c")
    refuse_unmodelled(rel.columns, rel.types, " of t")


@pytest.mark.parametrize(
    ("ddl_type", "exit_"),
    [
        ("UUID", "CAST(c AS VARCHAR)"),
        ("mood", "CAST(c AS VARCHAR)"),
        ("BIT", "CAST(c AS VARCHAR)"),
        ("BIGNUM", "CAST(c AS DECIMAL(p, 0))"),
        ("UUID[]", "CAST(c AS VARCHAR)"),
        ("STRUCT(a mood)", "CAST(c AS VARCHAR)"),
    ],
)
def test_refused_with_its_exit(ddl_type: str, exit_: str) -> None:
    with pytest.raises(ValueError, match="column c of t is") as e:
        _refuse(_db(), ddl_type)
    assert exit_ in str(e.value)


def test_uuid_message_names_the_exit() -> None:
    with pytest.raises(ValueError) as e:
        _refuse(_db(), "UUID")
    assert "lower-case hyphenated form" in str(e.value)


@pytest.mark.parametrize(
    "ddl_type",
    ["BIGINT", "DOUBLE", "DECIMAL(10, 2)", "VARCHAR", "DATE", "TIMESTAMP", "INTEGER[]",
     "STRUCT(a INT, b VARCHAR)", "MAP(VARCHAR, INT)", "HUGEINT", "BLOB", "INTERVAL"],
)  # fmt: skip
def test_modelled_types_pass(ddl_type: str) -> None:
    _refuse(_db(), ddl_type)


def test_ibis_uuid_names_the_exit() -> None:
    import ibis

    from sverify.plan_json import type_json

    with pytest.raises(UnsupportedError, match="CAST.*AS VARCHAR"):
        type_json(ibis.dtype("uuid"))


def test_uuid_after_cast_agrees() -> None:
    db = _db()
    q = db.execute
    text = [r[0] for r in q("SELECT CAST(id AS VARCHAR) FROM u ORDER BY id").fetchall()]
    assert text == sorted(UUIDS)
    assert text == [r[0] for r in q("SELECT id::VARCHAR FROM u ORDER BY id::VARCHAR").fetchall()]
    lo, hi = q("SELECT min(id)::VARCHAR, max(id)::VARCHAR FROM u").fetchall()[0]
    assert (lo, hi) == (min(UUIDS), max(UUIDS))
    assert q("SELECT min(id::VARCHAR), max(id::VARCHAR) FROM u").fetchall() == [(lo, hi)]


def test_uuid_equality_casts_the_string() -> None:
    db = _db()
    # The reason the column is refused as text: every spelling matches.
    assert db.execute("SELECT count(*) FROM u WHERE id = upper(id::VARCHAR)").fetchone() == (5,)
    assert db.execute(
        "SELECT count(*) FROM u WHERE id::VARCHAR = upper(id::VARCHAR)"
    ).fetchone() == (2,)
    with pytest.raises(duckdb.ConversionException):
        db.execute("SELECT id = 'nope' FROM u")


def test_enum_orders_by_declaration() -> None:
    db = _db()
    rows = db.execute("SELECT m::VARCHAR FROM e ORDER BY m").fetchall()
    assert [r[0] for r in rows] == ["sad", "ok", "happy"]
    assert db.execute("SELECT min(m)::VARCHAR, max(m)::VARCHAR FROM e").fetchone() == (
        "sad",
        "happy",
    )
