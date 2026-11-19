"""`sverify.engine`: what `verify` reads of its inputs."""

from __future__ import annotations


def test_verify_reads_input_columns_as_a_table_made_from_them_does() -> None:
    """`verify` holds no connection, but its plan reads each input as one
    would (a `timestamp` is `timestamp(6)`, #1485)."""
    import ibis

    from sverify.contracts import _as_arrow_gives
    from sverify.engine import connect, plan_json

    schema = ibis.schema({"k": "!int64", "ts": "timestamp", "d": "decimal(10, 2)"})
    con = connect()
    con.create("t", schema)
    mine = _as_arrow_gives({"t": schema})
    held = ibis.table(mine["t"], name="t")
    assert held.schema() == con.table("t").schema()
    for q in (lambda t: t.select("ts", "d"), lambda t: t.filter(t.k > 0).select(x=t.ts)):
        assert plan_json(con, q(held)) == plan_json(con, q(con.table("t")))
