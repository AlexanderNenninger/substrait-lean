"""What the node, pipeline and table-format tests share: the orders schema
and its tables, the transforms most of them chain, and small readers of
nodes and reports.

Transforms that share a name across test files but not a contract stay in
their files; the two `paid`s here differ in what they drop and promise, and
say so in their names."""

from collections.abc import Callable
from typing import Any

import pyarrow as pa
from deltalake import DeltaTable, write_deltalake
from ibis import _

import sverify as sv
from sverify.engines import create_table, run
from sverify_dev.examples import create_tables, orders
from sverify.io import DeltaSource

#: Orders with a non-NULL key and a nullable amount.
ORDERS = pa.schema(
    [
        pa.field("id", pa.int64(), nullable=False),
        pa.field("customer", pa.string()),
        pa.field("amount", pa.int64()),
    ]
)


def arrow_table(schema: pa.Schema, rows: list[tuple]) -> pa.Table:
    """`rows` (tuples in `schema`'s order) as an Arrow table."""
    return pa.Table.from_pylist(
        [dict(zip(schema.names, r, strict=True)) for r in rows], schema=schema
    )


def orders_table(rows: list[tuple]) -> pa.Table:
    return arrow_table(ORDERS, rows)


def make_orders(path, rows, *, cdf=True, constraints=None) -> DeltaSource:
    """A Delta table of `rows` at version 1 (the create is version 0), with
    its Change Data Feed unless `cdf` is False."""
    DeltaTable.create(
        path, ORDERS, configuration={"delta.enableChangeDataFeed": "true"} if cdf else None
    )
    if constraints:
        DeltaTable(path).alter.add_constraint(constraints)
    write_deltalake(path, orders_table(rows), mode="append")
    return DeltaSource(str(path))


def connect_with(orders=(), customers=()):
    """A connection holding `sverify_dev.examples`' orders and customers."""
    con = sv.connect()
    create_tables(con, orders, customers)
    return con


def bound_orders(rows):
    """`sverify_dev.examples`' unbound `orders`, bound to `rows`."""
    con = sv.connect()
    create_table(con, "orders", orders.schema(), rows)
    return con.table("orders")


# -- transforms -----------------------------------------------------------------


#: Keyed orders without a NULL amount.
@sv.transform(
    requires={"orders": [_.amount >= 0, _.id.notnull(), sv.unique("id")]},
    ensures=[_.amount >= 0, _.amount.notnull(), sv.unique("id")],
)
def paid(orders):
    return orders.filter(orders.amount.notnull())


def _paid_nonzero():
    @sv.transform(requires={"orders": [_.amount >= 0]}, ensures=[_.amount > 0])
    def paid(orders):
        return orders.filter(orders.amount > 0)

    return paid


#: Orders without a zero amount, keyed or not (`amount` is NOT NULL in the
#: schemas its tests use). Its nodes are named "paid" too, like `paid`'s:
#: a node is named after its transform's function.
paid_nonzero = _paid_nonzero()


@sv.transform(
    requires={"t": [_.amount >= 0, _.amount.notnull(), sv.unique("id")]},
    ensures=[_.doubled >= 0, _.doubled.notnull(), sv.unique("id")],
)
def doubled(t):
    return t.select(t.id, t.customer, doubled=t.amount * 2)


# -- reading nodes and reports ------------------------------------------------------


def _nulls_last(row: tuple) -> tuple:
    return tuple((v is None, v) for v in row)


def rows(node) -> list[tuple]:
    """A refreshed node's rows, sorted (NULLs last)."""
    return sorted((tuple(r.values()) for r in node.to_arrow().to_pylist()), key=_nulls_last)


def recomputed(node, *sources) -> list[tuple]:
    """`node`'s plan run from scratch on the current tables of `sources`
    (static or versioned): what its maintained state must equal."""
    con = sv.connect()
    for src in sources:
        con.put(src.name, src.snapshot().table)
    return sorted((tuple(r.values()) for r in run(con, node.plan).to_pylist()), key=_nulls_last)


def discharged(found) -> dict[tuple[str, str], str]:
    """How each precondition was established, by (table, condition)."""
    return {(p.table, p.condition): p.source for p in found}


def spy_on(monkeypatch, target: str, record: Callable[..., Any]) -> list[Any]:
    """Patch the function at `target` (a dotted path) to append
    `record(*args)` to the returned list before each call."""
    module, name = target.rsplit(".", 1)
    real = getattr(__import__(module, fromlist=[name]), name)
    seen: list[Any] = []

    def spy(*args, **kwargs):
        seen.append(record(*args, **kwargs))
        return real(*args, **kwargs)

    monkeypatch.setattr(target, spy)
    return seen


def batch(node, **refresh):
    """Refresh `node` (with `refresh`'s arguments) and return its own stage's
    batch report: the source versions it went from and to, the changes and
    the preconditions checked on them."""
    report = node.refresh(**refresh)[node.name].report
    assert report is not None, f"{node.name}: the refresh computed it in full"
    return report
