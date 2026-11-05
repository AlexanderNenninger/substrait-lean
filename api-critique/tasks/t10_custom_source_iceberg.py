"""Task 10: an API that returns new events since a cursor, into an Iceberg table.

The data engineer's other common job: a source that isn't a table format
(`from_query` over an HTTP API or a database), a rollup, an Iceberg sink in a
local SQL catalog, a restart.
"""

import datetime as dt
import shutil
import tempfile

import pyarrow as pa
from ibis import _
from pyiceberg.catalog.sql import SqlCatalog

import sverify as sv
from sverify.io import from_query

# A fake upstream: an append-only event log, queried by timestamp.
t0 = dt.datetime(2026, 11, 5, 9, 0)
LOG = [
    {"event_id": 1, "ts": t0, "user_id": 7, "kind": "click"},
    {"event_id": 2, "ts": t0 + dt.timedelta(minutes=1), "user_id": 7, "kind": "buy"},
    {"event_id": 3, "ts": t0 + dt.timedelta(minutes=2), "user_id": 8, "kind": "click"},
]
SCHEMA = pa.schema(
    [("event_id", pa.int64()), ("ts", pa.timestamp("us")), ("user_id", pa.int64()), ("kind", pa.string())]
)


def fetch(since):
    """What I'd write against a real API: rows with ts > since."""
    rows = [r for r in LOG if since is None or r["ts"] > since]
    return pa.Table.from_pylist(rows, schema=SCHEMA)


import inspect  # noqa: E402

print("from_query:", inspect.signature(from_query))
print(inspect.getdoc(from_query).split("\n\n")[0])

events = from_query(fetch, cursor_on="ts", name="events")


@sv.transform(
    requires={"events": [sv.unique("event_id"), _.event_id.notnull(), _.user_id.notnull(), _.kind.notnull()]},
    ensures=[sv.unique("user_id", "kind"), _.n >= 1],
)
def per_user(events):
    return events.group_by(["user_id", "kind"]).aggregate(n=events.count())


warehouse = tempfile.mkdtemp()
catalog = SqlCatalog("local", uri=f"sqlite:///{warehouse}/cat.db", warehouse=f"file://{warehouse}")
catalog.create_namespace("analytics")

from sverify.io import IcebergSink  # noqa: E402

node = events.pipe(per_user).write(IcebergSink(catalog, "analytics.per_user"))
print(node.refresh())

LOG.append({"event_id": 4, "ts": t0 + dt.timedelta(minutes=3), "user_id": 7, "kind": "click"})
print(node.refresh())
print(sorted(node.to_arrow().to_pylist(), key=str))

# A late event, older than the cursor: what happens?
LOG.append({"event_id": 5, "ts": t0 - dt.timedelta(minutes=10), "user_id": 9, "kind": "click"})
from sverify.errors import AuditError  # noqa: E402

try:
    node.refresh(audit=True)
except AuditError as e:
    print("audit:", e)
print("without audit:\n", node.refresh().summary())
print(sorted(node.to_arrow().to_pylist(), key=str))  # is user 9 there?

# Restart: build the same nodes again, refresh.
events2 = from_query(fetch, cursor_on="ts", name="events")
node2 = events2.pipe(per_user).write(IcebergSink(catalog, "analytics.per_user"))
print("after restart:\n", node2.refresh())
print("table rows:", catalog.load_table("analytics.per_user").scan().to_arrow().num_rows)
print("properties:", catalog.load_table("analytics.per_user").properties)
shutil.rmtree(warehouse)
