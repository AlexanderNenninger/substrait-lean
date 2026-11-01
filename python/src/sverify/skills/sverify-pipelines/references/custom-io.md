# Your own sources and sinks, and credentials

Read from an API, a database or a folder of files, and write to anything,
with the same exactly-once writes and contracts as Delta and Iceberg.

## A source: `read(since)` returns new rows and a cursor

`from_query(fn, cursor_on=...)` covers the high-water-mark case: `fn(since)`
returns the rows whose `cursor_on` is above `since` (all of them when `since`
is None), and the next read starts from the greatest value read.

```python
import pyarrow as pa
import pyarrow.compute as pc
from ibis import _

import sverify as sv
from sverify.io import from_query

events = pa.table({"id": [1, 2], "ts": [10, 20], "amount": [30, 5]})


def events_after(since):
    return (
        events
        if since is None
        else events.filter(pc.call_function("greater", [events["ts"], since]))
    )


@sv.transform(requires={"events": [_.amount >= 0]}, ensures=[_.amount > 10])
def big(events):
    return events.filter(events.amount > 10)


node = big(from_query(events_after, cursor_on="ts", name="events"))
node.refresh()
events = pa.concat_tables([events, pa.table({"id": [3], "ts": [30], "amount": [50]})])
print(node.refresh())
# big:
#   events@v1→v2: 1 insert(s), 0 delete(s); Δ trusted as rows appended to events v1→v2, assuming rows only arrive with a greater ts
# ...
```

Each read that changes something is a new version. The report repeats what
the batches assume; `refresh(audit=True)` reads `fn(None)` up to the cursor
and raises `sverify.errors.AuditError` where a row arrived late, below the
cursor. Other helpers:

* `from_frame(fn, name=...)`: `fn()` returns the whole table on every
  refresh; each read is diffed against the last, so the change is exact.
* `from_files(path, format="parquet", name=...)`: the files new in a
  directory (local, `s3://`, ...) since the last refresh, appended.

For anything else, subclass `Source`. `read` returns a `Batch` (an Arrow
table, a Polars or pandas DataFrame) with a cursor and a kind: `"append"`
(new rows), `"snapshot"` (the whole table, diffed) or `"changes"` (rows
added, and `deletes=` rows removed):

```python
from sverify.io import Batch, Source


class Prices(Source):
    """A price list fetched whole: the source diffs each fetch."""

    def __init__(self, fetch):
        super().__init__("prices")
        self.fetch = fetch

    def read(self, since):
        return Batch(self.fetch(), kind="snapshot")


prices = Prices(lambda: pa.table({"sku": ["a", "b"], "price": [3, 4]}))
print(prices.latest(), prices.snapshot().table.num_rows)
# 1 2
```

What such sources can and cannot promise:

* They have no metadata, so preconditions on them are checked on the rows.
* They keep the table as of the latest read in memory (joins and keys need
  it).
* A restarted job reads them in full again. Their versions continue above
  the ones the job's sinks recorded, so the stored nodes reading them are
  recomputed and written once, never skipped by mistake.
* A table format with statistics and a change feed implements the full
  `sverify.io.VersionedSource` protocol instead (`schema`, `latest`,
  `snapshot`, `changes`), building its results with `Snapshot` and
  `SourceBatch.unchanged`, `.from_changes` and `.from_snapshot`.

## A sink: `write(change)`, and `committed()` for exactly once

`Sink.write` gets a `SinkChange`: `inserts` and `deletes` since the last
write (Arrow tables), or with `replace` the whole `table`, and the
`contract` to record. sverify skips a state whose `contract.epoch` the sink
has already committed, unless another plan committed it (`contract.plan`
differs): then it hands `write` the whole table with `replace`. `committed()` reads the last contract back from the
sink, so that holds across restarts too; without it, sverify remembers for
the life of the process.

```python
import json
from pathlib import Path

from sverify.io import Contract, Sink, StaticSource


class JsonLines(Sink):
    """Each state as a JSON lines file, with the contract beside it."""

    def __init__(self, path):
        super().__init__(Path(path).stem, location=str(path))
        self.path = Path(path)
        self.record = self.path.with_suffix(".contract.json")

    def committed(self):
        if not self.record.exists():
            return None
        return Contract.from_json(self.record.read_text())

    def write(self, change):
        rows = change.table.to_pylist()
        self.path.write_text("".join(json.dumps(r) + "\n" for r in rows))
        self.record.write_text(change.contract.to_json())


orders = StaticSource(pa.table({"id": [1, 2], "ts": [1, 2], "amount": [30, 5]}), name="events")
stored = big(orders).write(JsonLines("big.jsonl"))
print(stored.refresh().writes[0])
# big from events@v0: overwrite, 1 row(s) written, 0 deleted
print(big(orders).write(JsonLines("big.jsonl")).refresh().writes[0])  # a restarted job
# big from events@v0: already committed
```

* `sink_from(fn, name=...)` hands the whole table to `fn` whenever it
  changes: `node.write(sink_from(lambda t: t.to_pandas().to_csv("out.csv"),
  name="out"))`.
* `change.schema` has the columns the node proves NOT NULL as not nullable.
  Store `change.contract.checks` as constraints where the target has them.
* Nodes reading a stored node read what this process wrote, with its exact
  changes; override `source()` to have them read the sink instead.
* `write` may return a `sverify.io.SinkWrite` to report its own mode and
  version; None reports `"overwrite"` or `"update"`.

## Credentials and storage

sverify stores no credentials: it passes options to the library doing the
I/O, and the contract a sink records holds none.

* **Delta** (S3, GCS, Azure): delta-rs's default chain applies when no
  options are given: environment variables (`AWS_REGION`,
  `AWS_ACCESS_KEY_ID`, ...), `~/.aws` profiles, instance or pod roles.
  Prefer it. Otherwise give `storage_options`: a `sverify.io.Storage`
  shared by every table, holding a mapping or a function that returns fresh
  options, called whenever a table is opened (so expiring tokens renew).
  `repr` shows option names only.
* **Iceberg** (REST, Glue, ...): the pyiceberg catalog holds them, from
  `load_catalog` properties, `~/.pyiceberg.yaml` or `PYICEBERG_*` variables.
* **Files** (`from_files`): the filesystem `path`'s URI names, with its
  default chain, or `filesystem=` a `pyarrow.fs.FileSystem`.
* **Your own source or sink**: take a `Storage` and call `options()` when
  you connect, rather than literal keys, which travel with any pickled
  object.

```python
from sverify.io import DeltaSink, DeltaSource, Storage


def s3_options():
    # Fetch short-lived credentials here, e.g. from boto3 or a vault.
    return {"AWS_REGION": "eu-central-1"}


s3 = Storage(s3_options)
orders_s3 = DeltaSource("s3://lake/orders", storage_options=s3)  # nothing opened yet
paid_s3 = DeltaSink("s3://lake/paid", storage_options=s3)
print(s3, Storage({"AWS_SECRET_ACCESS_KEY": "..."}))
# Storage(s3_options) Storage(AWS_SECRET_ACCESS_KEY)
```

```yaml
# ~/.pyiceberg.yaml: an Iceberg REST catalog with a token
catalog:
  lake:
    uri: https://catalog.example.com
    token: <from your secret store>
```
