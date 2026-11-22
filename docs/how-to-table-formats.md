# Delta Lake and Iceberg

The examples on this page run in order (`python/tests/test_readme.py`), from this setup:

```python
import ibis
import pyarrow as pa
import sverify as sv
from ibis import _
from sverify.io import Changes, StaticSource

orders = StaticSource(
    pa.table({"id": [1, 2], "customer": ["ada", "bob"], "amount": [30, 5]}), name="orders"
)
orders.apply(Changes(inserts=[(3, "cy", 50)], deletes=[(1, "ada", 30)]))  # now orders holds bob and cy
from sverify.io import DeltaSink, DeltaSource
```

## A complete job, in outline

The tasks below build on this job, the first notebook of the
[tour](../README.md#the-tour) in outline: a Delta table of card payments,
a contract that finds double charges, a sink, and a refresh from the
Change Data Feed.

```python
import datetime as dt
from pathlib import Path
from tempfile import mkdtemp

import pyarrow as pa
from deltalake import DeltaTable, write_deltalake
from sverify.engines import ENGINES
from sverify.io import DeltaSink, DeltaSource

lake = Path(mkdtemp())
TXN = pa.schema([
    pa.field("txn_id", pa.int64(), nullable=False),
    pa.field("card_id", pa.int64(), nullable=False),
    pa.field("merchant", pa.string()),
    pa.field("amount_cents", pa.int64(), nullable=False),
    pa.field("ts", pa.timestamp("us"), nullable=False),
])

def txns(*rows):
    return pa.Table.from_pylist([dict(zip(TXN.names, r)) for r in rows], schema=TXN)

def at(minute):
    return dt.datetime(2026, 3, 2, 9, minute)

write_deltalake(lake / "transactions",
                txns((1, 10, "coffee", 450, at(0)), (2, 10, "coffee", 450, at(2)),
                     (3, 11, "books", 2599, at(10))),
                configuration={"delta.enableChangeDataFeed": "true"})
DeltaTable(lake / "transactions").alter.add_constraint({"non_negative": "amount_cents >= 0"})

@sv.transform(
    requires={"transactions": [sv.unique("txn_id"), _.amount_cents >= 0,
                               _.ts < dt.datetime(2100, 1, 1)]},
    ensures=[sv.unique("first_txn", "duplicate_txn"), _.first_txn < _.duplicate_txn,
             _.merchant.notnull(), _.amount_cents >= 0],
)
def duplicate_payments(transactions):
    a, b = transactions, transactions.view()
    return a.join(
        b,
        (a.card_id == b.card_id) & (a.merchant == b.merchant)
        & (a.amount_cents == b.amount_cents) & (a.txn_id < b.txn_id)
        & (b.ts >= a.ts) & (b.ts <= a.ts + ibis.interval(minutes=5)),
    ).select(first_txn=a.txn_id, duplicate_txn=b.txn_id, merchant=a.merchant,
             amount_cents=a.amount_cents)

transactions = DeltaSource(str(lake / "transactions"))
dups = transactions.pipe(duplicate_payments)  # proves the contract
sink = DeltaSink(str(lake / "duplicate_payments"))
stored = dups.write(sink)  # NOT NULL and CHECK constraints from `ensures`, the contract in the commit
first = stored.refresh()   # checks the preconditions, computes, writes
for p in first["duplicate_payments"].preconditions:
    print(p)
# transactions: unique(txn_id) (checked on data)
# transactions: (_.amount_cents >= 0) (Delta constraint)
# transactions: (_.ts < datetime(2100, 1, 1)) (file stats @v1)

# A late duplicate of transaction 3 arrives, and transaction 2 is reversed.
t = DeltaTable(lake / "transactions")
write_deltalake(t, txns((4, 11, "books", 2599, at(13))), mode="append")
t.delete("txn_id = 2")
print(stored.refresh())  # the Change Data Feed v1→v3, the proved delta plans, one MERGE commit
# duplicate_payments:
#   transactions@v1→v3: 1 insert(s), 1 delete(s); Δ trusted as coming from Delta CDF v1→v3
# ...
#   wrote duplicate_payments from transactions@v3: merge v3, 1 row(s) written, 1 deleted
assert stored.to_arrow().to_pylist() == [
    {"first_txn": 3, "duplicate_txn": 4, "merchant": "books", "amount_cents": 2599}]

for engine in ENGINES:  # the same rows on DuckDB and Polars
    again = duplicate_payments(transactions)
    again.refresh(engine=engine)
    assert again.to_arrow().to_pylist() == stored.to_arrow().to_pylist()
```

## Delta Lake and Iceberg
`sverify.io` reads and writes Delta Lake (delta-rs) and Iceberg (pyiceberg)
tables. A table format plays four roles:

* A change source. A transform reads `DeltaSource(uri)` or
  `IcebergSource(catalog, identifier)` directly. The first `refresh()` loads
  a snapshot and records its version; each later one reads the Change Data
  Feed (or, for Iceberg, the files that appends added) from that version to
  the latest, applies it, and records the new version. A failed refresh
  changes nothing, so a retry never applies a batch twice. Where the history
  is gone (CDF off, files vacuumed, row-level deletes in Iceberg), the data
  files that changed are diffed, and the report says so.
  `refresh(audit=True)` also compares the batch with the new snapshot and
  every node with a recompute, before committing anything (`AuditError`).
  A Delta table, local or on S3, and a local Iceberg table are never loaded
  into Python: the pipeline holds the Parquet files of its version, with the
  rows that deletion vectors or position delete files remove, and each engine
  reads them itself: DuckDB with `read_parquet`, Polars with
  `scan_parquet` on the streaming engine, Spark with its Parquet reader. A
  Delta table's partition values come from its log, and its column mapping by
  name or by id is followed, so a renamed column is found. Iceberg files are
  read by field id, and equality deletes apply to the files written before
  them. S3 tables are read through DuckDB's `httpfs` with a temporary secret
  made from the `Storage`, kept out of SQL text and logs; with no explicit
  key, DuckDB's `aws` extension is needed, and without it the table reads
  through Arrow (sverify installs nothing). A table the scan cannot describe
  also reads through Arrow: a Delta table with other reader features, column
  mapping over nested columns, partition columns whose type the log's values
  do not give exactly, or deletion vectors on S3; stores other than S3; an
  Iceberg table whose files are not local Parquet or have no field ids.
* A source of preconditions. `requires` conditions are proved from
  schema nullability, Delta CHECK constraints and per-file statistics:
  min/max of integers, doubles (only where the files count no NaN), dates
  and timestamps, and NULL counts, so a nullable column still proves
  `amount >= 0 OR amount IS NULL`. A batch only uses the statistics of the
  files it added. Strings, decimals and zoned timestamps get no bounds, and
  keys are always checked on the data, since neither format enforces them.
* Proved file pruning (Delta). `DeltaSource(uri, where="amount * 2 > 100")`
  reads only the rows on which the condition is TRUE, and skips a file only
  if Lean proves from its statistics that the condition is TRUE on none of
  its rows. That covers conditions the readers' own statistics pushdown
  doesn't, such as arithmetic on a column. Changes are filtered the same
  way, and the condition becomes a fact about every row for the contracts.
* A sink that carries the contract. `node.write(DeltaSink(uri))` and
  `node.write(IcebergSink(catalog, identifier))` store a node in one commit
  per state, exactly once (keyed by the source versions). A Delta source
  dropped and created again at the same path has a new table id, which the
  contract records: its sinks are rewritten from the new table. When two
  processes refresh the same `DeltaSink`, the second to commit an epoch
  writes nothing: if the first wrote the same state, its refresh reports
  "already committed"; otherwise it raises `ConcurrentWriteError`, and its
  next refresh recovers.
  The proved guarantees become NOT NULL columns and CHECK constraints (Delta)
  or table properties (Iceberg). The NOT NULL columns are those `ensures`
  states (`_.id.notnull()`) and those the proved report shows are never NULL
  (not nullable in `report.output`).
  The commit records the plan hash, the
  source versions and the contract (`sverify.io.Contract`, under the key
  `sverify.contract`, in the format of
  [`sink-contract.schema.json`](../python/src/sverify/schemas/sink-contract.schema.json),
  which every 1.x release reads: [stability.md](stability.md#the-formats)).
  A job that reads the table gets its preconditions from them. After the first write, `DeltaSink` MERGEs each
  change in one commit, and `IcebergSink` writes it as one snapshot of
  position delete files and a data file of the new rows.
  `IcebergSink(catalog, identifier, location=..., partition_by=[("ts", "day")],
  properties={...})` creates its table at that location, partitioned and
  with those properties, which a catalog without a default location, such
  as Unity Catalog's, needs.
  A streaming sink adds a snapshot and small files on every refresh.
  `DeltaSink(uri, compact_every=..., vacuum_retention=...)` and
  `IcebergSink(catalog, identifier, compact_every=..., snapshot_retention=...)`
  compact the table after every so many writes and then remove what older
  versions alone used; `maintain()` does it on demand.

Schema changes. A batch whose data fits the old schema (added columns,
widened types whose values still fit) is read in it, and the report names
the change. Otherwise the nodes reading the source are planned again and
recomputed, except a node with a contract, whose proof was for the old
schema: `refresh` then raises `SchemaError` and changes nothing.

Tables outside a table format, such as a small lookup table, are
`StaticSource(table, version=1, name="regions")`, so that sinks still have a
version for every input; `regions.apply(Changes(...))` changes some rows,
and `regions.replace(new_table, version=2)` swaps the table, which recomputes
the nodes that read it.

Your own sources and sinks take one method each. A `sverify.io.Source`
implements `read(since)`, which returns the new rows and a cursor;
`from_query(fn, cursor_on="ts")`, `from_frame(fn)` and `from_files(path)`
build one from a function or a directory. Sverify numbers the reads as
versions, works out the change, and says in the report what the reads
assume ("rows only arrive with a greater ts"), which `refresh(audit=True)`
checks. A `sverify.io.Sink` implements `write(change)` and optionally
`contract()`, and sverify writes each state once, with its contract;
`sink_from(fn)` hands the whole table to a function. `Storage` holds object
store options and credentials by name for every table that needs them
([Credentials](how-to-credentials.md#credentials)). [Notebook 5](../notebooks/05_pipelines_and_engines.py) of the tour walks
through both.

`sverify.io.flight.FlightSource(location, table)` reads a table of a
numbered batch log on an Arrow Flight server (`pip install
'sverify[flight]'`). The server numbers each batch it receives with
`do_put`, one counter across tables, and keeps them in order. `do_get` with
the ticket `{"table": t, "after": n}` streams the batches numbered above
`n`, each with `{"seq": s}` as app metadata, and names in the stream's schema
metadata the `floor`, the lowest number it still holds; an optional
`"until": m` stops at `m`. The source's cursor is `{"seq": n, "floor": f}`,
the number of the last batch read and the floor at that read. A refresh
appends the new batches, as they arrived and without a copy, and the batches
below the floor, which the server dropped past its retention, come back as
deletes, so the source holds the server's window of rows. A restarted job
resumes at the cursor its sink recorded, unless the server dropped batches
since; then it reads the whole log again. The report states what this assumes: the server numbers batches in
order of arrival, never changes one, and drops only whole batches below its
floor. `sverify.testing.FlightLog()` is a small in-memory server that keeps such a log
(`keep=` batches per table, or `drop(table, below=n)`), the one
[the tests](../python/tests/test_io_flight.py) run against. With `schema=`, a
`FlightSource` proves contracts without asking the server, and `credentials=`
names a bearer token ([Credentials](how-to-credentials.md#credentials)):

```python
import pyarrow.flight as fl
from sverify.io.flight import FlightSource
from sverify.testing import FlightLog

log = FlightLog(keep=10_000)  # on 127.0.0.1, at a free port
location = f"grpc://127.0.0.1:{log.port}"


def send(rows):
    batch = pa.table(rows)
    writer, _ = fl.connect(location).do_put(fl.FlightDescriptor.for_path("samples"), batch.schema)
    writer.write_table(batch)
    writer.close()


@sv.transform()
def busy(samples):
    return samples.filter(samples.cpu > 0.5)


send({"host": ["pi3"], "cpu": [0.75]})
node = busy(FlightSource(location, "samples"))
node.refresh()
send({"host": ["nas"], "cpu": [0.9]})
print(node.refresh())
# busy:
#   samples@v1→v2: 1 insert(s), 0 delete(s); Δ trusted as rows appended to samples v1→v2, assuming the Flight server numbers batches in order of arrival, ...
log.shutdown()
```

A restarted job resumes from its sink and skips the recompute. You build the
same nodes again and refresh; a stored node takes the stored rows only if
its plan and source versions match what the sink recorded; otherwise it is
computed, and the report says why. A source of your own resumes too if it
implements `restore(cursor)`: the sink records the source's cursor next to
its version, and the restarted job starts from the table as of that cursor
and reads only what is new since. `from_query` and `from_files` do this; a
cursor whose rows are gone (`restore` returns None) reads the whole table
again:

```python
restarted = DeltaSource(str(lake / "transactions")).pipe(duplicate_payments).write(
    DeltaSink(str(lake / "duplicate_payments")))
print(restarted.refresh())
# duplicate_payments:
#   resumed from .../duplicate_payments@v3
# ...
#   wrote duplicate_payments from transactions@v3: already committed (v3)
```

A `DeltaSink` that writes every minute gathers commits and small files,
which readers replay and open. Its options keep the table small:
`checkpoint_interval` and `log_retention` set the table's checkpoint interval
and log retention, `compact_every=n` compacts the table after every `n`
writes, and `vacuum_retention` then removes the files older versions needed.
`sink.maintain(vacuum_retention=...)` does the same by hand. These commits carry the
contract, and a restarted job resumes past them, as it does past another
writer's `OPTIMIZE`, `VACUUM`, property or constraint change. A commit that
changes rows, by anyone else, makes the job compute the node again. Keep the
log retention longer than the gap between two writes: the contract is read
from the log.

Each refresh report names what it trusted: that the change feed turns the
old snapshot into the new one, and that writers and file statistics are
correct (Delta's millisecond timestamp maxima are widened by 999 µs; with
deletion vectors the statistics cover deleted rows too, which still bounds
the live ones). Iceberg tables with equality deletes are read on DuckDB from local Parquet files without partition fields, and otherwise can't be read. What is
proved is listed under [Table formats](proved-theorems.md#table-formats).
