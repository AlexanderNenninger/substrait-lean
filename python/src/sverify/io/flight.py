"""Arrow Flight: `FlightSource` reads a table of a numbered batch log, and
`FlightLog` is a small server that keeps one.

The protocol, which any Flight server can implement:

* `do_put` to the descriptor path `[table]` appends record batches to the
  table. The server numbers each batch it receives, with one counter across
  tables, keeps them in that order, and answers each with
  `{"seq": n}` as app metadata.
* `do_get` with the ticket `{"table": t, "after": n, "until": m}` (JSON;
  `after` and `until` may be null or left out) streams the batches of `t`
  numbered in `(n, m]`, in order, each with `{"seq": s}` as app metadata.
  The stream's schema metadata has `floor`, the lowest number the server
  still holds for `t` (the next number to come if it holds none). A table
  nothing was sent to yet streams no batches.
* The server drops only whole batches, and only below its floor: the
  batches past its retention.

`FlightSource`'s cursor is `{"seq": n, "floor": f}`: the number of the last
batch read and the floor it was read at. A refresh asks for the batches after
`n` and appends them; the batches it holds that are now below the floor come
back as deletes, so the source holds the server's window of rows. The
batches are registered with the engine as they arrived, without a copy.

Needs `pyarrow` built with Flight, as the PyPI wheels are:
`pip install 'sverify[flight]'`.
"""

from __future__ import annotations

import json
import threading
import warnings
from collections.abc import Iterator
from typing import Any

import pyarrow as pa

try:
    import pyarrow.flight as fl
except ImportError as e:  # pragma: no cover - pyarrow built without Flight
    raise ImportError(
        "sverify.io.flight needs pyarrow with Flight: pip install 'sverify[flight]'"
    ) from e

from sverify.io._secrets import Secret, as_secret
from sverify.io._source import Batch, Source

ASSUMES = (
    "the Flight server numbers batches in order of arrival, never changes one, "
    "and drops only whole batches below its floor"
)


def _meta(seq: int) -> pa.Buffer:
    return pa.py_buffer(json.dumps({"seq": seq}).encode())


class FlightSource(Source):
    """A table of a numbered batch log on an Arrow Flight server, such as
    `FlightLog` (the module's docstring has the protocol).

    The cursor is `{"seq": n, "floor": f}`, the number of the last batch
    read and the server's floor at that read. Each refresh streams the
    batches after `n` (`do_get`) and appends them; the batches below the
    server's floor, dropped past its retention, come back as deletes. A
    restarted job resumes at a cursor its sink recorded (`restore`) unless
    the server dropped batches since: their rows can't be read as deletes
    any more, so the job reads the whole log again. The refresh report
    states what this rests on: the server numbers batches in order of
    arrival, never changes one, and drops only whole batches below its
    floor. `refresh(audit=True)` reads the batches
    up to the cursor again and compares.

    Args:
        location: The server, such as `"grpc://pi3:8815"`.
        table: The table's name on the server.
        name: The table's name in the plans that read it. Default: `table`.
        schema: The table's schema. With it, contracts are proved without
            asking the server, and a log that starts empty works. Default:
            the first batch's.
        secret: The bearer token, by name or reference (`sverify.io.Secret`,
            such as `"env:FLIGHT_TOKEN"`), read at each connection and sent
            as the `authorization` header. Default: None.
        token: The bearer token's value. Deprecated: it travels with the
            source; name it with `secret` instead. Default: None.
        timeout: Seconds a call may take. Default: 30.

    Examples:
        ```python
        import pyarrow as pa
        import pyarrow.flight as fl
        import sverify as sv
        from sverify.io.flight import FlightLog, FlightSource

        server = FlightLog()
        client = fl.connect(f"grpc://127.0.0.1:{server.port}")
        writer, _ = client.do_put(
            fl.FlightDescriptor.for_path("samples"),
            pa.schema([("host", pa.string()), ("cpu", pa.float64())]),
        )
        writer.write_table(pa.table({"host": ["a"], "cpu": [0.5]}))
        writer.close()


        @sv.transform()
        def busy(samples):
            return samples.filter(samples.cpu > 0.25)


        node = busy(FlightSource(f"grpc://127.0.0.1:{server.port}", "samples"))
        node.refresh()
        ```
    """

    def __init__(
        self,
        location: str,
        table: str,
        *,
        name: str | None = None,
        schema: pa.Schema | None = None,
        secret: str | Secret | None = None,
        token: str | None = None,
        timeout: float = 30.0,
    ):
        super().__init__(name or table, schema=schema, assumes=ASSUMES)
        self.location, self.table = location, table
        self.secret = as_secret(secret, "FlightSource(secret=)")
        if token is not None:
            warnings.warn(
                "FlightSource(token=) is deprecated: name the token with secret= "
                "(such as secret='env:FLIGHT_TOKEN'), so no value travels with the source",
                DeprecationWarning,
                stacklevel=2,
            )
        self.token, self.timeout = token, timeout
        self._client: fl.FlightClient | None = None
        self._held: dict[int, pa.RecordBatch] = {}
        """The batches read and not dropped yet, by number, in order."""

    def __getstate__(self) -> dict[str, Any]:
        state = self.__dict__.copy()
        state["_client"] = None
        return state

    def __repr__(self) -> str:
        return f"FlightSource({self.location!r}, {self.table!r})"

    def _get(
        self, after: int | None, until: int | None = None
    ) -> tuple[list[tuple[int, pa.RecordBatch]], int]:
        """The batches numbered in `(after, until]`, and the server's floor."""
        if self._client is None:
            self._client = fl.connect(self.location)
        token = self.secret.value() if self.secret is not None else self.token
        headers = [(b"authorization", f"Bearer {token}".encode())] if token else []
        options = fl.FlightCallOptions(headers=headers, timeout=self.timeout)
        ticket = {"table": self.table, "after": after, "until": until}
        try:
            reader = self._client.do_get(fl.Ticket(json.dumps(ticket).encode()), options)
            meta = reader.schema.metadata or {}
            if b"floor" not in meta:
                raise ValueError(
                    f"{self.name}: the Flight stream names no floor in its schema metadata"
                )
            floor = int(meta[b"floor"])
            got = []
            for chunk in reader:
                seq = json.loads(chunk.app_metadata.to_pybytes())["seq"]
                got.append((seq, chunk.data.replace_schema_metadata(None)))
        except fl.FlightUnavailableError:
            self._client = None  # connect again on the next read
            raise
        return got, floor

    def _window(self) -> pa.Table:
        """The batches held, as one table without a copy."""
        if not self._held:
            return self._st().table.schema.empty_table()
        return self._fit(pa.Table.from_batches(list(self._held.values())))

    def _changed(self, table: pa.Table, inserts: pa.Table, deletes: pa.Table) -> pa.Table:
        # The window is the batches held, so nothing needs matching.
        return self._window()

    def read(self, since: Any) -> Batch | None:
        if since is None:
            self._held.clear()
        after = None if since is None else since["seq"]
        got, floor = self._get(after)
        deletes = [self._held.pop(s) for s in [s for s in self._held if s < floor]]
        self._held.update(got)
        if not got and not deletes:
            return None
        table = pa.Table.from_batches([b for _, b in got]) if got else None
        cursor = {"seq": got[-1][0] if got else after, "floor": floor}
        if not deletes:
            return Batch(table, cursor=cursor)
        empty = pa.Table.from_batches([], schema=deletes[0].schema)
        return Batch(
            empty if table is None else table,
            cursor=cursor,
            kind="changes",
            deletes=pa.Table.from_batches(deletes),
        )

    def reread(self, cursor: Any) -> Any:
        """The server's batches up to `cursor`, for `refresh(audit=True)`."""
        if cursor is None:
            return self._st().table.schema.empty_table()
        got, _ = self._get(None, until=cursor["seq"])
        schema = self._st().table.schema
        return pa.Table.from_batches([b for _, b in got]) if got else schema.empty_table()

    def restore(self, cursor: Any) -> Any:
        """The table as of `cursor`, a cursor a sink recorded in an earlier
        process: the batches up to it, or None if the server dropped
        batches since (their rows would never come back as deletes)."""
        if not isinstance(cursor, dict) or not {"seq", "floor"} <= cursor.keys():
            return None
        got, floor = self._get(None, until=cursor["seq"])
        if cursor["floor"] <= cursor["seq"] and floor > cursor["floor"]:
            return None  # the lowest batch held at the cursor is gone
        self._held = dict(got)
        if not got:
            return None if self._declared is None else self._declared.empty_table()
        return pa.Table.from_batches([b for _, b in got])


class FlightLog(fl.FlightServerBase):
    """A Flight server that keeps tables as numbered batch logs in memory,
    the server `FlightSource` reads (the module's docstring has the
    protocol). It starts serving when created.

    Args:
        location: Where to listen. Default: `"grpc://127.0.0.1:0"`, a free
            port (`port` says which).
        keep: The batches each table keeps; older ones are dropped after a
            `do_put`. Default: None, all of them.
        **kwargs: Passed to `pyarrow.flight.FlightServerBase`, such as
            `middleware` for authentication.

    Attributes:
        port: The port it listens on.
    """

    def __init__(self, location: str = "grpc://127.0.0.1:0", *, keep: int | None = None, **kwargs):
        super().__init__(location, **kwargs)
        self.keep = keep
        self.seq = 0
        self.tables: dict[str, tuple[pa.Schema, list[tuple[int, pa.RecordBatch]]]] = {}
        self._lock = threading.Lock()

    def drop(self, table: str, below: int) -> None:
        """Drop the batches of `table` numbered below `below`, as a
        retention does."""
        with self._lock:
            if table in self.tables:
                schema, batches = self.tables[table]
                self.tables[table] = (schema, [(s, b) for s, b in batches if s >= below])

    def _floor(self, batches: list[tuple[int, pa.RecordBatch]]) -> int:
        return batches[0][0] if batches else self.seq + 1

    def do_put(self, context, descriptor, reader, writer):
        if descriptor.descriptor_type != fl.DescriptorType.PATH or len(descriptor.path) != 1:
            raise fl.FlightServerError("the descriptor is a path of one table name")
        name = descriptor.path[0].decode()
        schema = reader.schema.remove_metadata()
        with self._lock:
            known = self.tables.setdefault(name, (schema, []))[0]
        if not known.equals(schema):
            raise fl.FlightServerError(f"{name}: the batches' schema is not the table's: {known}")
        for chunk in reader:
            with self._lock:
                if chunk.data is not None and chunk.data.num_rows:
                    self.seq += 1
                    batches = self.tables[name][1]
                    batches.append((self.seq, chunk.data.replace_schema_metadata(None)))
                    if self.keep is not None and len(batches) > self.keep:
                        del batches[: len(batches) - self.keep]
                seq = self.seq
            writer.write(_meta(seq))

    def do_get(self, context, ticket):
        try:
            req = json.loads(ticket.ticket)
            name, after, until = req["table"], req.get("after"), req.get("until")
        except (ValueError, KeyError, TypeError, AttributeError) as e:
            raise fl.FlightServerError(f'the ticket is {{"table": ..., "after": ...}}: {e}') from e
        with self._lock:
            schema, batches = self.tables.get(name, (pa.schema([]), []))
            picked = [
                (s, b)
                for s, b in batches
                if (after is None or s > after) and (until is None or s <= until)
            ]
            floor = self._floor(batches)

        def stream() -> Iterator[tuple[pa.RecordBatch, pa.Buffer]]:
            for s, b in picked:
                yield b, _meta(s)

        return fl.GeneratorStream(schema.with_metadata({"floor": str(floor)}), stream())
