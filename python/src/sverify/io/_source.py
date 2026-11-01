"""Sources you write yourself: one `read(since)` method that returns the
new rows and a cursor, as in data-warehousing-with-polars.

Internal: not part of sverify's public API, which is `sverify`, `sverify.io`,
`sverify.engines` and `sverify.errors`; it may change in any release. The
public names (`Source`, `Batch`, `from_query`, `from_frame`, `from_files`)
are re-exported by `sverify.io`.

A `Source` turns its batches into the versioned model the pipeline runs on
(`VersionedSource`): each batch that changes something is a new version, the
source keeps the table as of its latest version in memory, and it hands out
the change between two versions as an append (trusted), a change (trusted)
or the diff of two full reads (exact). It has no metadata, so preconditions
on it are checked on the rows.
"""

from __future__ import annotations

from abc import ABC, abstractmethod
from collections.abc import Callable
from dataclasses import dataclass, field
from typing import Any, Literal

import pyarrow as pa
import pyarrow.compute as pc

from sverify._weighted import expanded, negated, positive, weighted
from sverify.engine import plain_schema
from sverify.incremental import (
    Snapshot,
    SourceBatch,
    _apply_change,
    snapshot_diff,
)
from sverify.steps import Pipeable

Kind = Literal["append", "snapshot", "changes"]

KEEP = 64
"""Batches a source keeps, so nodes that fell behind by more read the
latest table instead (and are recomputed)."""


@dataclass(frozen=True)
class Batch:
    """What a `Source` read: new rows and the cursor to read from next time.

    Attributes:
        table: The rows, as an Arrow table, a Polars or pandas DataFrame, a
            Polars LazyFrame, or anything else `pyarrow.table` accepts. What
            they are depends on `kind`.
        cursor: Where the next read starts: `read(since=cursor)`. Any value,
            such as the greatest timestamp read or the files read so far.
            Default: None.
        kind: `"append"`: `table` is rows added since the last read (the
            default). `"snapshot"`: `table` is the whole table; the source
            diffs it against the last read. `"changes"`: `table` is rows
            added and `deletes` rows removed (one copy each).
        deletes: With `kind="changes"`, the rows removed, in the same forms
            as `table`. Default: None.
    """

    table: Any
    cursor: Any = None
    kind: Kind = "append"
    deletes: Any = None


def as_arrow(data: Any) -> pa.Table:
    """`data` as an Arrow table: an Arrow table or record batch reader, a
    Polars DataFrame or LazyFrame, a pandas DataFrame, or what
    `pyarrow.table` accepts."""
    if isinstance(data, pa.Table):
        return data
    if isinstance(data, pa.RecordBatchReader):
        return data.read_all()
    module = type(data).__module__.split(".")[0]
    if module == "polars":
        if hasattr(data, "collect"):
            data = data.collect()
        return data.to_arrow()
    if module == "pandas":
        return pa.Table.from_pandas(data, preserve_index=False)
    return pa.table(data)


@dataclass
class _Entry:
    version: int
    inserts: pa.Table
    deletes: pa.Table
    kind: Kind | None
    """None: a version that changes nothing (`_resume_after`)."""


@dataclass
class _State:
    version: int
    table: pa.Table
    cursor: Any = None
    log: list[_Entry] = field(default_factory=list)
    floor: int = 0
    """The log holds every batch after this version."""


class Source(Pipeable, ABC):
    """A table you read yourself: subclass it and implement `read`.

    `read(since)` returns what is new since the cursor of the last read (a
    `Batch`), or None if nothing is. The first read gets `since=None` and
    returns the whole table. Each batch that changes something is a new
    version of the source (1, 2, ...), and a refresh hands the nodes reading
    it exactly the change between their version and the latest:

    - `kind="append"` batches are the rows added. That rests on an
      assumption, such as "rows are only ever appended, in order of `ts`":
      state it as `assumes`, and the refresh report repeats it.
      `refresh(audit=True)` reads the whole table again (`reread`) and
      raises `AuditError` where the assumption broke.
    - `kind="snapshot"` batches are the whole table. The source diffs each
      against the last, so the change is exact and nothing is assumed.
    - `kind="changes"` batches are rows added and removed, trusted as read.

    The source keeps the table as of its latest version in memory, since
    joins and keys need it, and has no metadata: preconditions on it are
    checked on the rows. Versions count reads in this process, so a
    restarted job reads the whole table again. A stored node reading it
    is then recomputed and written again in full, with versions above the
    ones its sink recorded, so its sink still writes exactly once.

    Args:
        name: The table's name in the plans that read it.
        schema: The table's schema, if the first read may return nothing.
            Default: the first batch's.
        assumes: What the batches rest on, such as `"rows are only
            appended, in order of ts"`. Default: None.

    Attributes:
        name: The table's name in the plans that read it.
        assumes: What the batches rest on, or None.

    Examples:
        A source reading new rows from a list, by an increasing id:

        ```python
        import pyarrow as pa
        import sverify as sv
        from sverify.io import Batch, Source

        rows = [{"id": 1, "amount": 30}, {"id": 2, "amount": 5}]


        class Orders(Source):
            def read(self, since):
                new = [r for r in rows if since is None or r["id"] > since]
                if not new:
                    return None
                return Batch(pa.Table.from_pylist(new), cursor=new[-1]["id"])


        @sv.transform()
        def big_orders(orders):
            return orders.filter(orders.amount > 10)


        big = big_orders(Orders("orders", assumes="ids only grow"))
        big.refresh()
        rows.append({"id": 3, "amount": 50})
        print(big.refresh())
        # big_orders:
        #   orders@v1→v2: 1 insert(s), 0 delete(s); Δ trusted as rows appended
        #   to orders v1→v2, assuming ids only grow
        #   view big_orders: orders@v2
        ```
    """

    name: str = "table"
    assumes: str | None = None
    _declared: pa.Schema | None = None
    _state: _State | None = None
    _base: int = 0

    def __init__(
        self,
        name: str,
        *,
        schema: pa.Schema | None = None,
        assumes: str | None = None,
    ):
        self.name = name
        self._declared = schema
        if assumes is not None:
            self.assumes = assumes

    @abstractmethod
    def read(self, since: Any) -> Batch | None:
        """What is new since the last read.

        Args:
            since: The cursor of the last batch read, or None on the first
                read (and after a batch whose cursor is None).

        Returns:
            The new rows (`Batch`), or None if nothing is new.
        """

    def reread(self, cursor: Any) -> Any:
        """The whole table as of `cursor`, read again from scratch, for
        `refresh(audit=True)`. Override it to read only up to `cursor`, so
        rows that arrive meanwhile are not reported as a mismatch.

        Args:
            cursor: The cursor of the latest batch.

        Returns:
            The rows, in any form `Batch.table` takes. Default: the table of
            `read(None)`, or no rows.
        """
        batch = self.read(None)
        return self._st().table.schema.empty_table() if batch is None else batch.table

    # -- the versioned source the pipeline reads -----------------------------

    def schema(self) -> pa.Schema:
        """The table's schema (the first batch's, or `schema=`)."""
        return self._st().table.schema

    def latest(self) -> int:
        """Read what is new, and return the latest version."""
        if self._state is None:
            return self._st().version
        self._take(self.read(self._state.cursor))
        return self._state.version

    def snapshot(self, version: int | None = None) -> Snapshot:
        """The table as of the latest read.

        Args:
            version: The latest version, or None for it.

        Returns:
            The version and the rows, with no facts.

        Raises:
            ValueError: `version` is not the latest; the source keeps only
                its latest table.
        """
        st = self._st()
        if version not in (None, st.version):
            raise ValueError(f"{self.name} keeps only its latest read, v{st.version}")
        return Snapshot(st.version, st.table, [])

    def changes(self, since: int, until: int | None = None) -> SourceBatch:
        """The change from version `since` to the latest, as a refresh reads
        it: the batches read in between.

        Args:
            since: The version the node's state was computed from.
            until: The latest version, or None for it.

        Returns:
            The rows the batches added and removed, or, if they are no
            longer kept, the latest table.

        Raises:
            ValueError: `until` is not the latest version.
        """
        st = self._st()
        if until not in (None, st.version):
            raise ValueError(f"{self.name} keeps only its latest read, v{st.version}")
        if since == st.version:
            return SourceBatch.unchanged(since, schema=st.table.schema)
        if since < st.floor:
            return SourceBatch.from_snapshot(
                since, st.version, st.table, reason=f"{self.name}'s batches since v{since} are gone"
            )
        entries = [e for e in st.log if e.version > since]
        kinds = {e.kind for e in entries if e.kind is not None}
        span = f"{self.name} v{since}→v{st.version}"
        texts = []
        if "append" in kinds:
            texts.append(f"Δ trusted as rows appended to {span}")
        if "changes" in kinds:
            texts.append(f"Δ trusted as the changes read from {span}")
        if "snapshot" in kinds:
            texts.append(f"Δ = the difference of full reads of {span}")
        trusted = "; ".join(texts)
        if texts and self.assumes and kinds != {"snapshot"}:
            trusted += f", assuming {self.assumes}"
        schema = st.table.schema
        return SourceBatch.from_changes(
            since,
            st.version,
            inserts=pa.concat_tables([e.inserts for e in entries] or [schema.empty_table()]),
            deletes=pa.concat_tables([e.deletes for e in entries] or [schema.empty_table()]),
            trusted=trusted,
            kind="snapshot diff" if kinds == {"snapshot"} else "change feed",
            schema=schema,
        )

    # -- internals ------------------------------------------------------------

    def _st(self) -> _State:
        """The state, reading the table the first time."""
        if self._state is None:
            batch = self.read(None)
            schema = self._declared
            if schema is None:
                if batch is None:
                    raise ValueError(
                        f"{self.name}: the first read returned nothing; give the source schema="
                    )
                schema = as_arrow(batch.table).schema
            schema = plain_schema(schema)
            self._state = _State(self._base, schema.empty_table())
            self._take(batch)
        return self._state

    def _fit(self, data: Any) -> pa.Table:
        schema = self._st().table.schema
        table = as_arrow(data)
        try:
            return table.select(schema.names).cast(schema)
        except (KeyError, pa.ArrowException) as e:
            raise ValueError(
                f"{self.name}: a batch does not fit the source's schema "
                f"({', '.join(f'{f.name}: {f.type}' for f in schema)}): {e}"
            ) from e

    def _take(self, batch: Batch | None) -> None:
        """Make `batch` the next version, if it changes anything."""
        st = self._state
        assert st is not None
        if batch is None:
            return
        empty = st.table.schema.empty_table()
        rows = self._fit(batch.table)
        if batch.kind == "append":
            inserts, deletes = rows, empty
            table = pa.concat_tables([st.table, rows]) if rows.num_rows else st.table
        elif batch.kind == "snapshot":
            if rows.equals(st.table):
                inserts = deletes = empty
            else:
                diff = snapshot_diff(st.table, rows)
                inserts = expanded(positive(diff))
                deletes = expanded(positive(negated(diff)))
            table = rows
        elif batch.kind == "changes":
            inserts = rows
            deletes = empty if batch.deletes is None else self._fit(batch.deletes)
            change = pa.concat_tables([weighted(inserts, 1), weighted(deletes, -1)])
            table = _apply_change(st.table, change, self.name)
        else:
            raise ValueError(f"{self.name}: unknown batch kind {batch.kind!r}")
        st.cursor = batch.cursor
        if not inserts.num_rows and not deletes.num_rows:
            return
        st.version += 1
        st.table = table
        self._log(_Entry(st.version, inserts, deletes, batch.kind))

    def _log(self, entry: _Entry) -> None:
        st = self._state
        assert st is not None
        st.log.append(entry)
        if len(st.log) > KEEP:
            st.floor = st.log.pop(0).version

    def _resume_after(self, version: int) -> None:
        """A sink recorded this source at `version` in an earlier process:
        number the versions of this process above it, so that they keep
        growing. The table read so far becomes version `version + 1`."""
        if self._state is None:
            self._base = max(self._base, version)
            return
        st = self._state
        if st.version <= version:
            st.version = version + 1
            empty = st.table.schema.empty_table()
            self._log(_Entry(st.version, empty, empty, None))

    def _reread(self, version: int) -> pa.Table:
        """For an audit: the whole table at `version`, read again."""
        st = self._st()
        assert version == st.version
        return self._fit(self.reread(st.cursor))


class _Query(Source):
    def __init__(
        self,
        fn: Callable[[Any], Any],
        cursor_on: str,
        name: str,
        schema: pa.Schema | None,
    ):
        assumes = f"rows only arrive with a greater {cursor_on}"
        super().__init__(name, schema=schema, assumes=assumes)
        self.fn, self.cursor_on = fn, cursor_on

    def read(self, since: Any) -> Batch | None:
        data = self.fn(since)
        if data is None:
            return None
        table = as_arrow(data)
        if not table.num_rows:
            return None
        return Batch(table, cursor=pc.call_function("max", [table.column(self.cursor_on)]).as_py())

    def reread(self, cursor: Any) -> Any:
        table = as_arrow(self.fn(None))
        if cursor is None:
            return table.schema.empty_table()
        return table.filter(pc.call_function("less_equal", [table.column(self.cursor_on), cursor]))


def from_query(
    fn: Callable[[Any], Any],
    *,
    cursor_on: str,
    name: str,
    schema: pa.Schema | None = None,
) -> Source:
    """A source that reads new rows by a high-water mark: `fn(since)`
    returns the rows whose `cursor_on` column is greater than `since` (all
    rows when `since` is None), and the next read starts from the greatest
    value it returned.

    This assumes rows only arrive with a greater `cursor_on` than any read
    before; a late or corrected row is missed. The refresh report says so,
    and `refresh(audit=True)` catches it: it reads `fn(None)` up to the
    cursor and compares.

    Args:
        fn: Called with the last cursor, or None; returns the new rows (an
            Arrow table, a Polars or pandas DataFrame, ...) or None.
        cursor_on: The column whose greatest value is the cursor.
        name: The table's name in the plans that read it.
        schema: The table's schema, if `fn(None)` may return nothing.
            Default: that of the first rows.

    Returns:
        The source.

    Examples:
        ```python
        import pyarrow as pa
        import pyarrow.compute as pc
        import sverify as sv
        from sverify.io import from_query

        payments = pa.table({"id": [1, 2], "ts": [10, 20], "amount": [30, 5]})


        def new_payments(since):
            if since is None:
                return payments
            return payments.filter(pc.greater(payments["ts"], since))


        @sv.transform()
        def big(payments):
            return payments.filter(payments.amount > 10)


        node = big(from_query(new_payments, cursor_on="ts", name="payments"))
        node.refresh()
        ```
    """
    return _Query(fn, cursor_on, name, schema)


class _Frame(Source):
    def __init__(self, fn: Callable[[], Any], name: str, schema: pa.Schema | None):
        super().__init__(name, schema=schema)
        self.fn = fn

    def read(self, since: Any) -> Batch | None:
        data = self.fn()
        return None if data is None else Batch(data, kind="snapshot")


def from_frame(fn: Callable[[], Any], *, name: str, schema: pa.Schema | None = None) -> Source:
    """A source that reads the whole table on every refresh: `fn()` returns
    it. Each read is diffed against the last, so the nodes reading it get
    the exact change and nothing is assumed; a read that changes nothing is
    no new version.

    Args:
        fn: Returns the table (an Arrow table, a Polars or pandas DataFrame,
            ...), or None if it is not there.
        name: The table's name in the plans that read it.
        schema: The table's schema, if `fn()` may return None. Default:
            that of the first read.

    Returns:
        The source.

    Examples:
        ```python
        import pyarrow as pa
        from sverify.io import from_frame

        regions = from_frame(
            lambda: pa.table({"customer": ["ada"], "region": ["eu"]}), name="regions"
        )
        ```
    """
    return _Frame(fn, name, schema)


class _Files(Source):
    def __init__(
        self,
        path: str,
        format: str,
        name: str,
        schema: pa.Schema | None,
        filesystem: Any,
    ):
        super().__init__(name, schema=schema, assumes="files are only added, never changed")
        self.path, self.format = path, format
        self.filesystem = filesystem

    def _files(self) -> tuple[Any, list[str]]:
        import pyarrow.fs as pafs

        fs, root = (
            (self.filesystem, self.path)
            if self.filesystem is not None
            else pafs.FileSystem.from_uri(self.path)
        )
        infos = fs.get_file_info(pafs.FileSelector(root, recursive=True))
        suffix = f".{self.format}"
        paths = [i.path for i in infos if i.type == pafs.FileType.File and i.path.endswith(suffix)]
        return fs, sorted(paths)

    def _scan(self, fs: Any, paths: list[str]) -> pa.Table:
        import pyarrow.dataset as ds

        schema = None if self._state is None else self._state.table.schema
        return ds.dataset(paths, format=self.format, filesystem=fs, schema=schema).to_table()

    def read(self, since: Any) -> Batch | None:
        fs, paths = self._files()
        seen = set(since or [])
        new = [p for p in paths if p not in seen]
        if not new:
            return None
        return Batch(self._scan(fs, new), cursor=sorted(seen | set(new)))

    def reread(self, cursor: Any) -> Any:
        fs, _ = self._files()
        return self._scan(fs, list(cursor or []))


def from_files(
    path: str,
    *,
    format: str = "parquet",
    name: str,
    schema: pa.Schema | None = None,
    filesystem: Any = None,
) -> Source:
    """A source that reads the files dropped in a directory: each refresh
    reads the files that are new since the last, and appends their rows.
    The cursor is the list of files read.

    This assumes files are only added: a file changed or removed after it
    was read is not noticed, except by `refresh(audit=True)`, which reads
    the files read so far again and compares.

    Args:
        path: The directory, as a path or a URI such as `s3://bucket/drop`.
        format: The files' format and suffix, as `pyarrow.dataset` names it:
            `"parquet"` (the default), `"csv"`, `"feather"`, `"json"`.
        name: The table's name in the plans that read it.
        schema: The table's schema, if the directory may start empty.
            Default: that of the first files.
        filesystem: A `pyarrow.fs.FileSystem` to read `path` with, such as
            one with credentials. Default: the one `path`'s URI names, with
            its default credentials (environment, profile, role).

    Returns:
        The source.
    """
    return _Files(path, format, name, schema, filesystem)
