"""A view's state as parts of Parquet files, for every engine that writes and
reads Parquet itself (#173 N6, #1329, N14).

A state (`PartsState`) is a list of parts: directories of Parquet files, each
with its own lifetime (a part is deleted once no handle holds it), and the
Arrow schema of the weighted table they hold. The table is the sum of the
parts: their union, with the weights of equal rows added. A merge with `keep`
writes the change as a new part and leaves the others where they are, so a
refresh costs the change and not the state. The Lean merge plan (`Store.merge`:
union, group by every column, add the weights, drop zeros) adds the parts up:

- when something reads the table: `view`, `attach`, `to_arrow`, `retire`, and
  `expanded` or `has_negative` unless the parts alone answer (below). No row
  and no answer leaves a state whose parts are not added up;
- when the parts passed a bound (`PartsState.needs_compaction`): the rows
  added since the last time hold as many rows as that sum, or there are more
  than `MAX_PARTS` parts. The files on disk then stay within about twice the
  consolidated state.

An operation that is linear in the weights runs on the parts as they are:
`negated`, the key filters of `with_keys` and `without_keys` (a filter of an
added-up state stays added up) and `expanded` where every weight of every part
is positive (a row is as many copies as its weights add up to). A weight sum
that leaves 64 bits is raised at the merge that adds the parts up, which can
be later than the refresh that caused it; no answer comes from such a state.
The plan is the one definition of row equality: nothing else adds weights.

An engine supplies a `Backend`: the frames it computes lazily, writing one as
a part, reading parts as they lie, and running the merge plan over two
frames, with a few small frame operations. `PartsStore` is the rest.

The state location is a directory the engine and the driver both read: a
temporary directory for the local session (`SVERIFY_STATE_LOCATION` names
another). A part's row count and weight range come from its Parquet footers,
which the driver reads where it can see the files; elsewhere the backend
measures them. A cluster needs a location it reads and writes, which N6c's
state-location setting brings.
"""

from __future__ import annotations

import atexit
import contextlib
import glob
import os
import shutil
import tempfile
import uuid
import weakref
from abc import ABC, abstractmethod
from collections.abc import Callable, Sequence
from typing import TYPE_CHECKING, Any

import pyarrow as pa
import pyarrow.parquet as pq

from sverify._arrow_state import ArrowOps
from sverify._scan import Native, _q
from sverify._store import State
from sverify._weighted import WEIGHT

if TYPE_CHECKING:
    import duckdb

#: More parts than this are added up.
MAX_PARTS = 16

_DIR: str | None = None


def state_dir() -> str:
    """The state location: `SVERIFY_STATE_LOCATION`, else a directory of the
    process removed at exit."""
    global _DIR
    if _DIR is None:
        given = os.environ.get("SVERIFY_STATE_LOCATION")
        if given:
            os.makedirs(given, exist_ok=True)
            _DIR = given
        else:
            _DIR = tempfile.mkdtemp(prefix="sverify-state-")
            atexit.register(shutil.rmtree, _DIR, ignore_errors=True)
    return _DIR


def new_part_path() -> str:
    """A fresh directory name in the state location (the backend writes it)."""
    return os.path.join(state_dir(), f"part-{uuid.uuid4().hex}")


def write_part(backend: Backend, frame: Any, schema: pa.Schema, *, merged: bool = False) -> Part:
    """A new part: the backend writes `frame` to a fresh directory of the
    state location. A write that fails leaves no directory behind."""
    path = new_part_path()
    try:
        backend.write(frame, schema, path, merged=merged)
        return Part(path, schema, backend)
    except BaseException:
        _remove(path)
        raise


class Backend(ABC):
    """What an engine supplies. A frame is the engine's lazy table; the
    schema is the Arrow schema of a weighted table, with `WEIGHT` where it has
    one."""

    @abstractmethod
    def write(self, frame: Any, schema: pa.Schema, path: str, *, merged: bool = False) -> None:
        """`frame` (the columns of `schema`, by position, in its types)
        written to the directory `path`. `merged`: the frame is the merge
        plan's result, whose weight sum may have left 64 bits (raise it)."""

    @abstractmethod
    def read(self, parts: Sequence[Part], schema: pa.Schema) -> Any:
        """The union of the parts as they lie, in the columns of `schema`."""

    @abstractmethod
    def run(self, plan: str, schema: pa.Schema, a: Any, b: Any) -> Any:
        """The merge plan over the frames `a` and `b`, with the names of
        `schema`."""

    @abstractmethod
    def arrow(self, frame: Any, schema: pa.Schema, *, merged: bool = False) -> pa.Table:
        """`frame` collected as an Arrow table in `schema`."""

    @abstractmethod
    def frame(self, table: pa.Table) -> Any:
        """An Arrow table as a frame."""

    @abstractmethod
    def measure(self, path: str, weighted: bool) -> tuple[int, int | None, int | None]:
        """A part's rows and weight range, where the driver cannot read its
        footers."""

    @abstractmethod
    def with_weight(self, frame: Any, weight: int) -> Any:
        """`frame` with a `WEIGHT` column of `weight` appended."""

    @abstractmethod
    def negate(self, frame: Any) -> Any:
        """`frame` with its weights negated."""

    @abstractmethod
    def copies(self, frame: Any, names: Sequence[str]) -> Any:
        """The columns `names` of `frame`, each row as many times as its
        weight (every weight is at least 1)."""

    @abstractmethod
    def filtered(
        self, left: Any, schema: pa.Schema, columns: Sequence[str], keys: Any, *, anti: bool
    ) -> Any:
        """The rows of `left` whose `columns` are (or, `anti`, are not) among
        the rows of the frame `keys`. NaN is one value, `-0.0` is `0.0` and
        NULL equals NULL."""

    @abstractmethod
    def split(self, frame: Any, column: str, cutoff: Any) -> tuple[int, Any]:
        """How many distinct values of `column` are at most `cutoff` in
        `frame`, and the rows above it."""


def _remove(path: str) -> None:
    with contextlib.suppress(OSError):
        shutil.rmtree(path)


def footers(files: list[str], weighted: bool) -> tuple[int, int | None, int | None]:
    """The rows and the weight range of Parquet files, from their footers."""
    rows, low, high = 0, None, None
    for f in files:
        pf = pq.ParquetFile(f)
        meta = pf.metadata
        rows += meta.num_rows
        if not weighted or meta.num_rows == 0:
            continue
        i = pf.schema_arrow.names.index(WEIGHT)
        for g in range(meta.num_row_groups):
            s = meta.row_group(g).column(i).statistics
            if s is None or not s.has_min_max:
                raise LookupError("no statistics")
            low = s.min if low is None else min(low, s.min)
            high = s.max if high is None else max(high, s.max)
    return rows, low, high


class Part:
    """A directory of Parquet files, deleted with its last holder.

    Attributes:
        path: The directory.
        rows: How many rows it holds.
        low: The least weight in it, None if it has no weight column.
        high: The greatest weight in it, None if it has none.
    """

    def __init__(self, path: str, schema: pa.Schema, backend: Backend):
        self.path = path
        weakref.finalize(self, _remove, path)
        weighted = WEIGHT in schema.names
        if "://" not in path:
            try:
                self.rows, self.low, self.high = footers(
                    glob.glob(os.path.join(path, "*.parquet")), weighted
                )
                return
            except (OSError, ValueError, LookupError):
                pass
        self.rows, self.low, self.high = backend.measure(path, weighted)


class Lazy:
    """A weighted table the engine has not computed yet (a run's result,
    weights set on one, a state's rows as they lie): a frame and its Arrow
    schema. Nothing is added up in it; a merge writes it as a part."""

    def __init__(self, frame: Any, schema: pa.Schema, backend: Backend):
        self.frame, self.schema, self.backend = frame, schema, backend

    def view(self, *_: Any) -> Any:
        return self.frame


class PartsState(Native):
    """A weighted table held as parts of Parquet files.

    Attributes:
        parts: The parts; the table is their sum.
        schema: The table's Arrow schema, with `WEIGHT` where it has one.
        backend: The engine that wrote them.
        plan: The merge plan that adds the parts up.
        consolidated: Whether the parts are added up already (one part, equal
            rows once, no zero weight).
        base: Whether the first part is an added-up state that the others
            came after.
    """

    def __init__(
        self,
        parts: Sequence[Part],
        schema: pa.Schema,
        backend: Backend,
        *,
        plan: str | None = None,
        consolidated: bool = False,
        base: bool = False,
    ):
        self.parts, self.schema, self.backend = tuple(parts), schema, backend
        self.plan, self.base = plan, base
        # Plain rows (no weight column) have nothing to add up.
        self.consolidated = consolidated or WEIGHT not in schema.names

    def raw(self) -> Any:
        """The union of the parts as they lie, in the state's columns."""
        if not self.parts:
            return self.backend.frame(self.schema.empty_table())
        return self.backend.read(self.parts, self.schema)

    def needs_compaction(self) -> bool:
        """The parts are added up when they are many, or when the rows added
        since the base are as many as the base holds."""
        if self.consolidated:
            return False
        if len(self.parts) > MAX_PARTS:
            return True
        if not self.base or not self.parts[0].rows:
            return False
        return sum(p.rows for p in self.parts[1:]) >= self.parts[0].rows

    def consolidate(self) -> PartsState:
        """Adds the parts up by the merge plan, into one part (in place)."""
        if self.consolidated:
            return self
        assert self.plan is not None, (
            "parts that are not added up come with the plan that adds them"
        )
        frame = self.backend.run(
            self.plan, self.schema, self.raw(), self.backend.frame(self.schema.empty_table())
        )
        self.parts = (write_part(self.backend, frame, self.schema, merged=True),)
        self.consolidated = self.base = True
        return self

    def range(self) -> tuple[int | None, int | None]:
        """The least and the greatest weight over the parts."""
        lows = [p.low for p in self.parts if p.low is not None]
        highs = [p.high for p in self.parts if p.high is not None]
        return (min(lows) if lows else None, max(highs) if highs else None)

    def positive(self) -> bool:
        """Every weight of every part is positive, so the weights of equal
        rows add up to a positive weight."""
        low, _ = self.range()
        return low is None or low > 0

    def view(self, *_: Any) -> Any:
        """The table as a frame over its files (added up first)."""
        return self.consolidate().raw()

    def attach(
        self, db: duckdb.DuckDBPyConnection, name: str, *, table: bool = False
    ) -> Callable[[], None]:
        self.consolidate()
        kind = "TABLE" if table else "VIEW"
        if self.parts:
            cols = ", ".join(_q(c) for c in self.schema.names)
            globs = ", ".join(
                "'" + os.path.join(p.path, "*.parquet").replace("'", "''") + "'" for p in self.parts
            )
            body = f"SELECT {cols} FROM read_parquet([{globs}])"
        else:
            body = (
                "SELECT "
                + ", ".join(f"NULL AS {_q(c)}" for c in self.schema.names)
                + " WHERE false"
            )
        db.execute(f"CREATE OR REPLACE TEMP {kind} {_q(name)} AS {body}")

        def drop() -> None:
            db.execute(f"DROP {kind} IF EXISTS {_q(name)}")

        return drop

    def to_arrow(self) -> pa.Table:
        return self.backend.arrow(self.view(), self.schema)

    def readable(self) -> bool:
        return all(os.path.isdir(p.path) for p in self.parts)


def _frame_of(z: Any, backend: Backend) -> Any:
    """A weighted table of any shape the store meets as a frame, its parts as
    they lie (not added up)."""
    if isinstance(z, PartsState):
        return z.raw()
    if isinstance(z, Lazy):
        return z.frame
    return backend.frame(z)


def _parts_of(z: Any, schema: pa.Schema, backend: Backend) -> tuple[Part, ...]:
    """The parts that make `z`: a state's own, a result or a change written
    as one (none for an empty table)."""
    if isinstance(z, PartsState):
        return z.parts
    if isinstance(z, pa.Table) and z.num_rows == 0:
        return ()
    return (write_part(backend, _frame_of(z, backend), schema),)


class PartsStore(ArrowOps):
    """A view's state as parts of Parquet files that the engine writes
    (`PartsState`). A weighted table that is an Arrow table (a change, the
    state per group) is handled as the Arrow store does. An engine's store
    names its `Backend` in `default_backend`."""

    keep = True

    @abstractmethod
    def default_backend(self) -> Backend:
        """The engine's own backend, for a table that holds none."""

    def _backend_of(self, *handles: Any) -> Backend:
        """The backend of the first handle that has one, else the engine's."""
        for h in handles:
            if isinstance(h, PartsState | Lazy):
                return h.backend
        return self.default_backend()

    def merge(
        self, plan: str, schema: pa.Schema, a: State, b: State, *, keep: bool
    ) -> State | pa.Table:
        backend = self._backend_of(a, b)
        if keep:
            parts = (*_parts_of(a, schema, backend), *_parts_of(b, schema, backend))
            parts = tuple(p for p in parts if p.rows)
            held = a if isinstance(a, PartsState) else None
            out = PartsState(
                parts,
                schema,
                backend,
                plan=plan,
                consolidated=held is not None and held.consolidated and parts == held.parts,
                base=held is not None and held.base and bool(parts) and parts[0] is held.parts[0],
            )
            return out.consolidate() if out.needs_compaction() else out
        frame = backend.run(plan, schema, _frame_of(a, backend), _frame_of(b, backend))
        return backend.arrow(frame, schema, merged=True)

    def kept(self, table: pa.Table) -> State:
        backend = self.default_backend()
        parts = tuple(p for p in _parts_of(table, table.schema, backend) if p.rows)
        return PartsState(parts, table.schema, backend, consolidated=True, base=bool(parts))

    def weighted(self, rows: Any, weight: int = 1) -> State:
        if not isinstance(rows, PartsState | Lazy):
            return super().weighted(rows, weight)
        out = pa.schema([*rows.schema, pa.field(WEIGHT, pa.int64())])
        backend = rows.backend
        frame = backend.with_weight(rows.view(), weight)
        return Lazy(frame, out, backend)

    def negated(self, z: State) -> State:
        if not isinstance(z, PartsState | Lazy):
            return super().negated(z)
        return Lazy(z.backend.negate(_frame_of(z, z.backend)), z.schema, z.backend)

    def expanded(self, z: State) -> pa.Table | PartsState:
        """Each row as many times as its weight, as parts of its own (without
        `WEIGHT`). Where every weight is positive the parts alone give the
        copies; otherwise the parts are added up first, and a negative weight
        left is an error."""
        if not isinstance(z, PartsState):
            return super().expanded(z)
        names = [c for c in z.schema.names if c != WEIGHT]
        schema = pa.schema([z.schema.field(c) for c in names])
        if not z.positive():
            low, _ = z.consolidate().range()
            if low is not None and low < 0:
                raise ValueError("a bag of rows cannot hold a negative number of copies")
        low, high = z.range()
        if not z.parts or (low == 1 and high == 1):
            return PartsState(z.parts, schema, z.backend)  # every row once: the parts' own files
        frame = z.backend.copies(z.raw(), names)
        return PartsState((write_part(z.backend, frame, schema),), schema, z.backend)

    def has_negative(self, z: State) -> bool:
        if not isinstance(z, PartsState):
            return super().has_negative(z)
        if z.positive():
            return False  # weights of one sign add up to that sign
        low, _ = z.consolidate().range()
        return low is not None and low < 0

    def retire(self, view: Any, column: str, cutoff: Any) -> int:
        z = view.state
        if not isinstance(z, PartsState):
            return super().retire(view, column, cutoff)
        # Added up first: a row whose weights cancelled is not a bucket.
        gone, kept = z.backend.split(z.view(), column, cutoff)
        part = write_part(z.backend, kept, z.schema)
        view.state = PartsState(
            (part,), z.schema, z.backend, plan=z.plan, consolidated=True, base=bool(part.rows)
        )
        return gone

    def with_keys(self, z: State, columns: Sequence[str], keys: Any) -> State:
        if not isinstance(z, PartsState):
            return super().with_keys(z, columns, keys)
        return self._by_keys(z, columns, keys, anti=False)

    def without_keys(self, z: State, columns: Sequence[str], keys: Any) -> State:
        if not isinstance(z, PartsState):
            return super().without_keys(z, columns, keys)
        return self._by_keys(z, columns, keys, anti=True)

    def _by_keys(self, z: PartsState, columns: Sequence[str], keys: Any, *, anti: bool) -> State:
        # A filter by key is linear: it runs on the parts as they lie, and its
        # result is as added up as they are.
        b = z.backend
        out = b.filtered(z.raw(), z.schema, columns, _frame_of(keys, b), anti=anti)
        part = write_part(b, out, z.schema)
        return PartsState(
            (part,),
            z.schema,
            b,
            plan=z.plan,
            consolidated=z.consolidated,
            base=z.consolidated and bool(part.rows),
        )
