"""Table histories for the native-scan property (#173, design note section 5.1).

A history is a list of steps on one table: append rows, delete rows, add a
column. The first step may partition the table. `build_delta` and
`build_iceberg` run a history on a real table and give back its `Source`; every
engine's scan of a descriptor is tested over the same histories against the
Arrow route (`tests/test_io_native.py`).

A `Delete` rewrites the files it touches (delta-rs writes no deletion vectors,
Iceberg no position deletes here): those are covered by the fixture and the sink
tests in `test_io_native.py`.

Histories go beyond what a native read covers today (partitions): a source
falls back to Arrow there, and the property says so. As a
native read learns a case, the test that pins the fallback turns into one that
compares the rows.
"""

from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path

import pyarrow as pa
from hypothesis import strategies as st

from sverify.io import DeltaSource, IcebergSource

#: Column `x` takes the doubles the engines treat apart: the zeros and NaN.
XS = [0.5, float("nan"), -0.0, 0.0, None, -2.5]
KS = ["a", "b", "c"]


@dataclass(frozen=True)
class Append:
    ids: tuple[int, ...]


@dataclass(frozen=True)
class Delete:
    """Delete the rows with `id < below`."""

    below: int


@dataclass(frozen=True)
class AddColumn:
    """Add the nullable `string` column `name`; later appends fill it."""

    name: str


RENAME = "<rename x to y>"


@dataclass(frozen=True)
class Rename:
    """Rename the double column `x` to `y` (Iceberg: files written before keep `x`)."""


Step = Append | Delete | AddColumn | Rename


@dataclass(frozen=True)
class History:
    """`steps` on a table, partitioned by `k` or not."""

    partitioned: bool
    steps: tuple[Step, ...]

    def columns(self, upto: int | None = None) -> list[str]:
        extra = [s.name for s in self.steps[:upto] if isinstance(s, AddColumn)]
        renamed = any(isinstance(s, Rename) for s in self.steps[:upto])
        return ["id", "k", "y" if renamed else "x", *extra]


def rows(history: History, ids: tuple[int, ...], upto: int) -> pa.Table:
    """The rows of an `Append`, with the columns added by the steps before it."""
    data = {
        "id": pa.array(ids, pa.int64()),
        "k": pa.array([KS[i % 3] for i in ids], pa.string()),
        history.columns(upto)[2]: pa.array([XS[i % len(XS)] for i in ids], pa.float64()),
    }
    for name in history.columns(upto)[3:]:
        data[name] = pa.array([f"{name}{i}" for i in ids], pa.string())
    return pa.table(data)


@st.composite
def histories(
    draw, max_steps: int = 5, partitioned: bool | None = None, renames: bool = False
) -> History:
    """Histories that start with an append, so no table is empty at creation
    (an empty table is its own test)."""
    ids = st.integers(0, 40)
    first = Append(tuple(draw(st.lists(ids, min_size=1, max_size=6, unique=True))))
    steps: list[Step] = [first]
    added, renamed = 0, False
    for _ in range(draw(st.integers(0, max_steps - 1))):
        kind = draw(st.sampled_from(["append", "append", "delete", "add", *(["rename"] * renames)]))
        if kind == "append":
            steps.append(Append(tuple(draw(st.lists(ids, min_size=1, max_size=6, unique=True)))))
        elif kind == "delete":
            steps.append(Delete(draw(st.integers(0, 41))))
        elif kind == "rename":
            if not renamed:
                steps.append(Rename())
                renamed = True
        elif added < 2:
            steps.append(AddColumn(f"c{added}"))
            added += 1
    return History(draw(st.booleans()) if partitioned is None else partitioned, tuple(steps))


def build_delta(path: Path, history: History) -> DeltaSource:
    """Run `history` on a Delta table at `path`: one commit per step."""
    from deltalake import DeltaTable, write_deltalake

    created = False
    for n, step in enumerate(history.steps):
        match step:
            case Append(ids):
                table = rows(history, ids, n)
                write_deltalake(
                    path,
                    table,
                    mode="append" if created else "error",
                    schema_mode="merge" if created else None,
                    partition_by=["k"] if history.partitioned and not created else None,
                )
                created = True
            case Delete(below):
                DeltaTable(str(path)).delete(f"id < {below}")
            case AddColumn() | Rename():
                pass  # the column appears with the next append (schema merge)
    return DeltaSource(str(path))


def build_iceberg(catalog, name: str, history: History) -> IcebergSource:
    """Run `history` on an Iceberg table in `catalog` (its first step is an append)."""
    from pyiceberg.types import StringType

    first = history.steps[0]
    assert isinstance(first, Append)
    data = rows(history, first.ids, 0)
    table = catalog.create_table(name, schema=data.schema)
    if history.partitioned:
        with table.update_spec() as update:
            update.add_identity("k")
    table.append(data)
    # A column is added (or renamed) just before the next append: pyiceberg's own read of a
    # snapshot older than the schema fails (test_iceberg_added_and_renamed_columns).
    pending: list[str] = []
    for n, step in enumerate(history.steps[1:], 1):
        match step:
            case Append(ids):
                for col in pending:
                    with table.update_schema() as update:
                        if col == RENAME:
                            update.rename_column("x", "y")
                        else:
                            update.add_column(col, StringType())
                pending.clear()
                table.append(rows(history, ids, n))
            case Delete(below):
                table.delete(f"id < {below}")
            case AddColumn(col):
                pending.append(col)
            case Rename():
                pending.append(RENAME)
    return IcebergSource(catalog, name)
