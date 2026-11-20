"""What a pipeline holds of an Arrow-fed input between refreshes (#1329, A1).

One row per source kind, for one engine, in a fresh process: the bytes held
by the source object, by the connection (as an Arrow table) and by the store
(the sealed copy's Arrow size), and the driver's peak resident memory after
the first load and after a small change (`ru_maxrss`).

    python -m sverify_dev.input_held ENGINE KIND ROWS

`KIND` is `delta` (files the engine reads itself), `direct` (a source that
makes its rows per call and holds no table), `append` (`sverify.io.Source`
with append batches) or `static` (`StaticSource`). The same script runs on
main, where nothing is sealed (`Pipeline.inputs` is missing), for the
numbers before.
"""

from __future__ import annotations

import gc
import json
import resource
import sys
import tempfile

import numpy as np
import pyarrow as pa
from deltalake import write_deltalake

import sverify as sv
from sverify.incremental import Snapshot, SourceBatch
from sverify.io import Batch, DeltaSource, Source, StaticSource

CHANGE = 1_000


def rows(lo: int, hi: int) -> pa.Table:
    ids = np.arange(lo, hi, dtype=np.int64)
    rng = np.random.default_rng(lo)
    return pa.table(
        {
            "id": ids,
            "cust": rng.integers(0, 1000, ids.size),
            "amount": rng.random(ids.size) + 1,
            "qty": rng.integers(1, 9, ids.size),
        }
    )


class Direct:
    """The rows `0..n` of `rows`, made on each call: no table held."""

    name = "t"

    def __init__(self, n: int):
        self.n, self.v = n, 0

    def schema(self) -> pa.Schema:
        return rows(0, 0).schema

    def latest(self) -> int:
        return self.v

    def snapshot(self, version: int | None = None) -> Snapshot:
        return Snapshot(self.v if version is None else version, rows(0, self.n), [])

    def changes(self, since: int, until: int | None = None) -> SourceBatch:
        end = self.v if until is None else until
        if end == since:
            return SourceBatch.unchanged(since)
        return SourceBatch.from_changes(
            since, end, inserts=rows(self.n, self.n + CHANGE), trusted="Δ"
        )


class Appended(Source):
    def __init__(self, n: int):
        super().__init__("t", assumes="ids only grow")
        self.n, self.last = n, None

    def read(self, since):
        if since is None:
            return Batch(rows(0, self.n), cursor=self.n)
        if self.last == since:
            return None
        return Batch(rows(since, since + CHANGE), cursor=since + CHANGE)


@sv.transform()
def per_cust(t):
    return t.group_by("cust").aggregate(n=t.id.count(), qty=t.qty.sum())


def nbytes(x: object) -> int:
    return x.nbytes if isinstance(x, pa.Table) else 0


def source_held(src: object) -> int:
    held = sum(nbytes(v) for v in vars(src).values())
    state = getattr(src, "_state", None)
    if state is not None:
        held += nbytes(state.table) + sum(
            nbytes(getattr(e, "change", None)) for e in getattr(state.log, "_entries", [])
        )
    return held + nbytes(getattr(src, "table", None))


def store_held(pipe: object) -> int:
    held = 0
    for state, _ in getattr(pipe, "inputs", {}).values():
        held += nbytes(state.to_arrow() if hasattr(state, "to_arrow") else state)
    return held


def peak_mb() -> float:
    peak = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
    return peak / (2**20 if sys.platform == "darwin" else 2**10)


def main(engine: str, kind: str, n: int) -> dict:
    path = ""
    if kind == "delta":
        path = tempfile.mkdtemp() + "/t"
        write_deltalake(path, rows(0, n), configuration={"delta.enableChangeDataFeed": "true"})
        src = DeltaSource(path)
    elif kind == "direct":
        src = Direct(n)
    elif kind == "append":
        src = Appended(n)
    else:
        src = StaticSource(rows(0, n), name="t")
    node = per_cust(src)
    node.refresh(engine=engine)
    gc.collect()
    first = peak_mb()
    if kind == "delta":
        write_deltalake(path, rows(n, n + CHANGE), mode="append")
    elif kind == "direct":
        assert isinstance(src, Direct)
        src.v = 1
    elif kind == "static":
        assert isinstance(src, StaticSource)
        src.apply(sv.io.Changes(inserts=rows(n, n + CHANGE)))
    node.refresh(engine=engine)
    gc.collect()
    pipe = node._stage.pipe
    held = pipe.con.get("t")
    out = {
        "engine": engine,
        "kind": kind,
        "rows": n,
        "source_mb": source_held(src) / 2**20,
        "connection_mb": nbytes(held) / 2**20,
        "connection_is": type(held).__name__,
        "store_mb": store_held(pipe) / 2**20,
        "peak_after_first_mb": first,
        "peak_after_change_mb": peak_mb(),
    }
    print(json.dumps(out))
    return out


if __name__ == "__main__":
    main(sys.argv[1], sys.argv[2], int(sys.argv[3]))
