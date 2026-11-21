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
import os
import resource
import sys
import tempfile
import threading
import time

import numpy as np
import pyarrow as pa
from deltalake import write_deltalake

import sverify as sv
from sverify._store import store_for
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
        return Snapshot(
            version=self.v if version is None else version, table=rows(0, self.n), facts=[]
        )

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
            return Batch(table=rows(0, self.n), cursor=self.n)
        if self.last == since:
            return None
        return Batch(table=rows(since, since + CHANGE), cursor=since + CHANGE)


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


def rss_mb() -> float:
    with open("/proc/self/statm", encoding="utf-8") as f:
        return int(f.read().split()[1]) * 4096 / 2**20


class Sampler:
    """The resident memory of the process, sampled from a thread (Linux):
    where the main thread was each time it passed a new high above `floor`."""

    def __init__(self) -> None:
        self.floor = 0.0
        self.high = 0.0
        self.steps: list[tuple[float, str]] = []
        self.on = True
        self.main = threading.main_thread().ident or 0
        threading.Thread(target=self._run, daemon=True).start()

    def start(self) -> None:
        self.floor = self.high = rss_mb()

    def _run(self) -> None:
        while self.on:
            now = rss_mb()
            if now > self.high and self.floor:
                self.high = now
                frame = sys._current_frames().get(self.main)
                names = []
                while frame is not None and len(names) < 40:
                    code = frame.f_code
                    if "sverify" in code.co_filename or "polars" in code.co_filename:
                        base = os.path.basename(code.co_filename)
                        names.append(f"{base}:{code.co_name}:{frame.f_lineno}")
                    frame = frame.f_back
                self.steps.append((now, " < ".join(names[:7])))
            time.sleep(0.002)


def profiled(owner: object, name: str, label: str, sampler: Sampler, out: list) -> None:
    """Wrap `owner.name` so that each call records what it adds to the
    process's resident memory above its start, and its wall time."""
    inner = getattr(owner, name)

    def call(*args, **kwargs):
        start, t0 = rss_mb(), time.perf_counter()
        who = ">".join(sys._getframe(i).f_code.co_name for i in (1, 2, 3))
        rows = [getattr(a, "num_rows", None) for a in args if hasattr(a, "num_rows")]
        try:
            return inner(*args, **kwargs)
        finally:
            out.append(
                (f"{label} rows={rows} from {who}", sampler.high - start, time.perf_counter() - t0)
            )

    setattr(owner, name, call)


def profile_calls(engine: str, out: list, sampler: Sampler) -> None:
    from sverify import _state, incremental

    profiled(_state.Merger, "__call__", "Merger.__call__", sampler, out)
    profiled(incremental, "put_table", "put_table", sampler, out)
    profiled(incremental, "matching", "matching", sampler, out)
    profiled(incremental, "arrow_of", "arrow_of", sampler, out)
    view = incremental.IncrementalView
    for m in ("_delta", "_linear_change", "_touched_change", "_semi_change", "_diff"):
        profiled(view, m, f"IncrementalView.{m}", sampler, out)
    for store in {type(store_for(engine))}:
        for m in ("expanded", "kept", "has_negative", "merge", "negated", "apply"):
            profiled(store, m, f"{store.__name__}.{m}", sampler, out)


def main(engine: str, kind: str, n: int, profile: bool = False) -> dict:
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
    calls: list = []
    started = time.perf_counter()
    sampler = Sampler() if profile else None
    base = 0.0
    if sampler is not None:
        profile_calls(engine, calls, sampler)
        sampler.start()
        base = rss_mb()
    node.refresh(engine=engine)
    seconds = time.perf_counter() - started
    gc.collect()
    peak = peak_mb()  # before the measurement below reads the state
    if sampler is not None:
        for label, added, secs in calls:
            if added > 5:
                print(f"PROFILE {engine} {kind} {label} +{added:.0f} MB {secs:.2f}s")
        print(f"PROFILE {engine} {kind} refresh high +{sampler.high - base:.0f} MB over {base:.0f}")
        last = 0.0
        for rss, where in sampler.steps:
            if rss - last >= 40:
                print(f"PROFILE {engine} {kind} reached {rss:.0f} MB in {where}")
                last = rss
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
        "peak_after_change_mb": peak,
        "added_by_change_mb": peak - first,
        "change_refresh_s": seconds,
    }
    print(json.dumps(out))
    return out


if __name__ == "__main__":
    main(sys.argv[1], sys.argv[2], int(sys.argv[3]), "profile" in sys.argv[4:])
