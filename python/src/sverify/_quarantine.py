"""Quarantine: the rows of a source that break its preconditions, set aside
so the rest flows (#184).

Internal: not part of sverify's public API. `on_violation` (on a transform or
a source) and the reports (`QuarantineReport`, `Refresh.outcome`) are.

A stage's base table for source `t` holds `kept(S)` of the source's snapshot
`S`; the pipeline keeps `Q(S) = S - kept(S)`:

- `R(S)`: the rows on which every row condition is TRUE (a FALSE or NULL
  breaks it, as `violations` counts).
- For each key `unique(k)` in turn: the rows whose key occurs once among the
  rows left. Every row of a repeated key is set aside, so `kept` needs no
  order between rows and is a function of the snapshot (D24), the same
  whether computed in full or batch by batch.

Each condition is closed under subsets, so `kept(S)` meets every one
(`SubstraitLean/Quarantine.lean`), and the node's contract theorem
(`contract_sound`) holds on it. The pipeline's batch checks run unchanged on
the kept change after the split: a mistake here raises rather than letting a
row through.

Conditions with no rule for which rows break them (`max_rows`,
`arrives_within`, assumed `SUM` bounds) hold the stage at its versions
instead (`Held`), as `hold` does.
"""

from __future__ import annotations

import json
from collections.abc import Iterable, Mapping, Sequence
from dataclasses import dataclass, field
from datetime import UTC, datetime
from typing import Any, Literal

import pyarrow as pa

from sverify._cursor import _TAG, cursor_json, cursor_value
from sverify._weighted import (
    WEIGHT,
    _call,
    _indices,
    _q,
    _sql,
    concat,
    consolidated,
    expanded,
    grouped,
    has_negative,
    negated,
    negative,
    positive,
    rows_of,
    weighted,
    weights_in,
)

type Policy = Literal["error", "quarantine", "hold"]
"""What a refresh does with a batch that breaks a precondition: raise
`PreconditionError` (the default), set the offending rows aside and go on
(`quarantine`), or commit nothing for the batch and hold the node at its
versions (`hold`)."""

POLICIES: tuple[Policy, ...] = ("error", "quarantine", "hold")
_RANK = {"quarantine": 0, "hold": 1, "error": 2}

EXAMPLES = 10
"""How many rows set aside a report shows."""

_IDX = "__sverify_qi"

FORMAT = 1
"""The version of the quarantine table's format (`docs/stability.md`)."""


def check_policy(policy: object, what: str = "on_violation") -> Policy | None:
    """`policy` if it is one of `POLICIES` or None, else `ValueError`."""
    if policy is not None and policy not in POLICIES:
        raise ValueError(f"{what} must be one of {', '.join(map(repr, POLICIES))}, not {policy!r}")
    return policy  # type: ignore[return-value]


def strictest(policies: Iterable[Policy]) -> Policy:
    """The strictest of `policies`: error, then hold, then quarantine."""
    return max(policies, key=_RANK.__getitem__, default="error")


def resolve(stated: Iterable[Policy | None], source: Policy | None) -> Policy:
    """The policy of one condition: the strictest that the transforms stating
    it set, where a transform that set none takes the source's (and a source
    that sets none, error)."""
    return strictest((p or source or "error") for p in stated)


class Held(Exception):  # noqa: N818 - a control-flow signal, caught by nodes
    """A batch (or the first load) breaks a condition whose policy holds the
    stage: nothing was applied. Carries the `PreconditionError` that says why."""

    def __init__(self, error: Exception, policy: Policy):
        super().__init__(str(error))
        self.error, self.policy = error, policy


# -- the rows set aside --------------------------------------------------------


@dataclass
class Entry:
    """One distinct row set aside, with its copies and why."""

    row: dict[str, Any]
    copies: int
    conditions: list[str]
    reason: str
    version: int
    at: datetime


def _key(row: Mapping[str, Any]) -> str:
    """A row's identity among the rows set aside: its values as JSON, with
    NaN and -0.0 as the model compares them."""
    return json.dumps([_canon(v) for v in row.values()], default=str, sort_keys=True)


def _canon(v: Any) -> Any:
    if isinstance(v, float):
        return "NaN" if v != v else v + 0.0
    if isinstance(v, dict):
        return {k: _canon(x) for k, x in v.items()}
    if isinstance(v, list | tuple):
        return [_canon(x) for x in v]
    return v


@dataclass
class Quarantined:
    """The rows of one source set aside, by identity."""

    schema: pa.Schema
    entries: dict[str, Entry] = field(default_factory=dict)

    def copy(self) -> Quarantined:
        return Quarantined(self.schema, dict(self.entries))

    @property
    def total(self) -> int:
        return sum(e.copies for e in self.entries.values())

    def weighted(self, only: Sequence[str] | None = None) -> pa.Table:
        """The rows as a weighted table; with `only`, those keys."""
        es = list(self.entries.values()) if only is None else [self.entries[k] for k in only]
        rows = pa.Table.from_pylist([e.row for e in es], schema=self.schema)
        return rows.append_column(WEIGHT, pa.array([e.copies for e in es], pa.int64()))

    def added_since(self, old: Quarantined) -> list[Entry]:
        """The copies set aside here beyond those `old` holds."""
        out = []
        for k, e in self.entries.items():
            n = e.copies - (old.entries[k].copies if k in old.entries else 0)
            if n > 0:
                out.append(Entry(e.row, n, e.conditions, e.reason, e.version, e.at))
        return out

    def table(self) -> pa.Table:
        """The rows, each copy once, with why they were set aside."""
        es = list(self.entries.values())
        rows = expanded(self.weighted())
        reps = [e for e in es for _ in range(e.copies)]
        return (
            rows.append_column(
                "_conditions", pa.array([e.conditions for e in reps], pa.list_(pa.string()))
            )
            .append_column("_reason", pa.array([e.reason for e in reps], pa.string()))
            .append_column("_source_version", pa.array([e.version for e in reps], pa.int64()))
        )


# -- classifying rows ----------------------------------------------------------


def row_failures(con: Any, rows: pa.Table, conds: Sequence[Any]) -> list[list[str]]:
    """For each row of the plain table `rows`, the labels of the row
    conditions that are not TRUE on it (FALSE or NULL), in `conds`' order.
    Runs on `con` (a `sverify.connect()` connection), as the checks do."""
    from sverify.conditions import label
    from sverify.conditions import resolve as resolve_cond
    from sverify.engine import put_table

    n = rows.num_rows
    out: list[list[str]] = [[] for _ in range(n)]
    if not n or not conds:
        return out
    name = "__sverify_quarantine"
    put_table(con, name, rows.append_column(_IDX, _indices(n)))
    try:
        table: Any = con.table(name)
        for c in conds:
            if isinstance(c, str):
                import ibis

                backend: Any = ibis.get_backend(table)
                sql = ibis.to_sql(table, dialect=backend.name)
                query = f'SELECT "{_IDX}" FROM ({sql}) AS "t" WHERE NOT coalesce(({c}), FALSE)'
                hit = [r[0] for r in backend.raw_sql(query).fetchall()]
            else:
                pred: Any = resolve_cond(c, table)
                bad = table.filter(~pred.fill_null(False)).select(_IDX)
                hit = bad.to_pyarrow().column(0).to_pylist()
            for i in hit:
                out[i].append(label(c))
    finally:
        con.drop(name)
    return out


def _key_counts(pool: pa.Table, cols: Sequence[str]) -> list[int]:
    """For each row of the weighted table `pool`, the copies over all rows
    with its key `cols` (NULLs equal, as `duplicate_keys` counts)."""
    if not pool.num_rows:
        return []
    indexed = pool.append_column(_IDX, _indices(pool.num_rows))
    part = ", ".join(map(_q, cols))
    out = _sql(
        f"SELECT CAST(sum({_q(WEIGHT)}) OVER (PARTITION BY {part}) AS BIGINT) AS n, {_q(_IDX)} "
        f"FROM z ORDER BY {_q(_IDX)}",
        z=indexed,
    )
    return out.column("n").to_pylist()


def _show_key(row: Mapping[str, Any], cols: Sequence[str]) -> str:
    return ", ".join(f"{c} = {row[c]!r}" for c in cols)


@dataclass
class _Split:
    ok: pa.Table
    """Weighted rows kept."""
    bad: pa.Table
    """Weighted rows set aside."""
    conditions: list[list[str]]
    reasons: list[str]


def apply_keys(pool: pa.Table, keys: Sequence[Any]) -> _Split:
    """The rows of the consolidated weighted table `pool` whose key occurs
    once, for each key in turn among the rows left; the others, with why."""
    bad_parts: list[pa.Table] = []
    conditions: list[list[str]] = []
    reasons: list[str] = []
    ok = pool
    for k in keys:
        counts = _key_counts(ok, k.cols)
        if not counts:
            continue
        mask = pa.array([n > 1 for n in counts])
        bad = ok.filter(mask)
        if bad.num_rows:
            bad_parts.append(bad)
            for r, n in zip(bad.to_pylist(), [n for n in counts if n > 1], strict=True):
                conditions.append([k.label])
                reasons.append(f"{_show_key(r, k.cols)} is on {n} rows")
        ok = ok.filter(_call("invert", mask))
    bad = concat(bad_parts) if bad_parts else pool.slice(0, 0)
    return _Split(ok, bad, conditions, reasons)


def _row_reason(labels: Sequence[str]) -> str:
    return "breaks " + ", ".join(labels)


def split_rows(con: Any, rows: pa.Table, row_conds: Sequence[Any]) -> _Split:
    """The consolidated weighted table `rows` split by the row conditions."""
    fails = row_failures(con, rows_of(rows), row_conds)
    mask = pa.array([bool(f) for f in fails], pa.bool_())
    bad_fails = [f for f in fails if f]
    return _Split(
        rows.filter(_call("invert", mask)),
        rows.filter(mask),
        bad_fails,
        [_row_reason(f) for f in bad_fails],
    )


# -- what a split changes --------------------------------------------------------


@dataclass
class Moves:
    """What a split does to one source's rows: the change to its base table
    (the kept rows), and to the rows set aside."""

    kept: pa.Table
    """The base table's change, a weighted table: `kept(S') - kept(S)`."""
    quarantined: Quarantined
    """The rows set aside after the batch."""
    set_aside: list[Entry]
    """Rows set aside by this batch (new rows, or kept rows a new duplicate
    retracted), each with the copies added."""
    released: int
    """Copies that left the quarantine for the base table."""
    deleted: int
    """Copies set aside that the batch deletes upstream."""


def _entries(
    split: _Split, version: int, at: datetime, old: Quarantined | None = None
) -> list[tuple[str, Entry]]:
    out = []
    for r, w, conds, reason in zip(
        rows_of(split.bad).to_pylist(),
        split.bad.column(WEIGHT).to_pylist(),
        split.conditions,
        split.reasons,
        strict=True,
    ):
        k = _key(r)
        prev = old.entries.get(k) if old is not None else None
        out.append(
            (
                k,
                Entry(
                    r,
                    w,
                    conds,
                    reason,
                    prev.version if prev else version,
                    prev.at if prev else at,
                ),
            )
        )
    return out


def split_snapshot(
    con: Any,
    rows: pa.Table,
    row_conds: Sequence[Any],
    keys: Sequence[Any],
    version: int,
    *,
    old: Quarantined | None = None,
    at: datetime | None = None,
) -> tuple[pa.Table, Quarantined]:
    """`kept(S)` of the plain table `rows`, and `Q(S)`; rows set aside
    before (`old`) keep when and at which version they were."""
    at = at or datetime.now(UTC)
    pool = grouped(weighted(rows, 1))
    first = split_rows(con, pool, row_conds)
    second = apply_keys(first.ok, keys)
    q = Quarantined(rows.schema)
    for k, e in _entries(first, version, at, old) + _entries(second, version, at, old):
        q.entries[k] = e
    return expanded(second.ok).cast(rows.schema), q


def split_batch(
    con: Any,
    kept: pa.Table,
    quarantined: Quarantined,
    change: pa.Table,
    row_conds: Sequence[Any],
    keys: Sequence[Any],
    version: int,
    *,
    at: datetime | None = None,
) -> Moves:
    """Split a source-level batch (`change`, a weighted table, relative to
    `kept ⊎ quarantined`) into the base table's change and the new rows set
    aside, so that afterwards the base table is `kept(S')` and the rows set
    aside `Q(S')`."""
    at = at or datetime.now(UTC)
    change = consolidated(change)
    q = quarantined.copy()
    deletes, inserts = negative(change), positive(change)
    all_deletes = rows_of(deletes)
    # Deletes of rows set aside leave the quarantine; the rest, the base table.
    deleted = 0
    removed: dict[str, int] = {}
    if deletes.num_rows and q.entries:
        in_q = weights_in(q.weighted(), rows_of(deletes)).to_pylist()
        rest = []
        for r, w, have in zip(
            rows_of(deletes).to_pylist(), deletes.column(WEIGHT).to_pylist(), in_q, strict=True
        ):
            take = min(-w, have)
            if take:
                k = _key(r)
                e = q.entries[k]
                e = Entry(e.row, e.copies - take, e.conditions, e.reason, e.version, e.at)
                if e.copies:
                    q.entries[k] = e
                else:
                    del q.entries[k]
                deleted += take
                removed[k] = take
            rest.append(w + take)
        deletes = deletes.set_column(
            deletes.num_columns - 1, WEIGHT, pa.array(rest, pa.int64())
        ).filter(_call("not_equal", pa.array(rest, pa.int64()), 0))
    first = split_rows(con, inserts, row_conds)
    if keys:
        key_labels = {k.label for k in keys}
        key_only = [k for k, e in q.entries.items() if set(e.conditions) <= key_labels]
        if len(keys) == 1:
            # The other keys' rows keep their status: only the keys the batch
            # touches are counted again.
            cols = list(keys[0].cols)
            touched = concat([rows_of(first.ok), all_deletes]).select(cols)
            affected = _sql(f"SELECT DISTINCT {', '.join(map(_q, cols))} FROM t", t=touched)
            same = " AND ".join(f"k.{_q(c)} IS NOT DISTINCT FROM a.{_q(c)}" for c in cols)
            old_kept = _sql(
                f"SELECT k.* FROM k WHERE EXISTS (SELECT 1 FROM a WHERE {same})",
                k=kept,
                a=affected,
            ).cast(kept.schema)
            if key_only and affected.num_rows:
                q_rows = q.weighted(key_only)
                hits = (
                    _sql(
                        f"SELECT {_q(_IDX)} FROM k WHERE EXISTS (SELECT 1 FROM a WHERE {same}) "
                        "ORDER BY 1",
                        k=q_rows.append_column(_IDX, _indices(q_rows.num_rows)),
                        a=affected,
                    )
                    .column(0)
                    .to_pylist()
                )
                key_only = [key_only[i] for i in hits]
            else:
                key_only = []
        else:
            old_kept = kept
        old = weighted(old_kept, 1)
        held = q.weighted(key_only) if key_only else old.slice(0, 0)
        for k in key_only:
            del q.entries[k]
        pool = consolidated(
            old, held.cast(old.schema), first.ok.cast(old.schema), deletes.cast(old.schema)
        )
        if has_negative(pool):
            raise ValueError("changes delete rows that are not in the table")
        second = apply_keys(pool, keys)
        delta = consolidated(second.ok, negated(old))
        for k, e in _entries(second, version, at, quarantined):
            q.entries[k] = e
    else:
        delta = consolidated(first.ok, deletes)
    for k, e in _entries(first, version, at, quarantined):
        prev = q.entries.get(k)
        if prev is not None:
            e = Entry(e.row, prev.copies + e.copies, e.conditions, e.reason, prev.version, prev.at)
        q.entries[k] = e
    # What moved: copies above what was held (less what the batch deleted)
    # were set aside; copies below it were released.
    added: list[Entry] = []
    released = 0
    for k in dict.fromkeys([*quarantined.entries, *q.entries]):
        before = quarantined.entries[k].copies if k in quarantined.entries else 0
        before -= removed.get(k, 0)
        after = q.entries[k].copies if k in q.entries else 0
        if after > before:
            e = q.entries[k]
            added.append(Entry(e.row, after - before, e.conditions, e.reason, e.version, e.at))
        else:
            released += before - after
    return Moves(delta, q, added, released, deleted)


# -- reports -------------------------------------------------------------------


@dataclass
class QuarantineReport:
    """What one refresh did to the rows of one source set aside (#184).
    `str()` gives one line.

    Attributes:
        source: The source's name in the node.
        quarantined: Rows this refresh quarantined: new rows that break a
            condition, or kept rows a new duplicate key took out.
        by_condition: Of those, how many break each condition, by its label
            as `requires` states it.
        released: Rows set aside before that went to the node: the key they
            repeated is now on one row.
        deleted: Rows set aside before that the source deleted.
        total: Rows quarantined after the refresh, in all.
        examples: Up to 10 of the rows set aside, with `_conditions`,
            `_reason` and `_source_version` columns.
        table: Where the rows set aside are stored: the quarantine table's
            location, or None if only this process holds them
            (`Node.quarantined`).
    """

    source: str
    quarantined: int
    by_condition: dict[str, int]
    released: int
    deleted: int
    total: int
    examples: pa.Table | None = None
    table: str | None = None

    def __str__(self) -> str:
        what = ", ".join(f"{n} × {c}" for c, n in self.by_condition.items())
        parts = []
        if self.quarantined:
            parts.append(f"{self.quarantined} row(s) quarantined" + (f" ({what})" if what else ""))
        if self.released:
            parts.append(f"{self.released} released")
        if self.deleted:
            parts.append(f"{self.deleted} deleted upstream")
        where = f" at {self.table}" if self.table else ""
        parts.append(f"{self.total} in quarantine{where}")
        return f"{self.source}: " + ", ".join(parts)

    def to_dict(self) -> dict[str, Any]:
        """The report as JSON values, for `Refresh.to_json`."""
        return {
            "source": self.source,
            "quarantined": self.quarantined,
            "by_condition": dict(self.by_condition),
            "released": self.released,
            "deleted": self.deleted,
            "total": self.total,
            "table": self.table,
            "examples": [] if self.examples is None else _json_rows(self.examples),
        }


def _json_rows(table: pa.Table) -> list[dict[str, Any]]:
    return json.loads(json.dumps(table.to_pylist(), default=str))


def report(
    source: str, moves_or_q: Moves | Quarantined, table: str | None = None
) -> QuarantineReport:
    """The report of a batch's `Moves`, or of a first load's rows set aside."""
    if isinstance(moves_or_q, Moves):
        new, q = moves_or_q.set_aside, moves_or_q.quarantined
        released, deleted = moves_or_q.released, moves_or_q.deleted
    else:
        q = moves_or_q
        new, released, deleted = list(q.entries.values()), 0, 0
    by: dict[str, int] = {}
    for e in new:
        for c in e.conditions:
            by[c] = by.get(c, 0) + e.copies
    examples = None
    if new:
        shown = Quarantined(q.schema, {str(i): e for i, e in enumerate(new[:EXAMPLES])})
        examples = shown.table().slice(0, EXAMPLES)
    return QuarantineReport(
        source,
        sum(e.copies for e in new),
        by,
        released,
        deleted,
        q.total,
        examples,
        table,
    )


# -- the quarantine table ------------------------------------------------------

TABLE_SCHEMA = pa.schema(
    [
        pa.field("source", pa.string(), nullable=False),
        pa.field("row", pa.string(), nullable=False),
        pa.field("copies", pa.int64(), nullable=False),
        pa.field("conditions", pa.list_(pa.string()), nullable=False),
        pa.field("reason", pa.string(), nullable=False),
        pa.field("source_version", pa.int64(), nullable=False),
        pa.field("quarantined_at", pa.timestamp("us", tz="UTC"), nullable=False),
        pa.field("node", pa.string(), nullable=False),
    ]
)
"""The columns of the quarantine table, format 1 (`docs/stability.md`)."""


def _enc(v: Any) -> Any:
    if isinstance(v, float) and v != v:
        return {_TAG: "double", "value": "NaN"}
    if isinstance(v, float) and v in (float("inf"), float("-inf")):
        return {_TAG: "double", "value": "Infinity" if v > 0 else "-Infinity"}
    if isinstance(v, list):
        return [_enc(x) for x in v]
    if isinstance(v, dict):
        return {k: _enc(x) for k, x in v.items()}
    return cursor_json(v)


def _dec(v: Any) -> Any:
    if isinstance(v, dict) and v.get(_TAG) == "double":
        return float(v["value"])
    if isinstance(v, list):
        return [_dec(x) for x in v]
    if isinstance(v, dict) and _TAG not in v:
        return {k: _dec(x) for k, x in v.items()}
    return cursor_value(v)


def encode_row(row: Mapping[str, Any]) -> str:
    """A row as the quarantine table's `row`: JSON, with the tagged encoding
    of the sink record's cursors for datetimes, dates, times, decimals and
    bytes (`{"$cursor": "date", "value": "2026-11-05"}`), and NaN and the
    infinities tagged "double"."""
    return json.dumps({k: _enc(v) for k, v in row.items()})


def decode_row(text: str) -> dict[str, Any]:
    """The row `encode_row` wrote."""
    return {k: _dec(v) for k, v in json.loads(text).items()}


def table_rows(node: str, held: Mapping[str, Quarantined]) -> pa.Table:
    """The quarantine table's rows for the rows set aside of each source."""
    rows = [
        {
            "source": src,
            "row": encode_row(e.row),
            "copies": e.copies,
            "conditions": e.conditions,
            "reason": e.reason,
            "source_version": e.version,
            "quarantined_at": e.at,
            "node": node,
        }
        for src, q in sorted(held.items())
        for e in q.entries.values()
    ]
    return pa.Table.from_pylist(rows, schema=TABLE_SCHEMA)


SCHEMA = "https://alexandernenninger.github.io/substrait-lean/schemas/quarantine/1.json"
"""The `$schema` of a quarantine table's record: its schema's `$id`."""


def record(node: str, epoch: int, sources: Mapping[str, int]) -> dict[str, Any]:
    """What each write of the quarantine table records with it: which state
    of the node it matches."""
    return {
        "$schema": SCHEMA,
        "format": FORMAT,
        "node": node,
        "epoch": epoch,
        "sources": dict(sources),
    }


def read_record(data: Mapping[str, Any]) -> dict[str, Any]:
    """A record read back; refuses a format newer than this version reads."""
    fmt = data.get("format", 1)
    if not isinstance(fmt, int) or fmt > FORMAT:
        raise ValueError(
            f"the quarantine table's record has format {fmt!r}, and this version of sverify "
            f"reads format {FORMAT} or older: upgrade sverify"
        )
    return dict(data)


RECORD_KEY = "sverify.quarantine"
"""Where a quarantine table's write records `record`: a Delta commit's
`commitInfo` key, an Iceberg snapshot's summary key."""
