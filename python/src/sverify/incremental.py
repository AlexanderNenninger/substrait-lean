"""Incrementally maintained views on DataFusion or Polars, with delta plans from Lean.

The verified part is the delta plan: `substrait-check --delta` compiles the
view's Substrait plan with `Rel.delta`, splits it into union-free terms
(`Rel.terms`) and applies the weight-column encoding (`Rel.weighted`). Lean
proves the concatenated results are the change to the view
(`Rel.incremental_sound`, `Rel.zeval_terms`, `Rel.weighted_eval`). This module
is the trusted glue around it: it keeps the view as rows with multiplicities,
builds the change tables, runs the delta plans on DataFusion or Polars and merges the
result. A batch is computed completely before anything is replaced, so a
failing batch changes nothing.

A view of a contracted transformation (`sverify.transform`, possibly
composed) keeps its proved postconditions in every state: the preconditions
on the base tables are checked once in full, and then only on each batch
(row conditions on the inserted rows, `unique` keys against the kept keys;
`Spec.update`, `Triple.maintained` in `SubstraitLean/Compose.lean`).

A `Pipeline` maintains views that read each other. Each view's change becomes
the change table of the views that read it (the DBSP chain rule,
`Rel.chain_sound`). A view without a delta rule (left join, fetch, window) is
recomputed and diffed, which still yields its change for the views
downstream (`ZSet.diff_correct`).

A pipeline can read its base tables from a table format (`sverify.io`):
`Pipeline.source` loads a snapshot and records its version, and `refresh`
applies the format's change feed from the recorded version to the latest,
advancing the version in the same commit. The feed is trusted to turn the
old snapshot into the new one (`ChangeFeed`, `Rel.cdf_sound` in
`SubstraitLean/TableFormat.lean`), and every `RefreshReport` says so; where
the feed is unavailable, the new snapshot is diffed against the view's state
instead and the views reading it are recomputed (`ChangeFeed.of_diff`).
"""

from __future__ import annotations

import json
import math
from collections import Counter
from collections.abc import Mapping, Sequence
from dataclasses import dataclass, field
from typing import Literal, Protocol

import ibis.expr.types as ir
import pyarrow as pa

from sverify.contracts import (
    ON_DATA,
    Condition,
    Discharged,
    Fact,
    PreconditionError,
    References,
    Unique,
    discharge,
    label,
    register_facts,
    register_view,
    table_facts,
    view_contract,
)
from sverify.engine import (
    Connection,
    Engine,
    plan_json,
    put_table,
    read_tables,
    run_checker,
    run_plan,
    to_arrow,
    written_plan,
)

Row = tuple
WEIGHT = "__weight"


class NotIncremental(Exception):
    """The plan is outside the fragment with verified delta rules."""


def delta_plans(plan_json: str) -> list[str]:
    """Ask Lean for the weighted delta plans of a Substrait JSON plan; the
    change to the view is the concatenation of their outputs."""
    code, out, err = run_checker(("--delta",), plan_json)
    if code == 3:
        raise NotIncremental(err.strip())
    if code != 0:
        raise ValueError(f"substrait-check --delta failed: {err.strip()}")
    return out.splitlines()


def _value_key(x: object) -> object:
    # The model has one NaN, equal to itself (Python's is not), and one zero
    # (`-0.0 + 0.0` is `0.0`).
    if isinstance(x, float):
        return "NaN" if math.isnan(x) else x + 0.0
    return x


def row_key(row: Row) -> tuple:
    """Rows compare as the model compares them (see `_value_key`)."""
    return tuple(_value_key(x) for x in row)


def arrow_rows(table: pa.Table) -> list[Row]:
    return [tuple(r.values()) for r in table.to_pylist()]


@dataclass
class Changes:
    """Rows to insert into and delete from one table (bag semantics: each
    deleted row removes one occurrence)."""

    inserts: Sequence[Row] = field(default_factory=list)
    deletes: Sequence[Row] = field(default_factory=list)


def consolidate(ch: Changes) -> Changes:
    """The net change: a row both inserted and deleted cancels out."""
    net = Counter[tuple]()
    examples: dict[tuple, Row] = {}
    for rows, w in ((ch.inserts, 1), (ch.deletes, -1)):
        for r in rows:
            k = row_key(tuple(r))
            net[k] += w
            examples.setdefault(k, tuple(r))
    return Changes(
        inserts=[examples[k] for k, n in net.items() for _ in range(max(n, 0))],
        deletes=[examples[k] for k, n in net.items() for _ in range(max(-n, 0))],
    )


def snapshot_diff(old: pa.Table, new: pa.Table) -> Changes:
    """The change turning `old` into `new` (bag difference)."""
    return consolidate(Changes(inserts=arrow_rows(new), deletes=arrow_rows(old)))


@dataclass
class Snapshot:
    """A table at one version, as a source hands it to a pipeline."""

    version: int
    table: pa.Table
    facts: list[Fact]
    """What the metadata says about every row (schema nullability is in
    `table.schema`)."""


@dataclass
class SourceBatch:
    """What a source has between a recorded version and its latest one.

    Either `changes` from the format's change feed (the net change, with
    `facts` about the inserted rows and the `trusted` assumption it rests
    on), or the new `snapshot` alone with the reason the feed is unavailable
    (`fallback`)."""

    start: int
    end: int
    snapshot_facts: list[Fact]
    """What the metadata says about every row at `end`."""
    changes: Changes | None = None
    facts: list[Fact] = field(default_factory=list)
    trusted: str = ""
    """E.g. "Δ trusted as coming from Delta CDF v3→v5"."""
    kind: Literal["change feed", "snapshot diff"] = "change feed"
    """A snapshot diff is exact (`ChangeFeed.of_diff`): only the snapshots
    are trusted."""
    snapshot: pa.Table | None = None
    fallback: str | None = None


class Source(Protocol):
    """A versioned table: a Delta table or an Iceberg table (`sverify.io`)."""

    def snapshot(self, version: int | None = None) -> Snapshot:
        """The table at `version`, or at its latest version."""
        ...

    def changes(self, since: int) -> SourceBatch: ...


@dataclass
class SourceRefresh:
    table: str
    start: int
    end: int
    mode: Literal["unchanged", "change feed", "snapshot diff", "recomputed"]
    detail: str = ""
    inserts: int = 0
    deletes: int = 0

    def __str__(self) -> str:
        if self.mode == "unchanged":
            return f"{self.table}@v{self.start}: no new version"
        span = f"{self.table}@v{self.start}→v{self.end}"
        counts = f"{self.inserts} insert(s), {self.deletes} delete(s)"
        if self.mode == "recomputed":
            return f"{span}: recomputed from scratch ({self.detail}); {counts}"
        return f"{span}: {counts}; {self.detail}"


@dataclass
class RefreshReport:
    sources: list[SourceRefresh]
    preconditions: list[Discharged]
    """How each precondition on the batch was established."""
    versions: dict[str, dict[str, int]]
    """For each view, the version of every source it reads."""
    audited: bool = False
    """The batch was compared with the new snapshot, and each view with its
    recomputation, and they agreed."""

    @property
    def recomputed(self) -> list[str]:
        return [s.table for s in self.sources if s.mode == "recomputed"]

    def __str__(self) -> str:
        lines = [str(s) for s in self.sources]
        lines += [f"requires {p}" for p in self.preconditions]
        for v, vs in self.versions.items():
            lines.append(f"view {v}: " + ", ".join(f"{t}@v{n}" for t, n in vs.items()))
        if self.audited:
            lines.append("audit: batch matches the new snapshots; views match recomputation")
        return "\n".join(lines)


class AuditError(Exception):
    """In audit mode, the change feed or a view disagrees with recomputation."""


class IncrementalView:
    """A query result kept up to date from table changes instead of recomputed.

    `query` is an Ibis expression or SQL over tables of `con` (`connect()`).
    The view is also registered as table `name`. `engine` (default: the
    connection's) runs the plans: the view's plan as Lean read it
    (`written_plan`) and the delta plans, all over the tables of `con`; with
    an engine named, preconditions are also checked there.

    If `query` is the result of contracted transformations, `guarantees` are
    its proved postconditions; they hold in every state of the view, because
    every batch is checked against the preconditions on the base tables
    (`requires`). A standalone view refuses a query without delta rules
    (`NotIncremental`); in a `Pipeline` such a view is recomputed instead.
    """

    def __init__(
        self,
        con: Connection,
        query: ir.Table | str,
        name: str,
        engine: Engine | None = None,
        *,
        pipeline: Pipeline | None = None,
    ):
        self.con, self.name = con, name
        self.engine: Engine = engine or con.engine
        contract = None if isinstance(query, str) else view_contract(query)
        plan = json.loads(plan_json(con, query))
        self.columns: list[str] = plan["relations"][0]["root"]["names"]
        self.tables = read_tables(plan)
        # Publishing the view would replace the table it is computed from.
        if name in self.tables:
            raise ValueError(f"view name {name!r} is a table the view reads")
        self.fallback: str | None = None
        """Why the view has no delta plans and is recomputed, if it is."""
        try:
            self.deltas = delta_plans(json.dumps(plan))
        except NotIncremental as e:
            if pipeline is None:
                raise
            self.deltas, self.fallback = [], str(e)
        self.plan = written_plan(json.dumps(plan))
        self.requires: dict[str, list[Condition]] = contract.requires if contract else {}
        self.guarantees: list[Condition] = contract.guarantees if contract else []
        self.pipeline = pipeline or Pipeline(con, engine)
        self.pipeline._check_new_requires(self.requires)
        result = run_plan(con, self.plan, self.engine)
        self.schema = result.schema
        self.counts: Counter[tuple] = Counter()
        self.examples: dict[tuple, Row] = {}
        self._add(arrow_rows(result), 1)
        self._publish()
        self.table: ir.Table = con.table(name)
        """The view as a table for other queries; contracted transformations
        that read it build on `guarantees`."""
        if contract is not None:
            register_view(self.table, contract)
        self.pipeline._views.append(self)

    def _add(self, rows: Sequence[Row], weight: int) -> None:
        for r in rows:
            k = row_key(r)
            self.counts[k] += weight
            self.examples.setdefault(k, r)

    def _arrow(self, counts: Mapping[tuple, int]) -> pa.Table:
        return to_arrow(
            [self.examples[k] for k, n in counts.items() for _ in range(n)], self.schema
        )

    def _publish(self) -> None:
        put_table(self.con, self.name, self._arrow(self.counts))

    @property
    def versions(self) -> dict[str, int]:
        """The version of every source the view reads, e.g. `{"orders": 41}`
        (shown as `orders@v41`)."""
        return self.pipeline.lineage(self.name)

    def rows(self) -> list[Row]:
        """The view's contents as a bag of rows, in a canonical order."""
        out = [self.examples[k] for k, n in self.counts.items() for _ in range(n)]
        return sorted(out, key=lambda r: repr(row_key(r)))

    def recompute(self) -> list[Row]:
        """The view computed from scratch, for checking."""
        rows = arrow_rows(run_plan(self.con, self.plan, self.engine))
        return sorted(rows, key=lambda r: repr(row_key(r)))

    def apply(self, changes: Mapping[str, Changes]) -> None:
        """Apply changes to base tables, and to every view of the pipeline."""
        self.pipeline.apply(changes)

    def _delta(self, deltas: Mapping[str, ZRows]) -> tuple[Counter[tuple], dict[tuple, Row]]:
        """The view's change, from its delta plans. The tables hold their old
        contents; `t$delta` is loaded with each input's change."""
        con = self.con
        try:
            for t in self.tables:
                _load_delta_table(con, t, deltas.get(t, []))
            delta = Counter[tuple]()
            examples: dict[tuple, Row] = {}
            for plan in self.deltas:
                for r in arrow_rows(run_plan(con, plan, self.engine)):
                    k = row_key(r[:-1])
                    delta[k] += r[-1]
                    examples.setdefault(k, r[:-1])
        finally:
            for t in self.tables:
                con.drop(t + "$delta")
        return delta, examples

    def _diff(self, new_tables: Mapping[str, pa.Table]) -> tuple[Counter[tuple], dict[tuple, Row]]:
        """The view's change by recomputing it on the new inputs and diffing."""
        con = self.con
        old = {t: con.arrow[t] for t in self.tables if t in new_tables}
        try:
            for t in old:
                put_table(con, t, new_tables[t])
            rows = arrow_rows(run_plan(con, self.plan, self.engine))
        finally:
            for t, table in old.items():
                put_table(con, t, table)
        delta = Counter[tuple]()
        examples: dict[tuple, Row] = {}
        for r in rows:
            k = row_key(r)
            delta[k] += 1
            examples.setdefault(k, r)
        delta.subtract(self.counts)
        return delta, examples


ZRows = list[tuple[Row, int]]
"""A change as rows with weights (positive: inserted, negative: deleted)."""


def _load_delta_table(con: Connection, t: str, rows: ZRows) -> None:
    base = con.arrow[t].schema
    schema = pa.schema([*base, pa.field(WEIGHT, pa.int64())])
    put_table(con, t + "$delta", to_arrow([(*r, w) for r, w in rows], schema))


class Pipeline:
    """Views that read each other, maintained together.

        pipe = sv.Pipeline(con)
        big = pipe.view("big", doubled(paid(con.table("orders"))))
        pipe.view("by_id", summarize(big.table))
        pipe.apply({"orders": sv.Changes(inserts=[...])})

    A view may read base tables and views added before it, as `view.table`.
    `apply` runs the views in order: each view's change is the change table
    of the views that read it, so every intermediate result is materialized
    once and shared. Views without delta rules are recomputed and diffed
    (`fallbacks`). Preconditions of contracted views are checked per batch.

    Base tables may instead come from a table format (`source`), and then
    change only through `refresh`.
    """

    def __init__(self, con: Connection, engine: Engine | None = None):
        self.con = con
        self.engine: Engine | None = engine
        """The engine for plans and precondition checks; None: the
        connection's for plans, Ibis on the connection for checks."""
        self._views: list[IncrementalView] = []
        self.requires: dict[str, list[Condition]] = {}
        """Preconditions on base tables, of every contracted view."""
        self.preconditions: list[Discharged] = []
        """How each precondition was established on the full base tables."""
        self._keys: dict[tuple[str, tuple[str, ...]], Counter[tuple]] = {}
        self.sources: dict[str, Source] = {}
        self.versions: dict[str, int] = {}
        """The version of each source table the pipeline's state reflects."""

    def source(self, name: str, source: Source) -> ir.Table:
        """Load the latest snapshot of `source` as base table `name`, record
        its version and what its metadata says about it."""
        if name in self.sources or name in self.views:
            raise ValueError(f"the pipeline already has a table {name!r}")
        snap = source.snapshot()
        put_table(self.con, name, snap.table)
        register_facts(self.con, name, snap.facts)
        self.sources[name] = source
        self.versions[name] = snap.version
        return self.con.table(name)

    def view(self, name: str, query: ir.Table | str) -> IncrementalView:
        if name in self.views or name in self.sources:
            raise ValueError(f"the pipeline already has a view {name!r}")
        return IncrementalView(self.con, query, name, self.engine, pipeline=self)

    @property
    def views(self) -> dict[str, IncrementalView]:
        return {v.name: v for v in self._views}

    @property
    def fallbacks(self) -> dict[str, str]:
        """Views that are recomputed and diffed, with the reason."""
        return {v.name: v.fallback for v in self._views if v.fallback is not None}

    def lineage(self, name: str) -> dict[str, int]:
        """The version of every source table that `name` (a view or table)
        is computed from."""
        if name in self.versions:
            return {name: self.versions[name]}
        out: dict[str, int] = {}
        if (v := self.views.get(name)) is not None:
            for t in v.tables:
                out.update(self.lineage(t))
        return out

    def _check_new_requires(self, requires: Mapping[str, Sequence[Condition]]) -> None:
        """Establish a new view's preconditions on the full base tables, once:
        from metadata where possible, else on the data."""
        for t, conds in requires.items():
            if t in self.views:
                raise ValueError(f"preconditions on view {t!r} must be proved, not checked")
            if refs := [label(c) for c in conds if isinstance(c, References)]:
                raise ValueError(f"incremental views do not support foreign keys yet: {refs}")
            known = {label(c) for c in self.requires.get(t, [])}
            new = [c for c in conds if label(c) not in known]
            for c in new:
                if isinstance(c, Unique):
                    index = Counter(
                        _key_of(row, _positions(self.con, t, c)) for row in _rows(self.con, t)
                    )
                    if dup := sum(n - 1 for n in index.values() if n > 1):
                        raise PreconditionError(f"{dup} row(s) of {t} violate {label(c)}")
                    self._keys[(t, c.cols)] = index
                    self.preconditions.append(Discharged(t, label(c), ON_DATA))
            table = self.con.table(t)
            rowwise = [c for c in new if not isinstance(c, Unique)]
            self.preconditions += discharge(
                table, t, rowwise, self.engine, table_facts(table), f"row(s) of {t}"
            )
            self.requires.setdefault(t, []).extend(new)

    def _check_batch(
        self, changes: Mapping[str, Changes], facts: Mapping[str, Sequence[Fact]]
    ) -> tuple[dict[tuple[str, tuple[str, ...]], Counter[tuple]], list[Discharged]]:
        """Establish the base-table preconditions on a batch alone: row
        conditions on the inserted rows (from `facts` about them where
        possible), keys of the inserted rows against each other and the keys
        the batch keeps. Returns the new key indexes."""
        indexes = {}
        found: list[Discharged] = []
        for t, ch in changes.items():
            conds = self.requires.get(t, [])
            rowwise = [c for c in conds if not isinstance(c, Unique)]
            if rowwise and ch.inserts:
                name = t + "$inserts"
                put_table(self.con, name, to_arrow(ch.inserts, self.con.arrow[t].schema))
                try:
                    found += discharge(
                        self.con.table(name),
                        t,
                        rowwise,
                        self.engine,
                        facts.get(t),
                        f"inserted row(s) of {t}",
                    )
                finally:
                    self.con.drop(name)
            for c in conds:
                if not isinstance(c, Unique):
                    continue
                pos = _positions(self.con, t, c)
                index = self._keys[(t, c.cols)].copy()
                index.subtract(_key_of(r, pos) for r in ch.deletes)
                inserted = [_key_of(r, pos) for r in ch.inserts]
                index.update(inserted)
                if clash := sum(1 for k in set(inserted) if index[k] > 1):
                    raise PreconditionError(f"{clash} inserted key(s) of {t} violate {label(c)}")
                indexes[(t, c.cols)] = +index
                found.append(Discharged(t, label(c), ON_DATA))
        return indexes, found

    def apply(self, changes: Mapping[str, Changes]) -> None:
        """Apply changes to base tables and bring every view up to date."""
        sourced = set(changes) & set(self.sources)
        if sourced:
            raise ValueError(f"{sorted(sourced)} change through their source; call refresh()")
        self._apply(changes)

    def refresh(self, *, audit: bool = False) -> RefreshReport:
        """Bring every source table to its latest version, and the views with it.

        Each source's change since the recorded version comes from its change
        feed (trusted, and the report says so) or, where the feed is
        unavailable, from diffing the new snapshot against the current state,
        in which case the views reading it are recomputed. The new versions
        are recorded in the same commit as the new state, so a failed refresh
        changes nothing and a retry does not apply a batch twice.

        With `audit`, the batch is first compared with the new snapshots and,
        after the commit, every view with its recomputation (`AuditError`)."""
        changes: dict[str, Changes] = {}
        facts: dict[str, list[Fact]] = {}
        versions: dict[str, int] = {}
        snapshot_facts: dict[str, list[Fact]] = {}
        recompute: set[str] = set()
        report: list[SourceRefresh] = []
        for t, src in self.sources.items():
            start = self.versions[t]
            batch = src.changes(start)
            if batch.end == start:
                report.append(SourceRefresh(t, start, start, "unchanged"))
                continue
            current = self.con.arrow[t]
            if batch.changes is None:
                assert batch.snapshot is not None
                ch = snapshot_diff(current, batch.snapshot)
                recompute.add(t)
                # The diff's inserts are rows of the new snapshot.
                facts[t] = batch.snapshot_facts
                mode, detail = "recomputed", f"{batch.fallback}; Δ = snapshot v{batch.end} − state"
            else:
                ch = consolidate(batch.changes)
                facts[t] = batch.facts
                mode, detail = batch.kind, batch.trusted
            if audit and batch.changes is not None:
                got = _apply_to_table(self.con, t, ch)
                want = src.snapshot(batch.end).table
                if Counter(map(row_key, arrow_rows(got))) != Counter(
                    map(row_key, arrow_rows(want))
                ):
                    raise AuditError(
                        f"{t}: the change feed v{start}→v{batch.end} does not turn the "
                        f"state into snapshot v{batch.end}; nothing was applied"
                    )
            changes[t], versions[t] = ch, batch.end
            snapshot_facts[t] = batch.snapshot_facts
            report.append(
                SourceRefresh(t, start, batch.end, mode, detail, len(ch.inserts), len(ch.deletes))
            )
        found = self._apply(changes, facts=facts, recompute=recompute, versions=versions)
        for t, fs in snapshot_facts.items():
            register_facts(self.con, t, fs)
        if audit:
            for v in self._views:
                if v.rows() != v.recompute():
                    raise AuditError(f"view {v.name} differs from its recomputation")
        return RefreshReport(
            report, found, {v.name: v.versions for v in self._views}, audited=audit
        )

    def _apply(
        self,
        changes: Mapping[str, Changes],
        *,
        facts: Mapping[str, Sequence[Fact]] | None = None,
        recompute: set[str] | None = None,
        versions: Mapping[str, int] | None = None,
    ) -> list[Discharged]:
        """Apply `changes` and bring every view up to date. Views reading a
        table in `recompute` (directly or through other views) are recomputed
        and diffed; `versions` are recorded with the commit."""
        con = self.con
        views = self.views
        bad = set(changes) & set(views)
        if bad:
            raise ValueError(f"views change only through their inputs: {sorted(bad)}")
        read = {t for v in self._views for t in v.tables}
        unknown = set(changes) - read
        if unknown:
            raise ValueError(f"no view reads {sorted(unknown)}")
        # New base tables first: this also checks that every delete exists.
        new_tables = {t: _apply_to_table(con, t, ch) for t, ch in changes.items()}
        indexes, found = self._check_batch(changes, facts or {})
        deltas: dict[str, ZRows] = {
            t: [(tuple(r), 1) for r in ch.inserts] + [(tuple(r), -1) for r in ch.deletes]
            for t, ch in changes.items()
        }
        stale = set(recompute or ())
        updates: list[tuple[IncrementalView, Counter[tuple], dict[tuple, Row]]] = []
        # Views read the *old* tables (and their inputs' changes), so nothing
        # is replaced until every view has its change.
        for v in self._views:
            if not any(deltas.get(t) for t in v.tables):
                continue
            rerun = v.fallback is not None or any(t in stale for t in v.tables)
            if rerun:
                stale.add(v.name)
            delta, examples = v._diff(new_tables) if rerun else v._delta(deltas)
            merged = v.counts.copy()
            merged.update(delta)
            if any(n < 0 for n in merged.values()):
                raise ValueError(f"changes delete rows that are not in the inputs of {v.name}")
            for k, r in examples.items():
                v.examples.setdefault(k, r)
            merged = +merged
            deltas[v.name] = [(v.examples[k], n) for k, n in delta.items() if n != 0]
            new_tables[v.name] = v._arrow(merged)
            updates.append((v, merged, examples))
        # Commit: nothing above changed any table, view or version.
        for t in changes:
            put_table(con, t, new_tables[t])
        self._keys.update(indexes)
        self.versions.update(versions or {})
        for v, merged, _ in updates:
            v.counts = merged
            v._publish()
        return found


def _rows(con: Connection, t: str) -> list[Row]:
    return arrow_rows(con.arrow[t])


def _positions(con: Connection, t: str, key: Unique) -> list[int]:
    names = con.arrow[t].schema.names
    return [names.index(c) for c in key.cols]


def _key_of(row: Row, positions: Sequence[int]) -> tuple:
    return row_key(tuple(row[i] for i in positions))


def _apply_to_table(con: Connection, t: str, ch: Changes) -> pa.Table:
    current = con.arrow[t]
    rows = arrow_rows(current)
    for r in ch.deletes:
        k = row_key(tuple(r))
        hit = next((i for i, x in enumerate(rows) if row_key(x) == k), None)
        if hit is None:
            raise ValueError(f"cannot delete {r!r} from {t}: no such row")
        rows.pop(hit)
    rows += [tuple(r) for r in ch.inserts]
    return to_arrow(rows, current.schema)
