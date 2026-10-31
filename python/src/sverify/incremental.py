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
"""

from __future__ import annotations

import json
import math
from collections import Counter
from collections.abc import Mapping, Sequence
from dataclasses import dataclass, field

import ibis.expr.types as ir
import pyarrow as pa

from sverify.contracts import (
    Condition,
    PreconditionError,
    Unique,
    label,
    register_view,
    view_contract,
    violations,
)
from sverify.engine import (
    Backend,
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
    # Python's float equality differs from DataFusion's total order: there
    # NaN equals itself, and -0.0 and 0.0 (or -NaN and NaN) are different.
    if isinstance(x, float) and (math.isnan(x) or x == 0):
        return ("NaN" if math.isnan(x) else "zero", math.copysign(1.0, x))
    return x


def row_key(row: Row) -> tuple:
    """Rows compare as DataFusion compares them (see `_value_key`)."""
    return tuple(_value_key(x) for x in row)


def arrow_rows(table: pa.Table) -> list[Row]:
    return [tuple(r.values()) for r in table.to_pylist()]


@dataclass
class Changes:
    """Rows to insert into and delete from one table (bag semantics: each
    deleted row removes one occurrence)."""

    inserts: Sequence[Row] = field(default_factory=list)
    deletes: Sequence[Row] = field(default_factory=list)


class IncrementalView:
    """A query result kept up to date from table changes instead of recomputed.

    `query` is an Ibis expression or SQL over tables of `con`, an Ibis
    DataFusion backend. The view is also registered as table `name`.
    `engine` runs the plans: the view's plan as Lean read it
    (`written_plan`) and the delta plans, all over the tables of `con`.

    If `query` is the result of contracted transformations, `guarantees` are
    its proved postconditions; they hold in every state of the view, because
    every batch is checked against the preconditions on the base tables
    (`requires`). A standalone view refuses a query without delta rules
    (`NotIncremental`); in a `Pipeline` such a view is recomputed instead.
    """

    def __init__(
        self,
        con: Backend,
        query: ir.Table | str,
        name: str,
        engine: Engine = "datafusion",
        *,
        pipeline: Pipeline | None = None,
    ):
        self.con, self.name, self.engine = con, name, engine
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
        result = run_plan(con, self.plan, engine)
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
                if con.con.table_exist(t + "$delta"):
                    con.con.deregister_table(t + "$delta")
        return delta, examples

    def _diff(self, new_tables: Mapping[str, pa.Table]) -> tuple[Counter[tuple], dict[tuple, Row]]:
        """The view's change by recomputing it on the new inputs and diffing."""
        con = self.con
        old = {t: con.con.table(t).to_arrow_table() for t in self.tables if t in new_tables}
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


def _load_delta_table(con: Backend, t: str, rows: ZRows) -> None:
    base = con.con.table(t).schema()
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
    """

    def __init__(self, con: Backend, engine: Engine = "datafusion"):
        self.con, self.engine = con, engine
        self._views: list[IncrementalView] = []
        self.requires: dict[str, list[Condition]] = {}
        """Preconditions on base tables, of every contracted view."""
        self._keys: dict[tuple[str, tuple[str, ...]], Counter[tuple]] = {}

    def view(self, name: str, query: ir.Table | str) -> IncrementalView:
        if name in self.views:
            raise ValueError(f"the pipeline already has a view {name!r}")
        return IncrementalView(self.con, query, name, self.engine, pipeline=self)

    @property
    def views(self) -> dict[str, IncrementalView]:
        return {v.name: v for v in self._views}

    @property
    def fallbacks(self) -> dict[str, str]:
        """Views that are recomputed and diffed, with the reason."""
        return {v.name: v.fallback for v in self._views if v.fallback is not None}

    def _check_new_requires(self, requires: Mapping[str, Sequence[Condition]]) -> None:
        """Check a new view's preconditions on the full base tables, once."""
        for t, conds in requires.items():
            if t in self.views:
                raise ValueError(f"preconditions on view {t!r} must be proved, not checked")
            known = {label(c) for c in self.requires.get(t, [])}
            for c in conds:
                if label(c) in known:
                    continue
                if isinstance(c, Unique):
                    index = Counter(
                        _key_of(row, _positions(self.con, t, c)) for row in _rows(self.con, t)
                    )
                    if dup := sum(n - 1 for n in index.values() if n > 1):
                        raise PreconditionError(f"{dup} row(s) of {t} violate {label(c)}")
                    self._keys[(t, c.cols)] = index
                elif n := violations(self.con.table(t), c, self.engine):
                    raise PreconditionError(f"{n} row(s) of {t} violate {label(c)}")
                self.requires.setdefault(t, []).append(c)

    def _check_batch(
        self, changes: Mapping[str, Changes]
    ) -> dict[tuple[str, tuple[str, ...]], Counter[tuple]]:
        """Check the base-table preconditions on a batch alone: row
        conditions on the inserted rows, keys of the inserted rows against
        each other and the keys the batch keeps. Returns the new key indexes."""
        indexes = {}
        for t, ch in changes.items():
            conds = self.requires.get(t, [])
            rowwise = [c for c in conds if not isinstance(c, Unique)]
            if rowwise and ch.inserts:
                name = t + "$inserts"
                put_table(self.con, name, to_arrow(ch.inserts, self.con.con.table(t).schema()))
                try:
                    for c in rowwise:
                        if n := violations(self.con.table(name), c, self.engine):
                            raise PreconditionError(
                                f"{n} inserted row(s) of {t} violate {label(c)}"
                            )
                finally:
                    self.con.con.deregister_table(name)
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
        return indexes

    def apply(self, changes: Mapping[str, Changes]) -> None:
        """Apply changes to base tables and bring every view up to date."""
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
        indexes = self._check_batch(changes)
        deltas: dict[str, ZRows] = {
            t: [(tuple(r), 1) for r in ch.inserts] + [(tuple(r), -1) for r in ch.deletes]
            for t, ch in changes.items()
        }
        updates: list[tuple[IncrementalView, Counter[tuple], dict[tuple, Row]]] = []
        # Views read the *old* tables (and their inputs' changes), so nothing
        # is replaced until every view has its change.
        for v in self._views:
            if not any(deltas.get(t) for t in v.tables):
                continue
            delta, examples = v._diff(new_tables) if v.fallback else v._delta(deltas)
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
        # Commit: nothing above changed any table or view.
        for t in changes:
            put_table(con, t, new_tables[t])
        self._keys.update(indexes)
        for v, merged, _ in updates:
            v.counts = merged
            v._publish()


def _rows(con: Backend, t: str) -> list[Row]:
    return arrow_rows(con.con.table(t).to_arrow_table())


def _positions(con: Backend, t: str, key: Unique) -> list[int]:
    names = con.con.table(t).schema().names
    return [names.index(c) for c in key.cols]


def _key_of(row: Row, positions: Sequence[int]) -> tuple:
    return row_key(tuple(row[i] for i in positions))


def _apply_to_table(con: Backend, t: str, ch: Changes) -> pa.Table:
    current = con.con.table(t).to_arrow_table()
    rows = arrow_rows(current)
    for r in ch.deletes:
        k = row_key(tuple(r))
        hit = next((i for i, x in enumerate(rows) if row_key(x) == k), None)
        if hit is None:
            raise ValueError(f"cannot delete {r!r} from {t}: no such row")
        rows.pop(hit)
    rows += [tuple(r) for r in ch.inserts]
    return to_arrow(rows, current.schema)
