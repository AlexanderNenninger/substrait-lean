"""Nodes: contracted transforms composed over sources, stored with `.write`
and kept up to date with `refresh`.

Internal: not part of sverify's public API, which is `sverify`, `sverify.io`,
`sverify.engines` and `sverify.errors`; it may change in any release. The
public names (`Node`, `group`) are re-exported by `sverify`.

    orders = DeltaSource("s3://lake/orders")
    p = orders.pipe(paid).write(DeltaSink("s3://lake/paid"))
    r = p.pipe(revenue).write(DeltaSink("s3://lake/revenue"))
    r.refresh(engine="polars")

Piping a source or a node into a step (`Node.pipe`: a contracted transform,
`sverify.sql(query)` or a plain function) builds a node, as does calling a
contracted transform (`sverify.transform`) on it: `orders.pipe(paid)` is
`paid(orders)`. Its contract is checked then, on placeholder tables with the
sources' schemas: its postconditions are proved, and a precondition on
another node's result must follow from what that node guarantees
(`CompositionError`). Preconditions on sources are checked on the data when
the node is refreshed, and then on every batch.

A node's *stage* is what one incremental view (`sverify.incremental`)
maintains: the transforms from the node up to the sources or stored nodes it
reads, fused into one plan. Only `.write` ends a stage. The stored node's
table is then a source of the stages that read it, through its change feed,
and what they may assume about it is what its own stage proved: the
preconditions on that stage's sources were checked there, and the sink
records the guarantees with the table. `refresh` brings the stages a node
needs up to date, upstream first, each once per call, and writes every
stored node once; `group` does that for several nodes against the same
source versions.
"""

from __future__ import annotations

import warnings
from collections.abc import Sequence
from dataclasses import dataclass, field, replace
from typing import TYPE_CHECKING, Any, Literal, Protocol

import ibis
import ibis.expr.types as ir
import pyarrow as pa

from sverify._retention import RetentionReport
from sverify.contracts import ON_DATA, Discharged, _lookup, _register, label
from sverify.engine import ENGINES, connect, plain_schema, written_plan
from sverify.ibis_substrait import to_substrait_json
from sverify.incremental import IncrementalView, Pipeline, RefreshReport, Source, Stored
from sverify.observation import PLAN_BOUND, Observation
from sverify.steps import Step, as_transform

if TYPE_CHECKING:
    import pandas
    import polars

    from sverify.contracts import ContractedTransform, Report
    from sverify.io._common import Contract, SinkWrite
    from sverify.routes import Route, RouteKind


class Sink(Protocol):
    """What `Node.write` needs of a sink (`sverify.io.DeltaSink`, `IcebergSink`).

    `sverify.io.Sink` implements it, and a sink of your own subclasses that;
    the methods it asks for are private, called by `refresh`.

    Attributes:
        name: The stored table's name in the plans that read it (the sink's
            `name=`, by default the last part of its URI or identifier).
    """

    name: str

    def _attach(self, view: IncrementalView) -> None: ...

    def _commit(self) -> SinkWrite: ...

    def _stored(self) -> Stored | None: ...

    def _source(self) -> Source: ...

    def committed(self) -> Contract | None: ...


class Node:
    """The result of a contracted transform over sources or other nodes.

        r = orders.pipe(paid).pipe(revenue)              # one fused plan
        r = orders.pipe(paid).write(sink).pipe(revenue)  # paid is stored, revenue reads it
        r.refresh(engine="polars")
        r.to_pandas()

    Built by piping a source (`sverify.io`) or a node into a step (`pipe`),
    or by calling a transform (`sverify.transform`) on it, which is the same:
    `orders.pipe(paid)` is `paid(orders)`. Its contract is checked then. `write(sink)`
    stores the node and returns the stored node, which downstream transforms
    read as a versioned source. `refresh` brings the node and every node it
    reads up to date; the results come from the last refresh, through
    `to_arrow`, `to_polars`, `to_pandas` and `table` (an Ibis table).

    The node keeps its state while the process runs; a stored node's table
    is its durable state, so a restarted job resumes from it.

    Attributes:
        name: The node's name: the transform's, or for a stored node the
            sink's `name`. It names the node in `Refresh` and `Status`, and
            a stored node's table in the plans that read it.

    Examples:
        Two contracted transforms over an in-memory source, first fused into
        one plan, then with the first one stored in a Delta table:

        ```python
        import tempfile

        import pyarrow as pa
        import sverify as sv
        from ibis import _
        from sverify.io import DeltaSink, StaticSource

        orders = StaticSource(
            pa.table({"id": [1, 2], "customer": ["ada", "bob"], "amount": [30, 5]}),
            name="orders",
        )

        @sv.transform(
            requires={"orders": [_.amount >= 0, _.amount < 1_000_000_000, sv.unique("id")]},
            ensures=[_.amount > 10, _.amount < 1_000_000_000, sv.unique("id")],
        )
        def paid(orders):
            return orders.filter(orders.amount > 10)

        @sv.transform(
            requires={"t": [_.amount > 10, _.amount < 1_000_000_000]},
            ensures=[_.doubled > 20],
        )
        def doubled(t):
            return t.select(t.id, doubled=t.amount * 2)

        r = orders.pipe(paid).pipe(doubled)  # one fused plan, proved here
        r.refresh()  # computed, on DuckDB by default
        r.to_arrow().to_pylist()  # [{'id': 1, 'doubled': 60}]

        lake = tempfile.mkdtemp()
        p = orders.pipe(paid).write(DeltaSink(f"{lake}/paid"))  # stored: a source
        r = p.pipe(doubled).write(DeltaSink(f"{lake}/doubled"))
        r.refresh()  # paid first, then doubled; each written once

        orders.apply(sv.Changes(inserts=[(3, "cy", 50)], deletes=[(1, "ada", 30)]))
        r.refresh(engine="polars")  # updated from the changes alone
        r.to_arrow().to_pylist()  # [{'id': 3, 'doubled': 100}]
        r.to_polars(); r.to_pandas(); r.table  # the same rows, other forms
        ```
    """

    def __init__(self, name: str, expr: ir.Table, inputs: Sequence[Node]):
        self.name = name
        self._expr = expr
        self._inputs = list(inputs)
        self._stage: _Stage | None = None
        self._plan: str | None = None

    def __repr__(self) -> str:
        cols = ", ".join(f"{n}: {t}" for n, t in self.schema.items())
        return f"<{type(self).__name__.strip('_')} {self.name} ({cols})>"

    @property
    def schema(self) -> ibis.Schema:
        """The node's columns and their types, known when the node is built."""
        return self._expr.schema()

    @property
    def internal_plan(self) -> str:
        """The Substrait plan (JSON) of the node's stage, as Lean checked and
        wrote it: what every engine runs. It uses sverify's own extension
        URNs, so only sverify reads it (`sverify.engines.to_sql`, `run`,
        `delta_plans`); `Report.to_substrait()` is the portable plan.
        `sverify.engines.delta_plans(plan)` are the plans that maintain it
        from changes.

        The stage reads the sources and stored nodes upstream under their
        names, so a stored node's plan is that of the node it stores."""
        if self._plan is None:
            self._plan = written_plan(to_substrait_json(self._query()._expr))
        return self._plan

    @property
    def plan(self) -> str:
        """Deprecated: `internal_plan`, sverify's own form of the plan
        (`Report.to_substrait()` is the portable one)."""
        warnings.warn(
            "Node.plan is deprecated; read node.internal_plan (sverify's own form of the "
            "plan), or report.to_substrait() for a portable Substrait plan",
            DeprecationWarning,
            stacklevel=2,
        )
        return self.internal_plan

    @property
    def report(self) -> Report | None:
        """The `Report` of the contract that made the node's result: the
        last transform's proof over its inputs, where a contracted node
        upstream is a placeholder table under that transform's name, assumed
        to meet what it guarantees. None for a source, or a node of a
        transform without a contract."""
        return _proof(self)

    def to_substrait(
        self,
        format: Literal["json", "binary"] = "json",
        *,
        shims: Literal["apply", "annotate", "refuse"] = "apply",
    ) -> str | bytes:
        """The node's verified plan for any conforming Substrait consumer,
        with its contract as metadata: `Report.to_substrait` of `report`.

        The plan is the last transform's: it reads a contracted node
        upstream as a table under that transform's name, and the contract's
        `requires` on it are what that node guarantees. Export each node of a
        pipeline for the whole of it. `internal_plan` is the fused stage in
        sverify's internal form.

        Args:
            format: `"json"` (protobuf JSON, a string) or `"binary"` (the
                serialized `substrait.Plan`).
            shims: What to do at a spec gap the proof depends on (see
                `Report.to_substrait`).

        Returns:
            The plan, as protobuf JSON or bytes.

        Raises:
            sverify.errors.ExportError: The node has no contract (a source,
                or a plain function's node), its report is not proved, or
                the plan has no conforming Substrait form that keeps the
                proof.
        """
        from sverify.substrait_export import ExportError

        report = self.report
        if report is None:
            raise ExportError(
                f"node {self.name!r} has no contract to export: it is a source or the "
                "result of a transform without one; wrap the step in sv.transform"
            )
        return report.to_substrait(format, shims=shims)

    def pipe(self, step: Step, /, **inputs: Any) -> Node:
        """Apply `step` to this node, left to right: `orders.pipe(paid)` is
        `paid(orders)`, and a job reads in the order its data flows.

        The chained node fills the step's first table parameter, and the
        step's other inputs come by keyword. The contract is checked as when
        the transform is called: `orders.pipe(paid)` builds the same node,
        and the same plan, as `paid(orders)`.

        Args:
            step: What to apply: a contracted transform (`sverify.transform`);
                a SQL step, `sverify.sql(query)`, whose inputs are the tables
                the query reads; or a plain function from Ibis tables to an
                Ibis table, which is a transform with no contract.
            **inputs: The step's other inputs, by parameter name: sources,
                nodes, or plain values. For a SQL step, the keywords are
                table names in the query, and the chained node is the one
                table left over.

        Returns:
            The node `step` builds.

        Raises:
            TypeError: `step` is not a step, or an input is missing, given
                twice (as the chained node and by keyword) or unknown; the
                message names the step's parameters. For a SQL step, a table
                of the query has no input, the chained node is left unused,
                or `as_` is not the table left over.
            sverify.errors.CompositionError: A precondition on another
                node's result does not follow from what that node guarantees.
            sverify.errors.VerificationError: A postcondition could not be
                proved.

        Examples:
            With `orders`, `paid` and `doubled` from the `Node` example, and
            a lookup table of customers:

            ```python
            customers = StaticSource(
                pa.table({"customer": ["ada", "cy"], "region": ["eu", "us"]}),
                name="customers",
            )

            r = orders.pipe(paid).pipe(doubled)  # the same node as doubled(paid(orders))
            regional = orders.pipe(paid).pipe(  # SQL, with the chained node as orders
                sv.sql(
                    "SELECT o.id, c.region FROM orders o "
                    "JOIN customers c ON o.customer = c.customer"
                ),
                customers=customers,
            )
            big = orders.pipe(lambda t: t.filter(t.amount > 20))  # no contract
            sv.group(r, regional, big).refresh()
            regional.to_arrow().to_pylist()  # [{'id': 3, 'region': 'us'}]
            ```
        """
        transform = as_transform(step)
        args, kwargs = transform._pipe_args(self, inputs)
        return derive(transform, args, kwargs)

    def write(self, sink: Sink) -> Node:
        """Store this node in `sink` (`sverify.io.DeltaSink`, `IcebergSink`),
        as a cache in the middle of a job or as its output. Each refresh
        writes it once, upstream first, exactly once per state. Returns the
        stored node, which transforms read as a versioned source.

        Nothing is written until a refresh. Downstream transforms may assume
        about the stored node what this node's stage proved: the
        preconditions on its sources are checked there, not again by the
        stages that read it. Without a `write`, transforms fuse into one plan
        and the intermediate rows are never stored.

        Args:
            sink: Where to store the node, such as `DeltaSink(uri)` or
                `IcebergSink(catalog, identifier)`. A sink stores one node.

        Returns:
            The stored node, named by the sink's `name`. Refreshing it (or
            any node that reads it) writes the sink.

        Raises:
            ValueError: `sink` already stores a node.

        Examples:
            With `orders`, `paid` and `doubled` from the `Node` example, in
            a new directory:

            ```python
            lake = tempfile.mkdtemp()
            p = orders.pipe(paid).write(DeltaSink(f"{lake}/paid"))
            r = p.pipe(doubled).write(DeltaSink(f"{lake}/doubled"))
            [w.mode for w in r.refresh().writes]  # ['created', 'created']
            ```
        """
        return _Stored(self, sink)

    def refresh(
        self,
        *,
        engine: Any = None,
        audit: bool = False,
        route: RouteKind | Literal["auto"] = "auto",
        unverified: bool = False,
        reproducible: Observation | None = None,
    ) -> Refresh:
        """Bring this node and every node it reads up to date, and write the
        stored ones. `engine` runs the plans: `"duckdb"` (in memory, the
        default), `"polars"`, `"datafusion"`, `"spark"` or a Spark session. With
        `audit`, every batch is compared with recomputation before it is
        applied (`AuditError`).

        A stored node's sink commits each state once, by its epoch, so a
        rerun must reproduce its rows up to the sink's `reproducible` (rows
        as a multiset, doubles within the plan's bound and other values
        exact by default): a node whose result is
        not determined up to row order, or whose engine varies between runs
        more than that, is refused before anything runs (#444, D10, D20).
        Each node with a contract is refused unless its report is proved,
        or `unverified=True` (`Report.run`), or its transform says
        `on_unproved="warn"`; its proof is taken to `engine`
        by a route (`sverify.routes.choose`, D13), or the refresh is
        refused. `StageRefresh.route` records it.

        Each node is refreshed once per call, upstream first, against each
        source's latest version when the call starts, and every stored node
        is written once. The first refresh computes a node in full, or
        resumes a stored node from its table; later ones apply the changes to
        the sources with the delta plans Lean derives, or recompute and diff
        a node that has none (`status` says which).

        Args:
            engine: What runs the plans: `"duckdb"`, `"polars"`,
                `"datafusion"`, `"spark"` or a Spark session. It may differ
                from one refresh to the next. Default None: DuckDB, in
                memory, the engine of the nodes' state (as `Report.run`'s
                None is its connection's).
            audit: Whether to compare every batch with recomputation before
                applying it. Default False.
            route: `"auto"` (the default) chooses a route for each node
                with a contract; `"native"`, `"translated"`, `"transfer"` or
                `"recheck"` takes that one or refuses (`"reference"` is a
                deprecated alias of `"translated"`).
            unverified: Refresh nodes whose contract is not proved anyway;
                their route is `"unverified"`, with what was not proved, and
                an `UnverifiedRunWarning` says so. Default False: such a
                node refuses the refresh, unless its transform says
                `on_unproved="warn"`.
            reproducible: What a rerun must reproduce for every node
                (`sv.equivalent(...)`, D20), over each sink's own. Default
                None: a stored node needs its sink's, another node nothing.

        Returns:
            A `Refresh`: what was done to each node, upstream first.
            `print` it for the full report, or log `summary()` for one line
            per node.

        Raises:
            sverify.errors.PreconditionError: A precondition on a source does
                not hold on its rows (checked in full on the first refresh,
                then on each batch).
            sverify.errors.SchemaError: A source's schema changed in a way the
                contract, proved against the old schema, cannot follow.
            sverify.errors.AuditError: With `audit`, a batch disagrees with
                recomputation; nothing was applied.
            sverify.errors.UnverifiedRunError: A node's contract is not
                proved (a `VerificationError` and a `RouteError`); nothing
                was refreshed.
            sverify.errors.RouteError: A stored node's result is not
                determined up to row order, or no route takes a node's proof
                to `engine`; nothing was refreshed.

        Examples:
            With `r` from the `Node` example:

            ```python
            result = r.refresh(engine="polars")
            print(result)  # one entry per node, upstream first
            r.to_arrow().to_pylist()  # [{'id': 3, 'doubled': 100}]
            ```
        """
        from sverify.routes import checked_route

        return group(self).refresh(
            engine=engine,
            audit=audit,
            route=checked_route(route),
            unverified=unverified,
            reproducible=reproducible,
        )

    def status(self) -> Status:
        """Where the node stands: the source versions of its state, where it
        is stored, and whether it is recomputed rather than maintained.

        Returns:
            A `Status` with one `NodeStatus`, for this node.
        """
        return group(self).status()

    def _view(self) -> IncrementalView:
        if self._stage is None:
            raise RuntimeError(f"{self.name} has no state yet: call refresh() first")
        return self._stage.view

    @property
    def table(self) -> ir.Table:
        """The node's state as an Ibis table, to query further.

        Raises:
            RuntimeError: The node has not been refreshed yet.
        """
        return self._view().table

    @property
    def versions(self) -> dict[str, int]:
        """The version of every source the node's state reflects, by name,
        such as `{"paid": 3}`. A stage reads the sources and stored nodes
        directly upstream, so these are their versions.

        Raises:
            RuntimeError: The node has not been refreshed yet.
        """
        return self._view().versions

    def to_arrow(self) -> pa.Table:
        """The node's state as an Arrow table.

        Returns:
            The node's rows as of the last refresh.

        Raises:
            RuntimeError: The node has not been refreshed yet.
        """
        view = self._view()
        return view.con.arrow[view.name]

    def to_polars(self) -> polars.DataFrame:
        """The node's state as a Polars DataFrame (needs `polars`).

        Returns:
            The node's rows as of the last refresh.

        Raises:
            RuntimeError: The node has not been refreshed yet.
        """
        import polars as pl

        out = pl.from_arrow(self.to_arrow())
        assert isinstance(out, pl.DataFrame)
        return out

    def to_pandas(self) -> pandas.DataFrame:
        """The node's state as a pandas DataFrame (needs `pandas`).

        Returns:
            The node's rows as of the last refresh.

        Raises:
            RuntimeError: The node has not been refreshed yet.
        """
        return self.to_arrow().to_pandas()

    # -- the node's stage ---------------------------------------------------

    def _query(self) -> Node:
        """The node whose expression this node's stage computes."""
        return self

    def _leaves(self) -> list[Node]:
        """The sources and stored nodes this node's stage reads."""
        out: list[Node] = []

        def walk(n: Node) -> None:
            if isinstance(n, _Source | _Stored):
                if not any(n is o for o in out):
                    out.append(n)
                return
            for i in n._inputs:
                walk(i)

        walk(self._query())
        return out

    def _refresh(
        self, pins: dict[int, int], engine: Any, audit: bool, route: Route | None = None
    ) -> StageRefresh:
        leaves = self._leaves()
        for leaf in leaves:
            if isinstance(leaf, _Stored):
                # Its stage was refreshed earlier in this call.
                pins.setdefault(id(leaf), leaf._reader.latest())
        versions = {leaf.name: pins[id(leaf)] for leaf in leaves}
        sink = self.sink if isinstance(self, _Stored) else None
        out = StageRefresh(self.name, None, route=route, transform=_made_by(self))
        if self._stage is None:
            self._stage = _Stage.build(self, leaves, versions, engine, sink)
            out.started = self._stage.view.resumed or "computed"
            out.preconditions = list(self._stage.pipe.preconditions)
            out.postconditions = list(self._stage.view.postconditions)
            if self._stage.view.versions != versions:
                out.report = self._stage.refresh(versions, audit)
        else:
            self._stage.use(engine)
            out.report = self._stage.refresh(versions, audit)
        if sink is not None:
            out.write = sink._commit()
        # After the write: a sink keeps the buckets the state drops.
        out.retention = self._stage.pipe.retire()
        return out


class _Source(Node):
    """A source as a node: the leaf of a stage."""

    def __init__(self, source: Source):
        schema = ibis.Schema.from_pyarrow(plain_schema(source.schema()))
        super().__init__(source.name, ibis.table(schema, name=source.name), [])
        self.source = source


class _Derived(Node):
    """A contracted transform's result."""

    def __init__(self, transform: ContractedTransform, expr: ir.Table, inputs: Sequence[Node]):
        super().__init__(transform.name, expr, inputs)
        self.transform = transform


class _Stored(Node):
    """A node stored in a sink; downstream, a source whose contract is what
    the stored node's stage proved."""

    def __init__(self, upstream: Node, sink: Sink):
        if getattr(sink, "_node", None) is not None:
            raise ValueError(f"sink {sink.name!r} already stores a node")
        expr = ibis.table(upstream.schema, name=sink.name)
        prov = _lookup(upstream._expr.op())
        if prov is not None:
            # Its sources' preconditions, and its runtime-checked
            # postconditions, are checked by its own stage, not by the
            # stages reading it.
            _register(expr.op(), replace(prov, external={}, checked=[]))
        super().__init__(sink.name, expr, [upstream])
        sink._node = self  # type: ignore[attr-defined]
        self.upstream, self.sink = upstream, sink
        self._reader: Source = sink._source()

    def _query(self) -> Node:
        return self.upstream


def _recreated(sink: Sink, leaves: Sequence[Node], stored: Stored) -> bool:
    """Whether a source of the state `sink` stored is another table now: at
    the stored version, its table id is not the one the sink recorded (it
    was dropped and created again, #516). Then the stored state is not a
    state of the sources, and the node is computed again."""
    from sverify.io._common import _TableSource

    committed = sink.committed()
    ids = committed.table_ids if committed is not None else None
    if not ids:
        return False
    for leaf in leaves:
        src = leaf.source if isinstance(leaf, _Source) else leaf._reader  # type: ignore[attr-defined]
        if (
            leaf.name in ids
            and isinstance(src, _TableSource)
            and src._table_id(stored.sources[leaf.name]) != ids[leaf.name]
        ):
            return True
    return False


class _Stage:
    """One incremental view and the pipeline around it: the state of a node."""

    def __init__(self, pipe: Pipeline, view: IncrementalView):
        self.pipe, self.view = pipe, view

    @staticmethod
    def build(
        node: Node,
        leaves: Sequence[Node],
        versions: dict[str, int],
        engine: Any,
        sink: Sink | None,
    ) -> _Stage:
        """The stage at `versions`, or resumed from what `sink` stored (at
        its versions; the caller refreshes it to `versions`)."""
        stored = sink._stored() if sink is not None else None
        if stored is not None and (
            set(stored.sources) != set(versions)
            or any(stored.sources[t] > n for t, n in versions.items())
            or (sink is not None and _recreated(sink, leaves, stored))
        ):
            stored = None
        if stored is not None:
            try:
                stage = _Stage._load(node, leaves, stored.sources, engine, stored)
            except Exception:  # noqa: BLE001 - e.g. the stored versions were vacuumed
                stored = None
            else:
                if sink is not None:
                    sink._attach(stage.view)
                return stage
        stage = _Stage._load(node, leaves, versions, engine, None)
        if sink is not None:
            sink._attach(stage.view)
        return stage

    @staticmethod
    def _load(
        node: Node,
        leaves: Sequence[Node],
        versions: dict[str, int],
        engine: Any,
        resume: Stored | None,
        implied: dict[str, str] | None = None,
    ) -> _Stage:
        """The stage, with each source in `implied` reading only the rows
        that pass its predicate. Without `implied`, the predicates the
        view implies on its sources are found (`_implied`), and the stage
        is built again with them."""
        from sverify.io._common import _TableSource

        con = connect(engine if engine in ENGINES else "duckdb")
        pipe = Pipeline(con)
        mapping = {}
        for leaf in leaves:
            src = leaf.source if isinstance(leaf, _Source) else leaf._reader  # type: ignore[attr-defined]
            if implied and leaf.name in implied and isinstance(src, _TableSource):
                src = src._restricted(implied[leaf.name])
            table = pipe.source(leaf.name, src, version=versions[leaf.name])
            mapping[leaf._expr.op()] = table.op()
        query = node._query()._expr
        root = query.op()
        bound: ir.Table = (mapping[root] if root in mapping else root.replace(mapping)).to_expr()  # type: ignore[attr-defined]
        if (prov := _lookup(root)) is not None:
            _register(bound.op(), prov)
        name = node.name
        taken = set(versions)
        view_name, n = name, 1
        while view_name in taken:
            n += 1
            view_name = f"{name}_{n}"
        view = pipe.view(view_name, bound, resume=resume)
        prunable = {t for t, src in pipe.sources.items() if isinstance(src, _TableSource)}
        if implied is None and prunable:
            found = {t: p for t, p in _implied(pipe, bound).items() if t in prunable}
            if found:
                return _Stage._load(node, leaves, versions, engine, resume, found)
        stage = _Stage(pipe, view)
        stage.use(engine)
        return stage

    def use(self, engine: Any) -> None:
        if engine in ENGINES:
            self.pipe.con.engine = engine
        self.view.engine = engine

    def refresh(self, versions: dict[str, int], audit: bool) -> RefreshReport:
        return self.pipe.refresh(until=versions, audit=audit, retire=False)


# Facts that hold at every version of a source: CHECK constraints, which
# Delta enforces on every write, and a source's own filter. File statistics
# change with each version, so a predicate implied from them could be wrong
# at the next refresh.
_STABLE_FACTS = ("Delta constraint", "source filter")


def _implied(pipe: Pipeline, query: ir.Table) -> dict[str, str]:
    """The predicate `query` implies on each source table (#81, Lean's
    `Rel.need_eval`): the view's result is the same on the rows that pass
    it. Derived from the preconditions, which every refresh establishes,
    and the facts that hold at every version (`_STABLE_FACTS`)."""
    from sverify.contracts import TableCondition, table_facts, verify

    requires: dict[str, list[Any]] = {}
    for t in pipe.sources:
        conds: list[Any] = [
            c for c in pipe.requires.get(t, []) if not isinstance(c, TableCondition)
        ]
        facts = table_facts(pipe.con.table(t)) or []
        conds += [f.condition for f in facts if f.source in _STABLE_FACTS]
        requires[t] = conds
    try:
        report = verify(query, requires=requires, ensures=[], counterexamples=0, on_inferred="off")
    except Exception:  # noqa: BLE001 - a plan the checker cannot read implies nothing
        return {}
    return report.implied


@dataclass
class StageRefresh:
    """What one refresh did to one node: how its state started (on the first
    refresh), what the batch was, and what its sink wrote. `str()` shows
    them in that order; `summary()` gives one line, unless the refresh did
    something `notable`."""

    node: str
    """The node's name."""
    report: RefreshReport | None
    """The batch: the source versions it went from and to, the changes,
    how they were applied and the preconditions checked on them. None on a
    first refresh that computed or resumed the state at the latest
    versions."""
    started: str | None = None
    """"computed", or "resumed from <table>@v<n>", on the first refresh."""
    write: SinkWrite | None = None
    preconditions: list[Discharged] = field(default_factory=list)
    """On the first refresh: how each precondition on the sources was
    established on the full tables (later batches: `report.preconditions`)."""
    retention: list[RetentionReport] = field(default_factory=list)
    """For a node over a source with `arrives_within`: its open time
    buckets, those dropped from its state after the write, and the bound."""
    postconditions: list[Discharged] = field(default_factory=list)
    """On the first refresh: the postconditions the node's transform did not
    prove and checks on its output (`on_unproved="runtime"`), checked on the
    full result (later batches: `report.postconditions`)."""
    route: Route | None = None
    """With `refresh(route=...)`: how the node's proof reached the engine
    (D13), with its class; None without a route or a contract."""
    transform: str | None = None
    """For a stored node, the transform that made it, where its name differs
    from the node's (the sink's): the entry is headed `daily_revenue →
    daily:` (#695)."""

    @property
    def heading(self) -> str:
        """How the entry is headed: the node, after the transform that made
        it where the names differ."""
        return self.node if self.transform is None else f"{self.transform} → {self.node}"

    @property
    def notable(self) -> list[str]:
        """Why this entry deserves more than one line, or []: the first
        refresh (how the state started and how the preconditions were
        established on the full tables), a source whose change could not be
        applied incrementally, a schema change, or a sink that replaced its
        table's rows."""
        out = [self.started] if self.started else []
        if self.report is not None:
            out += self.report.notable
        if self.write is not None and self.write.mode == "overwrite":
            out.append("the sink overwrote its table")
        out += [f"retention off: {r.off}" for r in self.retention if r.off is not None]
        return out

    def summary(self) -> str:
        """One line, for the log of a job that refreshes often:
        "paid: changes from orders v3→v4 (change feed), requires checked on
        2 row(s), merge v5: +2 −0". With something `notable`, the full entry
        (`str()`) instead."""
        if self.notable or self.report is None:
            return str(self)
        sources = self.report.sources
        spans = ", ".join(s.span().replace("@", " ") for s in sources)
        if all(s.mode == "unchanged" for s in sources):
            parts = [f"{spans} unchanged"]
        else:
            modes = {s.mode for s in sources}
            how = [m for m in ("change feed", "snapshot diff") if m in modes]
            parts = [f"changes from {spans}" + (f" ({', '.join(how)})" if how else "")]
        pre = self.report.preconditions
        # "checked on data, watermark …" (#294) is checked on data too.
        meta = sum(not p.source.startswith(ON_DATA) for p in pre)
        if meta < len(pre):
            text = f"requires checked on {sum(s.inserts for s in sources)} row(s)"
            parts.append(text + (f" ({meta} proved from metadata)" if meta else ""))
        elif pre:
            parts.append("requires proved from metadata")
        parts += [f"{n} touched group(s) recomputed" for n in self.report.touched.values()]
        parts += [f"{n} row(s) in touched frames recomputed" for n in self.report.framed.values()]
        parts += ["recomputed and diffed" for _ in self.report.diffed]
        if self.report.postconditions:
            # On the rows the batch inserts into the node (keys on its state).
            parts.append(f"{len(self.report.postconditions)} ensures checked on data")
        parts += [
            f"{r.column}: {r.open}/{r.bound} bucket(s) open, {r.retired} retired"
            for r in self.retention
            if r.off is None
        ]
        if (w := self.write) is not None:
            if w.mode == "skipped":
                parts.append("already committed")
            else:
                at = "" if w.version is None else f" v{w.version}"
                parts.append(f"{w.mode}{at}: +{w.inserted} −{w.deleted}")
        return f"{self.heading}: " + ", ".join(parts)

    def __str__(self) -> str:
        lines = [f"{self.heading}:"]
        if self.started:
            lines.append(f"  {self.started}")
        lines += [f"  requires {p}" for p in self.preconditions]
        lines += [f"  ensures {p}" for p in self.postconditions]
        if self.route is not None:
            lines.append(f"  route on {self.route.engine}: {self.route}")
        if self.report is not None:
            lines += [f"  {line}" for line in str(self.report).splitlines()]
        if self.write is not None:
            lines.append(f"  wrote {self.write}")
        lines += [f"  {r}" for r in self.retention]
        return "\n".join(lines)


@dataclass
class Refresh:
    """What a refresh did, node by node, upstream first: returned by
    `Node.refresh` and `Group.refresh`. `str()` shows each node's entry;
    `summary()` one line per node, for a job that refreshes often;
    `refresh["paid"]` is the entry of the node named "paid".

    Attributes:
        nodes: One `StageRefresh` per node refreshed: the nodes asked for and
            the stored nodes they read, each once, upstream first.
    """

    nodes: list[StageRefresh]

    def __getitem__(self, name: str) -> StageRefresh:
        for s in self.nodes:
            if s.node == name:
                return s
        raise KeyError(name)

    @property
    def writes(self) -> list[SinkWrite]:
        """What each stored node's sink wrote (`sverify.io.SinkWrite`),
        upstream first."""
        return [s.write for s in self.nodes if s.write is not None]

    @property
    def notable(self) -> bool:
        """Whether any node's entry has something `StageRefresh.notable`."""
        return any(s.notable for s in self.nodes)

    def summary(self) -> str:
        """One line per node (`StageRefresh.summary`), upstream first; a node
        whose refresh did something notable (its first refresh, a recompute,
        a schema change, an overwrite) gets its full entry.

        Returns:
            The summary, such as "paid: changes from orders v3→v4 (change
            feed), requires checked on 2 row(s), merge v5: +2 −0".
        """
        return "\n".join(s.summary() for s in self.nodes)

    def __str__(self) -> str:
        return "\n".join(str(s) for s in self.nodes)


@dataclass
class NodeStatus:
    """Where one node stands; see `Node.status`. `str()` gives one line,
    such as "doubled: paid@v3; stored in lake/doubled"."""

    node: str
    """The node's name."""
    versions: dict[str, int] | None
    """The version of every source the node's state reflects (as
    `Node.versions`), or None if it has not been refreshed in this process."""
    stored: str | None = None
    """The table the node is stored in (a Delta URI or an Iceberg
    identifier), or None if it is not stored."""
    recomputed: str | None = None
    """Why the node is recomputed on every refresh instead of maintained,
    or None if it is maintained from changes (or not refreshed yet)."""
    touched: str | None = None
    """Why the node has no delta rules, when it is maintained by
    recomputing only the groups each batch touches (an aggregate, or a
    window's partitions or frames)."""
    framed: bool = False
    """The node recomputes window rows near the change, by their frames
    (touched frames)."""

    def __str__(self) -> str:
        if self.versions is None:
            text = f"{self.node}: not refreshed yet"
        else:
            text = f"{self.node}: " + ", ".join(f"{t}@v{n}" for t, n in self.versions.items())
        if self.stored:
            text += f"; stored in {self.stored}"
        if self.recomputed:
            text += f"; recomputed ({self.recomputed})"
        if self.touched and self.framed:
            text += f"; touched frames recomputed (no delta rules: {self.touched})"
        elif self.touched:
            text += f"; touched groups recomputed (no delta rules: {self.touched})"
        return text


@dataclass
class Status:
    """Where each node of a group stands: returned by `Node.status` and
    `Group.status`. `str()` gives one line per node.

    Attributes:
        nodes: One `NodeStatus` per node, in the order they were given.
    """

    nodes: list[NodeStatus] = field(default_factory=list)

    def __str__(self) -> str:
        return "\n".join(str(s) for s in self.nodes)


class Group:
    """Nodes refreshed together; see `group`.

    Attributes:
        nodes: The nodes, in the order given.
    """

    def __init__(self, nodes: Sequence[Node]):
        bad = [n for n in nodes if not isinstance(n, Node) or isinstance(n, _Source)]
        if bad or not nodes:
            raise TypeError(f"group takes nodes (results of transforms), got {bad or 'none'}")
        self.nodes = list(nodes)

    def _order(self) -> list[Node]:
        """Every node to refresh: the members and the stored nodes they read,
        each once, upstream first."""
        order: list[Node] = []

        def visit(n: Node) -> None:
            if any(n is o for o in order):
                return
            for leaf in n._leaves():
                if isinstance(leaf, _Stored):
                    visit(leaf)
            order.append(n)

        for n in self.nodes:
            visit(n)
        return order

    def refresh(
        self,
        *,
        engine: Any = None,
        audit: bool = False,
        route: RouteKind | Literal["auto"] = "auto",
        unverified: bool = False,
        reproducible: Observation | None = None,
    ) -> Refresh:
        """Refresh every node against the same source versions (each
        source's latest when the refresh starts), sharing the stored nodes
        they read: each is refreshed and written once. See `Node.refresh`.

        Args:
            engine: What runs the plans: `"duckdb"`, `"polars"`,
                `"datafusion"`, `"spark"` or a Spark session. Default None:
                DuckDB, in memory.
            audit: Whether to compare every batch with recomputation before
                applying it. Default False.
            route: How each node's proof reaches `engine`; see
                `Node.refresh`.
            unverified: Refresh nodes whose contract is not proved anyway;
                see `Node.refresh`.
            reproducible: What a rerun must reproduce; see `Node.refresh`.

        Returns:
            A `Refresh` with an entry for every node refreshed: the nodes and
            the stored nodes they read, each once, upstream first.

        Raises:
            sverify.errors.PreconditionError: A precondition on a source does
                not hold on its rows.
            sverify.errors.SchemaError: A source's schema changed in a way a
                contract cannot follow.
            sverify.errors.AuditError: With `audit`, a batch disagrees with
                recomputation; nothing was applied.
            sverify.errors.UnverifiedRunError: A node's contract is not
                proved; nothing was refreshed.
            sverify.errors.RouteError: A stored node is not determined up to
                row order, or no route takes a node's proof to `engine`;
                nothing was refreshed.
        """
        from sverify._hooks import PLANNED, is_collecting
        from sverify.routes import checked_route

        if is_collecting():
            raise RuntimeError(
                "refresh() ran while sverify checked this file without running it "
                "(sverify check, sverify.cli.discover): run it under "
                '`if __name__ == "__main__":`, or with `sverify refresh <file>:<node>`'
            )
        if engine is None:
            engine = "duckdb"
        route = checked_route(route)
        order = self._order()
        chosen = _routes(order, engine, route, reproducible, unverified)
        if (planned := PLANNED.get()) is not None:
            planned()
        for n in order:
            if isinstance(n, _Stored) and n._stage is None:
                _continue_versions(n)
        pins: dict[int, int] = {}
        for n in order:
            for leaf in n._leaves():
                if isinstance(leaf, _Source) and id(leaf) not in pins:
                    pins[id(leaf)] = leaf.source.latest()
        return Refresh([n._refresh(pins, engine, audit, chosen.get(id(n))) for n in order])

    def status(self) -> Status:
        """Where each node stands (`Node.status`).

        Returns:
            A `Status` with one `NodeStatus` per node of the group (not the
            stored nodes they read, unless they are in the group).
        """
        out = Status()
        for n in self.nodes:
            stage = n._stage
            stored = None
            if isinstance(n, _Stored):
                stored = getattr(n.sink, "location", n.name)
            out.nodes.append(
                NodeStatus(
                    n.name,
                    None if stage is None else stage.view.versions,
                    stored,
                    None if stage is None else _recomputed(stage.view),
                    None if stage is None or stage.view.touched is None else stage.view.fallback,
                    stage is not None and stage.view.strategy == "touched frames",
                )
            )
        return out


def _recomputed(view: IncrementalView) -> str | None:
    """Why a view is recomputed and diffed on every batch, or None."""
    if not view.recomputed:
        return None
    off = f"; no touched groups: {view.touched_off}" if view.touched_off else ""
    return f"{view.fallback}{off}"


def _continue_versions(node: _Stored) -> None:
    """The sources of a stored node's stage whose versions restart with the
    process (`sverify.io.Source`) start at the versions and cursors its
    sink recorded, if they can restore their table there; else they number
    their versions above, so that its epochs keep growing and it writes
    exactly once."""
    resumes = {}
    for leaf in node._leaves():
        src = leaf.source if isinstance(leaf, _Source) else leaf._reader  # type: ignore[attr-defined]
        if (resume := getattr(src, "_resume_after", None)) is not None:
            resumes[leaf.name] = resume
    committed = getattr(node.sink, "committed", None)
    contract = committed() if resumes and committed is not None else None
    if contract is None:
        return
    cursors = getattr(contract, "cursors", {})
    for name, resume in resumes.items():
        if name in cursors:
            resume(contract.sources[name], cursors[name])
        elif name in contract.sources:
            resume(contract.sources[name])


def _proof(node: Node) -> Report | None:
    """The report of the contract that made the node's result, if any."""
    prov = _lookup(node._query()._expr.op())
    return None if prov is None else prov.report


def _warns(node: Node) -> bool:
    """Whether the transform that made the node's result says
    `on_unproved="warn"`: its refreshes run it unverified (#690)."""
    prov = _lookup(node._query()._expr.op())
    return prov is not None and getattr(prov.transform, "on_unproved", None) == "warn"


def _routes(
    order: Sequence[Node],
    engine: Any,
    route: RouteKind | Literal["auto"],
    reproducible: Observation | None = None,
    unverified: bool = False,
) -> dict[int, Route]:
    """Each node's route to `engine` (by `id`), checked before anything runs.

    A node whose contract is not proved is refused, or, with `unverified`,
    runs by the route `"unverified"` with a warning. What a rerun must
    reproduce (D20): a stored node's sink commits each epoch once,
    so it needs the sink's `reproducible` (rows as a multiset, doubles
    within the plan's bound, by default), or `reproducible` where the
    refresh states one; another node needs `reproducible`, or nothing. The
    engine's run-to-run variation must refine it, on every route."""
    from sverify import routes
    from sverify.contracts import UnverifiedRunError

    out: dict[int, Route] = {}
    e = routes.engine_name(engine)
    for n in order:
        report = _proof(n)
        if report is None:
            continue
        name = _display(n)
        needed = reproducible
        if needed is None and isinstance(n, _Stored):
            needed = getattr(n.sink, "reproducible", PLAN_BOUND)
        warns = not unverified and _warns(n)
        if (unverified or warns) and not routes.verified(report):
            if needed is not None:
                problems, _ = routes.reproducibility(report, e, needed)
                if problems:
                    hint = "" if report.deterministic else f"; {routes.ties_fix(report)}"
                    raise routes.RouteError(
                        routes.Route(
                            e,
                            None,
                            report.semantics,
                            f"{name}: a rerun must give the same result: "
                            + "; ".join(problems)
                            + hint,
                            report.deterministic,
                            cls="refused",
                            reproducible=needed,
                        )
                    )
            chosen = routes.unverified(report, engine)
            why = " (on_unproved='warn')" if warns else ""
            warnings.warn(
                f"refreshing {name} on {e} unverified{why}: {chosen.reason}",
                routes.UnverifiedRunWarning,
                stacklevel=4,
            )
            out[id(n)] = chosen
            continue
        chosen = routes.choose(report, engine, route, reproducible=needed)
        if chosen.refused:
            refused = replace(chosen, reason=f"{name}: {chosen.reason}")
            if not routes.verified(report):
                reason = refused.reason.replace(
                    "run(..., unverified=True) runs it anyway",
                    "refresh(unverified=True), or on_unproved='warn' on the transform, "
                    "runs it anyway",
                )
                raise UnverifiedRunError(report, replace(refused, reason=reason))
            raise routes.RouteError(refused)
        out[id(n)] = chosen
    return out


def _made_by(n: Node) -> str | None:
    """The transform that made a stored node, where its name differs from
    the node's."""
    if isinstance(n, _Stored):
        made_by = getattr(n._query(), "name", None)
        if made_by and made_by != n.name:
            return made_by
    return None


def _display(n: Node) -> str:
    """How a refusal names a node: by the transform that made it, and, for
    a stored node, where it is stored."""
    if isinstance(n, _Stored):
        made = n._query()
        made_by = getattr(made, "name", None)
        if made_by and made_by != n.name:
            return f"{made_by} (stored as {n.name})"
    return n.name


def group(*nodes: Node) -> Group:
    """Several nodes to refresh together, against the same source versions:
    `sv.group(a, b).refresh()`. A stored node they share is refreshed and
    written once; `.status()` reports on each.

    Args:
        *nodes: The nodes to refresh together: results of transforms, stored
            or not (not sources).

    Returns:
        A `Group`, with `refresh` and `status`.

    Raises:
        TypeError: No nodes are given, or one is not a node (a source, or an
            Ibis table).

    Examples:
        Two outputs that read the same stored node, with `p` and `r` from
        the `Node` example:

        ```python
        @sv.transform()
        def customers(t):
            return t.select(t.customer)

        g = sv.group(r, p.pipe(customers))  # fan-out: p is piped twice
        result = g.refresh()  # paid is refreshed and written once
        [s.node for s in result.nodes]  # ['paid', 'doubled', 'customers']
        print(g.status())  # one line per node
        ```
    """
    return Group(nodes)


# -- building nodes ------------------------------------------------------------


def is_source(value: Any) -> bool:
    """A versioned table (`sverify.io`) rather than an Ibis table or a node."""
    return not isinstance(value, ir.Table | Node) and all(
        callable(getattr(value, m, None)) for m in ("snapshot", "changes", "latest", "schema")
    )


def wants_node(args: Sequence[Any], kwargs: dict[str, Any]) -> bool:
    """A transform called on these arguments builds a node."""
    return any(isinstance(v, Node) or is_source(v) for v in [*args, *kwargs.values()])


def _source_node(source: Source) -> _Source:
    """The node of a source: one per source, so that every transform reading
    it reads the same table."""
    node = getattr(source, "_sverify_node", None)
    if node is None:
        node = _Source(source)
        source._sverify_node = node  # type: ignore[attr-defined]
    return node


def derive(transform: ContractedTransform, args: Sequence[Any], kwargs: dict[str, Any]) -> Node:
    """`transform` applied to sources and nodes: the contract is checked on
    their placeholder tables, and the result is a node."""
    inputs: list[Node] = []

    def lift(v: Any) -> Any:
        if isinstance(v, ir.Table):
            raise TypeError(
                f"{transform.name} mixes a node or source with an Ibis table: "
                "read the table through a source, e.g. sverify.io.StaticSource(table)"
            )
        if not isinstance(v, Node) and not is_source(v):
            return v
        node = v if isinstance(v, Node) else _source_node(v)
        if isinstance(node, _Derived) and (prov := _lookup(node._expr.op())) and prov.checked:
            raise ValueError(
                f"{node.name} checks {', '.join(label(c) for c in prov.checked)} on its "
                f"output at refresh (on_unproved='runtime'), which {transform.name} would "
                "fuse away: store it first, with .write(sink)"
            )
        inputs.append(node)
        return node._expr

    lifted_args = [lift(a) for a in args]
    lifted_kwargs = {k: lift(v) for k, v in kwargs.items()}
    tables: dict[str, Node] = {}
    for node in inputs:
        for leaf in [node] if isinstance(node, _Source | _Stored) else node._leaves():
            other = tables.setdefault(leaf.name, leaf)
            if other is not leaf:
                raise ValueError(
                    f"{transform.name} reads two tables named {leaf.name!r}: "
                    "give one of the sources or sinks another name (name=...)"
                )
    expr = transform._build(lifted_args, lifted_kwargs, node=True)
    return _Derived(transform, expr, inputs)
