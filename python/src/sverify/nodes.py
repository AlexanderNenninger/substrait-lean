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

from collections.abc import Sequence
from dataclasses import dataclass, field, replace
from typing import TYPE_CHECKING, Any, Protocol

import ibis
import ibis.expr.types as ir
import pyarrow as pa

from sverify.contracts import Discharged, _lookup, _register
from sverify.engine import ENGINES, connect, plain_schema, written_plan
from sverify.ibis_substrait import to_substrait_json
from sverify.incremental import IncrementalView, Pipeline, RefreshReport, Source, Stored
from sverify.steps import Step, as_transform

if TYPE_CHECKING:
    import pandas
    import polars

    from sverify.contracts import ContractedTransform
    from sverify.io._common import SinkWrite


class Sink(Protocol):
    """What `Node.write` needs of a sink (`sverify.io.DeltaSink`, `IcebergSink`).

    The sinks in `sverify.io` implement it; the methods it asks for are
    private, called by `refresh`, so a sink has no public `write` of its own.

    Attributes:
        name: The stored table's name in the plans that read it (the sink's
            `name=`, by default the last part of its URI or identifier).
    """

    name: str

    def _attach(self, view: IncrementalView) -> None: ...

    def _commit(self) -> SinkWrite: ...

    def _stored(self) -> Stored | None: ...

    def _source(self) -> Source: ...


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
            requires={"orders": [_.amount >= 0, sv.unique("id")]},
            ensures=[_.amount > 10, sv.unique("id")],
        )
        def paid(orders):
            return orders.filter(orders.amount > 10)

        @sv.transform(requires={"t": [_.amount > 10]}, ensures=[_.doubled > 20])
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
    def plan(self) -> str:
        """The Substrait plan (JSON) of the node's stage, as Lean checked and
        wrote it: what every engine runs. `sverify.engines.delta_plans(plan)`
        are the plans that maintain it from changes.

        The stage reads the sources and stored nodes upstream under their
        names, so a stored node's plan is that of the node it stores."""
        if self._plan is None:
            self._plan = written_plan(to_substrait_json(self._query()._expr))
        return self._plan

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

    def refresh(self, *, engine: Any = "duckdb", audit: bool = False) -> Refresh:
        """Bring this node and every node it reads up to date, and write the
        stored ones. `engine` runs the plans: `"duckdb"` (in memory),
        `"polars"`, `"datafusion"`, `"spark"` or a Spark session. With
        `audit`, every batch is compared with recomputation before it is
        applied (`AuditError`).

        Each node is refreshed once per call, upstream first, against each
        source's latest version when the call starts, and every stored node
        is written once. The first refresh computes a node in full, or
        resumes a stored node from its table; later ones apply the changes to
        the sources with the delta plans Lean derives, or recompute and diff
        a node that has none (`status` says which).

        Args:
            engine: What runs the plans: `"duckdb"` (the default, in memory),
                `"polars"`, `"datafusion"`, `"spark"` or a Spark session. It
                may differ from one refresh to the next.
            audit: Whether to compare every batch with recomputation before
                applying it. Default False.

        Returns:
            A `Refresh`: what was done to each node, upstream first.

        Raises:
            sverify.errors.PreconditionError: A precondition on a source does
                not hold on its rows (checked in full on the first refresh,
                then on each batch).
            sverify.errors.SchemaError: A source's schema changed in a way the
                contract, proved against the old schema, cannot follow.
            sverify.errors.AuditError: With `audit`, a batch disagrees with
                recomputation; nothing was applied.

        Examples:
            With `r` from the `Node` example:

            ```python
            result = r.refresh(engine="polars")
            print(result)  # one entry per node, upstream first
            r.to_arrow().to_pylist()  # [{'id': 3, 'doubled': 100}]
            ```
        """
        return group(self).refresh(engine=engine, audit=audit)

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

    def _refresh(self, pins: dict[int, int], engine: Any, audit: bool) -> StageRefresh:
        leaves = self._leaves()
        for leaf in leaves:
            if isinstance(leaf, _Stored):
                # Its stage was refreshed earlier in this call.
                pins.setdefault(id(leaf), leaf._reader.latest())
        versions = {leaf.name: pins[id(leaf)] for leaf in leaves}
        sink = self.sink if isinstance(self, _Stored) else None
        out = StageRefresh(self.name, None)
        if self._stage is None:
            self._stage = _Stage.build(self, leaves, versions, engine, sink)
            out.started = self._stage.view.resumed or "computed"
            out.preconditions = list(self._stage.pipe.preconditions)
            if self._stage.view.versions != versions:
                out.report = self._stage.refresh(versions, audit)
        else:
            self._stage.use(engine)
            out.report = self._stage.refresh(versions, audit)
        if sink is not None:
            out.write = sink._commit()
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
            # Its sources' preconditions are checked by its own stage, not
            # by the stages reading it.
            _register(expr.op(), replace(prov, external={}))
        super().__init__(sink.name, expr, [upstream])
        sink._node = self  # type: ignore[attr-defined]
        self.upstream, self.sink = upstream, sink
        self._reader: Source = sink._source()

    def _query(self) -> Node:
        return self.upstream


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
    ) -> _Stage:
        con = connect(engine if engine in ENGINES else "duckdb")
        pipe = Pipeline(con)
        mapping = {}
        for leaf in leaves:
            src = leaf.source if isinstance(leaf, _Source) else leaf._reader  # type: ignore[attr-defined]
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
        stage = _Stage(pipe, view)
        stage.use(engine)
        return stage

    def use(self, engine: Any) -> None:
        if engine in ENGINES:
            self.pipe.con.engine = engine
        self.view.engine = engine

    def refresh(self, versions: dict[str, int], audit: bool) -> RefreshReport:
        return self.pipe.refresh(until=versions, audit=audit)


@dataclass
class StageRefresh:
    """What one refresh did to one node: how its state started (on the first
    refresh), what the batch was, and what its sink wrote. `str()` shows
    them in that order."""

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

    def __str__(self) -> str:
        lines = [f"{self.node}:"]
        if self.started:
            lines.append(f"  {self.started}")
        lines += [f"  requires {p}" for p in self.preconditions]
        if self.report is not None:
            lines += [f"  {line}" for line in str(self.report).splitlines()]
        if self.write is not None:
            lines.append(f"  wrote {self.write}")
        return "\n".join(lines)


@dataclass
class Refresh:
    """What a refresh did, node by node, upstream first: returned by
    `Node.refresh` and `Group.refresh`. `str()` shows each node's entry;
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

    def __str__(self) -> str:
        if self.versions is None:
            text = f"{self.node}: not refreshed yet"
        else:
            text = f"{self.node}: " + ", ".join(f"{t}@v{n}" for t, n in self.versions.items())
        if self.stored:
            text += f"; stored in {self.stored}"
        if self.recomputed:
            text += f"; recomputed ({self.recomputed})"
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

    def refresh(self, *, engine: Any = "duckdb", audit: bool = False) -> Refresh:
        """Refresh every node against the same source versions (each
        source's latest when the refresh starts), sharing the stored nodes
        they read: each is refreshed and written once. See `Node.refresh`.

        Args:
            engine: What runs the plans: `"duckdb"` (the default, in memory),
                `"polars"`, `"datafusion"`, `"spark"` or a Spark session.
            audit: Whether to compare every batch with recomputation before
                applying it. Default False.

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
        """
        order = self._order()
        pins: dict[int, int] = {}
        for n in order:
            for leaf in n._leaves():
                if isinstance(leaf, _Source) and id(leaf) not in pins:
                    pins[id(leaf)] = leaf.source.latest()
        return Refresh([n._refresh(pins, engine, audit) for n in order])

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
                stored = getattr(n.sink, "uri", None) or getattr(n.sink, "identifier", n.name)
            out.nodes.append(
                NodeStatus(
                    n.name,
                    None if stage is None else stage.view.versions,
                    stored,
                    None if stage is None else stage.view.fallback,
                )
            )
        return out


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
    expr = transform(*lifted_args, **lifted_kwargs)
    return _Derived(transform, expr, inputs)
