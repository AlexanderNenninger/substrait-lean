"""Lineage and run events in OpenLineage (#792), emitted and read.

OpenLineage is the standard for lineage events: Airflow, Spark and dbt emit
it, and Marquez, DataHub, OpenMetadata and the cloud catalogs read it.
Sverify emits a run per refreshed node and reads what upstream jobs emitted.

    from sverify import openlineage

    node.refresh(lineage=openlineage.Lineage("http://localhost:5000"))  # Marquez
    node.refresh(lineage=openlineage.Lineage("events.jsonl"))           # a file
    node.refresh(lineage=openlineage.Lineage())   # openlineage.yml, OPENLINEAGE_*

    upstream = openlineage.read("events.jsonl").dataset(orders)
    upstream.schema, upstream.version, upstream.producer
    @sv.transform(requires={"orders": upstream.requires})

Emitting is off unless a refresh gets `lineage=` (or the command line
`--lineage`): without it sverify sends nothing and opens no connection.

* Each refreshed node is a job (`namespace`, the node's name) and each
  refresh of it a run: START, then COMPLETE, or FAIL with the error (a node
  held by a failed precondition, or an exception), or ABORT for the nodes an
  earlier failure kept from running.
* Inputs are the node's sources and the stored nodes it reads, at their
  versions, with `schema`, `dataSource`, `version` and, for the
  preconditions checked on their rows, `dataQualityAssertions`. The output
  is the node's sink, with `schema`, `dataSource`, `version`,
  `columnLineage` from the plan, `outputStatistics` and the custom facet
  `sverify_contract` (`FACET_SCHEMA_URL`, format `FACET_FORMAT`): the contract, each
  postcondition's status, the route and class, quarantined rows, and the
  verified plan exported to Substrait, from which a downstream job proves
  the contract again.
* `read` reads events from a JSON lines file (the file transport's), a
  list of events, or a Marquez server (`marquez`). An upstream dataset's
  `requires` holds the postconditions of its `sverify_contract` facet that
  sverify proves again from the exported plan (`sv.from_substrait`); every
  other claim, and every other tool's `dataQualityAssertions`, is checked
  evidence (`evidence`), never proof.

`SPEC_VERSION` is the OpenLineage spec the events follow (the spec of the
pinned `openlineage-python`, `CLIENT_VERSION`), which the tests validate
them against. `Lineage()` without a target needs that client:
`pip install 'sverify[openlineage]'`; the file, console and HTTP targets
need nothing.
"""

from __future__ import annotations

import json
import os
import sys
import urllib.parse
import urllib.request
import uuid
import warnings
from collections.abc import Iterable, Mapping, Sequence
from dataclasses import dataclass, field
from datetime import UTC, datetime
from pathlib import Path
from typing import TYPE_CHECKING, Any

if TYPE_CHECKING:
    import ibis

    from sverify.contracts import Condition, Report
    from sverify.nodes import Node, StageRefresh

__all__ = [
    "CLIENT_VERSION",
    "FACET_FORMAT",
    "FACET_SCHEMA_URL",
    "SPEC_VERSION",
    "Assertion",
    "Events",
    "Lineage",
    "LineageWarning",
    "Upstream",
    "marquez",
    "read",
]

#: The OpenLineage spec the events follow, as its `$id` names it.
SPEC_VERSION = "2-0-2"
#: The `openlineage-python` release `sverify[openlineage]` installs and the
#: tests run against.
CLIENT_VERSION = "1.55.0"
#: The version of the `sverify_contract` facet's format.
FACET_FORMAT = 1
#: The `_schemaURL` of the `sverify_contract` facet: its JSON schema's `$id`
#: (`sverify/schemas/openlineage-contract-facet.schema.json`).
FACET_SCHEMA_URL = (
    "https://alexandernenninger.github.io/substrait-lean/schemas/"
    f"openlineage-contract-facet/{FACET_FORMAT}.json"
)
_SPEC = f"https://openlineage.io/spec/{SPEC_VERSION}/OpenLineage.json"
_FACETS = "https://openlineage.io/spec/facets"
_FACET_URLS = {
    "schema": f"{_FACETS}/1-2-0/SchemaDatasetFacet.json#/$defs/SchemaDatasetFacet",
    "dataSource": f"{_FACETS}/1-0-1/DatasourceDatasetFacet.json#/$defs/DatasourceDatasetFacet",
    "version": f"{_FACETS}/1-0-1/DatasetVersionDatasetFacet.json#/$defs/DatasetVersionDatasetFacet",
    "columnLineage": f"{_FACETS}/1-2-0/ColumnLineageDatasetFacet.json"
    "#/$defs/ColumnLineageDatasetFacet",
    "dataQualityAssertions": f"{_FACETS}/1-1-0/DataQualityAssertionsDatasetFacet.json"
    "#/$defs/DataQualityAssertionsDatasetFacet",
    "outputStatistics": f"{_FACETS}/1-0-2/OutputStatisticsOutputDatasetFacet.json"
    "#/$defs/OutputStatisticsOutputDatasetFacet",
    "errorMessage": f"{_FACETS}/1-0-1/ErrorMessageRunFacet.json#/$defs/ErrorMessageRunFacet",
    "jobType": f"{_FACETS}/2-0-4/JobTypeJobFacet.json#/$defs/JobTypeJobFacet",
    "processing_engine": f"{_FACETS}/1-1-1/ProcessingEngineRunFacet.json"
    "#/$defs/ProcessingEngineRunFacet",
}
_FACET = "sverify_contract"


class LineageWarning(UserWarning):
    """An event could not be sent (the server is down, the file is not
    writable): the refresh goes on, and the warning says why."""


def _version() -> str:
    from sverify.report_json import _sverify_version

    return _sverify_version()


def _producer() -> str:
    return f"https://github.com/AlexanderNenninger/substrait-lean/tree/v{_version()}/python"


def _facet(kind: str, **fields: Any) -> dict[str, Any]:
    return {"_producer": _producer(), "_schemaURL": _FACET_URLS[kind], **fields}


# -- datasets -------------------------------------------------------------------


def dataset_id(obj: Any) -> tuple[str, str]:
    """The OpenLineage namespace and name of a source or sink, by the
    naming conventions: a table in object storage is
    `("s3://bucket", "path")`, a local one `("file", "/abs/path")`, an
    Iceberg table `("iceberg://<catalog>", "<identifier>")`, and anything
    else `("sverify", <name>)`."""
    identifier = getattr(obj, "identifier", None)
    catalog = getattr(obj, "catalog", None)
    if identifier is not None and catalog is not None:
        ident = identifier if isinstance(identifier, str) else ".".join(identifier)
        return f"iceberg://{getattr(catalog, 'name', 'catalog')}", ident
    uri = getattr(obj, "uri", None) or getattr(obj, "location", None)
    name = str(getattr(obj, "name", "unknown"))
    if not uri or uri == name:
        return "sverify", name
    uri = str(uri)
    parsed = urllib.parse.urlparse(uri)
    if parsed.scheme in ("", "file") or len(parsed.scheme) == 1:  # a path, or C:\
        path = parsed.path if parsed.scheme == "file" else uri
        return "file", str(Path(path).expanduser().resolve())
    return f"{parsed.scheme}://{parsed.netloc}", parsed.path.lstrip("/")


def _leaf_object(leaf: Node) -> Any:
    from sverify.nodes import _Source, _Stored

    if isinstance(leaf, _Source):
        return leaf.source
    if isinstance(leaf, _Stored):
        return leaf.sink
    return leaf


def _schema_facet(schema: Any) -> dict[str, Any]:
    from ibis.backends.sql.datatypes import DuckDBType

    fields = [
        {"name": n, "type": DuckDBType.to_string(t), "ordinal_position": i}
        for i, (n, t) in enumerate(schema.items(), start=1)
    ]
    return _facet("schema", fields=fields)


def _source_facet(ns: str, name: str) -> dict[str, Any]:
    uri = name if ns == "file" else f"{ns}/{name}" if "://" in ns else f"{ns}:{name}"
    return _facet("dataSource", name=ns, uri=uri)


# -- column lineage from the plan -------------------------------------------------

_RANK = {"IDENTITY": 0, "TRANSFORMATION": 1, "AGGREGATION": 2}


def _fields(value: Any, reductions: list[Any] | None = None) -> list[Any]:
    """The `Field`s a value reads, without descending into relations, nor
    into a window's partition and order (which pick the rows, `INDIRECT`).
    The reductions it meets go to `reductions`."""
    import ibis.expr.operations as ops

    out: list[Any] = []
    seen: set[int] = set()
    stack = [value]
    while stack:
        v = stack.pop()
        if id(v) in seen:
            continue
        seen.add(id(v))
        if isinstance(v, ops.Field):
            out.append(v)
            continue
        if isinstance(v, ops.Relation):
            continue
        if isinstance(v, ops.Reduction) and reductions is not None:
            reductions.append(v)
        if isinstance(v, ops.WindowFunction):
            stack.append(v.func)
            continue
        for a in getattr(v, "__args__", ()):
            if isinstance(a, ops.Node):
                stack.append(a)
            elif isinstance(a, tuple | list):
                stack += [x for x in a if isinstance(x, ops.Node)]
            elif isinstance(a, Mapping):
                stack += [x for x in a.values() if isinstance(x, ops.Node)]
    return out


class _Tracer:
    """Which base table columns each column of a relation is computed
    from, and how: `IDENTITY` (copied), `TRANSFORMATION` or `AGGREGATION`."""

    def __init__(self) -> None:
        self.memo: dict[tuple[int, str], dict[tuple[str, str], str]] = {}

    def value(self, v: Any, how: str) -> dict[tuple[str, str], str]:
        out: dict[tuple[str, str], str] = {}
        reductions: list[Any] = []
        fields = _fields(v, reductions)
        if reductions:
            how = "AGGREGATION"
        for f in fields:
            for k, sub in self.column(f.rel, f.name).items():
                s = max(sub, how, key=_RANK.__getitem__)
                if k not in out or _RANK[s] > _RANK[out[k]]:
                    out[k] = s
        return out

    def column(self, rel: Any, name: str) -> dict[tuple[str, str], str]:
        import ibis.expr.operations as ops

        key = (id(rel), name)
        if key in self.memo:
            return self.memo[key]
        self.memo[key] = {}
        out: dict[tuple[str, str], str] = {}
        if isinstance(rel, ops.PhysicalTable):
            out = {(rel.name, name): "IDENTITY"}
        elif isinstance(rel, ops.Project | ops.JoinChain) and name in rel.values:
            v = rel.values[name]
            out = self.value(v, "IDENTITY" if isinstance(v, ops.Field) else "TRANSFORMATION")
        elif isinstance(rel, ops.Aggregate):
            if name in rel.groups:
                v = rel.groups[name]
                out = self.value(v, "IDENTITY" if isinstance(v, ops.Field) else "TRANSFORMATION")
            elif name in rel.metrics:
                out = self.value(rel.metrics[name], "AGGREGATION")
        elif isinstance(rel, ops.Set):
            out = dict(self.column(rel.left, name))
            for k, s in self.column(rel.right, name).items():
                if k not in out or _RANK[s] > _RANK[out[k]]:
                    out[k] = s
        elif (parent := getattr(rel, "parent", None)) is not None:
            out = self.column(parent, name)
        self.memo[key] = out
        return out

    def dataset(self, root: Any) -> dict[tuple[str, str], set[str]]:
        """The base columns that decide which rows there are: filters,
        join keys, groups, sort keys and window partitions."""
        import ibis.expr.operations as ops

        out: dict[tuple[str, str], set[str]] = {}

        def add(values: Iterable[Any], sub: str) -> None:
            for v in values:
                for k in self.value(v, "IDENTITY"):
                    out.setdefault(k, set()).add(sub)

        for rel in root.find(ops.Relation):
            if isinstance(rel, ops.Filter):
                add(rel.predicates, "FILTER")
            elif isinstance(rel, ops.JoinChain):
                for link in rel.rest:
                    add(link.predicates, "JOIN")
            elif isinstance(rel, ops.Aggregate):
                add(rel.groups.values(), "GROUP_BY")
            elif isinstance(rel, ops.Sort):
                add(rel.keys, "SORT")
        for w in root.find(ops.WindowFunction):
            add([*w.group_by, *w.order_by], "WINDOW")
        return out


def column_lineage(expr: Any, datasets: Mapping[str, tuple[str, str]]) -> dict[str, Any] | None:
    """The `columnLineage` facet of an Ibis table expression whose base
    tables are named as in `datasets` (table name to namespace and name),
    or None if no column reads one."""
    op = expr.op()
    tracer = _Tracer()

    def field(k: tuple[str, str], kind: str, subs: Iterable[str]) -> dict[str, Any] | None:
        if k[0] not in datasets:
            return None
        ns, name = datasets[k[0]]
        return {
            "namespace": ns,
            "name": name,
            "field": k[1],
            "transformations": [{"type": kind, "subtype": s} for s in sorted(subs)],
        }

    fields: dict[str, Any] = {}
    for col in expr.schema().names:
        ins = [field(k, "DIRECT", [s]) for k, s in sorted(tracer.column(op, col).items())]
        ins = [x for x in ins if x is not None]
        if ins:
            fields[col] = {"inputFields": ins}
    whole = [field(k, "INDIRECT", s) for k, s in sorted(tracer.dataset(op).items())]
    whole = [x for x in whole if x is not None]
    if not fields and not whole:
        return None
    facet = _facet("columnLineage", fields=fields)
    if whole:
        facet["dataset"] = whole
    return facet


# -- the sverify_contract facet --------------------------------------------------


def contract_facet(
    node: Node, entry: StageRefresh | None = None, *, plan: bool = True
) -> dict[str, Any] | None:
    """The `sverify_contract` facet of a node with a contract, after the
    refresh `entry`; None for a node without one. With `plan`, it carries
    the verified plan exported to Substrait, so a downstream job can prove
    the contract again."""
    from sverify.contracts import MaxRows, Unique
    from sverify.incremental import plan_digest
    from sverify.io._common import condition_sql

    report = node.report
    if report is None:
        return None
    schema = node.schema
    ensures = []
    for c in report.ensures:
        status = "proved" if c.proved else "checked" if c.checked else "not_proved"
        e: dict[str, Any] = {"label": c.label, "status": status}
        cond = c.condition
        if isinstance(cond, Unique):
            e["unique"] = list(cond.cols)
        elif isinstance(cond, MaxRows):
            e["max_rows"] = cond.n
        elif cond is not None:
            try:
                sql = condition_sql(cond, schema)
            except Exception:  # noqa: BLE001 - not a row condition sverify writes as SQL
                sql = None
            if sql is not None:
                e["sql"] = sql
        ensures.append(e)
    facet: dict[str, Any] = {
        "_producer": _producer(),
        "_schemaURL": FACET_SCHEMA_URL,
        "format": FACET_FORMAT,
        "sverify": _version(),
        "node": node.name,
        "plan": plan_digest(node.internal_plan),
        "proved": report.proved,
        "verdict": report.verdict,
        "semantics": report.semantics,
        "equivalence": str(report.observation),
        "requires": {t: list(labs) for t, labs in report.requires.items()},
        "ensures": ensures,
        "not_null": list(report.not_null),
    }
    if entry is not None:
        if entry.route is not None:
            r = entry.route
            facet["route"] = {"engine": r.engine, "kind": r.kind, "class": r.cls}
        facet["outcome"] = entry.outcome
        facet["quarantined"] = entry.quarantined
        if entry.held is not None:
            facet["held"] = entry.held
    if plan:
        export = _export(report)
        if export is not None:
            facet["substrait"] = export
    return facet


def _export(report: Report) -> dict[str, Any] | None:
    try:
        return json.loads(report.to_substrait(format="json"))
    except Exception:  # noqa: BLE001 - a plan sverify cannot export: the facet is then evidence only
        return None


# -- emitting --------------------------------------------------------------------


class _File:
    def __init__(self, path: str | Path):
        self.path = Path(path)

    def emit(self, event: Mapping[str, Any]) -> None:
        self.path.parent.mkdir(parents=True, exist_ok=True)
        with self.path.open("a") as f:
            f.write(json.dumps(event, sort_keys=True) + "\n")


class _Console:
    def emit(self, event: Mapping[str, Any]) -> None:
        print(json.dumps(event, sort_keys=True), file=sys.stdout, flush=True)


class _Http:
    def __init__(self, url: str, api_key: str | None, timeout: float):
        self.url = url.rstrip("/") + "/api/v1/lineage"
        self.api_key = api_key
        self.timeout = timeout

    def emit(self, event: Mapping[str, Any]) -> None:
        headers = {"Content-Type": "application/json"}
        if self.api_key:
            headers["Authorization"] = f"Bearer {self.api_key}"
        req = urllib.request.Request(  # noqa: S310 - the URL is the user's
            self.url, data=json.dumps(event).encode(), headers=headers, method="POST"
        )
        with urllib.request.urlopen(req, timeout=self.timeout) as resp:  # noqa: S310
            resp.read()


class _Client:
    """The OpenLineage client's transport, configured by `openlineage.yml`
    or the `OPENLINEAGE_*` variables."""

    def __init__(self) -> None:
        try:
            from openlineage.client import OpenLineageClient
        except ImportError as e:
            raise ImportError(
                "Lineage() without a target reads the OpenLineage client's configuration: "
                "pip install 'sverify[openlineage]', or give a file, 'console' or a URL"
            ) from e
        self.transport = OpenLineageClient().transport

    def emit(self, event: Mapping[str, Any]) -> None:
        if self.transport is not None:
            self.transport.emit(dict(event))  # type: ignore[arg-type]


class Lineage:
    """Where a refresh sends its OpenLineage events: `node.refresh(lineage=
    Lineage(...))`.

    Args:
        target: Where events go. None (the default) uses the OpenLineage
            client's own configuration (`openlineage.yml`, `OPENLINEAGE_URL`,
            `OPENLINEAGE__TRANSPORT__*`), which needs
            `sverify[openlineage]`; `"console"` prints one JSON line per
            event; an `http://` or `https://` URL posts to its
            `/api/v1/lineage` (Marquez, DataHub's OpenLineage endpoint); any
            other string or path appends JSON lines to that file. An object
            with an `emit(event: dict)` method (an OpenLineage client
            transport) is used as it is.
        namespace: The jobs' namespace. Default: `OPENLINEAGE_NAMESPACE`,
            else "default", the client's default.
        api_key: A bearer token for an HTTP target. Default:
            `OPENLINEAGE_API_KEY`.
        timeout: Seconds an HTTP target may take per event. Default 5.
        plan: Whether the `sverify_contract` facet carries the verified plan
            exported to Substrait, which a downstream job needs to prove the
            contract again. Default True.

    `OPENLINEAGE_DISABLED=true` turns every target off. A target that fails
    warns (`LineageWarning`) and the refresh goes on.
    """

    def __init__(
        self,
        target: Any = None,
        *,
        namespace: str | None = None,
        api_key: str | None = None,
        timeout: float = 5.0,
        plan: bool = True,
    ):
        self.namespace = namespace or os.environ.get("OPENLINEAGE_NAMESPACE") or "default"
        self.plan = plan
        self.disabled = os.environ.get("OPENLINEAGE_DISABLED", "").lower() in ("1", "true")
        self.target = target
        if self.disabled:
            self._transport: Any = None
        elif target is None:
            self._transport = _Client()
        elif hasattr(target, "emit"):
            self._transport = target
        elif target == "console":
            self._transport = _Console()
        elif str(target).startswith(("http://", "https://")):
            key = api_key or os.environ.get("OPENLINEAGE_API_KEY")
            self._transport = _Http(str(target), key, timeout)
        else:
            self._transport = _File(target)

    def __repr__(self) -> str:
        return f"Lineage({self.target!r}, namespace={self.namespace!r})"

    def emit(self, event: Mapping[str, Any]) -> None:
        """Send one event; a failure warns (`LineageWarning`)."""
        if self._transport is None:
            return
        try:
            self._transport.emit(event)
        except Exception as e:  # noqa: BLE001 - lineage never fails a refresh
            warnings.warn(
                f"OpenLineage event for {event.get('job', {}).get('name')} not sent: {e}",
                LineageWarning,
                stacklevel=2,
            )

    def _runs(self, order: Sequence[Node]) -> _Runs:
        return _Runs(self, order)


def _now() -> str:
    return datetime.now(UTC).isoformat()


class _Runs:
    """The runs of one refresh, one per node, as `Group.refresh` goes."""

    def __init__(self, lineage: Lineage, order: Sequence[Node]):
        self.lineage = lineage
        self.order = list(order)
        self.ids = {id(n): str(uuid.uuid4()) for n in self.order}
        self.started: set[int] = set()
        self.ended: set[int] = set()

    def _job(self, n: Node) -> dict[str, Any]:
        return {
            "namespace": self.lineage.namespace,
            "name": n.name,
            "facets": {
                "jobType": _facet(
                    "jobType", processingType="BATCH", integration="SVERIFY", jobType="NODE"
                )
            },
        }

    def _event(self, kind: str, n: Node, run_facets: Mapping[str, Any] | None = None) -> dict:
        facets = {
            "processing_engine": _facet(
                "processing_engine",
                name="sverify",
                version=_version(),
                openlineageAdapterVersion=_version(),
            ),
            **(run_facets or {}),
        }
        return {
            "eventType": kind,
            "eventTime": _now(),
            "producer": _producer(),
            "schemaURL": f"{_SPEC}#/$defs/RunEvent",
            "run": {"runId": self.ids[id(n)], "facets": facets},
            "job": self._job(n),
        }

    def _datasets(self, n: Node) -> tuple[list[tuple[Node, str, str]], tuple[str, str] | None]:
        from sverify.nodes import _Stored

        leaves = [(leaf, *dataset_id(_leaf_object(leaf))) for leaf in n._leaves()]
        out = dataset_id(n.sink) if isinstance(n, _Stored) else None
        return leaves, out

    def start(self, n: Node) -> None:
        """Emit the START of `n`'s run; a failure to build it warns."""
        self.started.add(id(n))
        self._guard(self._start, n)

    def complete(self, n: Node, entry: StageRefresh) -> None:
        """Emit the end of `n`'s run: COMPLETE, or FAIL if it was held."""
        self.ended.add(id(n))
        self._guard(self._complete, n, entry)

    @staticmethod
    def _guard(f: Any, *args: Any) -> None:
        try:
            f(*args)
        except Exception as e:  # noqa: BLE001 - lineage never fails a refresh
            warnings.warn(f"OpenLineage event not built: {e!r}", LineageWarning, stacklevel=3)

    def _start(self, n: Node) -> None:
        leaves, out = self._datasets(n)
        event = self._event("START", n)
        event["inputs"] = [{"namespace": ns, "name": name} for _, ns, name in leaves]
        event["outputs"] = [] if out is None else [{"namespace": out[0], "name": out[1]}]
        self.lineage.emit(event)

    def _complete(self, n: Node, entry: StageRefresh) -> None:
        leaves, out = self._datasets(n)
        versions = n._stage.view.versions if n._stage is not None else {}
        checked_pre = list(entry.preconditions) + (
            list(entry.report.preconditions) if entry.report is not None else []
        )
        ok = entry.held is None
        inputs = []
        for leaf, ns, name in leaves:
            facets: dict[str, Any] = {
                "schema": _schema_facet(leaf.schema),
                "dataSource": _source_facet(ns, name),
            }
            if leaf.name in versions:
                facets["version"] = _facet("version", datasetVersion=str(versions[leaf.name]))
            d: dict[str, Any] = {"namespace": ns, "name": name, "facets": facets}
            asserts = [
                {"assertion": p.condition, "success": ok, "column": None}
                for p in checked_pre
                if p.table == leaf.name
            ]
            if asserts:
                d["inputFacets"] = {
                    "dataQualityAssertions": _facet(
                        "dataQualityAssertions",
                        assertions=[{k: v for k, v in a.items() if v is not None} for a in asserts],
                    )
                }
            inputs.append(d)
        outputs = []
        if out is not None:
            facets = {
                "schema": _schema_facet(n.schema),
                "dataSource": _source_facet(*out),
            }
            w = entry.write
            if w is not None and w.version is not None:
                facets["version"] = _facet("version", datasetVersion=str(w.version))
            datasets = {leaf.name: (ns, name) for leaf, ns, name in leaves}
            lineage = column_lineage(n._query()._expr, datasets)
            if lineage is not None:
                facets["columnLineage"] = lineage
            post = list(entry.postconditions) + (
                list(entry.report.postconditions) if entry.report is not None else []
            )
            if post:
                facets["dataQualityAssertions"] = _facet(
                    "dataQualityAssertions",
                    assertions=[{"assertion": p.condition, "success": ok} for p in post],
                )
            contract = contract_facet(n, entry, plan=self.lineage.plan)
            if contract is not None:
                facets[_FACET] = contract
            d = {"namespace": out[0], "name": out[1], "facets": facets}
            if w is not None and w.mode != "skipped":
                d["outputFacets"] = {
                    "outputStatistics": _facet("outputStatistics", rowCount=w.inserted)
                }
            outputs.append(d)
        if entry.held is not None:
            event = self._event("FAIL", n, {"errorMessage": self._error(f"held: {entry.held}")})
        else:
            event = self._event("COMPLETE", n)
        event["inputs"], event["outputs"] = inputs, outputs
        self.lineage.emit(event)

    @staticmethod
    def _error(message: str, trace: str | None = None) -> dict[str, Any]:
        f = _facet("errorMessage", message=message, programmingLanguage="python")
        if trace:
            f["stackTrace"] = trace
        return f

    def fail(self, error: BaseException) -> None:
        """Close every run the refresh left open: FAIL for the node that
        raised (and for every node if nothing ran), ABORT for the rest."""
        import traceback

        message = f"{type(error).__name__}: {error}"
        trace = "".join(traceback.format_exception(error))
        nothing_ran = not self.started
        for n in self.order:
            if id(n) in self.ended:
                continue
            if id(n) not in self.started:
                self.start(n)
                self.ended.add(id(n))
                if not nothing_ran:
                    self.lineage.emit(self._event("ABORT", n))
                    continue
            self.lineage.emit(self._event("FAIL", n, {"errorMessage": self._error(message, trace)}))
            self.ended.add(id(n))


def runs(lineage: Any, order: Sequence[Node]) -> _Runs | None:
    """The runs of a refresh with `lineage=`, or None when it is off
    (`Group.refresh`)."""
    if lineage is None or lineage is False:
        return None
    if not isinstance(lineage, Lineage):
        lineage = Lineage(None if lineage is True else lineage)
    return lineage._runs(order)


# -- reading ---------------------------------------------------------------------


@dataclass(frozen=True)
class Assertion:
    """A check another job ran on a dataset: checked evidence, never proof.

    Attributes:
        assertion: What was checked (`not_null`, a condition's text, ...).
        success: Whether it passed.
        column: The column it is on, or None for the whole dataset.
        producer: The `producer` of the event that reported it.
        job: The job that ran it, as `namespace/name`.
    """

    assertion: str
    success: bool
    column: str | None
    producer: str
    job: str


@dataclass
class Upstream:
    """A dataset as upstream jobs' events describe it (`Events.dataset`).

    Attributes:
        namespace: The dataset's namespace.
        name: The dataset's name.
        fields: The `schema` facet's fields, as the events have them.
        version: The `version` facet's `datasetVersion`, if any.
        producer: The job of the last run that wrote it (`namespace/name`),
            its run id and the `producer` URI.
        contract: Its `sverify_contract` facet, if a sverify job wrote it.
        evidence: Checks other jobs ran on it (`dataQualityAssertions`), and
            the claims of a `sverify_contract` facet that sverify did not
            prove again: checked evidence, never proof.
    """

    namespace: str
    name: str
    fields: list[dict[str, Any]] = field(default_factory=list)
    version: str | None = None
    producer: dict[str, str] = field(default_factory=dict)
    contract: dict[str, Any] | None = None
    evidence: list[Assertion] = field(default_factory=list)
    _requires: list[Condition] | None = field(default=None, repr=False)
    _report: Report | None = field(default=None, repr=False)
    _why: str | None = field(default=None, repr=False)

    @property
    def schema(self) -> ibis.Schema:
        """The `schema` facet as an Ibis schema: DuckDB's and Spark's type
        names, and Ibis's own; a type none of them reads is `unknown`."""
        import ibis

        return ibis.schema({f["name"]: _ibis_type(f.get("type")) for f in self.fields})

    @property
    def verified(self) -> bool:
        """Whether sverify proved the `sverify_contract` facet's contract
        again: the facet carries its plan exported to Substrait, the
        checker proves the plan's postconditions (`sv.from_substrait`), and
        the export is the plan the facet names."""
        self._verify()
        return self._report is not None and self._report.proved

    @property
    def why_unverified(self) -> str | None:
        """Why the facet's contract counts as evidence only, or None if it
        is verified (or there is no facet)."""
        self._verify()
        return self._why

    @property
    def requires(self) -> list[Condition]:
        """The postconditions of the `sverify_contract` facet that sverify
        proves again, as conditions for a downstream transform's
        `requires`: SQL conditions, `sv.unique` and `sv.max_rows`. Empty
        when the facet is absent or not verified."""
        self._verify()
        return list(self._requires or [])

    def _verify(self) -> None:
        if self._requires is not None:
            return
        self._requires = []
        c = self.contract
        if c is None:
            return
        export = c.get("substrait")
        if export is None:
            self._why = "the facet carries no plan to prove again"
            self._claims(c)
            return
        import sverify as sv
        from sverify.contracts import max_rows, unique

        try:
            report = sv.from_substrait(export)
        except Exception as e:  # noqa: BLE001 - an export the checker rejects is evidence only
            self._why = f"the checker rejects the exported plan: {e}"
            self._claims(c)
            return
        self._report = report
        if not report.proved:
            self._why = f"the checker does not prove the exported plan: {report.verdict}"
            self._claims(c)
            return
        proved = {e.label for e in report.ensures if e.proved}
        unverified = []
        for e in c.get("ensures", []):
            if e.get("status") != "proved" or e.get("label") not in proved:
                unverified.append(e)
            elif "unique" in e:
                self._requires.append(unique(*e["unique"]))
            elif "max_rows" in e:
                self._requires.append(max_rows(int(e["max_rows"])))
            elif "sql" in e:
                self._requires.append(e["sql"])
            else:
                unverified.append(e)
        self._claims({**c, "ensures": unverified, "not_null": []})

    def _claims(self, c: Mapping[str, Any]) -> None:
        job = self.producer.get("job", "")
        prod = self.producer.get("producer", "")
        for e in c.get("ensures", []):
            self.evidence.append(
                Assertion(
                    f"sverify_contract: {e.get('label')} ({e.get('status')})",
                    e.get("status") in ("proved", "checked"),
                    None,
                    prod,
                    job,
                )
            )
        for col in c.get("not_null", []):
            self.evidence.append(
                Assertion("sverify_contract: not_null (proved)", True, col, prod, job)
            )


_SPARK_TYPES = {
    "long": "int64",
    "integer": "int32",
    "int": "int32",
    "short": "int16",
    "byte": "int8",
    "string": "string",
    "double": "float64",
    "float": "float32",
    "boolean": "boolean",
    "date": "date",
    "timestamp": "timestamp('UTC')",
    "timestamp_ntz": "timestamp",
    "binary": "binary",
}


def _ibis_type(t: Any) -> Any:
    import ibis.expr.datatypes as dt
    from ibis.backends.sql.datatypes import DuckDBType

    if not isinstance(t, str):
        return dt.unknown
    if t.lower() in _SPARK_TYPES:
        return dt.dtype(_SPARK_TYPES[t.lower()])
    try:
        return DuckDBType.from_string(t)
    except Exception:  # noqa: BLE001
        pass
    try:
        return dt.dtype(t.lower())
    except Exception:  # noqa: BLE001
        return dt.unknown


class Events:
    """OpenLineage events, as `read` gives them.

    Attributes:
        events: The run events, in the order read.
    """

    def __init__(self, events: Iterable[Mapping[str, Any]]):
        self.events = [dict(e) for e in events]

    def __len__(self) -> int:
        return len(self.events)

    def dataset(self, dataset: Any, name: str | None = None) -> Upstream:
        """What the events say of a dataset: the last COMPLETE run that
        wrote it, and every check any run made of it.

        Args:
            dataset: A source or sink (`DeltaSource`, `IcebergSink`, ...),
                named as `refresh` names it, or a namespace with `name`.
            name: The dataset's name, with a namespace for `dataset`.

        Returns:
            An `Upstream`; empty where no event names the dataset.
        """
        ns, nm = (dataset, name) if name is not None else dataset_id(dataset)
        up = Upstream(ns, nm)
        for e in self.events:
            job = e.get("job") or {}
            job_name = f"{job.get('namespace')}/{job.get('name')}"
            producer = str(e.get("producer", ""))
            for kind in ("inputs", "outputs"):
                for d in e.get(kind) or []:
                    if d.get("namespace") != ns or d.get("name") != nm:
                        continue
                    facets = d.get("facets") or {}
                    for facet in (facets, d.get("inputFacets") or {}):
                        dq = facet.get("dataQualityAssertions") or {}
                        for a in dq.get("assertions") or []:
                            up.evidence.append(
                                Assertion(
                                    str(a.get("assertion")),
                                    bool(a.get("success")),
                                    a.get("column"),
                                    producer,
                                    job_name,
                                )
                            )
                    if kind != "outputs" or e.get("eventType") != "COMPLETE":
                        if "schema" in facets and not up.fields:
                            up.fields = list(facets["schema"].get("fields") or [])
                        continue
                    if "schema" in facets:
                        up.fields = list(facets["schema"].get("fields") or [])
                    if "version" in facets:
                        up.version = facets["version"].get("datasetVersion")
                    up.producer = {
                        "job": job_name,
                        "run": str((e.get("run") or {}).get("runId", "")),
                        "producer": producer,
                    }
                    up.contract = facets.get(_FACET)
        return up


def read(source: str | Path | Iterable[Mapping[str, Any]]) -> Events:
    """Read OpenLineage events: a JSON lines file (one event per line, as
    the file transport and `Lineage(path)` write them), a JSON file holding
    one event or a list, or the events themselves.

    Args:
        source: The file, or the events as dicts.

    Returns:
        The `Events`.
    """
    if isinstance(source, str | Path):
        text = Path(source).read_text()
        stripped = text.lstrip()
        if stripped.startswith("["):
            return Events(json.loads(text))
        events = []
        for line in text.splitlines():
            if line.strip():
                events.append(json.loads(line))
        return Events(events)
    return Events(source)


def marquez(
    url: str,
    namespace: str,
    name: str,
    *,
    api_key: str | None = None,
    timeout: float = 10.0,
) -> Upstream:
    """A dataset as a Marquez server (or another server with Marquez's
    API) has it: its fields, its facets as of its current version, and the
    run that wrote that version.

    Args:
        url: The server, such as `http://localhost:5000`.
        namespace: The dataset's namespace.
        name: The dataset's name.
        api_key: A bearer token. Default: `OPENLINEAGE_API_KEY`.
        timeout: Seconds per request. Default 10.

    Returns:
        An `Upstream`, verified on demand like one from events.
    """
    key = api_key or os.environ.get("OPENLINEAGE_API_KEY")

    def get(path: str) -> Any:
        req = urllib.request.Request(url.rstrip("/") + path)  # noqa: S310
        if key:
            req.add_header("Authorization", f"Bearer {key}")
        with urllib.request.urlopen(req, timeout=timeout) as resp:  # noqa: S310
            return json.loads(resp.read())

    q = urllib.parse.quote
    base = f"/api/v1/namespaces/{q(namespace, safe='')}/datasets/{q(name, safe='')}"
    data = get(base)
    facets = data.get("facets") or {}
    up = Upstream(namespace, name)
    up.fields = [
        {"name": f["name"], "type": f.get("type")} for f in data.get("fields") or []
    ] or list((facets.get("schema") or {}).get("fields") or [])
    up.version = (facets.get("version") or {}).get("datasetVersion")
    up.contract = facets.get(_FACET)
    try:
        versions = get(base + "/versions?limit=1").get("versions") or []
    except Exception:  # noqa: BLE001 - the producer is a courtesy
        versions = []
    if versions:
        run = versions[0].get("createdByRun") or {}
        job = run.get("jobVersion") or {}
        up.producer = {
            "job": f"{job.get('namespace')}/{job.get('name')}",
            "run": str(run.get("id", "")),
            "producer": str(facets.get(_FACET, {}).get("_producer", "")),
        }
    for a in (facets.get("dataQualityAssertions") or {}).get("assertions") or []:
        up.evidence.append(
            Assertion(
                str(a.get("assertion")),
                bool(a.get("success")),
                a.get("column"),
                "",
                up.producer.get("job", ""),
            )
        )
    return up
