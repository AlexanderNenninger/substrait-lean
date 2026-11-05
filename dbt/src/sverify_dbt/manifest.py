"""A dbt project as `dbt compile` leaves it: `target/manifest.json`, and
`target/catalog.json` when `dbt docs generate` wrote one.

Only what the check needs is read: models with their compiled SQL, the
sources and seeds they read with their column types, and the generic tests.
"""

from __future__ import annotations

import json
import re
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any


@dataclass
class Column:
    """A column as the project declares it."""

    name: str
    data_type: str | None = None
    constraints: list[dict[str, Any]] = field(default_factory=list)


@dataclass
class Relation:
    """A model, source, seed or snapshot: anything a model can read."""

    unique_id: str
    resource_type: str
    name: str
    relation_name: str | None
    columns: dict[str, Column]
    """The declared columns (YAML), with their types and constraints."""
    catalog: dict[str, str] | None = None
    """The column types in catalog.json, in order, when it has the relation."""
    source_name: str | None = None
    path: str | None = None
    compiled_code: str | None = None
    language: str = "sql"
    materialized: str | None = None
    depends_on: list[str] = field(default_factory=list)
    contract: bool = False
    constraints: list[dict[str, Any]] = field(default_factory=list)
    """Model-level constraints (`constraints:` beside `columns:`)."""

    @property
    def is_model(self) -> bool:
        return self.resource_type == "model"

    @property
    def ref(self) -> str:
        """The relation as the user writes it in Jinja."""
        if self.resource_type == "source":
            return f"source('{self.source_name}', '{self.name}')"
        return f"ref('{self.name}')"

    def declared_types(self) -> dict[str, str] | None:
        """The column types the project states: catalog.json's, else the
        YAML's `data_type`s (a seed's `column_types` among them), if every
        declared column has one; None otherwise."""
        if self.catalog:
            return dict(self.catalog)
        if self.columns and all(c.data_type for c in self.columns.values()):
            return {c.name: c.data_type for c in self.columns.values()}  # type: ignore[misc]
        return None


@dataclass
class Test:
    """A data test: generic (`not_null`, `dbt_utils.accepted_range`, …)
    or singular (a SQL file of its own, `name` None)."""

    __test__ = False  # not a pytest class

    unique_id: str
    name: str
    """The test node's name, as `dbt ls` and selectors know it."""
    kind: str | None
    """The generic test, with its package: `not_null`,
    `dbt_utils.accepted_range`; None for a singular test."""
    kwargs: dict[str, Any]
    on: str | None
    """The unique id of the relation the test is on."""
    column: str | None
    depends_on: list[str]
    severity: str = "error"
    where: str | None = None
    error_if: str = "!= 0"
    fail_calc: str = "count(*)"

    @property
    def blocks(self) -> bool:
        """`dbt build` skips everything downstream when the test fails: it
        has severity error and fails on any failing row."""
        return (
            self.severity.lower() == "error"
            and _norm(self.error_if) == "!=0"
            and _norm(self.fail_calc) == "count(*)"
        )

    @property
    def short(self) -> str:
        """`not_null(order_id)`, `accepted_values(status)`: the test in a
        report line."""
        what = self.kind or "singular test"
        if self.kwargs.get("expression"):
            col = f"{self.column} " if self.column else ""
            return f"{what}({col}{self.kwargs['expression']})"
        cols = self.kwargs.get("combination_of_columns") or ([self.column] if self.column else [])
        return f"{what}({', '.join(cols)})" if cols else what


def _norm(s: str) -> str:
    return re.sub(r"\s+", "", s or "").lower()


@dataclass
class Project:
    """The parts of a compiled dbt project the check reads."""

    root: Path
    name: str
    relations: dict[str, Relation]
    tests: dict[str, Test]
    unit_tests: list[str]
    adapter: str
    dbt_version: str

    @property
    def models(self) -> list[Relation]:
        """The models, upstream first (a topological order of `depends_on`)."""
        out: list[Relation] = []
        seen: set[str] = set()

        def visit(uid: str) -> None:
            if uid in seen or uid not in self.relations:
                return
            seen.add(uid)
            for d in self.relations[uid].depends_on:
                visit(d)
            if self.relations[uid].is_model:
                out.append(self.relations[uid])

        for uid in sorted(self.relations):
            visit(uid)
        return out

    def tests_on(self, uid: str) -> list[Test]:
        return [t for t in self.tests.values() if t.on == uid]


class ProjectError(Exception):
    """The project cannot be read: no manifest, or not the DuckDB adapter."""


def load(project: str | Path, target_path: str | Path = "target") -> Project:
    """Read `<project>/<target_path>/manifest.json` (and `catalog.json`).

    Raises:
        ProjectError: There is no manifest (run `dbt compile` first), or the
            project does not use the DuckDB adapter.
    """
    root = Path(project)
    target = root / target_path
    path = target / "manifest.json"
    if not path.is_file():
        raise ProjectError(f"no {path}: run `dbt compile` in {root} first")
    manifest = json.loads(path.read_text())
    meta = manifest.get("metadata", {})
    adapter = meta.get("adapter_type") or "unknown"
    if adapter != "duckdb":
        raise ProjectError(
            f"the project uses the {adapter} adapter; sverify-dbt reads DuckDB projects only "
            "(the other engines wait on #271)"
        )
    catalog = _catalog(target / "catalog.json")
    relations: dict[str, Relation] = {}
    for uid, n in [*manifest["nodes"].items(), *manifest["sources"].items()]:
        kind = n["resource_type"]
        if kind not in ("model", "seed", "snapshot", "source"):
            continue
        config = n.get("config") or {}
        columns = {
            name: Column(name, c.get("data_type"), list(c.get("constraints") or []))
            for name, c in (n.get("columns") or {}).items()
        }
        if kind == "seed":
            for name, t in (config.get("column_types") or {}).items():
                columns.setdefault(name, Column(name)).data_type = t
        contract = (config.get("contract") or {}).get("enforced")
        relations[uid] = Relation(
            unique_id=uid,
            resource_type=kind,
            name=n["name"],
            relation_name=n.get("relation_name"),
            columns=columns,
            catalog=catalog.get(uid),
            source_name=n.get("source_name"),
            path=n.get("original_file_path"),
            compiled_code=n.get("compiled_code"),
            language=n.get("language") or "sql",
            materialized=config.get("materialized"),
            depends_on=list((n.get("depends_on") or {}).get("nodes") or []),
            contract=bool(contract),
            constraints=list(n.get("constraints") or []),
        )
    tests = {}
    for uid, n in manifest["nodes"].items():
        if n["resource_type"] != "test":
            continue
        meta_ = n.get("test_metadata") or {}
        config = n.get("config") or {}
        kwargs = dict(meta_.get("kwargs") or {})
        kind = None
        if meta_:
            ns = meta_.get("namespace")
            kind = f"{ns}.{meta_['name']}" if ns else meta_["name"]
        depends = list((n.get("depends_on") or {}).get("nodes") or [])
        tests[uid] = Test(
            unique_id=uid,
            name=n["name"],
            kind=kind,
            kwargs=kwargs,
            on=_tested(n, kwargs, depends, relations),
            column=n.get("column_name") or kwargs.get("column_name"),
            depends_on=depends,
            severity=config.get("severity") or "error",
            where=config.get("where"),
            error_if=config.get("error_if") or "!= 0",
            fail_calc=config.get("fail_calc") or "count(*)",
        )
    return Project(
        root=root,
        name=meta.get("project_name") or root.name,
        relations=relations,
        tests=tests,
        unit_tests=sorted(manifest.get("unit_tests") or {}),
        adapter=adapter,
        dbt_version=meta.get("dbt_version") or "unknown",
    )


def resolve(text: str, among: list[str], relations: dict[str, Relation]) -> str | None:
    """The relation `ref('x')` or `source('s', 't')` names, among `among`."""
    m = re.search(r"source\(\s*['\"]([^'\"]+)['\"]\s*,\s*['\"]([^'\"]+)['\"]\s*\)", text)
    if m:
        for uid in among:
            r = relations.get(uid)
            if r and r.resource_type == "source" and (r.source_name, r.name) == m.groups():
                return uid
        return None
    m = re.search(r"ref\(\s*(?:['\"][^'\"]+['\"]\s*,\s*)?['\"]([^'\"]+)['\"]", text)
    if m:
        for uid in among:
            r = relations.get(uid)
            if r and r.resource_type != "source" and r.name == m[1]:
                return uid
    return None


def _tested(
    n: dict[str, Any], kwargs: dict[str, Any], depends: list[str], rels: dict[str, Relation]
) -> str | None:
    if n.get("attached_node"):
        return n["attached_node"]
    model = kwargs.get("model")
    if isinstance(model, str) and (uid := resolve(model, depends, rels)):
        return uid
    return depends[0] if len(depends) == 1 else None


def _catalog(path: Path) -> dict[str, dict[str, str]]:
    """The column types of each relation in catalog.json, by unique id."""
    if not path.is_file():
        return {}
    data = json.loads(path.read_text())
    out = {}
    for uid, entry in [*data.get("nodes", {}).items(), *data.get("sources", {}).items()]:
        cols = sorted((entry.get("columns") or {}).values(), key=lambda c: c.get("index", 0))
        out[uid] = {c["name"]: c["type"] for c in cols}
    return out
