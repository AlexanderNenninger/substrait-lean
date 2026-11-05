"""What `check` found, per model, and the files it writes from it."""

from __future__ import annotations

from dataclasses import asdict, dataclass, field
from pathlib import Path
from typing import Any

from sverify_dbt.manifest import Relation, Test


@dataclass
class TestResult:
    """One of a model's tests or contract constraints."""

    __test__ = False  # not a pytest class

    test: str | None
    """The test's unique id; None for a constraint."""
    name: str | None
    """The test node's name, as selectors know it; None for a constraint."""
    label: str
    """`not_null(order_id)`, `primary_key(customer_id)`."""
    kind: str
    """`"test"` or `"constraint"`."""
    status: str = "pending"
    """`"proved"`, `"not proved"` or `"not checked"` (`"pending"` while
    the check runs)."""
    why: str | None = None
    """Why it is not proved or not checked."""
    counterexample: str | None = None
    """Inputs meeting every test upstream on which the model breaks it."""
    would_hold: dict[str, list[tuple[str | None, str]]] = field(default_factory=dict)
    """Tests on the inputs under which it would be proved: per input, the
    column and the test's YAML."""
    conditions: list[Any] = field(default_factory=list, repr=False)

    def skip(self, why: str) -> None:
        self.status, self.why = "not checked", why


@dataclass
class Needed:
    """A test an input needs before sverify can prove anything of the model:
    a precondition sverify inferred (`Report.needed`)."""

    on: str
    """The input, as `source('app', 'orders')` or `ref('stg_orders')`."""
    column: str | None
    test: str
    """The test to add, as YAML: `dbt_utils.accepted_range: {...}`."""
    because: str | None
    """The runtime error it rules out, and where."""
    condition: str
    """The condition, as SQL."""


@dataclass
class ContractIssue:
    """Where the model's result and its contract disagree."""

    column: str
    problem: str


@dataclass
class ModelResult:
    """Everything `check` found about one model."""

    name: str
    unique_id: str
    path: str | None
    ref: str
    refused: str | None = None
    """Why the model was not checked at all."""
    tests: list[TestResult] = field(default_factory=list)
    constraints: list[TestResult] = field(default_factory=list)
    """The contract's constraints, when the contract is enforced."""
    contract: list[ContractIssue] | None = None
    """The contract's mismatches (empty: it matches); None without an
    enforced contract."""
    needed: list[Needed] = field(default_factory=list)
    may_fail: list[str] = field(default_factory=list)
    """Runtime errors sverify could not rule out."""
    assumed: list[str] = field(default_factory=list)
    """Operations assumed not to overflow, which DuckDB checks as it runs."""
    deterministic: bool = True
    not_assumed: list[str] = field(default_factory=list)
    """Tests on the inputs left out of the preconditions, and why."""
    notes: list[str] = field(default_factory=list)
    sql: str | None = field(default=None, repr=False)
    """The compiled SQL as checked: each input read by its table name."""
    duckdb_types: dict[str, str] = field(default_factory=dict, repr=False)

    def refuse(self, why: str) -> ModelResult:
        self.refused = why
        for t in self.tests + self.constraints:
            if t.status == "pending":
                t.skip("the model was refused")
        return self

    def by_status(self, status: str) -> list[TestResult]:
        return [t for t in self.tests + self.constraints if t.status == status]


@dataclass
class CheckResult:
    """The result of `check` for a project."""

    project: str
    root: str
    models: list[ModelResult]
    tests: dict[str, Test] = field(repr=False)
    unit_tests: list[str] = field(default_factory=list)
    relations: dict[str, Relation] = field(default_factory=dict, repr=False)

    def suggestions(self) -> list[Suggestion]:
        """The tests sverify suggests adding, so that it proves more: what
        each model needs (`Report.needs`), and the tests on the inputs under
        which an unproved test would hold (`CheckedCondition.suggested`).
        One per relation, column and test."""
        by_ref = {r.ref: r for r in self.relations.values()}
        out: dict[tuple, Suggestion] = {}

        def add(ref: str, column: str | None, test: str, why: str) -> None:
            r = by_ref.get(ref)
            if r is None:
                return
            key = (r.unique_id, column, test)
            if key in out:
                out[key].because.append(why)
            else:
                out[key] = Suggestion(r, column, test, [why])

        for m in self.models:
            for n in m.needed:
                add(
                    n.on,
                    n.column,
                    n.test,
                    f"{m.name}: {n.because}" if n.because else f"{m.name} needs it",
                )
            for t in m.tests + m.constraints:
                for ref, tests in t.would_hold.items():
                    for column, test in tests:
                        add(ref, column, test, f"{m.name}: proves {t.label}")
        return list(out.values())

    def suggestions_yaml(self) -> str:
        """`suggestions` as a dbt properties file, with each test's reason as
        a comment: merge it into the project's YAML (dbt rejects a second
        entry for a relation another file describes)."""
        return suggestions_yaml(self.suggestions())

    def __getitem__(self, name: str) -> ModelResult:
        for m in self.models:
            if m.name == name:
                return m
        raise KeyError(name)

    @property
    def proved(self) -> list[TestResult]:
        """The tests proved before any model runs: `dbt build` may skip them."""
        return [t for m in self.models for t in m.tests if t.status == "proved"]

    @property
    def contract_errors(self) -> list[tuple[str, ContractIssue]]:
        return [(m.name, i) for m in self.models for i in m.contract or []]

    @property
    def unproved_constraints(self) -> list[tuple[str, TestResult]]:
        return [(m.name, c) for m in self.models for c in m.constraints if c.status != "proved"]

    def summary(self) -> str:
        tests = [t for m in self.models for t in m.tests]
        n = {s: sum(t.status == s for t in tests) for s in ("proved", "not proved", "not checked")}
        refused = sum(m.refused is not None for m in self.models)
        return (
            f"{len(self.models)} model(s), {refused} refused; {len(tests)} test(s): "
            f"{n['proved']} proved, {n['not proved']} not proved, {n['not checked']} not checked"
        )

    def __str__(self) -> str:
        lines: list[str] = []
        for m in self.models:
            lines += _model_lines(m)
            lines.append("")
        if self.unit_tests:
            lines.append(
                f"{len(self.unit_tests)} unit test(s) not checked: sverify-dbt reads "
                "data tests only"
            )
        lines.append(self.summary())
        return "\n".join(lines)

    def to_dict(self) -> dict[str, Any]:
        """The result as JSON-ready data."""
        out = []
        for m in self.models:
            d = asdict(m)
            for t in d["tests"] + d["constraints"]:
                t.pop("conditions", None)
            d.pop("sql", None)
            out.append(d)
        return {
            "project": self.project,
            "summary": self.summary(),
            "models": out,
            "unit_tests": self.unit_tests,
        }

    def selector(self, name: str = "sverify_proved") -> dict[str, Any]:
        """A dbt selector that selects the proved tests, for
        `dbt build --exclude selector:<name>`."""
        names = sorted({t.name for t in self.proved if t.name})
        definition: dict[str, Any] = (
            {"union": [{"method": "fqn", "value": n} for n in names]}
            if names
            # dbt has no empty selector: select a name no node has.
            else {"method": "fqn", "value": "sverify_dbt_nothing_proved"}
        )
        return {
            "name": name,
            "description": "Tests sverify-dbt proved from the tests upstream; generated, "
            "do not edit",
            "definition": definition,
        }

    def write_selectors(self, path: str | Path, name: str = "sverify_proved") -> Path:
        """Add (or replace) the selector `name` in a dbt selectors file,
        keeping its other selectors. dbt reads `selectors.yml` at the root
        of the project; then `dbt build --exclude selector:<name>` skips the
        proved tests."""
        import yaml

        path = Path(path)
        data: dict[str, Any] = {}
        if path.is_file():
            data = yaml.safe_load(path.read_text()) or {}
        selectors = [s for s in data.get("selectors") or [] if s.get("name") != name]
        selectors.append(self.selector(name))
        data["selectors"] = selectors
        path.write_text(yaml.safe_dump(data, sort_keys=False))
        return path


def _model_lines(m: ModelResult) -> list[str]:
    head = f"{m.name}" + (f" ({m.path})" if m.path else "")
    if m.refused:
        return [head, f"  refused: {m.refused}"]
    out = [head]
    proved = [t for t in m.tests if t.status == "proved"]
    if proved:
        out.append("  proved before the model runs (dbt build may skip them):")
        out += [f"    {t.label}" for t in proved]
    unproved = [t for t in m.tests if t.status == "not proved"]
    if unproved:
        out.append("  not proved (dbt build still runs them):")
        for t in unproved:
            out += _unproved(t)
    if m.contract is not None:
        if m.contract:
            out.append("  contract does not match:")
            out += [f"    {i.column}: {i.problem}" for i in m.contract]
        else:
            out.append("  contract: columns and types match")
        for c in m.constraints:
            if c.status == "proved":
                out.append(f"    {c.label}: proved")
            elif c.status == "not proved":
                out += _unproved(c, "not proved, ")
            else:
                out.append(f"    {c.label}: not checked, {c.why}")
    if m.needed:
        out.append("  needs these tests before anything is proved:")
        for n in m.needed:
            where = f"{n.on}, column {n.column}" if n.column else n.on
            out.append(f"    on {where}: {n.test}")
            if n.because:
                out.append(f"      ({n.because})")
    skipped = [t for t in m.tests if t.status == "not checked"]
    if skipped:
        out.append("  not checked:")
        out += [f"    {t.label}: {t.why}" for t in skipped]
    for e in m.may_fail:
        out.append(f"  may fail at run time: {e}")
    for a in m.assumed:
        out.append(f"  assumes {a} does not overflow (DuckDB raises if it does)")
    for n in m.notes:
        out.append(f"  note: {n}")
    return out


def _unproved(t: TestResult, status: str = "") -> list[str]:
    out = [f"    {t.label}: {status}{t.why}"]
    if t.counterexample:
        out.append(f"      counterexample: {t.counterexample}")
    for on, tests in t.would_hold.items():
        for col, yaml in tests:
            where = f"{on}, column {col}" if col else on
            out.append(f"      would hold with, on {where}: {yaml}")
    return out


@dataclass
class Suggestion:
    """A test to add to a relation (`CheckResult.suggestions`)."""

    relation: Relation
    column: str | None
    """The column it goes on; None for a test on the relation."""
    test: str
    """The test as YAML: `dbt_utils.accepted_range: {arguments: {...}}`."""
    because: list[str]
    """What it lets sverify prove, or which runtime error it rules out."""


def suggestions_yaml(suggestions: list[Suggestion]) -> str:
    """Suggestions as dbt YAML, grouped by relation and column."""
    if not suggestions:
        return "# sverify-dbt suggests no tests: nothing more is provable by adding one\n"
    groups: dict[str, dict[str, Any]] = {}
    for s in suggestions:
        r = s.relation
        g = groups.setdefault(r.unique_id, {"rel": r, "cols": {}})
        g["cols"].setdefault(s.column, []).append(s)
    lines = [
        "# Tests sverify-dbt suggests (sverify-dbt suggest): merge them into the",
        "# YAML that describes each relation.",
        "version: 2",
    ]
    sections = {"sources": [], "models": [], "seeds": [], "snapshots": []}
    for g in groups.values():
        r = g["rel"]
        kind = "sources" if r.resource_type == "source" else r.resource_type + "s"
        sections[kind].append(g)
    for kind, gs in sections.items():
        if not gs:
            continue
        lines.append(f"{kind}:")
        if kind == "sources":
            by_source: dict[str, list] = {}
            for g in gs:
                by_source.setdefault(g["rel"].source_name, []).append(g)
            for name, tables in by_source.items():
                lines += [f"  - name: {name}", "    tables:"]
                for g in tables:
                    lines += _relation_lines(g, "      ")
        else:
            for g in gs:
                lines += _relation_lines(g, "  ")
    return "\n".join(lines) + "\n"


def _relation_lines(g: dict[str, Any], pad: str) -> list[str]:
    lines = [f"{pad}- name: {g['rel'].name}"]
    table = g["cols"].pop(None, [])
    if table:
        lines.append(f"{pad}  data_tests:")
        lines += _test_lines(table, pad + "    ")
    if g["cols"]:
        lines.append(f"{pad}  columns:")
        for col, tests in g["cols"].items():
            lines += [f"{pad}    - name: {col}", f"{pad}      data_tests:"]
            lines += _test_lines(tests, pad + "        ")
    return lines


def _test_lines(tests: list[Suggestion], pad: str) -> list[str]:
    out = []
    for s in tests:
        out += [f"{pad}# {why}" for why in s.because]
        out.append(f"{pad}- {s.test}")
    return out
