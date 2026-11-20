"""Check a compiled dbt project with sverify: each model's tests and
contract, proved from the tests on what it reads.

Each model is checked on its own, as dbt builds it: its compiled SQL is
`sv.verify`'s transformation over its inputs (its `ref`s and `source`s), the
tests on those inputs are `requires`, and its own tests and contract
constraints are `ensures`. Under `dbt build` a failing test with severity
error skips every model downstream, so a model's inputs meet their tests
whenever it runs: they are its preconditions, proved or not.
"""

from __future__ import annotations

import re
import warnings
from collections.abc import Iterable
from pathlib import Path
from typing import Any

import duckdb
import sqlglot as sg
import sverify as sv
from sverify.conditions import label as condition_label
from sverify.errors import ConditionError

from sverify_dbt import mapping
from sverify_dbt.manifest import Project, Relation, Test, load
from sverify_dbt.result import (
    CheckResult,
    ContractIssue,
    ModelResult,
    Needed,
    TestResult,
)


def check(
    project: str | Path | Project,
    *,
    target_path: str | Path = "target",
    select: Iterable[str] | None = None,
    counterexamples: int = 200,
) -> CheckResult:
    """Check the tests and contracts of a dbt project after `dbt compile`.

    Args:
        project: The dbt project's directory, or a `Project` already loaded.
        target_path: The project's target directory, relative to it.
        select: Model names to report on (all by default). Their upstream
            models are checked too, since their tests are the inputs'.
        counterexamples: How many small inputs sverify tries for each
            unproved test; 0 skips the search.

    Returns:
        A `CheckResult`: per model, the tests proved, not proved and not
        checked, the contract, and the source tests it needs.

    Raises:
        sverify_dbt.ProjectError: No manifest, or not a DuckDB project.
    """
    proj = project if isinstance(project, Project) else load(project, target_path)
    return _Checker(proj, counterexamples).run(set(select) if select else None)


#: The bounds of the search for input tests that prove a model test
#: (`_blame_nulls`): at most this many uncovered input columns, and this many
#: extra checker calls per model.
_BLAME_COLUMNS = 12
_BLAME_CALLS = 24


class _Checker:
    def __init__(self, project: Project, counterexamples: int):
        self.p = project
        self.counterexamples = counterexamples
        self.names = _input_names(project.relations.values())
        self.con = duckdb.connect()
        self.results: dict[str, ModelResult] = {}
        self.proved: set[str] = set()
        """Unique ids of the tests proved so far, upstream first."""
        self.created: dict[str, str | None] = {}
        """Per relation, None once it is a table or view of the scratch
        database, else why not."""

    def run(self, select: set[str] | None) -> CheckResult:
        models = self.p.models
        if select:
            wanted = {m.unique_id for m in models if m.name in select}
            unknown = select - {m.name for m in models}
            if unknown:
                raise ValueError(f"no model named {', '.join(sorted(unknown))}")
            wanted = self._upstream(wanted)
            models = [m for m in models if m.unique_id in wanted]
        for m in models:
            self.results[m.unique_id] = self._model(m)
        shown = [r for r in self.results.values() if not select or r.name in select]
        return CheckResult(
            project=self.p.name,
            root=str(self.p.root),
            models=shown,
            tests={t.unique_id: t for t in self.p.tests.values()},
            unit_tests=self.p.unit_tests,
            relations=self.p.relations,
            selected=bool(select),
        )

    def _upstream(self, uids: set[str]) -> set[str]:
        out = set(uids)
        todo = list(uids)
        while todo:
            for d in self.p.relations[todo.pop()].depends_on:
                if d not in out and d in self.p.relations:
                    out.add(d)
                    todo.append(d)
        return out

    # ---- inputs -------------------------------------------------------------

    def _inputs(self, m: Relation) -> list[Relation]:
        """The relations `m`'s compiled SQL reads: its dependencies, with each
        ephemeral model replaced by what it reads, transitively. dbt inlines an
        ephemeral model into its consumer as a CTE, so the consumer's SQL names
        the ephemeral's inputs and never the ephemeral model."""
        out: dict[str, Relation] = {}

        def add(unique_id: str) -> None:
            r = self.p.relations.get(unique_id)
            if r is None or unique_id in out:
                return
            if r.is_model and r.materialized == "ephemeral":
                for d in r.depends_on:
                    add(d)
            else:
                out[unique_id] = r

        for d in m.depends_on:
            add(d)
        return list(out.values())

    def _ensure_relation(self, r: Relation) -> str | None:
        """Make `r` a table (sources, seeds) or view (models) of the scratch
        DuckDB database, with the project's column types; None when done,
        else why it cannot be."""
        if r.unique_id in self.created:
            return self.created[r.unique_id]
        why: str | None = None
        name = self.names[r.unique_id]
        if r.is_model:
            res = self.results.get(r.unique_id)
            if res is None or res.sql is None:
                why = f"{r.ref} could not be read" + (f" ({res.refused})" if res else "")
            else:
                try:
                    self.con.execute(f"CREATE VIEW {_q(name)} AS {res.sql}")
                except duckdb.Error as e:
                    why = f"DuckDB cannot plan {r.ref}: {_first_line(e)}"
        else:
            types = r.declared_types()
            if types is None:
                why = (
                    f"{r.ref} has no column types: give each of its columns a data_type in "
                    "its YAML, or run `dbt seed` (for a seed) and then `dbt docs generate`, so "
                    "that target/catalog.json has the types of the loaded table"
                )
            else:
                cols = ", ".join(f"{_q(c)} {t}" for c, t in types.items())
                try:
                    self.con.execute(f"CREATE TABLE {_q(name)} ({cols})")
                except duckdb.Error as e:
                    why = f"DuckDB does not know the column types of {r.ref}: {_first_line(e)}"
        self.created[r.unique_id] = why
        return why

    def _not_null(self, r: Relation) -> set[str]:
        """The columns of `r` its tests or contract keep from being NULL."""
        out = set()
        for t in self.p.tests_on(r.unique_id):
            if (
                self._holds(t)
                and t.kind
                in (
                    "not_null",
                    "dbt_expectations.expect_column_values_to_not_be_null",
                )
                and t.column
                and not t.where
                and not t.kwargs.get("row_condition")
            ):
                out.add(t.column)
        if r.contract:
            for c in r.columns.values():
                for k in c.constraints:
                    if k.get("type") in ("not_null", "primary_key"):
                        out.add(c.name)
            for k in r.constraints:
                if k.get("type") in ("not_null", "primary_key"):
                    out.update(k.get("columns") or [])
        return out

    def _holds(self, t: Test) -> bool:
        """The test holds when the model downstream runs: `dbt build` stops
        on its failure, or it is proved."""
        return t.blocks or t.unique_id in self.proved

    def _requires(self, m: Relation, inputs: list[Relation]) -> tuple[dict, list[str]]:
        """The preconditions per input table, and what was left out."""
        out: dict[str, list] = {}
        skipped: list[str] = []

        def table_of(uid: str) -> str | None:
            return self.names[uid] if uid in m.depends_on else None

        for r in inputs:
            name = self.names[r.unique_id]
            conds: list = []
            nn = self._not_null(r)
            for t in self.p.tests_on(r.unique_id):
                if not self._holds(t):
                    sev = t.severity.lower()
                    skipped.append(f"{r.ref}: {t.short} (severity {sev}, not proved)")
                    continue
                got = mapping.test_conditions(t, side="requires", table_of=table_of, not_null=nn)
                if got.conditions:
                    conds += got.conditions
                elif got.reason and t.kind != "relationships":
                    skipped.append(f"{r.ref}: {t.short}: {got.reason}")
            if r.is_model and r.contract:
                res = self.results.get(r.unique_id)
                for c in res.constraints if res else []:
                    if c.status == "proved":
                        conds += c.conditions
            out[name] = conds
        return out, skipped

    # ---- one model ----------------------------------------------------------

    def _model(self, m: Relation) -> ModelResult:
        res = ModelResult(
            name=m.name,
            unique_id=m.unique_id,
            path=m.path,
            ref=m.ref,
            enforced=bool(m.contract),
        )
        if m.materialized == "ephemeral":
            readers = sorted(r.name for r in self.p.models if m.unique_id in r.depends_on)
            res.notes.append(
                "ephemeral: dbt inlines it into "
                + (", ".join(readers) if readers else "no model")
                + " and runs no test on it; it is checked there"
            )
            for t in self.p.tests_on(m.unique_id):
                tr = TestResult(test=t.unique_id, name=t.name, label=t.short, kind="test")
                tr.skip("dbt runs no test on an ephemeral model")
                res.tests.append(tr)
            return res
        if m.language != "sql":
            return res.refuse(
                f"a {m.language} model: sverify reads SQL models only; dbt still runs its tests"
            )
        if not m.compiled_code:
            return res.refuse(
                "no compiled SQL in the manifest: run `dbt compile` (or `dbt build`) first; "
                "`dbt parse`, `dbt ls` and a `dbt test` without the model leave it out"
            )
        inputs = self._inputs(m)
        for r in inputs:
            why = self._ensure_relation(r)
            if why:
                return res.refuse(why)
        try:
            res.sql = _rewrite(
                m.compiled_code,
                {r.relation_name: self.names[r.unique_id] for r in inputs if r.relation_name},
                own=m.relation_name,
            )
        except _Unreadable as e:
            return res.refuse(str(e))
        try:
            out = self.con.execute(f"DESCRIBE {res.sql}").fetchall()
        except duckdb.Error as e:
            res.sql = None
            return res.refuse(
                f"DuckDB cannot plan the compiled SQL: {_first_line(e)}; sverify-dbt reads "
                "DuckDB projects (other adapters: see #271)"
            )
        res.duckdb_types = {row[0]: row[1] for row in out}
        # sverify reads DuckDB's type names (`verify(tables=...)`).
        tables = {
            self.names[r.unique_id]: {
                row[0]: row[1]
                for row in self.con.execute(
                    f"DESCRIBE SELECT * FROM {_q(self.names[r.unique_id])}"
                ).fetchall()
            }
            for r in inputs
        }
        requires, res.not_assumed = self._requires(m, inputs)
        ensures = self._ensures(m, res)
        report = self._verify(res, tables, requires, ensures)
        if report is None:
            return res
        self._read(report, m, res, ensures)
        self._blame_nulls(res, inputs, tables, requires, ensures)
        return res

    def _blame_nulls(
        self, res: ModelResult, inputs: list[Relation], tables: dict, requires: dict, ensures: list
    ) -> None:
        """For each test unproved because a row may fail it or a NULL may reach it, find the
        `not_null` tests on the inputs under which it holds: sverify suggests
        none for a NULL that comes through an expression. Tries every input
        column no test covers at once, then drops each that the proof does not
        need (`would_hold`)."""
        candidates = [
            (r, c)
            for r in inputs
            for c in tables[self.names[r.unique_id]]
            if c not in self._not_null(r)
        ]
        budget = [_BLAME_CALLS]
        for tr, cs in ensures:
            if (
                tr.status != "not proved"
                or tr.would_hold
                or tr.blocker not in ("may_be_false", "may_be_null")
            ):
                continue
            if len(candidates) > _BLAME_COLUMNS or budget[0] < 1:
                why = f"not searched for a source test: {len(candidates)} uncovered input columns"
                tr.why = f"{tr.why}; {why}" if tr.why else why
                continue
            budget[0] -= 1
            held = self._holds_with(res, tables, requires, cs, candidates)
            for pair in list(held or []):
                if budget[0] < 1:
                    break
                rest = [x for x in held or [] if x != pair]
                budget[0] -= 1
                if rest and self._holds_with(res, tables, requires, cs, rest):
                    held = rest
            for r, c in held or []:
                tr.would_hold.setdefault(r.ref, []).append((c, "not_null"))

    def _holds_with(
        self, res: ModelResult, tables: dict, requires: dict, cs: list, extra: list
    ) -> list | None:
        """`extra` (input, column) pairs when the conditions `cs` are proved
        with `IS NOT NULL` on each of them added to `requires`, else None."""
        if not extra:
            return None
        req = {t: list(v) for t, v in requires.items()}
        for r, c in extra:
            req[self.names[r.unique_id]].append(f"{mapping.ident(c)} IS NOT NULL")
        try:
            with warnings.catch_warnings():
                warnings.simplefilter("ignore")
                report = sv.verify(
                    res.sql,  # type: ignore[arg-type]
                    tables=tables,
                    requires=req,
                    ensures=cs,
                    semantics="duckdb",
                    on_inferred="error",
                    counterexamples=0,
                )
        except ValueError:
            return None
        return extra if all(c.portable for c in report.ensures) and not report.needs else None

    def _ensures(self, m: Relation, res: ModelResult) -> list[tuple[Any, list]]:
        """The conditions to prove, each with its test or constraint result."""
        cols = set(res.duckdb_types)
        out: list[tuple[Any, list]] = []
        for t in self.p.tests_on(m.unique_id):
            tr = TestResult(test=t.unique_id, name=t.name, label=t.short, kind="test")
            res.tests.append(tr)
            got = mapping.test_conditions(t, side="ensures", table_of=lambda _: None)
            missing = [c for c in got.columns if c not in cols]
            if got.schema:
                bad = got.schema(list(res.duckdb_types))
                tr.status, tr.why = ("proved", None) if bad is None else ("not proved", bad)
                if bad is None:
                    self.proved.add(t.unique_id)
            elif missing:
                tr.skip(f"the model has no column {', '.join(missing)}")
            elif not got.conditions:
                tr.skip(got.reason or "no condition")
            else:
                tr.conditions = got.conditions
                out.append((tr, got.conditions))
        if m.contract:
            pairs = [(c.name, k) for c in m.columns.values() for k in c.constraints]
            pairs += [(None, k) for k in m.constraints]
            for col, k in pairs:
                tr = TestResult(
                    test=None, name=None, label=mapping.constraint_label(k, col), kind="constraint"
                )
                res.constraints.append(tr)
                got = mapping.constraint_conditions(k, col)
                missing = [c for c in got.columns if c not in cols]
                if missing:
                    tr.skip(f"the model has no column {', '.join(missing)}")
                elif not got.conditions:
                    tr.skip(got.reason or "no condition")
                else:
                    tr.conditions = got.conditions
                    out.append((tr, got.conditions))
        return out

    def _verify(self, res: ModelResult, tables: dict, requires: dict, ensures: list) -> Any:
        """`sv.verify` of the model; a condition sverify cannot read is
        dropped with its reason, and a model it cannot read is refused."""

        def go(req: dict, ens: list) -> Any:
            with warnings.catch_warnings():
                warnings.simplefilter("ignore")
                return sv.verify(
                    res.sql,  # type: ignore[arg-type]
                    tables=tables,
                    requires=req,
                    ensures=ens,
                    semantics="duckdb",
                    on_inferred="error",
                    counterexamples=self.counterexamples,
                )

        while True:
            try:
                return go(requires, _checked(ensures))
            except ConditionError as e:  # drop the conditions it names, prove the rest (#699)
                if not self._drop(e, res, requires, ensures):
                    res.refuse(_refusal(e))
                    return None
            except ValueError as e:  # a refusal after planning: the model or a condition
                return self._isolate(go, res, requires, ensures, e)

    @staticmethod
    def _isolate(go: Any, res: ModelResult, requires: dict, ensures: list, first: Exception) -> Any:
        """A refusal `ConditionError` does not name (the checker's, after the
        plans exist): refuse the model if it fails alone, else prove each
        test's conditions on their own and skip the ones that fail."""
        none = {t: [] for t in requires}
        try:
            go(none, [])
        except ValueError:
            res.refuse(_refusal(first))
            return None
        for tr, cs in ensures:
            if tr.status == "not checked":
                continue
            try:
                go(none, cs)
            except ValueError as e:
                tr.skip(f"sverify cannot read its condition: {_first_line(e)}")
        try:
            return go(requires, _checked(ensures))
        except ValueError:
            res.refuse(_refusal(first))
            return None

    @staticmethod
    def _drop(e: ConditionError, res: ModelResult, requires: dict, ensures: list) -> bool:
        """Drop every condition `e` names, with its reason; False if it
        names none that is still there."""
        dropped = False
        for name, err in e.errors.items():
            for t, cs in requires.items():
                hit = [c for c in cs if _named(c) == name]
                if hit:
                    requires[t] = [c for c in cs if c not in hit]
                    res.not_assumed.append(
                        f"{t}: {_label(hit[0])}: sverify cannot read it ({_first_line(err)})"
                    )
                    dropped = True
            for tr, cs in ensures:
                if tr.status != "not checked" and any(_named(c) == name for c in cs):
                    tr.skip(f"sverify cannot read its condition: {_first_line(err)}")
                    dropped = True
        return dropped

    def _read(self, report: Any, m: Relation, res: ModelResult, ensures: list) -> None:
        # `report.ensures` is in the order of the conditions given, each
        # with its condition (`CheckedCondition.condition`).
        results = iter(report.ensures)
        needed = report.needs
        res.needed = _needed(report, self, m)
        res.may_fail = [str(i) for i in report.errors]
        res.deterministic = report.deterministic
        if not report.deterministic:
            res.notes.append(
                "rows may tie in an ORDER BY of a window or ordered aggregate, so DuckDB "
                "picks the order: a test that depends on it is not proved"
            )
        res.assumed = [i.shown or i.expr for i in report.assumed]
        for tr, cs in ensures:
            if tr.status == "not checked":
                continue
            checked = [next(results) for _ in cs]
            if any(r.condition is not c for r, c in zip(checked, cs, strict=True)):
                tr.skip("sverify reported on another condition")
                continue
            bad = [c for c in checked if not c.portable]
            if not bad and needed:
                tr.status = "not proved"
                tr.why = "proved only with the source tests listed under 'needs'"
            elif not bad:
                tr.status = "proved"
            else:
                c = bad[0]
                tr.status = "not proved"
                tr.why = _why(c)
                tr.blocker = c.reason
                tr.counterexample = str(c.counterexample) if c.counterexample else None
                tr.would_hold = {
                    _user_table(t, self): [mapping.as_dbt_test(_sql(x)) for x in xs]
                    for t, xs in (c.suggested or {}).items()
                }
            if tr.status == "proved" and tr.test:
                self.proved.add(tr.test)
        if m.materialized == "incremental":
            self._incremental(m, res)
        if m.contract:
            res.contract = self._contract(report, m, res)

    def _incremental(self, m: Relation, res: ModelResult) -> None:
        """An incremental model is checked as its full refresh, as compiled; its
        `is_incremental()` block is taken to only filter that query. An
        incremental run writes rows the full-refresh proof does not cover, so a
        proved test stays out of the skippable set unless the strategy keeps
        the model's key unique: `merge` or `delete+insert` on a `unique_key`
        that a proved `unique` test of the model names (the batch is unique on
        it, and each key is replaced). Then only the tests the old rows plus the
        batch still satisfy stay skippable: a row-level test (each row is
        checked alone) and a `unique` over a superset of the key."""
        key = set(m.unique_key or [])
        by_key = m.incremental_strategy in ("merge", "delete+insert") and key
        unique = by_key and any(
            t.status == "proved" and _unique_on(self.p.tests.get(t.test or "")) == key
            for t in res.tests
        )
        head = (
            "an incremental model, checked as its full refresh "
            "(its `is_incremental()` block only filters it)"
        )
        if unique:
            for t in res.tests:
                test = self.p.tests.get(t.test or "")
                cols = _unique_on(test)
                t.skippable = (cols is not None and key <= cols) or (
                    cols is None and _row_level(test)
                )
            kept = [t.name for t in res.tests if t.status == "proved" and not t.skippable]
            res.notes.append(
                f"{head}: {m.incremental_strategy} on {', '.join(sorted(key))} keeps that key "
                "unique, so its row-level tests and `unique` over that key may be skipped"
                + (
                    f"; dbt build still runs {', '.join(sorted(n for n in kept if n))}"
                    if kept
                    else ""
                )
            )
            return
        for t in res.tests:
            t.skippable = False
        res.notes.append(
            f"{head}: its tests hold for the full refresh; an incremental run "
            f"({m.incremental_strategy or 'default strategy'}"
            + (f" on {', '.join(sorted(key))}" if key else "")
            + ") can still break them, so dbt build keeps running them (proving the "
            "incremental branch is a follow-up)"
        )

    def _contract(self, report: Any, m: Relation, res: ModelResult) -> list[ContractIssue]:
        """The declared columns and types against the proved output schema
        (`Report.output`) and DuckDB's own types for the compiled SQL."""
        issues: list[ContractIssue] = []
        proved = {c: _duck_name(self.con, _ibis_to_duckdb(t)) for c, t in report.output.items()}
        actual = {c: _duck_name(self.con, t) for c, t in res.duckdb_types.items()}
        declared = {c.name: c.data_type for c in m.columns.values()}
        for c in declared:
            if c not in actual:
                issues.append(ContractIssue(c, "declared, but the model has no such column"))
        for c in actual:
            if c not in declared:
                issues.append(ContractIssue(c, "in the model's result, but not declared"))
        for c, t in declared.items():
            if c not in actual:
                continue
            if t is None:
                issues.append(ContractIssue(c, "declared without a data_type"))
                continue
            want = _duck_name(self.con, t)
            if want != actual[c]:
                issues.append(ContractIssue(c, f"declared {t}, but DuckDB gives {actual[c]}"))
            if proved.get(c) and proved[c] != actual[c]:
                res.notes.append(
                    f"column {c}: sverify's plan has type {proved[c]}, and DuckDB's SQL gives "
                    f"{actual[c]}; the contract check uses DuckDB's"
                )
        return issues


# ---- helpers ------------------------------------------------------------------


class _Unreadable(Exception):
    pass


def _input_names(relations: Iterable[Relation]) -> dict[str, str]:
    """A table name per relation, unique across the project: the model's or
    seed's name, a source's table name, or `<source>__<table>` where two
    collide."""
    rels = list(relations)
    counts: dict[str, int] = {}
    for r in rels:
        counts[r.name] = counts.get(r.name, 0) + 1
    out = {}
    for r in rels:
        name = r.name
        if counts[name] > 1 and r.resource_type == "source":
            name = f"{r.source_name}__{r.name}"
        if counts[r.name] > 1 and r.resource_type in ("seed", "snapshot"):
            name = f"{r.resource_type}__{r.name}"
        out[r.unique_id] = name
    return out


def _parts(t: sg.exp.Table) -> tuple[str, ...]:
    return tuple(p.lower() for p in (t.catalog, t.db, t.name) if p)


def _rewrite(sql: str, inputs: dict[str, str], own: str | None = None) -> str:
    """`sql` with each relation of `inputs` (dbt's `relation_name`) read by
    its input name, keeping what the query calls it (its alias, else its
    table name)."""
    try:
        tree = sg.parse_one(sql, read="duckdb")
    except sg.errors.ParseError as e:
        raise _Unreadable(f"the compiled SQL does not parse: {_first_line(e)}") from e
    wanted = {}
    for rel, name in inputs.items():
        t = sg.exp.to_table(rel, dialect="duckdb")
        wanted[_parts(t)] = name
    ctes = {c.alias_or_name.lower() for c in tree.find_all(sg.exp.CTE)}

    def find(t: sg.exp.Table) -> str | None:
        parts = _parts(t)
        if parts in wanted:
            return wanted[parts]
        hits = [n for p, n in wanted.items() if p[-len(parts) :] == parts]
        return hits[0] if len(hits) == 1 else None

    own_parts = _parts(sg.exp.to_table(own, dialect="duckdb")) if own else None
    unknown = []
    for t in list(tree.find_all(sg.exp.Table)):
        if not isinstance(t.this, sg.exp.Identifier):
            continue
        if not t.db and not t.catalog and t.name.lower() in ctes:
            continue
        name = find(t)
        if name is None and own_parts and _parts(t) == own_parts:
            raise _Unreadable(
                "it reads its own table, `{{ this }}`: this compile rendered the "
                "`is_incremental()` branch, since the model has run; compile with "
                "`dbt compile --full-refresh`"
            )
        if name is None:
            unknown.append(t.sql("duckdb"))
            continue
        alias = t.alias or t.name
        new = sg.exp.to_table(_q(name), dialect="duckdb")
        if alias != name:
            new.set("alias", sg.exp.TableAlias(this=sg.exp.to_identifier(alias)))
        t.replace(new)
    if unknown:
        raise _Unreadable(
            f"it reads {', '.join(dict.fromkeys(unknown))}, which is no ref or source of the "
            "model (a hard-coded table name, or one a macro wrote); read it with "
            "{{ ref() }} or {{ source() }}"
        )
    return tree.sql("duckdb")


def _q(name: str) -> str:
    return '"' + name.replace('"', '""') + '"'


def _checked(ensures: list) -> list:
    """The conditions of the tests still to check, in order."""
    return [c for tr, cs in ensures if tr.status != "not checked" for c in cs]


def _first_line(e: BaseException) -> str:
    lines = str(e).strip().splitlines()
    return lines[0] if lines else type(e).__name__


def _refusal(e: BaseException) -> str:
    """sverify's refusal of a model, in the user's terms: all of its message,
    so the exit sverify names at its end stays."""
    msg = " ".join(str(e).split()) or type(e).__name__
    m = re.match(r"(.*?) is not supported(?: yet)?;?(.*)", msg)
    if m:
        what = m[1].strip()
        if len(what) > 70:
            what = what[:67] + "..."
        rest = m[2].strip()
        if rest and not rest.startswith("("):
            rest = f"({rest})"
        return f"sverify cannot read {what} yet" + (f" {rest}" if rest else "")
    return f"sverify cannot check it: {msg}"


_WHY = {
    "observation": "proved only for some row orders DuckDB may pick",
    "not_a_key": "the tests upstream do not make it a key",
    "ties": "rows may tie in an ORDER BY, so DuckDB picks which rows it keeps",
    "always_false": "every row fails it",
    "may_be_false": "sverify cannot rule out a row that fails it, from the tests upstream",
    "may_be_null": "sverify cannot rule out a row that fails it, from the tests upstream",
    "not_proved_kind": "sverify checks this kind of condition on data only",
}


def _why(c: Any) -> str:
    """Why a condition is not proved, in a dbt user's terms
    (`CheckedCondition.reason`; its `why` speaks of `sv.unique` and
    `requires`)."""
    return _WHY.get(c.reason, f"sverify only knows it is {c.value}")


def _named(c: Any) -> str:
    """A condition as the keys of `ConditionError.errors` name it."""
    return condition_label(c)


def _label(c: Any) -> str:
    return c if isinstance(c, str) else c.label


def _sql(c: Any) -> str:
    """A suggested condition as SQL, as far as it can be."""
    return str(c) if isinstance(c, str) else getattr(c, "label", str(c))


def _user_table(name: str, checker: _Checker) -> str:
    for uid, n in checker.names.items():
        if n == name:
            return checker.p.relations[uid].ref
    return name


#: Tests that judge each row alone: the old rows and a batch satisfy them
#: whatever the strategy, as the batch's rows do.
_ROW_LEVEL = frozenset(
    {
        "not_null",
        "expect_column_values_to_not_be_null",
        "expect_column_values_to_be_null",
        "accepted_values",
        "expect_column_values_to_be_in_set",
        "expect_column_values_to_not_be_in_set",
        "accepted_range",
        "expect_column_values_to_be_between",
        "expression_is_true",
        "not_accepted_values",
        "not_empty_string",
        "expect_column_values_to_match_regex",
        "expect_column_values_to_not_match_regex",
        "expect_column_values_to_match_regex_list",
        "expect_column_values_to_not_match_regex_list",
        "expect_column_values_to_match_like_pattern",
        "expect_column_values_to_not_match_like_pattern",
        "expect_column_values_to_match_like_pattern_list",
        "expect_column_values_to_not_match_like_pattern_list",
        "expect_column_value_lengths_to_equal",
        "expect_column_value_lengths_to_be_between",
        "expect_column_pair_values_A_to_be_greater_than_B",
        "expect_column_pair_values_to_be_equal",
    }
)


def _row_level(t: Any) -> bool:
    return t is not None and bool(t.kind) and t.kind.split(".")[-1] in _ROW_LEVEL


def _unique_on(t: Any) -> set[str] | None:
    """The columns a `unique` test (without a `where`) says are unique."""
    if t is None or t.where or not t.kind:
        return None
    base = t.kind.split(".")[-1]
    if base == "unique" and t.column:
        return {t.column}
    if base == "unique_combination_of_columns":
        return set(t.kwargs.get("combination_of_columns") or []) or None
    return None


def _needed(report: Any, checker: _Checker, m: Relation) -> list[Needed]:
    """`Report.needs` as tests to add to the inputs."""
    out = []
    for n in report.needs:
        issue = n.issue
        out.append(
            Needed(
                on=_user_table(n.table, checker),
                column=n.column,
                test=mapping.dbt_test(n.column, n.op, n.value, n.sql),
                because=(
                    f"{issue.kind} in `{issue.shown or issue.expr}` otherwise" if issue else None
                ),
                condition=n.sql,
            )
        )
    return out


def _ibis_to_duckdb(t: Any) -> str:
    from ibis.backends.sql.datatypes import DuckDBType

    return DuckDBType.to_string(t)


def _duck_name(con: duckdb.DuckDBPyConnection, t: str) -> str:
    """DuckDB's own name of a type: `int` is INTEGER, `text` VARCHAR."""
    try:
        row = con.execute(f"SELECT typeof(CAST(NULL AS {t}))").fetchone()
        return str(row[0]) if row else t.upper()
    except duckdb.Error:
        return t.upper()
