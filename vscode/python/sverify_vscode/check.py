"""Run a Python file and check what it defines with sverify's public API,
then turn each report into what the editor shows: diagnostics with quick
fixes, hovers, code lenses and the contract sites completion reads.

The file runs as a module named `__sverify_check__`, so code under
`if __name__ == "__main__":` (runs on data, refreshes) does not run. Then:

- each `sv.ContractedTransform` in the module's globals is checked with
  `ContractedTransform.check` on the module's unbound tables
  (`ibis.table(schema, name=...)`) named like its parameters, or else its
  `last_report` is read, where the file called it;
- each `sv.Report` the module assigned to a name is matched with the
  `sv.verify(...)` call assigned to that name.

Only names `sverify` exports and the documented fields of what they return
are used (`UX-NOTES.md`, "Public API gaps").
"""

from __future__ import annotations

import ast
import contextlib
import difflib
import inspect
import io
import json
import os
import re
import runpy
import sys
import time
import traceback
import warnings
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any

import ibis
import ibis.expr.operations as ops
import sverify as sv

from .source import (
    CONTRACT_HELPERS,
    Edit,
    Range,
    Site,
    Source,
    Subject,
    add_requires,
    find_expr,
    import_datetime,
    import_underscore,
    label_code,
    sites,
    sql_strings,
    strip_parens,
    subjects,
)

ENGINES = ("duckdb", "polars")
ERROR, WARNING, INFO, HINT = 0, 1, 2, 3


@dataclass
class Record:
    """What one check of a subject produced."""

    report: sv.Report | None = None
    error: str | None = None
    inputs: dict[str, dict[str, str]] = field(default_factory=dict)
    output: dict[str, str] = field(default_factory=dict)
    seconds: float | None = None  # None: the file's own call, not timed


@dataclass
class Collected:
    """What a run of the file left: records of its transforms, by the first
    line of their definition, and of its reports, by the name they were
    assigned to."""

    transforms: dict[int, Record] = field(default_factory=dict)
    reports: dict[str, Record] = field(default_factory=dict)


def _types(schema: Any) -> dict[str, str]:
    return {n: str(t) for n, t in schema.items()}


def _report_record(report: sv.Report) -> Record:
    return Record(
        report=report,
        inputs={t: _types(s) for t, s in report.inputs.items()},
        output=_types(report.output),
    )


def _fresh_modules(root: Path) -> None:
    """Forget modules of the workspace, so a check reads them again."""
    for name, mod in list(sys.modules.items()):
        f = getattr(mod, "__file__", None)
        if f and Path(f).resolve().is_relative_to(root) and "site-packages" not in f:
            del sys.modules[name]


def _unbound(value: Any) -> bool:
    return isinstance(value, ibis.Table) and isinstance(value.op(), ops.UnboundTable)


def collect(path: str, globs: dict, counterexamples: int | None) -> Collected:
    """Check the transforms and read the reports of a module's globals."""
    p = Path(path).resolve()
    out = Collected()
    tables: dict[str, ibis.Table] = {}
    for name, v in globs.items():
        if _unbound(v):
            tables.setdefault(v.get_name(), v)
            tables[name] = v
    for name, v in globs.items():
        if isinstance(v, sv.Report):
            out.reports[name] = _report_record(v)
        if not isinstance(v, sv.ContractedTransform):
            continue
        fn = inspect.unwrap(v)
        code = getattr(fn, "__code__", None)
        if code is None or Path(code.co_filename).resolve() != p:
            continue
        params = list(inspect.signature(v).parameters)
        args = {q: tables[q] for q in params if q in tables}
        if len(args) == len(params) and params:
            rec = Record(inputs={q: _types(t.schema()) for q, t in args.items()})
            t0 = time.perf_counter()
            try:
                rec.report = v.check(**args)
                rec.output = _types(rec.report.output)
            except Exception as e:  # noqa: BLE001 - shown on the transform
                rec.error = f"{type(e).__name__}: {e}"
            rec.seconds = time.perf_counter() - t0
        elif v.last_report is not None:
            rec = _report_record(v.last_report)
        else:
            continue
        out.transforms[code.co_firstlineno] = rec
    return out


def run_file(path: str, counterexamples: int | None = None) -> tuple[Collected, dict]:
    """Run the file, then check what it defines. Returns what was collected
    and the exception the run ended with (empty if none)."""
    p = Path(path).resolve()
    _fresh_modules(p.parent)
    sys.path.insert(0, str(p.parent))
    failure: dict = {}
    globs: dict = {}
    # The budget of the file's own sv.verify calls and transform calls.
    before = os.environ.get("SVERIFY_COUNTEREXAMPLES")
    if counterexamples is not None:
        os.environ["SVERIFY_COUNTEREXAMPLES"] = str(counterexamples)
    try:
        with warnings.catch_warnings(), contextlib.redirect_stdout(io.StringIO()):
            warnings.simplefilter("ignore")
            try:
                globs = runpy.run_path(str(p), run_name="__sverify_check__")
            except Exception as e:  # noqa: BLE001 - shown as a diagnostic
                tb = traceback.extract_tb(e.__traceback__)
                line = next((f.lineno for f in reversed(tb) if Path(f.filename).resolve() == p), None)
                failure = {"message": f"{type(e).__name__}: {e}", "line": line}
                frame = e.__traceback__
                while frame is not None:
                    if Path(frame.tb_frame.f_code.co_filename).resolve() == p:
                        globs = dict(frame.tb_frame.f_globals)
                    frame = frame.tb_next
            collected = collect(path, globs, counterexamples)
    finally:
        sys.path.remove(str(p.parent))
        if before is None:
            os.environ.pop("SVERIFY_COUNTEREXAMPLES", None)
        else:
            os.environ["SVERIFY_COUNTEREXAMPLES"] = before
    return collected, failure


# -- what the editor shows ---------------------------------------------------


def _diag(rng: Range, severity: int, message: str, code: str, subject: int, fixes=(), related=()) -> dict:
    return {
        "range": list(rng),
        "severity": severity,
        "message": message,
        "code": code,
        "subject": subject,
        "fixes": list(fixes),
        "related": list(related),
    }


def _fix(title: str, edits: list[Edit | None], preferred: bool = False, preview: bool = True) -> dict | None:
    real = [e for e in edits if e is not None]
    if not real:
        return None
    return {"title": title, "edits": [e.json() for e in real], "preferred": preferred, "preview": preview}


#: The codes the fixes of the subject being built add to `requires`, per table.
_PENDING: dict[str, list[str]] = {}


def _add(src: Source, s: Subject, table: str, codes: list[str], tables: list[str]) -> Edit | None:
    """`add_requires`, remembered for the subject's "add all" fix."""
    have = _PENDING.setdefault(table, [])
    have += [c for c in codes if c not in have]
    return add_requires(src, s, table, codes, tables)


class Checked:
    """One file's check, as JSON for the client."""

    def __init__(self, src: Source, rec: Collected, failure: dict, seconds: float):
        self.src, self.rec = src, rec
        self.diagnostics: list[dict] = []
        self.hovers: list[dict] = []
        self.lenses: list[dict] = []
        self.sites: list[dict] = []
        self.subjects: list[dict] = []
        self.seconds = seconds
        self.failure = failure
        self._build()

    def json(self) -> dict:
        return {
            "file": self.src.path,
            "seconds": round(self.seconds, 3),
            "subjects": self.subjects,
            "diagnostics": self.diagnostics,
            "hovers": self.hovers,
            "lenses": self.lenses,
            "sites": self.sites,
        }

    # -- matching records to the source -------------------------------------

    def _records(self) -> list[tuple[Subject, Record | None]]:
        out = []
        for s in subjects(self.src):
            rec: Record | None = None
            if s.kind == "transform":
                first = s.node.decorator_list[0].lineno if s.node.decorator_list else s.node.lineno
                rec = self.rec.transforms.get(first) or self.rec.transforms.get(s.node.lineno)
            else:
                rec = self.rec.reports.get(s.name)
            out.append((s, rec))
        return out

    def _build(self) -> None:
        if self.failure:
            line = (self.failure.get("line") or 1) - 1
            self.diagnostics.append(
                _diag(
                    self.src.line_range(line),
                    ERROR,
                    f"sverify stopped here: {self.failure['message']}",
                    "run",
                    -1,
                )
            )
        for i, (s, rec) in enumerate(self._records()):
            self._subject(i, s, rec)

    def _subject(self, i: int, s: Subject, rec: Record | None) -> None:
        src = self.src
        anchor = src.range(s.anchor) if s.kind == "verify" else _name_range(src, s.node)
        self._validate_tables(i, s)
        if rec is None:
            if s.kind == "transform":
                params = ", ".join(s.params)
                msg = (
                    f"not checked: sverify has no schema for {params}. Define module-level "
                    f"unbound tables named {params} (ibis.table(schema, name=...))"
                )
                self.diagnostics.append(_diag(anchor, INFO, msg, "no-schema", i))
            elif not self.failure:
                msg = "not checked: assign the report to a name (report = sv.verify(...))"
                self.diagnostics.append(_diag(anchor, INFO, msg, "no-report", i))
            self.subjects.append({"kind": s.kind, "name": s.name, "range": list(anchor), "checked": False})
            return
        report = rec.report
        tables = list(rec.inputs) or (list(report.requires) if report else []) or s.params
        if s.kind == "transform" and s.params:
            tables = s.params
        site_list = sites(src, s, tables)
        for site in site_list:
            cols = rec.output if site.role == "ensures" else rec.inputs.get(site.table or "", {})
            self.sites.append(
                {
                    "range": list(src.range(site.node)),
                    "role": site.role,
                    "table": site.table,
                    "columns": cols,
                    "subject": i,
                }
            )
            self._validate(i, site, cols)
        flagged = any(d["subject"] == i and d["code"] == "unknown-column" for d in self.diagnostics)
        if flagged and rec.error and "has no attribute" in rec.error:
            pass  # the contract's unknown column, flagged where it is written
        elif rec.error:
            self.diagnostics.append(_diag(anchor, ERROR, rec.error, "error", i))
        if report is None:
            self.subjects.append({"kind": s.kind, "name": s.name, "range": list(anchor), "checked": False})
            return
        route_info = _routes(report)
        _PENDING.clear()
        first = len(self.diagnostics)
        self._ensures(i, s, report, site_list, tables)
        self._issues(i, s, report, tables)
        self._ties(i, s, report, tables, route_info)
        self._add_all(s, tables, self.diagnostics[first:])
        summary = _summary(report, route_info, rec.seconds)
        self.lenses.append({"range": list(anchor), "title": summary, "subject": i})
        md = _subject_markdown(s, report, route_info, rec)
        self.hovers.append({"range": list(anchor), "markdown": md})
        self._column_hovers(s, report, rec, site_list)
        self.subjects.append(
            {
                "kind": s.kind,
                "name": s.name,
                "range": list(anchor),
                "checked": True,
                "proved": report.proved,
                "seconds": None if rec.seconds is None else round(rec.seconds, 3),
                "summary": summary,
                "routes": route_info,
                "report": str(report),
            }
        )

    # -- postconditions -------------------------------------------------------

    def _ensures(
        self, i: int, s: Subject, report: sv.Report, site_list: list[Site], tables: list[str]
    ) -> None:
        src = self.src
        ens = next((x for x in site_list if x.role == "ensures"), None)
        items = ens.items if ens else []
        for k, c in enumerate(report.ensures):
            node = items[k] if len(items) == len(report.ensures) else _by_label(src, items, c.label)
            rng = (
                src.range(node)
                if node is not None
                else _name_range(src, s.node)
                if s.kind == "transform"
                else src.range(s.anchor)
            )
            if c.proved and not c.ignores:
                self.hovers.append({"range": list(rng), "markdown": f"**proved**: `{c.label}` — {c.value}"})
                continue
            if c.proved:
                msg = c.message
                self.diagnostics.append(_diag(rng, WARNING, msg, "observation", i))
                continue
            msg = c.message
            if c.counterexample is not None:
                msg += f"\ncounterexample: {c.counterexample}"
            fixes = []
            for t, labs in report.suggestions.get(c.label, {}).items():
                codes = [label_code(lab, src.sv, src.datetime) for lab in labs]
                fixes.append(
                    _fix(
                        f"Add {', '.join(codes)} to requires of {t}",
                        [_add(src, s, t, codes, tables), *_imports(src, codes)],
                        preferred=True,
                    )
                )
            if c.value == "not shown to be a key" and len(tables) == 1:
                m = re.fullmatch(r"unique\((.*)\)", c.label)
                if m:
                    code = label_code(c.label, src.sv, src.datetime)
                    fixes.append(
                        _fix(
                            f"Add {code} to requires of {tables[0]}",
                            [_add(src, s, tables[0], [code], tables)],
                        )
                    )
            if (
                c.nullable
                and len(tables) == 1
                and c.label not in report.suggestions
                and c.value != "not shown to be a key"
            ):
                codes = [f"_.{col}.notnull()" for col in c.nullable if col in self._input_cols(s, tables[0])]
                if codes:
                    fixes.append(
                        _fix(
                            f"Add {', '.join(codes)} to requires of {tables[0]}",
                            [_add(src, s, tables[0], codes, tables), import_underscore(src)],
                        )
                    )
            self.diagnostics.append(_diag(rng, ERROR, msg, "not-proved", i, [f for f in fixes if f]))

    def _input_cols(self, s: Subject, table: str) -> dict[str, str]:
        for site in self.sites:
            if site["role"] == "requires" and site["table"] == table:
                return site["columns"]
        return {}

    def _add_all(self, s: Subject, tables: list[str], diags: list[dict]) -> None:
        """One fix that adds every precondition the subject's fixes add."""
        n = sum(len(v) for v in _PENDING.values())
        if n < 2 or (s.requires is None and len(_PENDING) > 1):
            return
        edits = [add_requires(self.src, s, t, codes, tables) for t, codes in _PENDING.items()]
        codes = [c for v in _PENDING.values() for c in v]
        fix = _fix(
            f"Add all {n} preconditions sverify suggests for {s.name}", [*edits, *_imports(self.src, codes)]
        )
        for d in diags:
            if fix and d["code"] in {"needs", "not-proved", "may-fail", "ties", "assumed"} and d["fixes"]:
                d["fixes"].append(fix)

    # -- runtime errors, inferred and assumed preconditions -------------------

    def _where(self, s: Subject, shown: str | None) -> tuple[ast.AST | None, Range]:
        if shown:
            node, rng = find_expr(self.src, shown, s.body)
            if rng is not None:
                return node, rng
        return None, _name_range(self.src, s.node) if s.kind == "transform" else self.src.range(s.anchor)

    def _issues(self, i: int, s: Subject, report: sv.Report, tables: list[str]) -> None:
        src = self.src
        # Needed preconditions (on_inferred="error"), grouped by operation.
        for t, labs in report.needed.items():
            groups: dict[str, list[str]] = {}
            for lab in labs:
                issue = report.inferred_from.get(lab)
                groups.setdefault(issue.shown or issue.what if issue else lab, []).append(lab)
            for shown, group in groups.items():
                issues = [report.inferred_from[g] for g in group if g in report.inferred_from]
                node, rng = self._where(s, shown)
                kinds = " or ".join(dict.fromkeys(x.kind for x in issues))
                codes = [label_code(g, src.sv, src.datetime) for g in group]
                msg = f"needs {' and '.join(f'`{c}`' for c in codes)} on {t}"
                if issues:
                    msg += f": `{shown}` may fail with {kinds} otherwise"
                fixes = [
                    _fix(
                        f"Add {', '.join(codes)} to requires of {t}",
                        [_add(src, s, t, codes, tables), *_imports(src, codes)],
                        preferred=True,
                    ),
                    self._filter_fix(s, t, codes),
                    *self._guard_fixes(node, issues, src),
                ]
                self.diagnostics.append(_diag(rng, ERROR, msg, "needs", i, [f for f in fixes if f]))
        # Inferred and assumed silently ("warn" and "silent").
        if not report.needed:
            for t, labs in _inferred(report).items():
                for lab in labs:
                    issue = report.inferred_from.get(lab)
                    node, rng = self._where(s, issue.shown if issue else None)
                    code = label_code(lab, src.sv, src.datetime)
                    self.diagnostics.append(
                        _diag(
                            rng,
                            INFO,
                            f"assumes `{code}` on {t} (inferred; checked on the data)",
                            "inferred",
                            i,
                            [
                                f
                                for f in [
                                    _fix(
                                        f"State {code} in requires of {t}", [_add(src, s, t, [code], tables)]
                                    )
                                ]
                                if f
                            ],
                        )
                    )
        for issue in report.assumed:
            node, rng = self._where(s, issue.shown)
            msg = f"assumes: {issue.assumption}"
            hints = _hints_for(report, issue)
            if hints:
                msg += "\nhint: " + "\nhint: ".join(hints)
            self.diagnostics.append(_diag(rng, INFO, msg, "assumed", i))
        for issue in report.errors:
            if issue in report.assumed:
                continue
            node, rng = self._where(s, issue.shown)
            msg = f"may fail: {issue.message}"
            if issue.hint:
                msg += f"\nhint: {issue.hint}"
            fixes = []
            for t, labs in issue.suggested.items():
                codes = [label_code(lab, src.sv, src.datetime) for lab in labs]
                fixes.append(
                    _fix(
                        f"Add {', '.join(codes)} to requires of {t}",
                        [_add(src, s, t, codes, tables), *_imports(src, codes)],
                        preferred=True,
                    )
                )
            fixes += self._guard_fixes(node, [issue], src)
            self.diagnostics.append(_diag(rng, ERROR, msg, "may-fail", i, [f for f in fixes if f]))

    def _filter_fix(self, s: Subject, table: str, codes: list[str]) -> dict | None:
        """Filter the input first: rows that need the condition are dropped."""
        if s.kind != "transform" or table not in s.params or not s.node.body:
            return None
        first = s.node.body[0]
        if isinstance(first, ast.Expr) and isinstance(first.value, ast.Constant) and len(s.node.body) > 1:
            first = s.node.body[1]
        indent = self.src.indent_of(first.lineno)
        line = first.lineno - 1
        text = f"{indent}{table} = {table}.filter({', '.join(codes)})\n"
        return _fix(
            f"Drop the rows of {table} that fail {' and '.join(codes)} (filter first)",
            [Edit((line, 0, line, 0), text)],
        )

    def _guard_fixes(self, node: ast.AST | None, issues: list[Any], src: Source) -> list[dict]:
        """A CASE guard for a division by zero: NULL where the divisor is 0."""
        if not any(x.kind == "division by zero" for x in issues):
            return []
        if isinstance(node, ast.BinOp) and isinstance(node.op, (ast.Div, ast.FloorDiv, ast.Mod)):
            whole = src.segment(node)
            right = src.segment(node.right)
            prefix = "ibis" if src.has_ibis else "__import__('ibis')"
            text = f"{prefix}.ifelse({right} != 0, {whole}, None)"
            return [
                f
                for f in [
                    _fix(f"Guard the division: NULL where {right} is 0 (CASE)", [Edit(src.range(node), text)])
                ]
                if f
            ]
        if node is None:
            # A SQL division: CASE WHEN b <> 0 THEN a / b END
            out = []
            for issue in issues:
                if issue.kind != "division by zero" or not issue.shown:
                    continue
                m = re.fullmatch(r"(.+?)\s*(//|/|%)\s*(.+)", issue.shown)
                if not m:
                    continue
                for s_node in sql_strings(list(ast.walk(src.tree))):
                    raw = src.segment(s_node)
                    rx = re.compile(
                        r"((?:\w+\.)?"
                        + re.escape(m[1])
                        + r")\s*"
                        + ("(?://|/)" if m[2] == "//" else re.escape(m[2]))
                        + r"\s*((?:\w+\.)?"
                        + re.escape(m[3])
                        + r")\b",
                        re.IGNORECASE,
                    )
                    hit = rx.search(raw)
                    if hit:
                        base = src.node_offset(s_node)
                        rng = (*src.offset_pos(base + hit.start()), *src.offset_pos(base + hit.end()))
                        text = f"CASE WHEN {hit[2]} <> 0 THEN {hit[0]} END"
                        out.append(
                            _fix(f"Guard the division: NULL where {hit[2]} is 0 (CASE)", [Edit(rng, text)])
                        )
                        break
            return [f for f in out if f]
        return []

    # -- ties ------------------------------------------------------------------

    def _ties(self, i: int, s: Subject, report: sv.Report, tables: list[str], route_info: dict) -> None:
        src = self.src
        rng = _name_range(src, s.node) if s.kind == "transform" else src.range(s.anchor)
        suggestions: dict[str, list[str]] = {t: list(v) for t, v in report.ties.items()}
        for info in route_info.values():
            for t, labs in info.get("suggested", {}).items():
                for lab in labs:
                    if lab not in suggestions.setdefault(t, []):
                        suggestions[t].append(lab)
        if not report.deterministic or suggestions:
            fixes = []
            for t, labs in suggestions.items():
                codes = [label_code(lab, src.sv, src.datetime) for lab in labs]
                fixes.append(
                    _fix(
                        f"Add {', '.join(codes)} to requires of {t}",
                        [_add(src, s, t, codes, tables)],
                        preferred=True,
                    )
                )
            msg = report.notes[0] if not report.deterministic else "a route suggests more preconditions"
            self.diagnostics.append(_diag(rng, WARNING, msg, "ties", i, [f for f in fixes if f]))

    # -- validation and hovers of contracts -------------------------------------

    def _validate(self, i: int, site: Site, cols: dict[str, str]) -> None:
        """Columns a contract names that its table lacks."""
        if not cols:
            return
        src = self.src
        where = "the output" if site.role == "ensures" else site.table
        for item in site.items:
            for name, rng in _columns_named(src, item):
                if name in cols:
                    continue
                near = difflib.get_close_matches(name, list(cols), n=1)
                msg = (
                    f"{where} has no column `{name}`"
                    + (f"; did you mean `{near[0]}`?" if near else "")
                    + f" (columns: {', '.join(cols)})"
                )
                fixes = (
                    [_fix(f"Change to `{near[0]}`", [Edit(rng, near[0])], preferred=True, preview=False)]
                    if near
                    else []
                )
                self.diagnostics.append(_diag(rng, ERROR, msg, "unknown-column", i, [f for f in fixes if f]))
            if isinstance(item, ast.Call) and isinstance(item.func, ast.Attribute):
                if (
                    item.func.attr not in CONTRACT_HELPERS
                    and item.func.attr in {"within", "equivalent"}
                    and site.role == "requires"
                ):
                    self.diagnostics.append(
                        _diag(
                            src.range(item), ERROR, f"sv.{item.func.attr} belongs in ensures", "misplaced", i
                        )
                    )

    def _validate_tables(self, i: int, s: Subject) -> None:
        """`requires` keys that name no parameter of the transform."""
        if s.kind != "transform":
            return
        req = self.src.resolve(s.requires, s.node)
        if not isinstance(req, ast.Dict):
            return
        for k in req.keys:
            if isinstance(k, ast.Constant) and isinstance(k.value, str) and k.value not in s.params:
                near = difflib.get_close_matches(k.value, s.params, n=1)
                rng = self.src.range(k)
                msg = f"{s.name} has no parameter {k.value!r}: requires is keyed by parameter name"
                msg += f" ({', '.join(s.params)})"
                fixes = (
                    [_fix(f"Change to {near[0]!r}", [Edit(rng, json.dumps(near[0]))], True, False)]
                    if near
                    else []
                )
                self.diagnostics.append(_diag(rng, ERROR, msg, "unknown-table", i, [f for f in fixes if f]))

    def _column_hovers(self, s: Subject, report: sv.Report, rec: Record, site_list: list[Site]) -> None:
        src = self.src
        eps = report.epsilon or {}
        conds: dict[str, list[str]] = {}
        for c in report.ensures:
            for col in c.reads or ():
                mark = "proved" if c.proved else "not proved"
                conds.setdefault(col, []).append(f"`{c.label}`: {mark}")

        def out_md(col: str) -> str:
            lines = [f"**{col}** `{rec.output.get(col, '?')}` (output of {s.name})", ""]
            if col in report.facts:
                lines.append(f"proved: {report.facts[col]}")
            if col in eps:
                b = ", ".join(f"{k} ≤ {v}" for k, v in eps[col].items() if v is not None) or "unbounded"
                lines.append(f"\nε on an engine that sums in another order: {b}")
            if conds.get(col):
                lines += ["", "ensures:", *[f"- {x}" for x in conds[col]]]
            return "\n".join(lines)

        out_cols = set(report.facts) | set(rec.output)
        regions = [s.node] if s.kind == "transform" else s.body
        for region in regions:
            for n in ast.walk(region):
                if isinstance(n, ast.keyword) and n.arg in out_cols:
                    line = n.lineno
                    ch = src.char(line, n.col_offset)
                    self.hovers.append(
                        {"range": [line - 1, ch, line - 1, ch + len(n.arg)], "markdown": out_md(n.arg)}
                    )
        requires = report.requires
        for site in site_list:
            for item in site.items:
                for name, rng in _columns_named(src, item):
                    if site.role == "ensures" and name in out_cols:
                        self.hovers.append({"range": list(rng), "markdown": out_md(name)})
                    elif site.role == "requires" and site.table:
                        typ = rec.inputs.get(site.table, {}).get(name, "?")
                        stated = requires.get(site.table) or report.requires.get(site.table, [])
                        md = (
                            f"**{site.table}.{name}** `{typ}` (input)\n\nassumed of {site.table}:\n"
                            + "\n".join(f"- `{x}`" for x in stated)
                        )
                        self.hovers.append({"range": list(rng), "markdown": md})


def _imports(src: Source, codes: list[str]) -> list[Edit | None]:
    """The imports the codes a fix inserts need: `_`, `datetime`."""
    out = [import_underscore(src)] if any(c.startswith(("_.", "~_")) for c in codes) else []
    if any(re.search(r"(?<![\w.])datetime\(", c) for c in codes):
        out.append(import_datetime(src))
    return out


def _by_label(src: Source, items: list[ast.expr], lab: str) -> ast.expr | None:
    want = re.sub(r"\s+", "", strip_parens(lab))
    for n in items:
        seg = re.sub(r"\s+", "", src.segment(n)).strip("\"'")
        if seg == want or strip_parens(seg) == want:
            return n
    return None


def _name_range(src: Source, fn: ast.AST) -> Range:
    """The function's name in `def name(`."""
    if not isinstance(fn, ast.FunctionDef):
        return src.range(fn)
    line = src.lines[fn.lineno - 1]
    col = line.find(fn.name, line.find("def"))
    return (fn.lineno - 1, col, fn.lineno - 1, col + len(fn.name))


def _columns_named(src: Source, item: ast.expr) -> list[tuple[str, Range]]:
    """The columns a condition names: `_.x`, `_["x"]`, the arguments of
    `sv.unique("x")`, and columns of a SQL snippet."""
    out = []
    for n in ast.walk(item):
        if isinstance(n, ast.Attribute) and isinstance(n.value, ast.Name) and n.value.id == "_":
            line = n.end_lineno
            end = src.char(line, n.end_col_offset)
            out.append((n.attr, (line - 1, end - len(n.attr), line - 1, end)))
        elif isinstance(n, ast.Subscript) and isinstance(n.value, ast.Name) and n.value.id == "_":
            if isinstance(n.slice, ast.Constant) and isinstance(n.slice.value, str):
                out.append((n.slice.value, src.range(n.slice)))
        elif (
            isinstance(n, ast.Call)
            and isinstance(n.func, ast.Attribute)
            and n.func.attr in {"unique", "rows_per"}
        ):
            args = list(n.args)
            if n.func.attr == "rows_per" and args and isinstance(args[0], (ast.List, ast.Tuple)):
                args = list(args[0].elts)
            for a in args:
                if isinstance(a, ast.Constant) and isinstance(a.value, str):
                    r = src.range(a)
                    out.append((a.value, (r[0], r[1] + 1, r[2], r[3] - 1)))
    if isinstance(item, ast.Constant) and isinstance(item.value, str) and item.lineno == item.end_lineno:
        out += _sql_columns(src, item)
    return out


def _sql_columns(src: Source, item: ast.Constant) -> list[tuple[str, Range]]:
    import sqlglot
    from sqlglot import exp

    try:
        tree = sqlglot.parse_one(item.value, dialect="duckdb")
    except Exception:  # noqa: BLE001 - sverify reports it
        return []
    raw = src.segment(item)
    base = src.range(item)
    out = []
    for col in tree.find_all(exp.Column):
        m = re.search(r"\b" + re.escape(col.name) + r"\b", raw)
        if m:
            out.append((col.name, (base[0], base[1] + m.start(), base[0], base[1] + m.end())))
    return out


def _routes(report: sv.Report) -> dict[str, dict]:
    out = {}
    for e in ENGINES:
        try:
            with warnings.catch_warnings():
                warnings.simplefilter("ignore")
                r = report.route(e)
        except Exception as ex:  # noqa: BLE001 - shown in the hover
            out[e] = {"kind": None, "cls": "refused", "reason": f"{type(ex).__name__}: {ex}"}
            continue
        reason = r.reason
        if r.refused and reason.startswith("not verified"):
            reason = "not verified (see the diagnostics)"
        out[e] = {
            "kind": r.kind,
            "cls": r.cls if not r.refused else "refused",
            "evidence": r.evidence,
            "observation": str(r.observation) if r.observation is not None else None,
            "shims": list(r.shims),
            "reason": reason,
            "suggested": dict(r.suggested),
            "warnings": list(r.warnings),
        }
    return out


def _inferred(report: sv.Report) -> dict[str, list[str]]:
    """The preconditions sverify inferred, as labels per table: those of
    `requires` that `inferred_from` explains."""
    return {
        t: [lab for lab in labs if lab in report.inferred_from]
        for t, labs in report.requires.items()
        if any(lab in report.inferred_from for lab in labs)
    }


def _hints_for(report: sv.Report, issue: Any) -> list[str]:
    """The report's hints about an issue's column (shown as they are)."""
    return [h for h in report.hints if issue.column and f"`{issue.column}`" in h]


def _summary(report: sv.Report, route_info: dict, seconds: float | None) -> str:
    n = len(report.ensures)
    proved = sum(c.proved for c in report.ensures)
    head = "✓ proved" if report.proved else "✗ not proved"
    parts = [head, f"{proved}/{n} ensures"]
    if report.needed:
        parts.append(f"needs {sum(len(v) for v in report.needed.values())}")
    failing = [i for i in report.errors if i not in report.assumed]
    if failing:
        parts.append(f"{len(failing)} may fail")
    if report.assumed:
        parts.append(f"{len(report.assumed)} assumed")
    parts += [f"{e}: {info['cls'] or info['kind'] or '?'}" for e, info in route_info.items()]
    if seconds is not None:
        parts.append(f"{seconds:.1f} s")
    return "sverify " + " · ".join(parts)


def _subject_markdown(s: Subject, report: sv.Report, route_info: dict, rec: Record) -> str:
    status = "proved" if report.proved else "not proved"
    lines = [
        f"### sverify: {s.name} — {status}",
        f"semantics: `{report.semantics}`"
        + ("" if rec.seconds is None else f", checked in {rec.seconds:.2f} s"),
        "",
    ]
    needed = report.needed
    req = [
        f"- requires {t}: `{c}`" + (" (inferred)" if c in report.inferred_from else "")
        for t, cs in report.requires.items()
        for c in cs
        if c not in needed.get(t, ())
    ]
    lines += req
    lines += [f"- needs on {t}: `{c}`" for t, cs in needed.items() for c in cs]
    for c in report.ensures:
        mark = "✓" if c.portable else "✗"
        lines.append(f"- {mark} ensures `{c.label}`: {c.message}")
    lines += [f"- assumes: {i.assumption}" for i in report.assumed]
    lines += [f"- may fail: {i.message}" for i in report.errors if i not in report.assumed]
    if report.facts or report.rows is not None:
        lines += ["", "| output column | proved |", "|---|---|"]
        if report.rows is not None:
            lines.append(f"| (rows) | at most {report.rows:,} |")
        lines += [f"| `{n}` | {v} |" for n, v in report.facts.items()]
    lines += ["", "| engine | route | class | |", "|---|---|---|---|"]
    for e, info in route_info.items():
        extra = info.get("observation") or (", ".join(info.get("shims") or []) or info.get("reason", ""))
        route, cls = info.get("kind") or "refused", info.get("cls") or "?"
        lines.append(f"| {e} | {route} | {cls} | {extra.replace('|', '/')} |")
    if report.epsilon:
        eps = ", ".join(f"`{k}` {v}" for k, v in report.epsilon.items())
        lines += ["", f"ε per double column: {eps}"]
    lines += [x for n in report.notes for x in ("", f"note: {n}")]
    return "\n".join(lines)


def check(path: str, counterexamples: int | None = None) -> dict:
    t0 = time.perf_counter()
    text = Path(path).read_text()
    try:
        src = Source(path, text)
    except SyntaxError as e:
        return {
            "file": path,
            "seconds": 0,
            "subjects": [],
            "hovers": [],
            "lenses": [],
            "sites": [],
            "diagnostics": [
                _diag(
                    (max((e.lineno or 1) - 1, 0), 0, max((e.lineno or 1) - 1, 0), 200),
                    ERROR,
                    f"syntax error: {e.msg}",
                    "syntax",
                    -1,
                )
            ],
        }
    if "sverify" not in text:
        return {
            "file": path,
            "seconds": 0,
            "subjects": [],
            "hovers": [],
            "lenses": [],
            "sites": [],
            "diagnostics": [],
        }
    rec, failure = run_file(path, counterexamples)
    return Checked(src, rec, failure, time.perf_counter() - t0).json()
