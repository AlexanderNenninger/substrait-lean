"""The report as JSON (`Report.to_json`, `Report.from_json`, #736): a
versioned document for CI jobs and tools, in the format of
`sverify/schemas/report.schema.json`.

Within 1.x the format only gains optional keys, and a reader ignores keys it
does not know (`docs/stability.md`). Conditions travel as their labels, the
same text `str(report)` prints; `from_json` gives back a `Report` with the
same verdict, postconditions, issues, needs, facts and routes, without the
plan or the conditions as code.
"""

from __future__ import annotations

import dataclasses
import json
import re
from collections.abc import Collection, Mapping
from datetime import date, datetime, time, timedelta
from decimal import Decimal
from typing import TYPE_CHECKING, Any

from sverify._meta import VERSION

if TYPE_CHECKING:
    from sverify.conditions import CheckedCondition
    from sverify.observation import Observation
    from sverify.report import ColumnFacts, Issue, Needed, Report
    from sverify.routes import Route

#: The version of the report's JSON format (`format` in the document).
#: Format 1 was on main between #788 and the 1.0 renames, in no release:
#: `from_json` refuses it.
FORMAT = 4
#: The oldest format `from_json` reads. Format 3 gave `verdict` the `Verdict`'s
#: value and moved the first line of `str(report)` to `summary`; a report of
#: format 2 has no `summary`, and its `verdict` is that line. Format 4 named
#: `equivalence` `lenses` (in a route too), made each of `facts` an object
#: (text, nullable, bounds) and each of a postcondition's `needs` a whole
#: `needed` object; formats 2 and 3 are still read.
OLDEST = 2

Json = dict[str, Any]


def _sverify_version() -> str:
    """The installed version, as `sverify` read it at import: reading the
    package metadata again took 88 % of `to_json`'s time."""
    return VERSION


def _value(v: Any) -> Any:
    """A value of a counterexample as JSON: JSON's own values as they are,
    NaN and the infinities, decimals, dates, times and bytes as text."""
    if v is None or isinstance(v, bool | int | str):
        return v
    if isinstance(v, float):
        return v if v == v and v not in (float("inf"), float("-inf")) else str(v)
    if isinstance(v, datetime | date | time):
        return v.isoformat()
    if isinstance(v, Decimal | timedelta):
        return str(v)
    if isinstance(v, bytes):
        return v.hex()
    if isinstance(v, list | tuple):
        return [_value(x) for x in v]
    if isinstance(v, dict):
        return {str(k): _value(x) for k, x in v.items()}
    return str(v)


# -- the parts ------------------------------------------------------------------


def facts_json(f: ColumnFacts) -> Json:
    """A column's facts: their text, and the data (`ColumnFacts`), bounds as
    `_value` writes values."""
    return {
        "text": str(f),
        "nullable": f.nullable,
        "lower": _value(f.lower),
        "upper": _value(f.upper),
    }


_INTERVAL = re.compile(r"(?:(-?\d+) days?, )?(-?\d+):(\d\d):(\d\d(?:\.\d+)?)")


def _bound(v: Any, dtype: Any) -> Any:
    """A bound `facts_json` wrote, as a value of the column's type."""
    if v is None or isinstance(dtype, str) or dtype is None:
        return v
    if dtype.is_decimal():
        return Decimal(v)
    if dtype.is_floating():
        return float(v)
    if dtype.is_timestamp():
        return datetime.fromisoformat(v)
    if dtype.is_date():
        return date.fromisoformat(v)
    if dtype.is_interval() and (m := _INTERVAL.fullmatch(v)):
        days, h, mi, sec = m.groups()
        return timedelta(days=int(days or 0), hours=int(h), minutes=int(mi), seconds=float(sec))
    return v


def _facts(
    d: Mapping[str, Any], output: Mapping[str, Any], not_null: Collection[str]
) -> dict[str, ColumnFacts]:
    """The facts `facts_json` wrote; a report written before #704 has their
    text alone, and its `not_null` list."""
    from sverify.report import ColumnFacts

    out = {}
    for c, f in d.items():
        if isinstance(f, str):
            out[c] = ColumnFacts(c not in not_null, None, None, f)
            continue
        t = output.get(c)
        lo, hi = _bound(f.get("lower"), t), _bound(f.get("upper"), t)
        out[c] = ColumnFacts(bool(f.get("nullable", True)), lo, hi, f.get("text", ""))
    return out


def equivalence_json(obs: Observation) -> Json:
    """An equivalence (`sv.equivalent`): its text and its components, with
    a tolerance on doubles as `{"abs", "rel", "ulps"}`."""
    components: Json = {}
    for f in dataclasses.fields(obs):
        if f.name == "bound":
            continue
        v = getattr(obs, f.name)
        components[f.name] = dataclasses.asdict(v) if dataclasses.is_dataclass(v) else v
    return {"text": str(obs), "components": components}


def equivalence(d: Mapping[str, Any]) -> Observation:
    """The equivalence `equivalence_json` wrote; components this version
    does not know are left out."""
    from sverify.observation import Observation, Within

    known = {f.name for f in dataclasses.fields(Observation)} - {"bound"}
    comps = {k: v for k, v in (d.get("components") or {}).items() if k in known}
    if isinstance(comps.get("floats"), dict):
        w = comps["floats"]
        comps["floats"] = Within(w.get("abs"), w.get("rel"), w.get("ulps"))
    return Observation(**comps)


# -- needed preconditions (B1) --------------------------------------------------


def needed_json(n: Needed) -> Json:
    """A precondition the proof needs (`Report.needs`)."""
    return {
        "table": n.table,
        "label": n.label,
        "column": n.column,
        "op": n.op,
        "value": n.value,
        "sql": n.sql,
        "code": n.code,
        "issue": None if n.issue is None else issue_json(n.issue),
    }


def suggested_json(suggested: Mapping[str, Any]) -> list[Json]:
    """Suggested preconditions, labels per table, as `needed` objects that
    carry the table and the label."""
    from sverify.conditions import label

    return [
        {"table": t, "label": x if isinstance(x, str) else label(x)}
        for t, xs in suggested.items()
        for x in xs
    ]


def _needs(needs: Any) -> tuple[Needed, ...]:
    """The `Needed` of a list of `needed` objects, as `needed_json` writes
    them; one with only its table and label (written before #1288 API-5) as
    SQL. Its condition is its SQL."""
    from sverify.report import Needed, _needed

    out = []
    for n in needs or ():
        if n.get("table") is None:
            continue
        if "sql" not in n:
            out.append(_needed(n["table"], n["label"], "sql"))
            continue
        i = n.get("issue")
        out.append(
            Needed(
                n["table"],
                n.get("column"),
                n.get("op"),
                n.get("value"),
                n["sql"],
                n["label"],
                n.get("code") or n["label"],
                None if i is None else issue(i),
                condition=n["sql"],
            )
        )
    return tuple(out)


def suggested(needs: Any) -> dict[str, list[Any]]:
    """Labels per table, from a list of `needed` objects; those without a
    table are left out."""
    out: dict[str, list[Any]] = {}
    for n in needs or ():
        if n.get("table") is not None:
            out.setdefault(n["table"], []).append(n["label"])
    return out


# -- findings: SARIF's result shape (#793) --------------------------------------

#: The issues' kinds, by their rule ids.
_KINDS = {
    k.lower().replace(" ", "_"): k
    for k in (
        "division by zero",
        "overflow",
        "cast out of range",
        "negative exponent",
        "domain error",
        "SUM overflow",
        "overflow to infinity",
    )
}


#: The rule ids of the reasons whose Python name differs (B3).


def rule_id(kind: str) -> str:
    """An issue's kind as a code: snake_case (`"SUM overflow"` is
    `sum_overflow`)."""
    return kind.lower().replace(" ", "_").replace("-", "_")


def _finding(rule: str, level: str, kind: str, text: str, properties: Json) -> Json:
    return {
        "ruleId": rule,
        "level": level,
        "kind": kind,
        "message": {"text": text},
        "properties": properties,
    }


def issue_json(i: Issue) -> Json:
    """A runtime error the checker could not rule out, as a finding:
    `error` if a proof must rule it out, `warning` otherwise."""
    return _finding(
        rule_id(i.kind),
        "error" if i.error else "warning",
        "fail",
        i.message,
        {
            "shown": i.shown,
            "column": i.column,
            "hint": i.hint,
            "constant": i.constant,
            "under_and_or": i.under_and_or,
            "needs": _issue_needs(i),
        },
    )


def _issue_needs(i: Issue) -> list[Json]:
    """The preconditions that rule an issue out: those suggested per table,
    then those the inference found whose table it does not name
    (`"table": null`)."""
    from sverify.report import _labels_by_table

    out = suggested_json(_labels_by_table(i.needs))
    seen = {n["label"] for n in out}
    return out + [{"table": None, "label": x} for x in i._labels if x not in seen]


def assumed_json(i: Issue) -> Json:
    """An issue sverify assumes away and checks on the data while the job
    runs (a SUM that fits its type): a `note`."""
    out = issue_json(i)
    out["level"] = "note"
    out["kind"] = "informational"
    out["properties"]["assumption"] = i.assumption
    return out


def issue(d: Mapping[str, Any], assumed: bool = False) -> Issue:
    """An issue as `issue_json` or `assumed_json` wrote it: `assumed` for
    the report's `"assumed"` list."""
    from sverify.report import Issue

    p = d.get("properties") or {}
    rule = d["ruleId"]
    return Issue(
        _KINDS.get(rule, rule.replace("_", " ")),
        p.get("shown") or "",
        d.get("level") == "error",
        hint=p.get("hint"),
        column=p.get("column"),
        constant=p.get("constant", False),
        under_and_or=p.get("under_and_or", False),
        _labels=tuple(n["label"] for n in p.get("needs") or ()),
        shown=p.get("shown"),
        needs=list(_needs(p.get("needs"))),
        assumed=assumed,
    )


def checked_json(c: CheckedCondition) -> Json:
    """A postcondition, as a finding: `pass` where it is proved, `fail`
    where it is not. Its rule is `reason`, or `proved`."""
    cx = c.counterexample
    proved_level = "note" if c.reason else "none"
    level = proved_level if c.proved else "warning" if c.checked else "error"
    return _finding(
        c.reason or "proved",
        level,
        "pass" if c.proved else "fail",
        c.message,
        {
            "label": c.label,
            "value": c.value,
            "detail": c.detail,
            "checked": c.checked,
            "ignores": list(c.ignores),
            "reads": None if c.reads is None else list(c.reads),
            "nullable": None if c.nullable is None else list(c.nullable),
            "approx": c.approx,
            "needs": [needed_json(n) for n in c.needs],
            "counterexample": None
            if cx is None
            else {
                "text": str(cx),
                "tables": {t: _value(rows) for t, rows in cx.tables.items()},
                "output": _value(cx.output),
                "columns": {k: list(v) for k, v in cx.columns.items()},
            },
        },
    )


def checked(d: Mapping[str, Any]) -> CheckedCondition:
    from sverify.conditions import CheckedCondition
    from sverify.counterexample import Counterexample

    p = d.get("properties") or {}
    cx = p.get("counterexample")
    return CheckedCondition(
        p["label"],
        d.get("kind") == "pass",
        p["value"],
        counterexample=None
        if cx is None
        else Counterexample(
            {t: [tuple(r) for r in rows] for t, rows in cx["tables"].items()},
            [tuple(r) for r in cx["output"]],
            dict(cx["columns"]),
        ),
        checked=p.get("checked", False),
        needs=_needs(p.get("needs")),
        ignores=tuple(p.get("ignores", ())),
        reads=None if p.get("reads") is None else tuple(p["reads"]),
        approx=p.get("approx", False),
        nullable=None if p.get("nullable") is None else tuple(p["nullable"]),
        detail=p.get("detail"),
    )


# -- routes ---------------------------------------------------------------------


def route_json(r: Route) -> Json:
    # The evidence's provenance (#1166), where the route has one: a report
    # written before it reads back as it was.
    cited = {
        k: v
        for k, v in (
            ("facts", list(r.facts)),
            ("theorems", list(r.theorems)),
            ("version", r.version),
            ("issues", list(r.issues)),
            ("proved_facts", list(r.proved_facts)),
        )
        if v
    }
    return {
        "engine": r.engine,
        "kind": r.kind,
        "class": r.cls,
        "evidence": r.evidence,
        **cited,
        "semantics": r.profile,
        "reason": r.reason,
        "deterministic": r.deterministic,
        "warnings": list(r.warnings),
        "shims": list(r.shims),
        "failures": [dict(f) for f in r.failures],
        "lenses": None if r.lenses is None else equivalence_json(r.lenses),
        "bound_proved": r.bound_proved,
        "reproducible": None if r.reproducible is None else equivalence_json(r.reproducible),
        "rerun_evidence": r.rerun_evidence,
        "fallbacks": list(r.fallbacks),
        "needs": suggested_json(r.suggested),
    }


def route(d: Mapping[str, Any]) -> Route:
    from sverify.routes import Route

    def eq(key: str) -> Observation | None:
        v = d.get(key)
        return None if v is None else equivalence(v)

    return Route(
        d["engine"],
        d["kind"],
        d["semantics"],
        d["reason"],
        deterministic=d.get("deterministic", True),
        warnings=tuple(d.get("warnings", ())),
        failures=tuple(d.get("failures", ())),
        cls=d.get("class"),
        evidence=d.get("evidence"),
        facts=tuple(d.get("facts", ())),
        theorems=tuple(d.get("theorems", ())),
        version=d.get("version"),
        issues=tuple(d.get("issues", ())),
        proved_facts=tuple(d.get("proved_facts", ())),
        shims=tuple(d.get("shims", ())),
        reproducible=eq("reproducible"),
        rerun_evidence=d.get("rerun_evidence"),
        fallbacks=tuple(d.get("fallbacks", ())),
        lenses=eq("lenses") if "lenses" in d else eq("equivalence"),
        bound_proved=d.get("bound_proved"),
        suggested=suggested(d.get("needs")),
    )


# -- the report -----------------------------------------------------------------


def to_json(report: Report) -> Json:
    """`Report.to_json`, as a dict."""
    from sverify.conditions import label
    from sverify.report import black_boxes_json, proved_not_null

    return {
        "format": FORMAT,
        "sverify": _sverify_version(),
        "proved": report._proved,
        "verdict": str(report.verdict),
        "summary": report._summary,
        "semantics": report.semantics,
        "engine_version": report.engine_version,
        "dialect": report._dialect,
        "on_inferred": report._on_inferred,
        "lenses": equivalence_json(report.lenses),
        "deterministic": report.deterministic,
        "deterministic_exact": report._exact,
        "class_places": [dataclasses.asdict(t) for t in report._class_places],
        "rows": report.rows,
        "params": list(report._params),
        "requires": {t: list(labs) for t, labs in report.requires.items()},
        "inferred": {
            t: [
                {"label": label(c), "sql": str(c), "column": getattr(c, "column", None)} for c in cs
            ]
            for t, cs in report._inferred.items()
        },
        "ensures": [checked_json(c) for c in report.ensures],
        "issues": [issue_json(i) for i in report.issues],
        "assumed": [assumed_json(i) for i in report.assumed],
        "needs": [needed_json(n) for n in report.needs],
        "facts": {c: facts_json(f) for c, f in report.facts.items()},
        "not_null": proved_not_null(report),
        "output": {k: str(v) for k, v in report.output.items()},
        "routes": {e: route_json(r) for e, r in report.routes.items()},
        "ties": {
            "places": [dataclasses.asdict(t) for t in report._tie_places],
            "needs": suggested_json(report.ties),
        },
        "dialect_differences": [dataclasses.asdict(d) for d in report.dialect_differences],
        "rewrites": list(report._rewrites),
        "run_gate": report._run_gate,
        "implied": dict(report._implied),
        "transfer": None if report._transfer is None else [dict(f) for f in report._transfer],
        "floats_on": {e: list(ps) for e, ps in report._floats_on.items()},
        # The checker's verdicts its routes read (#1166): a report read back
        # routes as it did.
        "engines": report._engines,
        "sorted": report._sorted,
        "sequence_determined": report._sequence_determined,
        "checker": {"generated_proofs": report._generated_proofs},
        "depends": report._depends,
        # What a run checks on the data (#1863): a report read back prints the
        # same checks and keeps the as-of join's cap.
        "run_checks": {
            "margin": list(report._margin_checks),
            "asof": list(report._asof_checks),
            "asof_max_pairs": report._asof_max_pairs,
        },
        "black_boxes": black_boxes_json(report.black_boxes),
    }


def from_json(data: str | Mapping[str, Any]) -> Report:
    """`Report.from_json`: see there."""
    from sverify._dialect import DialectDifference
    from sverify.conditions import Inferred
    from sverify.report import Report, TiePlace, black_boxes_from_json

    d = json.loads(data) if isinstance(data, str) else data
    fmt = d.get("format")
    if not isinstance(fmt, int) or fmt > FORMAT:
        raise ValueError(
            f"the report's JSON has format {fmt!r}, and this version of sverify reads "
            f"format {FORMAT}: upgrade sverify"
        )
    if fmt < OLDEST:
        raise ValueError(
            f"the report's JSON has format {fmt}, which no release wrote: write it again "
            f"with this version of sverify (format {FORMAT})"
        )
    inferred: dict[str, list[Any]] = {}
    for t, cs in (d.get("inferred") or {}).items():
        out = []
        for c in cs:
            x = Inferred(c["sql"], c["label"])
            x.column = c.get("column")
            out.append(x)
        inferred[t] = out
    inferred_from = {
        n["label"]: issue(n["issue"]) for n in d.get("needs", []) if n.get("issue") is not None
    }
    issues = [issue(i) for i in d.get("issues", [])]
    ties = d.get("ties") or {}
    output = _output(d.get("output") or {}, d.get("not_null") or ())
    return Report(
        requires={t: list(labs) for t, labs in (d.get("requires") or {}).items()},
        ensures=[checked(c) for c in d.get("ensures", [])],
        facts=_facts(d.get("facts") or {}, output, d.get("not_null") or ()),
        deterministic=d.get("deterministic", True),
        # A report written before D48 has one level, the exact one.
        _exact=d.get("deterministic_exact", d.get("deterministic", True)),
        _class_places=[TiePlace(**t) for t in d.get("class_places", ties.get("places", []))],
        _windows_total=d.get("deterministic_exact", d.get("deterministic", True)),
        _tie_places=[TiePlace(**t) for t in ties.get("places", [])],
        issues=issues,
        _inferred=inferred,
        _implied=dict(d.get("implied") or {}),
        assumed=[issue(i, assumed=True) for i in d.get("assumed", [])],
        _params=list(d.get("params", [])),
        _hints=list(dict.fromkeys(i.hint for i in issues if i.hint)),
        _rewrites=list(d.get("rewrites", [])),
        _run_gate=d.get("run_gate"),
        dialect_differences=tuple(DialectDifference(**x) for x in d.get("dialect_differences", [])),
        rows=d.get("rows"),
        semantics=d.get("semantics", "reference"),
        engine_version=d.get("engine_version"),
        # A report written before the name `lenses` calls them `equivalence`.
        lenses=equivalence(lens)
        if (lens := d.get("lenses", d.get("equivalence")))
        else _plan_bound(),
        _floats_on={e: list(ps) for e, ps in (d.get("floats_on") or {}).items()},
        _engines=d.get("engines"),
        _sorted=d.get("sorted"),
        _sequence_determined=d.get("sequence_determined", False),
        _generated_proofs=(d.get("checker") or {}).get("generated_proofs"),
        _depends=d.get("depends"),
        _margin_checks=list((d.get("run_checks") or {}).get("margin") or []),
        _asof_checks=list((d.get("run_checks") or {}).get("asof") or []),
        _asof_max_pairs=(d.get("run_checks") or {}).get("asof_max_pairs"),
        black_boxes=black_boxes_from_json(d.get("black_boxes")),
        routes={e: route(r) for e, r in (d.get("routes") or {}).items()},
        _transfer=d.get("transfer"),
        output=output,
        _dialect=d.get("dialect", "ibis"),
        ties=suggested(ties.get("needs")),
        # 0.6 wrote "silent" for what is now "ignore".
        _on_inferred=_on_inferred(d.get("on_inferred")),
        _inferred_from=inferred_from,
    )


def _plan_bound() -> Observation:
    from sverify.observation import PLAN_BOUND

    return PLAN_BOUND


def _output(types: Mapping[str, str], not_null: Collection[str]) -> dict[str, Any]:
    """The output's types, as Ibis types where Ibis reads them; the `not_null`
    columns are not nullable (a report written before #704 types them
    nullable)."""
    import ibis

    out: dict[str, Any] = {}
    for k, v in types.items():
        try:
            out[k] = ibis.dtype(v)
        except Exception:  # a type this Ibis does not read: keep the text
            out[k] = v
        else:
            out[k] = out[k].copy(nullable=False) if k in not_null else out[k]
    return out


__all__ = ["FORMAT", "from_json", "rule_id", "to_json"]


def _on_inferred(value: Any) -> Any:
    """A report's `on_inferred`: 0.6 wrote "silent" for what is now "ignore"."""
    if value in (None, "silent"):
        return "ignore"
    return value
