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
from collections.abc import Mapping
from datetime import date, datetime, time, timedelta
from decimal import Decimal
from typing import TYPE_CHECKING, Any

from sverify._meta import VERSION

if TYPE_CHECKING:
    from sverify.conditions import CheckedCondition
    from sverify.observation import Observation
    from sverify.report import Issue, Needed, Report
    from sverify.routes import Route

#: The version of the report's JSON format (`format` in the document).
#: Format 1 was on main between #788 and the 1.0 renames, in no release:
#: `from_json` refuses it.
FORMAT = 2

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
_REASONS = {"observation": "equivalence"}


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


def issue(d: Mapping[str, Any]) -> Issue:
    from sverify.report import Issue, _needed

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
        needs=[
            _needed(t, lab, "sql") for t, labs in suggested(p.get("needs")).items() for lab in labs
        ],
    )


def checked_json(c: CheckedCondition) -> Json:
    """A postcondition, as a finding: `pass` where it is proved, `fail`
    where it is not. Its rule is `reason`, or `proved`."""
    cx = c.counterexample
    proved_level = "note" if c.reason else "none"
    level = proved_level if c.proved else "warning" if c.checked else "error"
    return _finding(
        _REASONS.get(c.reason, c.reason) if c.reason else "proved",
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
            "needs": suggested_json(c.suggested),
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
        suggested=suggested(p.get("needs")),
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
        "equivalence": None if r.observation is None else equivalence_json(r.observation),
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
        shims=tuple(d.get("shims", ())),
        reproducible=eq("reproducible"),
        rerun_evidence=d.get("rerun_evidence"),
        fallbacks=tuple(d.get("fallbacks", ())),
        observation=eq("equivalence"),
        bound_proved=d.get("bound_proved"),
        suggested=suggested(d.get("needs")),
    )


# -- the report -----------------------------------------------------------------


def to_json(report: Report) -> Json:
    """`Report.to_json`, as a dict."""
    from sverify.conditions import label

    return {
        "format": FORMAT,
        "sverify": _sverify_version(),
        "proved": report.proved,
        "verdict": report.verdict,
        "semantics": report.semantics,
        "dialect": report._dialect,
        "on_inferred": report._on_inferred,
        "equivalence": equivalence_json(report.observation),
        "deterministic": report.deterministic,
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
        "facts": dict(report.facts),
        "not_null": list(report.not_null),
        "output": {k: str(v) for k, v in report.output.items()},
        "routes": {e: route_json(r) for e, r in report.routes.items()},
        "ties": {
            "places": [dataclasses.asdict(t) for t in report._tie_places],
            "needs": suggested_json(report.ties),
        },
        "rewrites": list(report._rewrites),
        "implied": dict(report._implied),
        "transfer": None if report._transfer is None else [dict(f) for f in report._transfer],
        "floats_on": {e: list(ps) for e, ps in report._floats_on.items()},
    }


def from_json(data: str | Mapping[str, Any]) -> Report:
    """`Report.from_json`: see there."""
    from sverify.conditions import Inferred
    from sverify.report import Report, TiePlace

    d = json.loads(data) if isinstance(data, str) else data
    fmt = d.get("format")
    if not isinstance(fmt, int) or fmt > FORMAT:
        raise ValueError(
            f"the report's JSON has format {fmt!r}, and this version of sverify reads "
            f"format {FORMAT}: upgrade sverify"
        )
    if fmt < FORMAT:
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
    return Report(
        requires={t: list(labs) for t, labs in (d.get("requires") or {}).items()},
        ensures=[checked(c) for c in d.get("ensures", [])],
        facts=dict(d.get("facts") or {}),
        not_null=list(d.get("not_null", [])),
        deterministic=d.get("deterministic", True),
        _windows_total=d.get("deterministic", True),
        _tie_places=[TiePlace(**t) for t in ties.get("places", [])],
        issues=issues,
        _inferred=inferred,
        _implied=dict(d.get("implied") or {}),
        assumed=[issue(i) for i in d.get("assumed", [])],
        _params=list(d.get("params", [])),
        _hints=list(dict.fromkeys(i.hint for i in issues if i.hint)),
        _rewrites=list(d.get("rewrites", [])),
        rows=d.get("rows"),
        semantics=d.get("semantics", "reference"),
        observation=equivalence(d["equivalence"]) if d.get("equivalence") else _plan_bound(),
        _floats_on={e: list(ps) for e, ps in (d.get("floats_on") or {}).items()},
        routes={e: route(r) for e, r in (d.get("routes") or {}).items()},
        _transfer=d.get("transfer"),
        output=_output(d.get("output") or {}),
        _dialect=d.get("dialect", "ibis"),
        ties=suggested(ties.get("needs")),
        # 0.6 wrote "silent" for what is now "ignore".
        _on_inferred=_on_inferred(d.get("on_inferred")),
        _inferred_from=inferred_from,
    )


def _plan_bound() -> Observation:
    from sverify.observation import PLAN_BOUND

    return PLAN_BOUND


def _output(types: Mapping[str, str]) -> dict[str, Any]:
    """The output's types, as Ibis types where Ibis reads them."""
    import ibis

    out: dict[str, Any] = {}
    for k, v in types.items():
        try:
            out[k] = ibis.dtype(v)
        except Exception:  # a type this Ibis does not read: keep the text
            out[k] = v
    return out


__all__ = ["FORMAT", "from_json", "rule_id", "to_json"]


def _on_inferred(value: Any) -> Any:
    """A report's `on_inferred`: 0.6 wrote "silent" for what is now "ignore"."""
    if value in (None, "silent"):
        return "ignore"
    return value
