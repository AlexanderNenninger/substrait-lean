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

if TYPE_CHECKING:
    from sverify.contracts import CheckedCondition, Issue, Needed, Report
    from sverify.observation import Observation
    from sverify.routes import Route

#: The version of the report's JSON format (`format` in the document).
FORMAT = 1

Json = dict[str, Any]


def _sverify_version() -> str:
    from importlib.metadata import PackageNotFoundError, version

    try:
        return version("sverify")
    except PackageNotFoundError:
        return "unknown"


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


def observation_json(obs: Observation) -> Json:
    """An observation: its text, as `sv.equivalent` prints it, and its
    components, with a tolerance on doubles as `{"abs", "rel", "ulps"}`."""
    components: Json = {}
    for f in dataclasses.fields(obs):
        if f.name == "bound":
            continue
        v = getattr(obs, f.name)
        components[f.name] = dataclasses.asdict(v) if dataclasses.is_dataclass(v) else v
    return {"text": str(obs), "components": components}


def observation(d: Mapping[str, Any]) -> Observation:
    """The observation `observation_json` wrote; components this version
    does not know are left out."""
    from sverify.observation import Observation, Within

    known = {f.name for f in dataclasses.fields(Observation)} - {"bound"}
    comps = {k: v for k, v in (d.get("components") or {}).items() if k in known}
    if isinstance(comps.get("floats"), dict):
        w = comps["floats"]
        comps["floats"] = Within(w.get("abs"), w.get("rel"), w.get("ulps"))
    return Observation(**comps)


def issue_json(i: Issue) -> Json:
    return {
        "kind": i.kind,
        "expr": i.expr,
        "shown": i.shown,
        "column": i.column,
        "error": i.error,
        "message": i.message,
        "hint": i.hint,
        "constant": i.constant,
        "under_and_or": i.under_and_or,
        "needs": list(i.needs),
        "suggested": {t: list(labs) for t, labs in i.suggested.items()},
    }


def issue(d: Mapping[str, Any]) -> Issue:
    from sverify.contracts import Issue

    return Issue(
        d["kind"],
        d["expr"],
        d["error"],
        hint=d.get("hint"),
        column=d.get("column"),
        constant=d.get("constant", False),
        under_and_or=d.get("under_and_or", False),
        needs=tuple(d.get("needs", ())),
        shown=d.get("shown"),
        suggested={t: tuple(labs) for t, labs in (d.get("suggested") or {}).items()},
    )


def checked_json(c: CheckedCondition) -> Json:
    from sverify.contracts import label

    cx = c.counterexample
    return {
        "label": c.label,
        "proved": c.proved,
        "value": c.value,
        "reason": c.reason,
        "message": c.message,
        "detail": c.detail,
        "checked": c.checked,
        "ignores": list(c.ignores),
        "reads": None if c.reads is None else list(c.reads),
        "nullable": None if c.nullable is None else list(c.nullable),
        "approx": c.approx,
        "suggested": {t: [label(x) for x in cs] for t, cs in c.suggested.items()},
        "counterexample": None
        if cx is None
        else {
            "text": str(cx),
            "tables": {t: _value(rows) for t, rows in cx.tables.items()},
            "output": _value(cx.output),
            "columns": {k: list(v) for k, v in cx.columns.items()},
        },
    }


def checked(d: Mapping[str, Any]) -> CheckedCondition:
    from sverify.contracts import CheckedCondition
    from sverify.counterexample import Counterexample

    cx = d.get("counterexample")
    return CheckedCondition(
        d["label"],
        d["proved"],
        d["value"],
        counterexample=None
        if cx is None
        else Counterexample(
            {t: [tuple(r) for r in rows] for t, rows in cx["tables"].items()},
            [tuple(r) for r in cx["output"]],
            dict(cx["columns"]),
        ),
        checked=d.get("checked", False),
        suggested={t: list(labs) for t, labs in (d.get("suggested") or {}).items()},
        ignores=tuple(d.get("ignores", ())),
        reads=None if d.get("reads") is None else tuple(d["reads"]),
        approx=d.get("approx", False),
        nullable=None if d.get("nullable") is None else tuple(d["nullable"]),
        detail=d.get("detail"),
    )


def needed_json(n: Needed) -> Json:
    return {
        "table": n.table,
        "column": n.column,
        "op": n.op,
        "value": n.value,
        "sql": n.sql,
        "label": n.label,
        "code": n.code,
        "issue": None if n.issue is None else issue_json(n.issue),
    }


def route_json(r: Route) -> Json:
    return {
        "engine": r.engine,
        "kind": r.kind,
        "class": r.cls,
        "evidence": r.evidence,
        "profile": r.profile,
        "reason": r.reason,
        "deterministic": r.deterministic,
        "warnings": list(r.warnings),
        "shims": list(r.shims),
        "failures": [dict(f) for f in r.failures],
        "observation": None if r.observation is None else observation_json(r.observation),
        "bound_proved": r.bound_proved,
        "reproducible": None if r.reproducible is None else observation_json(r.reproducible),
        "rerun_evidence": r.rerun_evidence,
        "fallbacks": list(r.fallbacks),
        "suggested": {t: list(labs) for t, labs in r.suggested.items()},
    }


def route(d: Mapping[str, Any]) -> Route:
    from sverify.routes import Route

    def obs(key: str) -> Observation | None:
        v = d.get(key)
        return None if v is None else observation(v)

    return Route(
        d["engine"],
        d["kind"],
        d["profile"],
        d["reason"],
        deterministic=d.get("deterministic", True),
        warnings=tuple(d.get("warnings", ())),
        failures=tuple(d.get("failures", ())),
        cls=d.get("class"),
        evidence=d.get("evidence"),
        shims=tuple(d.get("shims", ())),
        reproducible=obs("reproducible"),
        rerun_evidence=d.get("rerun_evidence"),
        fallbacks=tuple(d.get("fallbacks", ())),
        observation=obs("observation"),
        bound_proved=d.get("bound_proved"),
        suggested={t: list(labs) for t, labs in (d.get("suggested") or {}).items()},
    )


# -- the report -----------------------------------------------------------------


def to_json(report: Report) -> Json:
    """`Report.to_json`, as a dict."""
    from sverify.contracts import label

    return {
        "format": FORMAT,
        "sverify": _sverify_version(),
        "proved": report.proved,
        "verdict": report.verdict,
        "semantics": report.semantics,
        "dialect": report.dialect,
        "on_inferred": report.on_inferred,
        "observation": observation_json(report.observation),
        "deterministic": report.deterministic,
        "rows": report.rows,
        "params": list(report.params),
        "requires": {t: list(labs) for t, labs in report.requires.items()},
        "inferred": {
            t: [
                {"label": label(c), "sql": str(c), "column": getattr(c, "column", None)} for c in cs
            ]
            for t, cs in report.inferred.items()
        },
        "ensures": [checked_json(c) for c in report.ensures],
        "issues": [issue_json(i) for i in report.issues],
        "assumed": [{**issue_json(i), "assumption": i.assumption} for i in report.assumed],
        "needs": [needed_json(n) for n in report.needs],
        "facts": dict(report.facts),
        "output": {k: str(v) for k, v in report.output.items()},
        "routes": {e: route_json(r) for e, r in report.routes.items()},
        "tie_places": [dataclasses.asdict(t) for t in report.tie_places],
        "ties": {t: list(labs) for t, labs in report.ties.items()},
        "hints": list(report.hints),
        "rewrites": list(report.rewrites),
        "implied": dict(report.implied),
        "transfer": None if report.transfer is None else [dict(f) for f in report.transfer],
        "floats_on": {e: list(ps) for e, ps in report.floats_on.items()},
    }


def from_json(data: str | Mapping[str, Any]) -> Report:
    """`Report.from_json`: see there."""
    from sverify.contracts import Inferred, Report, TiePlace

    d = json.loads(data) if isinstance(data, str) else data
    fmt = d.get("format")
    if not isinstance(fmt, int) or fmt > FORMAT:
        raise ValueError(
            f"the report's JSON has format {fmt!r}, and this version of sverify reads "
            f"format {FORMAT} or older: upgrade sverify"
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
    return Report(
        requires={t: list(labs) for t, labs in (d.get("requires") or {}).items()},
        ensures=[checked(c) for c in d.get("ensures", [])],
        facts=dict(d.get("facts") or {}),
        deterministic=d.get("deterministic", True),
        windows_total=d.get("deterministic", True),
        tie_places=[TiePlace(**t) for t in d.get("tie_places", [])],
        issues=[issue(i) for i in d.get("issues", [])],
        inferred=inferred,
        implied=dict(d.get("implied") or {}),
        assumed=[issue(i) for i in d.get("assumed", [])],
        params=list(d.get("params", [])),
        hints=list(d.get("hints", [])),
        rewrites=list(d.get("rewrites", [])),
        rows=d.get("rows"),
        semantics=d.get("semantics", "reference"),
        observation=observation(d["observation"]) if d.get("observation") else _plan_bound(),
        floats_on={e: list(ps) for e, ps in (d.get("floats_on") or {}).items()},
        routes={e: route(r) for e, r in (d.get("routes") or {}).items()},
        transfer=d.get("transfer"),
        output=_output(d.get("output") or {}),
        dialect=d.get("dialect", "ibis"),
        ties={t: list(labs) for t, labs in (d.get("ties") or {}).items()},
        on_inferred=d.get("on_inferred", "silent"),
        inferred_from=inferred_from,
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


__all__ = ["FORMAT", "from_json", "to_json"]
