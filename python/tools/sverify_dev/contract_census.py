"""The contract census (`catalogue/contracts.toml`): how contracts on
aggregates of doubles reach each engine since D25 and D30.

Maintainer tooling (`sverify_dev`): not in the wheel, and not part of
sverify's API.

Each case is a query over a dataset of `catalogue/schemas.toml` with a
contract. `census` verifies it and asks `routes.choose` how it reaches each
engine: `proved` (the route's evidence is proved in Lean), `tested` (it rests
on a test or a probe, with the causes) or `refused` (with the reason).
`catalogue/contracts.json` holds the results; rewrite it with

    uv run python -m sverify_dev.contract_census --write

and print the table of outcomes by cause and engine with `--table`.
`tests/test_contract_census.py` checks that the results still hold.
"""

from __future__ import annotations

import json
import sys
import tomllib
from collections import Counter
from dataclasses import dataclass
from typing import Any

from sverify_dev import catalogue as cat

CASES = cat.ROOT / "contracts.toml"
RESULTS = cat.ROOT / "contracts.json"
ENGINES = ("duckdb", "polars", "spark", "snowflake")


@dataclass(frozen=True)
class Case:
    id: str
    pattern: str
    dataset: str
    ibis: str
    requires: str
    ensures: str


def load_cases() -> list[Case]:
    data = tomllib.loads(CASES.read_text())
    return [Case(**c) for c in data["case"]]


def _scope(c: Case, schemas: dict[str, Any]) -> dict[str, Any]:
    import ibis
    from ibis import _

    import sverify

    ns: dict[str, Any] = {"ibis": ibis, "_": _, "sv": sverify}
    ns.update(cat.tables(schemas, c.dataset, "native"))
    return ns


def report_of(c: Case, schemas: dict[str, Any]) -> Any:
    """The case's `sv.verify` report."""
    import sverify

    ns = _scope(c, schemas)
    exec(c.ibis, ns)  # noqa: S102 - the census's own code
    requires = eval(c.requires, ns)  # noqa: S307
    ensures = eval(c.ensures, ns)  # noqa: S307
    return sverify.verify(ns["q"], requires=requires, ensures=ensures)


def _tested_causes(report: Any, route: Any, engine: str) -> list[str]:
    """Why a route that is taken rests on a test: the options whose rows are
    tested, a tolerance bound Lean does not prove, a postcondition robust only
    by the engine's facts, or one proved on the reference's orders only."""
    from sverify import routes

    causes: list[str] = []
    for d in report._depends or []:
        r = routes.row(engine, d.get("group"), d["option"])
        if r is not None and r.get("evidence") == "tested":
            causes.append(f"row tested: {routes._where(d.get('group'), d['option'])}")
    if route.bound_proved is False:
        causes.append("tolerance bound not proved")
    if routes._robust_tested(report, engine):
        causes.append("robust only by the engine's facts (#1045)")
    if routes._allowed_tested(report):
        causes.append("proved on the reference's orders only (open measure, #1071)")
    if not causes:
        causes.append("translation tested (no row for the options)")
    return sorted(set(causes))


def census_case(c: Case, schemas: dict[str, Any]) -> dict[str, Any]:
    from sverify import routes

    report = report_of(c, schemas)
    out: dict[str, Any] = {"pattern": c.pattern, "proved": report.proved}
    if unproved := [x.label for x in report.unproved]:
        out["unproved"] = unproved
    if errors := [str(i) for i in report.errors]:
        out["may_fail"] = errors
    engines: dict[str, Any] = {}
    for e in ENGINES:
        prof = routes.profiles().get(e)
        version = prof.versions[0] if prof is not None and prof.versions else None
        try:
            r = routes.choose(report, e, version=version)
        except Exception as err:  # noqa: BLE001 - recorded as the outcome
            engines[e] = {"outcome": "error", "reason": f"{type(err).__name__}: {err}"}
            continue
        if r.refused:
            engines[e] = {"outcome": "refused", "reason": r.reason}
        elif r.evidence == "proved":
            engines[e] = {"outcome": "proved", "class": r.cls}
        else:
            engines[e] = {
                "outcome": "tested",
                "class": r.cls,
                "causes": _tested_causes(report, r, e),
            }
    out["engines"] = engines
    return out


def census(cases: list[Case] | None = None) -> dict[str, dict[str, Any]]:
    schemas = cat.load_schemas()
    return {c.id: census_case(c, schemas) for c in cases or load_cases()}


#: A tested route's main cause, the first of its causes in this order: the
#: rows #929's tolerance work proves first, then the rest.
TESTED = [
    ("agg.fsum's rounding", "tested: double SUM/AVG rounding row (D25)"),
    ("win.agg's window_sum_algo", "tested: double SUM/AVG rounding row (D25)"),
    ("agg.var's", "tested: VAR/STDDEV row (D30)"),
    ("agg.quant's", "tested: quantile row"),
    ("tolerance bound not proved", "tested: tolerance bound not proved"),
    ("robust only by", "tested: robust only by the engine's facts (#1045)"),
    ("agg.isum's overflow", "tested: integer SUM overflow row"),
    ("row tested", "tested: NaN order, -0.0 or overflow row"),
    ("translation tested", "tested: translation tested"),
]

#: A refusal's class, by a phrase of its reason, the first that matches.
REFUSED = [
    ("no translation from the reference to", "refused: no route from the reference (Snowflake)"),
    ("which the observation ignores", "refused: postcondition reads doubles a tolerance ignores"),
    ("not verified: ensures", "refused: postcondition not proved"),
    ("no engine meets the observation's tolerance", "refused: tolerance unmet"),
    ("and the postcondition asks within", "refused: tolerance unmet"),
    ("may keep other rows", "refused: threshold rule (#568)"),
    ("not verified: may fail", "refused: may raise"),
    ("runs on duckdb only", "refused: function runs on DuckDB only (#271)"),
]


def cause_of(result: dict[str, Any]) -> str:
    """The main cause of one engine's outcome, for the table."""
    if result["outcome"] == "proved":
        return "proved"
    if result["outcome"] == "tested":
        causes = " ".join(result["causes"])
        return next(name for key, name in TESTED if key in causes)
    reason = result["reason"]
    return next(
        (name for key, name in REFUSED if key in reason), f"{result['outcome']}: {reason[:80]}"
    )


def table(results: dict[str, dict[str, Any]]) -> str:
    """Counts of outcomes by cause and engine, as Markdown."""
    counts: Counter[tuple[str, str]] = Counter()
    for res in results.values():
        for e, r in res["engines"].items():
            counts[cause_of(r), e] += 1
    causes = sorted({c for c, _ in counts}, key=lambda c: (c.split(":")[0] != "proved", c))
    lines = [
        "| Outcome and cause | " + " | ".join(ENGINES) + " |",
        "|---|" + "---:|" * len(ENGINES),
    ]
    lines += [f"| {c} | " + " | ".join(str(counts[c, e]) for e in ENGINES) + " |" for c in causes]
    totals: Counter[tuple[str, str]] = Counter(
        (r["outcome"], e) for res in results.values() for e, r in res["engines"].items()
    )
    for o in ("proved", "tested", "refused", "error"):
        if any(totals[o, e] for e in ENGINES):
            lines.append(f"| total {o} | " + " | ".join(str(totals[o, e]) for e in ENGINES) + " |")
    return "\n".join(lines)


def by_pattern(results: dict[str, dict[str, Any]]) -> str:
    """Outcomes per case, grouped by pattern, as Markdown."""
    lines = [
        "| Case | Pattern | " + " | ".join(ENGINES) + " |",
        "|---|---|" + "---|" * len(ENGINES),
    ]
    for cid, res in results.items():
        lines.append(
            f"| {cid} | {res['pattern']} | "
            + " | ".join(res["engines"][e]["outcome"] for e in ENGINES)
            + " |"
        )
    return "\n".join(lines)


def main() -> None:
    if "--write" in sys.argv:
        RESULTS.write_text(json.dumps(census(), indent=2, sort_keys=True) + "\n")
    results = json.loads(RESULTS.read_text())
    if "--table" in sys.argv:
        print(table(results))
        print()
        print(by_pattern(results))


if __name__ == "__main__":
    main()
