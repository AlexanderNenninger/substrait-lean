"""The proposer benchmark (#2246, step 0 of #2245): how much a proposer
could close, measured before any proposer API is built.

Maintainer tooling (`sverify_dev`): not in the wheel, and not part of
sverify's API. It measures, over the catalogue's queries
(`catalogue/queries/`), the contract census (`catalogue/contracts.toml`) and
the templates' contracted transforms (`templates/`):

* obligations: what each `verify` leaves open or closes by inference,
  one row each, classified by theory (`theory`): a postcondition not
  proved, an issue a proof must rule out (`Issue`), and a double `SUM` or
  `AVG` with no bound on its rows (`epsilon`'s `unbounded`). `closed_by` is
  `infer` where the checker's backward pass already proposes the
  precondition (the issue's `bound.needs`), and empty where it is open;
* rewrite headroom: per plan with a transformation, whether `Rel.optimize`
  changes it under the gate's rules and under every rule of `--rules`, and
  whether a search over the same rules would change it further. The search
  is not built; its lower bound here is a second pass over the optimized
  plan (a rule the single bottom-up pass misses) and each rule run alone
  (a rule that another, earlier in `Rel.rule`'s order, blocks at a node).
  An e-graph saturated with the same rules finds both.

Every number comes from the checker (`--contract` requests, replayed with a
`"rules"` field or another `transform`), so a long run belongs on homelab
(`homelab-run`):

    uv run python -m sverify_dev.proposer_bench            # the tables
    uv run python -m sverify_dev.proposer_bench --json out.json
    uv run python -m sverify_dev.proposer_bench --limit 5  # a slice
"""

from __future__ import annotations

import argparse
import contextlib
import json
import re
import statistics
import sys
import time
from collections import Counter
from collections.abc import Callable, Iterator
from dataclasses import asdict, dataclass, field
from pathlib import Path
from typing import Any

from sverify import contracts
from sverify_dev import catalogue as cat

REPO = cat.ROOT.parent
TEMPLATES = [
    REPO / "templates" / "pipelines" / "pipelines" / "gdp.py",
    REPO / "templates" / "orchestrators" / "orders.py",
]

#: Theories, in the order the table lists them.
THEORIES = ("LIA", "LRA", "NIA", "FP", "strings", "UF")

_STRING_OPS = re.compile(
    r"\b(UPPER|LOWER|SUBSTR\w*|LIKE|ILIKE|CONCAT|STRPOS|LENGTH|REGEXP\w*|TRIM|LTRIM|RTRIM|"
    r"REPLACE|STARTS_WITH|ENDS_WITH|CONTAINS)\b|\|\||\.(like|upper|lower|length|contains|"
    r"startswith|endswith|re_search|substr|strip)\(",
    re.IGNORECASE,
)
_DOUBLE = re.compile(r"DOUBLE|FLOAT|\bfp\b|_TO_DOUBLE", re.IGNORECASE)


@dataclass
class Obligation:
    source: str
    plan: str
    kind: str
    theory: str
    closed_by: str = ""
    why: str = ""


@dataclass
class Headroom:
    source: str
    plan: str
    gate: list[str] = field(default_factory=list)
    every: list[str] = field(default_factory=list)
    second_gate: list[str] = field(default_factory=list)
    second_every: list[str] = field(default_factory=list)
    alone: list[str] = field(default_factory=list)
    """The rules that change the plan when each is the only rule on."""
    error: str = ""


def _operand(s: str, i: int, step: int) -> str:
    """The operand of the binary operator at `s[i]` on one side: a
    parenthesised group or a run of non-space characters."""
    j = i + step
    while 0 <= j < len(s) and s[j] == " ":
        j += step
    depth, k = 0, j
    while 0 <= k < len(s):
        ch = s[k]
        if ch == ("(" if step > 0 else ")"):
            depth += 1
        elif ch == (")" if step > 0 else "("):
            if depth == 0:
                break
            depth -= 1
        elif ch == " " and depth == 0:
            break
        k += step
    return s[min(j, k) : max(j, k) + 1]


def _nonlinear(expr: str) -> bool:
    """Does `expr` multiply or divide two operands that both read a column?"""
    for m in re.finditer(r"(?<=\s)[*/](?=\s)", expr):
        if "$" in _operand(expr, m.start(), -1) and "$" in _operand(expr, m.start(), 1):
            return True
    return False


def theory(kind: str, expr: str, black_boxes: frozenset[str] = frozenset()) -> str:
    """The theory a proposer needs to close an obligation of `kind` on
    `expr` (Lean's notation for an issue, the Ibis text for a
    postcondition): strings, an uninterpreted black box, the rounding of
    doubles (`FP`), linear arithmetic over the reals (`LRA`, a value bound
    on doubles), nonlinear arithmetic, or linear integer arithmetic
    (integers and decimals)."""
    if _STRING_OPS.search(expr):
        return "strings"
    if any(re.search(rf"\b{re.escape(b)}\(", expr) for b in black_boxes):
        return "UF"
    if kind in {"overflow to infinity", "double bound"}:
        # Rounding and ±inf: a proposer must reason about doubles themselves.
        return "FP"
    if kind == "SUM overflow":
        # n rows times a column bound: linear once `max_rows` is a constant.
        return "LIA"
    if _DOUBLE.search(expr):
        # Over doubles, but about values: a proposer reasons over the reals.
        return "NIA" if _nonlinear(expr) else "LRA"
    return "NIA" if _nonlinear(expr) else "LIA"


def obligations(
    source: str, plan: str, out: dict[str, Any], black_boxes: frozenset[str]
) -> list[Obligation]:
    """The obligations one `--contract` report leaves open or closes by
    inference."""
    rows: list[Obligation] = []
    for item in out.get("ensures") or []:
        if not item.get("proved"):
            rows.append(
                Obligation(
                    source,
                    plan,
                    "postcondition",
                    theory("postcondition", item["name"], black_boxes),
                )
            )
    for issue in out.get("issues") or []:
        if not issue.get("error"):
            continue
        bound = issue.get("bound") or {}
        closed = "infer" if bound.get("needs") or issue.get("assumed") else ""
        rows.append(
            Obligation(
                source,
                plan,
                issue["kind"],
                theory(issue["kind"], issue["expr"], black_boxes),
                closed,
                "" if closed else bound.get("why", ""),
            )
        )
    for name, eps in (out.get("epsilon") or {}).items():
        if isinstance(eps, dict) and eps.get("unbounded"):
            rows.append(
                Obligation(source, plan, "double bound", "FP", "", f"no row bound on {name}")
            )
    return rows


@contextlib.contextmanager
def recording() -> Iterator[list[tuple[dict[str, Any], dict[str, Any], float]]]:
    """Record every `--contract` request `verify` sends, with its report and
    its time."""
    log: list[tuple[dict[str, Any], dict[str, Any], float]] = []
    run = contracts.run_checker

    def rec(flags: tuple[str, ...], text: str) -> tuple[int, str, str]:
        t0 = time.perf_counter()
        code, out, err = run(flags, text)
        if flags == ("--contract",) and code in (0, 4):
            log.append((json.loads(text), json.loads(out), time.perf_counter() - t0))
        return code, out, err

    contracts.run_checker = rec  # pyrefly: ignore[bad-assignment]
    try:
        yield log
    finally:
        contracts.run_checker = run


def _contract(request: dict[str, Any]) -> dict[str, Any] | None:
    code, out, _ = contracts.run_checker(("--contract",), json.dumps(request))
    return json.loads(out) if code in (0, 4) else None


def headroom(
    source: str, plan: str, request: dict[str, Any], out: dict[str, Any], rules: list[str]
) -> Headroom:
    """What `Rel.optimize` changes in one plan, and what a search over the
    same rules would change beyond it (the module's docstring)."""
    h = Headroom(source, plan, gate=list(out.get("rewrites") or []))
    every = _contract({**request, "rules": rules})
    if every is None:
        h.error = "the checker refused the request with every rule on"
        return h
    h.every = list(every.get("rewrites") or [])
    for opt, field_, extra in ((out, "second_gate", {}), (every, "second_every", {"rules": rules})):
        if opt.get("optimized") is None:
            continue
        again = _contract({**request, **extra, "transform": opt["optimized"]})
        if again is None:
            h.error = "the checker refused the optimized plan"
        else:
            setattr(h, field_, list(again.get("rewrites") or []))
    for r in rules:
        one = _contract({**request, "rules": [r]})
        if one is not None and one.get("rewrites"):
            h.alone.append(r)
    return h


def _catalogue() -> Iterator[tuple[str, str, Callable[[], object]]]:
    import sverify

    schemas = cat.load_schemas()
    for q in cat.load_queries():

        def run(q: cat.Query = q) -> object:
            query = cat.build(q, schemas, "native")
            inputs = cat.tables(schemas, q.dataset, "native") if isinstance(query, str) else None
            if q.requires is None or q.ensures is None:
                return sverify.verify(query, tables=inputs)
            requires, ensures = cat.contract(q, schemas, "native")
            return sverify.verify(query, requires=requires, ensures=ensures, tables=inputs)

        yield "catalogue", q.id, run


def _census() -> Iterator[tuple[str, str, Callable[[], object]]]:
    from sverify_dev import contract_census as census

    schemas = cat.load_schemas()
    for c in census.load_cases():
        yield "census", c.id, lambda c=c: census.report_of(c, schemas)


def _templates() -> Iterator[tuple[str, str, Callable[[], object]]]:
    from sverify.cli import _discover

    for path in TEMPLATES:
        yield "templates", path.name, lambda path=path: _discover.load(path)


def plans() -> Iterator[tuple[str, str, Callable[[], object]]]:
    yield from _catalogue()
    yield from _census()
    yield from _templates()


def measure(limit: int | None = None) -> dict[str, Any]:
    import subprocess

    from sverify._checker import checker_path

    def table(flag: str) -> Any:
        done = subprocess.run(
            [str(checker_path()), flag], capture_output=True, text=True, check=True, timeout=120
        )
        return json.loads(done.stdout)

    rule_table = table("--rules")
    rules = [r["name"] for r in rule_table]
    black_boxes = frozenset(b["name"] for b in table("--black-boxes"))
    obs: list[Obligation] = []
    rooms: list[Headroom] = []
    times: list[float] = []
    failed: list[str] = []
    for n, (source, plan, run) in enumerate(plans()):
        if limit is not None and n >= limit:
            break
        with recording() as log:
            try:
                run()
            except Exception as e:  # noqa: BLE001 - recorded, the run goes on
                failed.append(f"{source}/{plan}: {type(e).__name__}: {str(e)[:120]}")
        for i, (request, out, t) in enumerate(log):
            name = plan if len(log) == 1 else f"{plan}#{i}"
            times.append(t)
            obs += obligations(source, name, out, black_boxes)
            if request.get("transform") is not None:
                rooms.append(headroom(source, name, request, out, rules))
        print(f"{source}/{plan}: {len(log)} request(s)", file=sys.stderr)
    return {
        "rules": rules,
        "gate": [r["name"] for r in rule_table if r["on"]],
        "obligations": [asdict(o) for o in obs],
        "headroom": [asdict(h) for h in rooms],
        "failed": failed,
        "contract_seconds": times,
    }


def tables(data: dict[str, Any]) -> str:
    """The tables for #2245's comment, in Markdown."""
    obs = [Obligation(**o) for o in data["obligations"]]
    out = [
        "Obligations by theory (open, closed by `infer`):",
        "",
        "| Theory | " + " | ".join(("catalogue", "census", "templates", "all")) + " |",
        "|---|---:|---:|---:|---:|",
    ]
    sources = ("catalogue", "census", "templates")
    for t in THEORIES:
        cells = []
        for s in (*sources, None):
            sel = [o for o in obs if o.theory == t and (s is None or o.source == s)]
            cells.append(
                f"{sum(not o.closed_by for o in sel)} / {sum(bool(o.closed_by) for o in sel)}"
            )
        out.append(f"| {t} | " + " | ".join(cells) + " |")
    out += [
        "",
        "Open obligations by kind and theory:",
        "",
        "| Kind | Theory | Open | Why (most common) |",
        "|---|---|---:|---|",
    ]
    for (kind, th), n in Counter((o.kind, o.theory) for o in obs if not o.closed_by).most_common():
        why = Counter(o.why for o in obs if o.kind == kind and o.theory == th and not o.closed_by)
        out.append(f"| {kind} | {th} | {n} | {why.most_common(1)[0][0] or '-'} |")
    rooms = [Headroom(**h) for h in data["headroom"]]
    gate = set(data["gate"])
    ok = [h for h in rooms if not h.error]

    def count(pred: Callable[[Headroom], bool]) -> str:
        return str(sum(pred(h) for h in ok))

    out += [
        "",
        f"Rewrite headroom over {len(ok)} plans with a transformation"
        f" ({len(rooms) - len(ok)} refused):",
        "",
        "| Measure | Plans |",
        "|---|---:|",
        f"| `Rel.optimize` changes it, the gate's rules | {count(lambda h: bool(h.gate))} |",
        f"| `Rel.optimize` changes it, every rule | {count(lambda h: bool(h.every))} |",
        "| a second pass changes it again, the gate's rules | "
        + count(lambda h: bool(h.second_gate))
        + " |",
        f"| a second pass changes it again, every rule | {count(lambda h: bool(h.second_every))} |",
        "| a rule fires alone that every rule together does not | "
        + count(lambda h: bool(set(h.alone) - set(h.every)))
        + " |",
        "| left alone by `Rel.optimize` (gate), changed by a search over the gate's rules | "
        + count(lambda h: not h.gate and bool(h.second_gate or set(h.alone) & gate))
        + " |",
        "| left alone by `Rel.optimize` (every rule), changed by a search over every rule | "
        + count(lambda h: not h.every and bool(h.second_every or h.alone))
        + " |",
    ]
    ts = sorted(data["contract_seconds"])
    if ts:
        p95 = ts[min(len(ts) - 1, int(0.95 * len(ts)))]
        out += [
            "",
            f"`--contract` time per request: p50 {statistics.median(ts) * 1000:.0f} ms,"
            f" p95 {p95 * 1000:.0f} ms ({len(ts)} requests).",
        ]
    if data["failed"]:
        out += ["", f"Not measured ({len(data['failed'])}):"] + [f"- {f}" for f in data["failed"]]
    return "\n".join(out)


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    p.add_argument("--limit", type=int, help="measure the first N plans only")
    p.add_argument("--json", type=Path, help="write the measurements to this file")
    p.add_argument("--from-json", type=Path, help="print the tables of an earlier --json run")
    args = p.parse_args(argv)
    if args.from_json is not None:
        data = json.loads(args.from_json.read_text())
    else:
        data = measure(args.limit)
        if args.json is not None:
            args.json.write_text(json.dumps(data, indent=1) + "\n")
    print(tables(data))
    return 0


if __name__ == "__main__":
    sys.exit(main())
