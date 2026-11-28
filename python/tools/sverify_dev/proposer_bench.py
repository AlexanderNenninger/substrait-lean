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

* pairs that lift: for the query-pair sets of #958's validation step, how
  many pairs lift on both sides (`lift_pairs`): each query read as MySQL
  and written as DuckDB's SQL by SQLGlot, then lifted under the reference
  over the set's schema. No checker runs, so it runs anywhere:

    uv run python -m sverify_dev.proposer_bench --pairs DIR --json pairs.json
    uv run python -m sverify_dev.proposer_bench --from-json out.json --from-json pairs.json

  The sets are other projects' data and stay out of the repository. DIR
  holds, read as data only (their solvers and scripts are never run):

  - `sqlsolver_data/`: SQLSolver (SIGMOD 2024), Apache-2.0, at commit
    dcc2a91d8971a4c4d30b055f99d7d8428a1b754b of
    https://github.com/SJTU-IPADS/SQLSolver: `calcite/calcite_tests`,
    `db_rule_instances/spark_tests`, `no_order_by/tests_tpcc` and
    `tests_tpch`, and `schemas/calcite_test`, `tpcc` and `tpch.base.schema.sql`;
    pairs are consecutive lines.
  - `benchmarks/`: VeriEQL (OOPSLA 2024), the artifact
    `VeriEQL-artifact-evaluation.zip` of https://zenodo.org/records/10795614
    (version 5, md5 8869ce8f900bd11d7a2f85a12032b18b), its
    `verieql/benchmarks/*.jsonlines`; CC BY-NC 4.0 on Zenodo, and the
    archive's `license.md` is CC BY-NC-SA 4.0. Each line is one pair with
    its schema.
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


# --------------------------------------------------------------------------
# Pair sets: which of #958's query pairs lift


#: The pair sets `--pairs DIR` reads, by name: the file under DIR and the
#: schema it is read over (`None` where each pair carries its own). DIR holds
#: SQLSolver's `sqlsolver_data/` and VeriEQL's `benchmarks/` (the module doc
#: says where each comes from).
PAIR_SETS: dict[str, tuple[str, str | None]] = {
    "SQLSolver calcite": (
        "sqlsolver_data/calcite/calcite_tests",
        "sqlsolver_data/schemas/calcite_test.base.schema.sql",
    ),
    "SQLSolver spark": (
        "sqlsolver_data/db_rule_instances/spark_tests",
        "sqlsolver_data/schemas/calcite_test.base.schema.sql",
    ),
    "SQLSolver tpcc": (
        "sqlsolver_data/no_order_by/tests_tpcc",
        "sqlsolver_data/schemas/tpcc.base.schema.sql",
    ),
    "SQLSolver tpch": (
        "sqlsolver_data/no_order_by/tests_tpch",
        "sqlsolver_data/schemas/tpch.base.schema.sql",
    ),
    "VeriEQL calcite": ("benchmarks/calcite.jsonlines", None),
    "VeriEQL literature": ("benchmarks/literature.jsonlines", None),
    "VeriEQL leetcode": ("benchmarks/leetcode.jsonlines", None),
}


@dataclass
class PairSet:
    """One pair set's lifting: how many pairs lift on both sides, one or
    neither, and why a query is refused (its construct, or the error's
    first line), counted over queries."""

    name: str
    pairs: int = 0
    both: int = 0
    one: int = 0
    neither: int = 0
    why: dict[str, int] = field(default_factory=dict)


def _ibis_type(text: str) -> Any:
    """The Ibis type of a column type as MySQL writes it (both sets are
    MySQL's), or None where it has none: strings without their length and
    timestamps without a zone, as the lift's inputs are."""
    import ibis.expr.datatypes as dt
    from ibis.backends.sql.datatypes import MySQLType

    text = text.strip().lower()
    if text.startswith("enum"):
        return dt.string
    try:
        t = MySQLType.from_string(text)
    except Exception:  # noqa: BLE001 - an unknown type name, as VeriEQL's NONE
        return None
    if t.is_unknown():
        return None
    if t.is_string():
        return dt.string
    if t.is_timestamp():
        return dt.Timestamp()
    return t


def ddl_schemas(ddl: str) -> dict[str, Any]:
    """The tables of a file of MySQL `CREATE TABLE` statements, as Ibis
    schemas (columns `NOT NULL` non-nullable), or the reason one cannot be."""
    import ibis
    import sqlglot as sg

    out: dict[str, Any] = {}
    for stmt in sg.parse(ddl, read="mysql"):
        if not isinstance(stmt, sg.exp.Create) or not isinstance(stmt.this, sg.exp.Schema):
            continue
        cols: dict[str, Any] = {}
        bad = ""
        for c in stmt.this.expressions:
            if not isinstance(c, sg.exp.ColumnDef) or c.kind is None:
                continue
            t = _ibis_type(c.kind.sql("mysql"))
            if t is None:
                bad = f"column type {c.kind.sql('mysql')}"
                break
            not_null = any(
                isinstance(k.kind, sg.exp.NotNullColumnConstraint)
                and not k.kind.args.get("allow_null")
                for k in c.args.get("constraints") or []
            )
            cols[c.name] = t.copy(nullable=not not_null)
        out[stmt.this.this.name] = bad or ibis.schema(cols)
    return out


def json_schemas(schema: dict[str, Any], constraints: list[Any] | None) -> dict[str, Any]:
    """The tables of a VeriEQL pair, as Ibis schemas (its `not_null`
    columns non-nullable), or the reason one cannot be."""
    import ibis

    not_null = {
        k["not_null"]["value"].upper()
        for k in constraints or []
        if isinstance(k, dict) and "not_null" in k
    }
    out: dict[str, Any] = {}
    for table, columns in (schema or {}).items():
        cols: dict[str, Any] = {}
        bad = ""
        for col, text in columns.items():
            t = _ibis_type(str(text))
            if t is None:
                bad = f"column type {text}"
                break
            cols[col] = t.copy(nullable=f"{table}__{col}".upper() not in not_null)
        out[table] = bad or ibis.schema(cols)
    return out


def lift_reason(query: str, schemas: dict[str, Any]) -> str:
    """Empty where `query`, read as MySQL and written as DuckDB's SQL by
    SQLGlot, lifts under the reference over `schemas`; else why not."""
    import sqlglot as sg

    from sverify.engine import lift_sql_plan
    from sverify.errors import UnsupportedError
    from sverify_duckdb.sql import full_name_duckdb as full_name

    try:
        sql = sg.transpile(query, read="mysql", write="duckdb")[0]
    except sg.errors.SqlglotError:
        return "SQLGlot cannot read it as MySQL"
    try:
        read = {full_name(t) for t in sg.parse_one(sql, read="duckdb").find_all(sg.exp.Table)}
    except sg.errors.SqlglotError:
        return "SQLGlot cannot read its own DuckDB text"
    bad = {n: s for n, s in schemas.items() if isinstance(s, str) and full_name(n) in read}
    if bad:
        return f"schema: {next(iter(bad.values()))}"
    try:
        lift_sql_plan({n: s for n, s in schemas.items() if not isinstance(s, str)}, sql)
    except UnsupportedError as e:
        return e.construct or str(e).splitlines()[0][:80]
    except Exception as e:  # noqa: BLE001 - a crash of the lift is a finding too
        return f"crash: {type(e).__name__}"
    return ""


def _pairs_of(
    root: Path, file: str, schema: str | None
) -> Iterator[tuple[str, str, dict[str, Any]]]:
    path = root / file
    if schema is not None:
        tables = ddl_schemas((root / schema).read_text(encoding="utf-8"))
        lines = [x for x in path.read_text(encoding="utf-8").splitlines() if x.strip()]
        for a, b in zip(lines[::2], lines[1::2], strict=False):
            yield a, b, tables
        return
    for line in path.read_text(encoding="utf-8").splitlines():
        if line.strip():
            r = json.loads(line)
            yield r["pair"][0], r["pair"][1], json_schemas(r["schema"], r.get("constraint"))


#: Seconds a query may take to lift before it counts as refused ("timeout"),
#: so one query that hangs the lift cannot stall a run over 25,000 pairs.
LIFT_SECONDS = 10


class _Timeout(BaseException):  # past `lift_reason`'s `except Exception`
    pass


def _timed(query: str, schemas: dict[str, Any]) -> str:
    """`lift_reason`, "timeout" past `LIFT_SECONDS`."""
    import signal

    def stop(*_: object) -> None:
        raise _Timeout

    old = signal.signal(signal.SIGALRM, stop)
    signal.alarm(LIFT_SECONDS)
    try:
        return lift_reason(query, schemas)
    except _Timeout:
        return "timeout"
    finally:
        signal.alarm(0)
        signal.signal(signal.SIGALRM, old)


def lift_pairs(root: Path, limit: int | None = None) -> list[PairSet]:
    """Each of `PAIR_SETS` found under `root`, lifted pair by pair (the
    first `limit` pairs of each where given)."""
    out = []
    for name, (file, schema) in PAIR_SETS.items():
        if not (root / file).exists():
            continue
        s = PairSet(name)
        why: Counter[str] = Counter()
        for i, (a, b, tables) in enumerate(_pairs_of(root, file, schema)):
            if limit is not None and i >= limit:
                break
            reasons = [_timed(a, tables), _timed(b, tables)]
            why.update(r for r in reasons if r)
            s.pairs += 1
            ok = sum(not r for r in reasons)
            s.both += ok == 2
            s.one += ok == 1
            s.neither += ok == 0
        s.why = dict(why.most_common())
        out.append(s)
        print(f"{name}: {s.both} of {s.pairs} lift", file=sys.stderr, flush=True)
    return out


def pair_table(sets: list[PairSet]) -> list[str]:
    """The pair sets' table for #2245's comment, in Markdown."""
    out = [
        "Pairs that lift (both queries, read as MySQL, lift under the reference):",
        "",
        "| Set | Pairs | Both lift | One | Neither | Most common refusals (queries) |",
        "|---|---:|---:|---:|---:|---|",
    ]
    for s in sets:
        top = ", ".join(f"{w} ({n})" for w, n in list(s.why.items())[:4]) or "-"
        out.append(f"| {s.name} | {s.pairs} | {s.both} | {s.one} | {s.neither} | {top} |")
    return out


def tables(data: dict[str, Any]) -> str:
    """The tables for #2245's comment, in Markdown: the checker's where
    `data` has them, and the pair sets' where it has those."""
    out = _checker_tables(data) if "obligations" in data else []
    if "pairs" in data:
        out += ([""] if out else []) + pair_table([PairSet(**s) for s in data["pairs"]])
    return "\n".join(out)


def _checker_tables(data: dict[str, Any]) -> list[str]:
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
    return out


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    p.add_argument("--limit", type=int, help="measure the first N plans (or pairs of each set)")
    p.add_argument("--json", type=Path, help="write the measurements to this file")
    p.add_argument(
        "--from-json",
        type=Path,
        action="append",
        help="print the tables of earlier --json runs (repeatable; later runs win)",
    )
    p.add_argument(
        "--pairs",
        type=Path,
        help="lift the pair sets under this directory instead of asking the checker",
    )
    args = p.parse_args(argv)
    if args.from_json:
        data: dict[str, Any] = {}
        for f in args.from_json:
            data |= json.loads(f.read_text())
    else:
        if args.pairs is not None:
            data = {"pairs": [asdict(s) for s in lift_pairs(args.pairs, args.limit)]}
        else:
            data = measure(args.limit)
        if args.json is not None:
            args.json.write_text(json.dumps(data, indent=1) + "\n")
    print(tables(data))
    return 0


if __name__ == "__main__":
    sys.exit(main())
