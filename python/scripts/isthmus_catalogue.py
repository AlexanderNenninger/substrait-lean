"""Compile the query catalogue with Isthmus and compare with sverify's own
producers (`catalogue/status.json`).

Each query's SQL (the catalogue's own, or Ibis's Postgres SQL adapted to
Calcite) goes through Isthmus and `substrait-check`; a verified plan runs on
the engines, against DataFusion running the query's DataFusion SQL as the
reference (`catalogue.probe_engines`). Set `SVERIFY_CHECK` to compare checker
versions.

Usage: uv run python scripts/isthmus_catalogue.py [--json out.json] [query-id | suite ...]
"""

import argparse
import json
from collections import Counter
from typing import Any

import ibis
import sqlglot
import sqlglot.expressions as sge

from sverify import catalogue as cat
from sverify.engine import (
    SqlError,
    connect,
    isthmus_json,
    run_checker,
    run_sql,
    to_sql,
    written_plan,
)

#: Functions whose window frame Calcite refuses; their frame changes nothing.
RANKING = tuple(
    getattr(sge, n)
    for n in ("RowNumber", "Rank", "DenseRank", "Ntile", "PercentRank", "CumeDist", "Lag", "Lead")
    if hasattr(sge, n)
)


class Calcite(sqlglot.Dialect):
    class Generator(sqlglot.Generator):
        TRANSFORMS = {  # noqa: RUF012 - sqlglot's own convention
            **sqlglot.Generator.TRANSFORMS,
            sge.StrPosition: lambda self, e: (
                f"POSITION({self.sql(e, 'substr')} IN {self.sql(e, 'this')})"
            ),
        }


def calcite_sql(sql: str) -> str:
    """Ibis's Postgres SQL, adapted to Calcite's default conformance:
    `DATE_TRUNC` becomes `FLOOR(x TO unit)`, `DATE(x)` a cast, `GROUP BY`
    ordinals the selected expressions, and ranking and offset functions lose
    the frame Ibis writes for them."""
    tree = sqlglot.parse_one(sql, read="postgres")
    for t in list(tree.find_all(sge.TimestampTrunc, sge.DateTrunc)):
        unit = t.args.get("unit")
        name = unit.name if unit is not None else "DAY"
        t.replace(sge.Floor(this=t.this.copy(), to=sge.var(name.upper())))
    for d in list(tree.find_all(sge.Date, sge.TsOrDsToDate)):
        d.replace(sge.Cast(this=d.this.copy(), to=sge.DataType.build("DATE")))
    for select in tree.find_all(sge.Select):
        group = select.args.get("group")
        if group is None:
            continue
        exprs = [e.unalias() if isinstance(e, sge.Alias) else e for e in select.expressions]
        for i, g in enumerate(list(group.expressions)):
            if isinstance(g, sge.Literal) and g.is_int:
                group.expressions[i] = exprs[int(g.this) - 1].copy()
    for w in list(tree.find_all(sge.Window)):
        if isinstance(w.this, RANKING) and w.args.get("spec") is not None:
            w.set("spec", None)
    return tree.sql(dialect=Calcite)


def first_error(out: str) -> str:
    lines = [ln for ln in out.splitlines() if ln.startswith(("error:", "well-formed: no"))]
    return (lines or [out.strip()])[-1][:200]


def probe(q: cat.Query, schemas: dict[str, Any], profile: cat.Profile) -> dict[str, Any]:
    con = connect(sql_producer="isthmus")
    for name, table in cat.synthetic(schemas, q.dataset, profile).items():
        con.put(name, table)
    try:
        built = cat.build(q, schemas, profile)
        # The catalogue's SQL is DataFusion's; Ibis's Postgres SQL is closest to Calcite's.
        sql = (
            built if isinstance(built, str) else calcite_sql(ibis.to_sql(built, dialect="postgres"))
        )
    except Exception as e:  # noqa: BLE001 - recorded
        return {"isthmus": "no sql", "detail": str(e).splitlines()[0][:200]}
    try:
        plan = isthmus_json(con, sql)
    except SqlError as e:
        return {"isthmus": "refused", "detail": str(e)[:200]}
    code, out, err = run_checker((), plan)
    if code != 0:
        return {"isthmus": "ok", "checker": "rejected", "detail": first_error(out + err)}
    try:
        reference = cat._rows(run_sql(con, built if isinstance(built, str) else to_sql(built)))  # noqa: SLF001
    except Exception:  # noqa: BLE001 - DataFusion's own failures
        reference = None
    try:
        engines = cat.probe_engines(con, written_plan(plan), reference)
    except Exception as e:  # noqa: BLE001
        engines = {"all": f"error: {str(e).splitlines()[0][:150]}"}
    return {"isthmus": "ok", "checker": "verified", "engines": engines}


def effective(r: dict[str, Any]) -> dict[str, Any]:
    return r.get("as_double", r) if r.get("checker") != "verified" else r


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--json")
    ap.add_argument("only", nargs="*")
    args = ap.parse_args()
    schemas = cat.load_schemas()
    status = json.loads((cat.ROOT / "status.json").read_text())
    queries = [q for q in cat.load_queries() if not args.only or {q.id, q.suite} & set(args.only)]
    results: dict[str, dict[str, Any]] = {}
    for q in queries:
        if q.not_expressible is not None:
            continue
        r = probe(q, schemas, "native")
        if r.get("checker") != "verified" and cat.has_decimal(schemas, q.dataset):
            r["as_double"] = probe(q, schemas, "double")
        e = effective(r)
        own = cat.effective(status[q.id])["checker"] if q.id in status else "?"
        results[q.id] = {**r, "sverify": own}
        print(f"{q.id:28} {e['isthmus']:8} {e.get('checker', ''):9} sverify={own:9} "
              f"{json.dumps(e.get('engines', ''))[:80]} {e.get('detail', '')[:100]}")  # fmt: skip
    if args.json:
        with open(args.json, "w") as f:
            json.dump(results, f, indent=1)

    eff = effective
    verified = {k for k, r in results.items() if eff(r).get("checker") == "verified"}
    own = {k for k, r in results.items() if r["sverify"] == "verified"}
    print(f"\n{len(results)} queries; Isthmus: {len(verified)} verify; sverify: {len(own)}")
    both, only_i, only_s = len(verified & own), len(verified - own), len(own - verified)
    print(f"both: {both}, only Isthmus: {only_i}, only sverify: {only_s}")
    mismatch = [
        k for k in verified if any("mismatch" in v for v in eff(results[k])["engines"].values())
    ]
    print(f"verified, an engine disagrees with DataFusion's reference: {sorted(mismatch)}")
    print(Counter((eff(r)["isthmus"], eff(r).get("checker")) for r in results.values()))
    details = Counter(
        eff(r).get("detail", "")[:70] for r in results.values() if eff(r).get("detail")
    )
    for d, n in details.most_common(20):
        print(f"{n:4}  {d}")


if __name__ == "__main__":
    main()
