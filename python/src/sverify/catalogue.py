"""The query catalogue (`catalogue/` in the repository): real analytical queries,
and how far `sverify` gets with each.

The catalogue is hand-written TOML:

* `catalogue/features.toml`: the vocabulary of operators and features a query
  may need, each with Lean's support for it today;
* `catalogue/schemas.toml`: the tables of each dataset, as Ibis types, with
  value pools for the synthetic data;
* `catalogue/queries/*.toml`: the queries, each with its intent, source,
  licence, features, pitfalls and an Ibis expression (or SQL).

`probe` runs a query the way `sverify` runs everything (an Ibis expression
through `sverify`'s producer, SQL through DataFusion's, then `substrait-check`)
and runs it on DataFusion over small synthetic tables. When the checker
accepts the plan, it also runs Lean's written plan on Polars and DuckDB,
compares their rows with DataFusion's, and writes Snowflake SQL for it.
`catalogue/status.json` holds the results, `catalogue/INDEX.md` the readable
index and `catalogue/FINDINGS.md` the summary tables (between its `stats`
markers); regenerate all three with

    uv run python -m sverify.catalogue --write

`tests/test_catalogue.py` checks that the catalogue is well-formed and that
every recorded status still holds.
"""

from __future__ import annotations

import datetime as dt
import json
import random
import re
import sys
import tomllib
from collections import Counter
from dataclasses import dataclass, field
from decimal import Decimal
from pathlib import Path
from typing import Any, Literal

import ibis
import ibis.expr.types as ir
import pyarrow as pa
from ibis import _

from sverify.engine import (
    Connection,
    connect,
    plan_json,
    put_table,
    run_checker,
    run_plan,
    run_sql,
    to_sql,
    written_plan,
)
from sverify.ibis_substrait import Unsupported

ROOT = Path(__file__).resolve().parents[3] / "catalogue"

Profile = Literal["native", "double"]

#: Fields every query has.
REQUIRED = ("id", "title", "intent", "domain", "source", "features")
SOURCE_FIELDS = ("name", "url", "licence")
PITFALL_FIELDS = ("description", "engines", "quirks")
DOMAINS = (
    "benchmark", "retail", "web-analytics", "product-analytics", "finance", "saas",
    "iot", "hr", "movies", "logistics", "marketing", "generic",
)  # fmt: skip


@dataclass(frozen=True)
class Feature:
    key: str
    group: str
    description: str
    lean: Literal["yes", "partial", "no"]
    """Does Lean's model (and the parser) cover it today?"""
    note: str = ""


@dataclass(frozen=True)
class Query:
    id: str
    suite: str
    title: str
    intent: str
    domain: str
    dataset: str
    source: dict[str, str]
    features: list[str]
    pitfalls: list[str] = field(default_factory=list)
    ibis: str | None = None
    sql: str | None = None
    not_expressible: str | None = None
    rewrites: list[str] = field(default_factory=list)
    """Features of the original query that this formulation rewrote away, as
    `feature -> how` (an Ibis user would write it so)."""
    notes: str = ""

    @property
    def needs(self) -> list[str]:
        """Features of the original query: `features` plus the rewritten ones."""
        orig = [r.split("->")[0].strip() for r in self.rewrites]
        return self.features + [f for f in orig if f not in self.features]


def load_features(root: Path = ROOT) -> dict[str, Feature]:
    data = tomllib.loads((root / "features.toml").read_text())
    out: dict[str, Feature] = {}
    for group, feats in data.items():
        for key, f in feats.items():
            out[key] = Feature(key, group, f["description"], f["lean"], f.get("note", ""))
    return out


def load_pitfalls(root: Path = ROOT) -> dict[str, Any]:
    return tomllib.loads((root / "pitfalls.toml").read_text())


def load_schemas(root: Path = ROOT) -> dict[str, Any]:
    return tomllib.loads((root / "schemas.toml").read_text())


def load_queries(root: Path = ROOT) -> list[Query]:
    queries = []
    for path in sorted((root / "queries").glob("*.toml")):
        data = tomllib.loads(path.read_text())
        dataset = data.get("dataset", "")
        for q in data["query"]:
            missing = [k for k in REQUIRED if k not in q]
            if missing:
                raise ValueError(f"{path.name}: query {q.get('id', '?')} lacks {missing}")
            queries.append(
                Query(
                    id=q["id"],
                    suite=path.stem,
                    title=q["title"],
                    intent=q["intent"],
                    domain=q["domain"],
                    dataset=q.get("dataset", dataset),
                    source=q["source"],
                    features=q["features"],
                    pitfalls=q.get("pitfalls", []),
                    ibis=q.get("ibis"),
                    sql=q.get("sql"),
                    not_expressible=q.get("not_expressible"),
                    rewrites=q.get("rewrites", []),
                    notes=q.get("notes", ""),
                )
            )
    return queries


def validate(
    queries: list[Query],
    features: dict[str, Feature],
    schemas: dict[str, Any],
    pitfalls: dict[str, Any],
) -> list[str]:
    """Problems with the catalogue's structure (empty if none)."""
    problems = []
    for tag, p in pitfalls.items():
        problems += [f"pitfall {tag}: unknown key {k}" for k in p if k not in PITFALL_FIELDS]
    ids = Counter(q.id for q in queries)
    problems += [f"duplicate id {i}" for i, n in ids.items() if n > 1]
    for q in queries:
        where = f"{q.suite}/{q.id}"
        problems += [f"{where}: unknown feature {f!r}" for f in q.features if f not in features]
        if len(set(q.features)) != len(q.features):
            problems.append(f"{where}: repeated feature")
        if q.domain not in DOMAINS:
            problems.append(f"{where}: unknown domain {q.domain!r}")
        if q.dataset not in schemas["datasets"]:
            problems.append(f"{where}: unknown dataset {q.dataset!r}")
        missing = [k for k in SOURCE_FIELDS if not q.source.get(k)]
        if missing:
            problems.append(f"{where}: source lacks {missing}")
        if not q.source.get("url", "").startswith("https://"):
            problems.append(f"{where}: source url is not https")
        if sum(x is not None for x in (q.ibis, q.sql, q.not_expressible)) != 1:
            problems.append(f"{where}: needs exactly one of ibis, sql, not_expressible")
        for p in q.pitfalls:
            tag = p.split(":")[0].strip()
            if tag not in pitfalls:
                problems.append(f"{where}: unknown pitfall {tag!r}")
        for r in q.rewrites:
            orig = r.split("->")[0].strip()
            if "->" not in r or orig not in features:
                problems.append(f"{where}: rewrite {r!r} is not 'feature -> how'")
        if not q.intent.endswith("."):
            problems.append(f"{where}: intent should be one sentence ending in '.'")
    return problems


# Tables and synthetic data


def ibis_type(t: str, profile: Profile) -> str:
    if profile == "double" and t.startswith("decimal"):
        return "float64"
    return t


def tables(schemas: dict[str, Any], dataset: str, profile: Profile) -> dict[str, ir.Table]:
    spec = schemas["datasets"][dataset]["tables"]
    return {
        name: ibis.table({c: ibis_type(t, profile) for c, t in cols.items()}, name=name)
        for name, cols in spec.items()
    }


def _value(rng: random.Random, t: str, pool: list | None, nullable: bool) -> Any:
    if nullable and rng.random() < 0.1:
        return None
    if pool is not None:
        v = rng.choice(pool)
        if t == "date" and isinstance(v, str):
            return dt.date.fromisoformat(v)
        if t == "timestamp" and isinstance(v, str):
            return dt.datetime.fromisoformat(v)
        if t.startswith("decimal"):
            return Decimal(str(v))
        return v
    if t.startswith("int"):
        return rng.randint(0, 5)
    if t == "float64":
        return rng.choice([0.0, 0.5, 1.25, 2.0, 3.5, 10.0, -1.5])
    if t.startswith("decimal"):
        scale = int(t.split(",")[1].rstrip(")"))
        return Decimal(rng.randint(-100, 1000)).scaleb(-scale)
    if t == "string":
        return rng.choice(["a", "b", "ab", "c", ""])
    if t == "boolean":
        return rng.random() < 0.5
    if t == "date":
        return dt.date(1993, 1, 1) + dt.timedelta(days=rng.randint(0, 6 * 365))
    if t == "timestamp":
        return dt.datetime(2024, 1, 1) + dt.timedelta(minutes=rng.randint(0, 60 * 24 * 60))
    raise ValueError(f"no synthetic values for {t}")


def synthetic(
    schemas: dict[str, Any], dataset: str, profile: Profile, rows: int = 30, seed: int = 0
) -> dict[str, pa.Table]:
    """Small random tables for `dataset`. Columns draw from `values` pools
    where the schema gives one (so filters on literals match), integer
    columns from 0..5 (so joins on keys match), and are NULL one time in ten
    unless listed in `not_null`."""
    ds = schemas["datasets"][dataset]
    pools = ds.get("values", {})
    not_null = set(ds.get("not_null", []))
    out = {}
    for name, cols in ds["tables"].items():
        rng = random.Random(f"{seed}/{dataset}/{name}")
        arrow = tables(schemas, dataset, profile)[name].schema().to_pyarrow()
        data: dict[str, list] = {}
        for c, t in cols.items():
            nullable = f"{name}.{c}" not in not_null
            vals = [_value(rng, t, pools.get(f"{name}.{c}"), nullable) for _ in range(rows)]
            if profile == "double" and t.startswith("decimal"):
                vals = [None if v is None else float(v) for v in vals]
            data[c] = vals
        out[name] = pa.table({c: pa.array(v, arrow.field(c).type) for c, v in data.items()})
    return out


# Probing


def date_literal(s: str) -> ir.DateValue:
    """A DATE literal. `ibis.date("…")` compiles to `DATE_TRUNC('DAY', '…')`
    for DataFusion, which the checker refuses (date_trunc of a non-timestamp)."""
    return ibis.literal(s).cast("date")  # pyrefly: ignore


def build(q: Query, schemas: dict[str, Any], profile: Profile) -> ir.Table | str:
    """The query: an Ibis expression, or its DataFusion SQL."""
    if q.sql is not None:
        return q.sql
    assert q.ibis is not None
    import sverify

    ns: dict[str, Any] = {"ibis": ibis, "_": _, "sv": sverify, "D": date_literal}
    ns.update(tables(schemas, q.dataset, profile))
    exec(q.ibis, ns)  # noqa: S102 - the catalogue's own code
    return ns["q"]


def _value_of(v: object) -> object:
    """One representation per value: DataFusion types ROW_NUMBER as a decimal,
    DuckDB gives timestamp differences as month-day-nano intervals."""
    if isinstance(v, Decimal) and v == v.to_integral_value():
        return int(v)
    if isinstance(v, pa.MonthDayNano) and v.months == 0:
        return dt.timedelta(days=v.days, microseconds=v.nanoseconds // 1000)
    return v


def _rows(table: pa.Table) -> list[tuple]:
    return [tuple(_value_of(v) for v in r.values()) for r in table.to_pylist()]


def _canonical(rows: list[tuple]) -> list[str]:
    def norm(v: object) -> object:
        if isinstance(v, float) and v == int(v) and abs(v) < 2**53:
            return int(v)
        if isinstance(v, float):
            return round(v, 6)
        if isinstance(v, Decimal):
            return round(float(v), 6)
        return v

    return sorted(repr(tuple(norm(v) for v in r)) for r in rows)


def _first_line(e: BaseException | str) -> str:
    text = str(e).strip()
    return (text.splitlines() or [type(e).__name__])[0][:200]


def probe_engines(con: Connection, plan: str, reference: list[tuple] | None) -> dict[str, str]:
    """Run Lean's written plan on each engine and compare with DataFusion's
    rows (`reference`, None if DataFusion failed).

    Polars and DuckDB map to `runs` (they agree with DataFusion as bags on
    the synthetic tables; with a FETCH or a window, where ties make
    DataFusion's choice of rows legitimately differ, with each other, row for
    row where the order matters), `differs`, `refused: …` (the translation
    refuses the plan) or `error: …`. Snowflake is `sql` or `sql (tie_free)`
    (SQL written and parsed with sqlglot, not run) or `refused: …`."""
    import sqlglot

    from sverify import polars_engine
    from sverify.sql import Unsupported as Untranslatable
    from sverify.sql import parse_plan
    from sverify.sql import to_sql as plan_sql
    from sverify.sql.core import Fetch, Window, order_matters
    from sverify.sql.snowflake import SNOWFLAKE

    out: dict[str, str] = {}
    results: dict[str, list[tuple]] = {}
    for engine in ("polars", "duckdb"):
        try:
            results[engine] = _rows(run_plan(con, plan, engine))  # pyrefly: ignore
        except (polars_engine.Unsupported, Untranslatable) as e:
            out[engine] = f"refused: {_first_line(e)}"
        except Exception as e:  # noqa: BLE001 - runtime errors of either engine
            out[engine] = f"error: {_first_line(e)}"
    root = parse_plan(json.loads(plan)).root if results else None

    def has(r: object, kinds: tuple[type, ...]) -> bool:
        return isinstance(r, kinds) or any(
            has(getattr(r, k), kinds) for k in ("input", "left", "right") if hasattr(r, k)
        )

    for engine, got in results.items():
        if reference is None or has(root, (Fetch, Window)):
            # "The first n rows" of an unsorted input, and ROW_NUMBER or LAG
            # over ties, differ between engines (the synthetic data has ties);
            # Polars and DuckDB both follow Rel.eval's order, so they must agree.
            assert root is not None
            other = results.get("duckdb" if engine == "polars" else "polars")
            ok = other is None or (
                repr(got) == repr(other)
                if order_matters(root)
                else _canonical(got) == _canonical(other)
            )
        else:
            ok = _canonical(got) == _canonical(reference)
        out[engine] = "runs" if ok else "differs"
    try:
        text = plan_sql(json.loads(plan), SNOWFLAKE)
        out["snowflake"] = "sql"
    except Untranslatable as e:
        try:
            text = plan_sql(json.loads(plan), SNOWFLAKE, tie_free=True)
            out["snowflake"] = "sql (tie_free)"
        except Untranslatable:
            text = None
            out["snowflake"] = f"refused: {_first_line(e)}"
    if text is not None:
        sqlglot.parse_one(text, read="snowflake")
    return dict(sorted(out.items()))


def probe_profile(
    con: Connection, q: Query, schemas: dict[str, Any], profile: Profile
) -> dict[str, Any]:
    """The query's status on one profile of its dataset.

    Ibis expressions go through `sverify`'s own producer (`plan_json`), SQL
    through DataFusion's. `checker` is `verified`, `rejected` (by
    `substrait-check`, or with `stage: producer` by the producer, which
    refuses what Lean does not model) or `upstream`, in which case `stage`
    says where it failed: `ibis` (building the expression), `producer`,
    `datafusion` (planning the SQL) or `substrait` (DataFusion's Substrait
    producer). `datafusion` says whether DataFusion runs the query itself
    (Ibis's own SQL for an expression) on the synthetic tables, verified or
    not."""
    for name, table in synthetic(schemas, q.dataset, profile).items():
        put_table(con, name, table)
    try:
        query = build(q, schemas, profile)
    except Exception as e:  # noqa: BLE001 - any Ibis failure counts
        return {"checker": "upstream", "stage": "ibis", "detail": _first_line(e)}
    # DataFusion runs the query itself: Ibis's own SQL for an expression.
    try:
        sql = query if isinstance(query, str) else to_sql(query)
        reference: list[tuple] | None = _rows(run_sql(con, sql))
        ran = "runs"
    except Exception as e:  # noqa: BLE001 - DataFusion's own failures are findings
        reference, ran = None, f"error: {_first_line(e)}"
    if isinstance(query, str):
        try:
            con.datafusion.sql(query).logical_plan()
        except Exception as e:  # noqa: BLE001
            return {"checker": "upstream", "stage": "datafusion", "detail": _first_line(e)}
    try:
        plan = plan_json(con, query)
    except Unsupported as e:
        return {"checker": "rejected", "stage": "producer", "detail": _first_line(e),
                "datafusion": ran}  # fmt: skip
    except Exception as e:  # noqa: BLE001
        stage = "substrait" if isinstance(query, str) else "producer"
        return {"checker": "upstream", "stage": stage, "detail": _first_line(e),
                "datafusion": ran}  # fmt: skip
    code, stdout, stderr = run_checker((), plan)
    out = stdout + stderr
    if code != 0:
        lines = [ln for ln in out.splitlines() if ln.startswith(("error:", "well-formed: no"))]
        detail = _first_line((lines or [out])[-1])
        return {"checker": "rejected", "detail": detail, "datafusion": ran}
    return {
        "checker": "verified",
        "incremental": "incremental: yes" in out,
        "datafusion": ran,
        "engines": probe_engines(con, written_plan(plan), reference),
    }


def has_decimal(schemas: dict[str, Any], dataset: str) -> bool:
    spec = schemas["datasets"][dataset]["tables"]
    return any(t.startswith("decimal") for cols in spec.values() for t in cols.values())


def probe(con: Connection, q: Query, schemas: dict[str, Any]) -> dict[str, Any]:
    """The query's status; when it fails on its own types and the dataset has
    DECIMAL columns, also its status with DOUBLE in their place."""
    if q.not_expressible is not None:
        return {"checker": "none", "detail": q.not_expressible}
    result = probe_profile(con, q, schemas, "native")
    if result["checker"] != "verified" and has_decimal(schemas, q.dataset):
        result["as_double"] = probe_profile(con, q, schemas, "double")
    return result


def probe_all(queries: list[Query], schemas: dict[str, Any]) -> dict[str, dict[str, Any]]:
    con = connect()
    return {q.id: probe(con, q, schemas) for q in queries}


# Summaries


def effective(s: dict[str, Any]) -> dict[str, Any]:
    """The status that counts for the summaries: as DOUBLE when only that verifies."""
    return s.get("as_double", s) if s["checker"] != "verified" else s


def runs_on(s: dict[str, Any], engine: str) -> bool:
    e = effective(s)
    status = (
        e.get("datafusion", "") if engine == "datafusion" else e.get("engines", {}).get(engine, "")
    )
    return status == "runs" or status.startswith("sql")


def blockers(q: Query, features: dict[str, Feature]) -> list[str]:
    """The query's features Lean does not cover (fully)."""
    return [f for f in q.features if features[f].lean != "yes"]


def consistency(
    queries: list[Query], features: dict[str, Feature], status: dict[str, dict[str, Any]]
) -> list[str]:
    """Annotations that contradict the probes: a verified query needing a
    feature marked unsupported, or a refused query whose features are all
    marked supported."""
    problems = []
    for q in queries:
        s = status[q.id]
        e = effective(s)
        bad = [f for f in q.features if features[f].lean == "no"]
        if e is not s:  # verified only with DOUBLE in place of DECIMAL
            bad = [f for f in bad if f != "decimal"]
        if e["checker"] == "verified" and bad:
            problems.append(f"{q.id}: verified, yet uses {bad} (lean = 'no')")
        if e["checker"] in ("rejected", "upstream") and not blockers(q, features):
            problems.append(f"{q.id}: {e['checker']} ({e['detail']}), yet every feature is 'yes'")
        for st in (s, e) if e is not s else (s,):
            if st["checker"] in ("rejected", "upstream"):
                cause = blocker_of(st["detail"])
                if cause is None:
                    problems.append(f"{q.id}: no feature known for {st['detail']!r}")
                elif not cause & set(q.features):
                    problems.append(f"{q.id}: fails on {sorted(cause)}, which it does not list")
    return problems


#: What a failure message means: the features that can cause it.
BLOCKERS: list[tuple[str, set[str]]] = [
    (r"(sum|avg|min|max) of this type", {"decimal"}),
    (r"DECIMAL values", {"decimal"}),
    (r"(min|max) of doubles", {"min_max"}),
    (r"month and year intervals", {"interval_month"}),
    (r"date_part is only supported on timestamps", {"date_part"}),
    (r"date_trunc is only supported on timestamps", {"date_trunc"}),
    (r"date part 'EPOCH'|extract_epoch|to_char", {"epoch"}),
    (r"grouping sets", {"grouping_sets"}),
    (r"aggregate function: (median|approx_median|percentile)|'Quantile'", {"percentile"}),
    (r"aggregate function: (stddev|var)", {"stddev_var"}),
    (r"corr takes|aggregate function: (corr|covar)", {"corr"}),
    (r"string_agg|array_agg", {"string_agg"}),
    (r"approx_distinct", {"approx_distinct"}),
    (r"bool_and|bool_or", {"bool_agg"}),
    (r"ordered aggregates|aggregate function: first_value", {"arg_max", "pivot"}),
    (r"window function: (rank|dense_rank)", {"rank"}),
    (r"window function: (ntile|percent_rank|cume_dist)", {"ntile"}),
    (r"window function: (first_value|last_value|nth_value)", {"first_last_value"}),
    (
        r"window function: (sum|avg|count|min|max)",
        {"running_agg", "window_partition_agg", "rows_frame", "range_frame"},
    ),
    (r"frame offsets for (RANGE|ROWS)|following end point", {"range_frame", "rows_frame"}),
    (r"regexp_replace|regexp_extract", {"regex_replace"}),
    (r"split_part|concat_ws", {"string_split"}),
    (r"md5|sha|'Hash'", {"hash"}),
    (r"date_bin|'TimestampBucket'", {"time_bucket"}),
    (r"Kind\.str to Substrait\.Parse\.Kind\.other", {"dynamic_interval"}),
    (r"Kind\.time to Substrait\.Parse\.Kind\.other|AT TIME ZONE", {"timezone"}),
    (r"Kind\.date to Substrait\.Parse\.Kind\.str", {"cast_date"}),
    (r"Kind\.time to Substrait\.Parse\.Kind\.int|'TimestampDelta'", {"interval_to_number"}),
    (r"function (ln|exp|log|log10|log2|sqrt)/", {"math_transcendental"}),
    (r"Cannot convert <subquery>", {"scalar_subquery", "correlated_subquery"}),
    (r"Cannot convert Exists", {"exists_subquery"}),
    (r"inPredicate", {"not_in_subquery"}),
    (r"RecursiveQuery", {"recursive_cte"}),
    (r"Unnest", {"unnest", "generate_series"}),
    # sverify's Ibis producer
    (r"type decimal\(", {"decimal"}),
    (r"DateAdd|DateSub", {"interval_month", "interval_day_time", "dynamic_interval"}),
    (r"intervals in months", {"interval_month"}),
    (r"IntervalFromInteger", {"dynamic_interval"}),
    (r"DateDiff", {"date_diff"}),
    (r"aggregate (Add|Subtract|Multiply|Divide|Power) is not", {"agg_arithmetic"}),
    (r"sorting by an expression", {"sort_by_expression"}),
    (
        r"window frames are not supported",
        {"running_agg", "rows_frame", "range_frame", "first_last_value"},
    ),
    (r"window function (Mean|Sum|Count|Max|Min|StandardDev)", {"window_partition_agg"}),
    (r"window function (DenseRank|MinRank)", {"rank"}),
    (r"window function (NTile|PercentRank|CumeDist)", {"ntile"}),
    (r"window function (First|Last)", {"first_last_value"}),
    (r"aggregate (ArgMin|ArgMax|First|Last|Arbitrary)", {"arg_max"}),
    (r"aggregate (Median|Quantile)", {"percentile"}),
    (r"aggregate (StandardDev|Variance)", {"stddev_var"}),
    (r"aggregate (Correlation|Covariance)", {"corr"}),
    (r"aggregate GroupConcat", {"string_agg"}),
    (r"^(Ln|Exp|Log|Log10|Log2|Sqrt) is not", {"math_transcendental"}),
    (r"ExtractEpochSeconds", {"epoch", "interval_to_number"}),
    (r"ScalarSubquery", {"scalar_subquery", "correlated_subquery"}),
    (r"InSubquery", {"not_in_subquery"}),
    (r"RegexReplace|RegexExtract", {"regex_replace"}),
    (r"^Hash is not", {"hash"}),
    (r"TimestampBucket is not", {"time_bucket"}),
]


def blocker_of(detail: str) -> set[str] | None:
    """The features a failure message points at (None if not recognised)."""
    for pattern, feats in BLOCKERS:
        if re.search(pattern, detail):
            return feats
    return None


SYMBOL = {"verified": "✓", "rejected": "✗", "upstream": "–", "none": "·"}


def index(queries: list[Query], features: dict[str, Feature], status: dict[str, Any]) -> str:
    lines = [
        "# Query catalogue: index",
        "",
        "Generated by `uv run python -m sverify.catalogue --write`; do not edit by hand.",
        "",
        "Checker: ✓ verified, ✗ rejected by `substrait-check`, – fails before a "
        "plan exists (Ibis or DataFusion), · not expressible in Ibis or DataFusion "
        "SQL. *(dbl)* means it verifies only with DECIMAL columns read as DOUBLE. "
        "Engines: F DataFusion runs the query's SQL itself (verified or not); "
        "P Polars, D DuckDB, S Snowflake SQL run Lean's written plan of a "
        "verified query (agreeing with DataFusion on synthetic data). *Missing* "
        "lists the features of an unverified query that Lean lacks or covers "
        "only in part (`features.toml`).",
        "",
    ]
    for suite in dict.fromkeys(q.suite for q in queries):
        lines += [f"## {suite}", "", "| id | query | checker | engines | missing |",
                  "|---|---|---|---|---|"]  # fmt: skip
        for q in (q for q in queries if q.suite == suite):
            s = status[q.id]
            e = effective(s)
            mark = SYMBOL[s["checker"]]
            if s["checker"] != "verified" and e["checker"] == "verified":
                mark += " *(dbl)*"
            engines = "".join(
                letter
                for letter, name in (("F", "datafusion"), ("P", "polars"), ("D", "duckdb"),
                                     ("S", "snowflake"))
                if runs_on(s, name)
            )  # fmt: skip
            blocked = ", ".join(f"`{f}`" for f in missing(q, features, s))
            title = f"[{q.title}]({q.source['url']})"
            lines.append(f"| {q.id} | {title} | {mark} | {engines or '—'} | {blocked} |")
        lines.append("")
    return "\n".join(lines)


def missing(q: Query, features: dict[str, Feature], s: dict[str, Any]) -> list[str]:
    """What keeps an unverified query from verifying: its features Lean lacks
    (`no`), the partial ones its failure points at, and DECIMAL arithmetic.
    Only `decimal` if it verifies as DOUBLE; empty if it verifies."""
    e = effective(s)
    if e["checker"] == "verified":
        return ["decimal"] if e is not s else []
    cause = (blocker_of(e["detail"]) or set()) & set(q.features)
    # A query lists `decimal` when it computes with money, which Lean refuses;
    # the checker stops at an earlier error in some of them.
    cause.add("decimal")
    return [f for f in q.features if features[f].lean == "no" or f in cause]


def _pct(n: int, total: int) -> str:
    return f"{100 * n / total:.0f}%" if total else "–"


def stats(
    queries: list[Query],
    features: dict[str, Feature],
    status: dict[str, Any],
    pitfalls: dict[str, Any],
) -> str:
    """The tables of FINDINGS.md: status per suite, feature frequency, gaps
    ranked by the queries they block, engine refusals, pitfall frequency."""
    n = len(queries)
    out = ["### Status per suite", "",
           "| suite | queries | verified | as DOUBLE only | rejected | upstream "
           "| DataFusion runs | Polars | DuckDB | Snowflake SQL |",
           "|---|---|---|---|---|---|---|---|---|---|"]  # fmt: skip

    def row(name: str, qs: list[Query]) -> str:
        st = [status[q.id] for q in qs]
        ver = sum(s["checker"] == "verified" for s in st)
        dbl = sum(s["checker"] != "verified" and effective(s)["checker"] == "verified" for s in st)
        rej = sum(effective(s)["checker"] == "rejected" for s in st)
        up = sum(effective(s)["checker"] in ("upstream", "none") for s in st)
        engines = [
            sum(runs_on(s, e) for s in st) for e in ("datafusion", "polars", "duckdb", "snowflake")
        ]
        return (
            f"| {name} | {len(qs)} | {ver} | {dbl} | {rej} | {up} | "
            + " | ".join(map(str, engines))
            + " |"
        )

    for suite in dict.fromkeys(q.suite for q in queries):
        out.append(row(suite, [q for q in queries if q.suite == suite]))
    out += [row("**all**", queries), ""]

    uses = Counter(f for q in queries for f in q.needs)
    out += ["### Feature frequency", "",
            f"How many of the {n} queries need each feature (as originally written, so "
            "subqueries an Ibis formulation rewrote into joins count), and Lean's support.", "",
            "| feature | group | queries | share | Lean |", "|---|---|---|---|---|"]  # fmt: skip
    for f, k in uses.most_common():
        out.append(f"| `{f}` | {features[f].group} | {k} | {_pct(k, n)} | {features[f].lean} |")
    out.append("")

    miss = {q.id: missing(q, features, status[q.id]) for q in queries}
    blocked = Counter(f for m in miss.values() for f in m)
    sole = Counter(m[0] for m in miss.values() if len(m) == 1)
    out += ["### Gaps ranked by the queries they block", "",
            "*Blocks*: queries that do not verify (on their own types) and need the "
            "feature; *alone*: of those, the queries it is the only missing feature of, "
            "so closing it alone makes them verify (DECIMAL counts queries that verify "
            "only as DOUBLE). Engine refusals of verified queries are separate, below.", "",
            "| feature | blocks | alone | Lean | note |", "|---|---|---|---|---|"]  # fmt: skip
    for f, k in sorted(blocked.items(), key=lambda kv: (-kv[1], -sole[kv[0]], kv[0])):
        note = features[f].note.replace("|", "\\|")
        out.append(f"| `{f}` | {k} | {sole[f]} | {features[f].lean} | {note} |")
    out.append("")

    reasons: Counter[str] = Counter()
    for q in queries:
        for e, why in effective(status[q.id]).get("engines", {}).items():
            if why.startswith(("refused", "error", "differs")):
                reasons[f"{e}: {why[:110]}"] += 1
    verified = sum(effective(status[q.id])["checker"] == "verified" for q in queries)
    out += ["### Why engines refuse verified queries", "",
            f"Over the {verified} queries that verify (some only as DOUBLE):", "",
            "| engine: reason | queries |", "|---|---|"]  # fmt: skip
    out += [f"| {r} | {k} |" for r, k in reasons.most_common()]
    out.append("")

    tags = Counter(p.split(":")[0].strip() for q in queries for p in q.pitfalls)
    out += [
        "### Pitfall frequency",
        "",
        "| pitfall | queries | DataFusion quirks |",
        "|---|---|---|",
    ]
    for t, k in tags.most_common():
        quirks = ", ".join(pitfalls[t].get("quirks", [])) or "–"
        out.append(f"| `{t}` | {k} | {quirks} |")
    return "\n".join(out) + "\n"


STATS_START, STATS_END = "<!-- stats:start -->", "<!-- stats:end -->"


def with_stats(findings: str, table: str) -> str:
    pattern = re.compile(re.escape(STATS_START) + ".*?" + re.escape(STATS_END), re.S)
    if not pattern.search(findings):
        raise ValueError(f"FINDINGS.md has no {STATS_START} … {STATS_END} block")
    return pattern.sub(lambda _: f"{STATS_START}\n{table}{STATS_END}", findings)


def write(root: Path = ROOT) -> None:
    queries, features, schemas = load_queries(root), load_features(root), load_schemas(root)
    pitfalls = load_pitfalls(root)
    problems = validate(queries, features, schemas, pitfalls)
    if problems:
        raise SystemExit("\n".join(problems))
    status = probe_all(queries, schemas)
    (root / "status.json").write_text(json.dumps(status, indent=1, ensure_ascii=False) + "\n")
    (root / "INDEX.md").write_text(index(queries, features, status))
    findings = root / "FINDINGS.md"
    if findings.exists():
        table = stats(queries, features, status, pitfalls)
        findings.write_text(with_stats(findings.read_text(), table))
    for p in consistency(queries, features, status):
        print(p)


def main() -> None:
    if "--write" in sys.argv:
        write()
        return
    queries, features, schemas = load_queries(), load_features(), load_schemas()
    problems = validate(queries, features, schemas, load_pitfalls())
    print("\n".join(problems) or f"{len(queries)} queries, well-formed")
    only = [a for a in sys.argv[1:] if not a.startswith("-")]
    if only:
        con = connect()
        for q in queries:
            if q.id in only or q.suite in only:
                print(q.id, json.dumps(probe(con, q, schemas), ensure_ascii=False))


if __name__ == "__main__":
    main()
