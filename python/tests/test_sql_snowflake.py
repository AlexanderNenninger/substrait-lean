"""The Snowflake SQL dialect.

* Snapshots: the SQL for every accepted golden fixture and for the delta
  plans of the incremental pipelines (`SVERIFY_UPDATE_SNAPSHOTS=1` rewrites
  them). Every query must parse as Snowflake SQL (sqlglot).
* Emulation: the queries run on fakesnow (Snowflake's dialect translated to
  DuckDB) and are compared with Lean's own evaluation (`Rel.eval` through
  `substrait-check`). This checks the generated SQL end to end, but DuckDB is
  not Snowflake: it proves nothing about Snowflake's behaviour.
* Real Snowflake: the same comparisons, only when `SNOWFLAKE_ACCOUNT`,
  `SNOWFLAKE_USER` and a credential are in the environment.
"""

from __future__ import annotations

import json
import math
import os
import re
import uuid
from collections.abc import Callable, Mapping
from decimal import Decimal
from pathlib import Path

import pytest
import sqlglot

import sverify as sv
from sverify.engine import run_checker
from sverify.engines import create_table, substrait_json, written_plan
from sverify.examples import PIPELINES, create_tables
from sverify.incremental import delta_plans
from sverify.sql import Dialect, Unsupported, to_sql
from sverify.sql.snowflake import SNOWFLAKE

pytestmark = pytest.mark.backend("snowflake")

ROOT = Path(__file__).resolve().parents[2]
FIXTURES = ROOT / "tests" / "fixtures"
SNAPSHOTS = Path(__file__).parent / "sql_snapshots"
UPDATE = os.environ.get("SVERIFY_UPDATE_SNAPSHOTS") == "1"

# The SQL view test of test_incremental.py, next to the Ibis pipelines.
SQL_QUERY = "select o.id, c.city from orders o, customers c where o.amount > 20"

ORDERS = [
    (1, "ada", 30),
    (2, "bob", 5),
    (2, "bob", 5),
    (3, None, 25),
    (4, "cy", None),
    (5, "ada", 0),
]
CUSTOMERS = [("ada", "Paris"), ("bob", None), (None, "Rome"), ("ada", "Lyon")]
DELTAS = {
    "orders$delta": [(6, "bob", 50, 1), (2, "bob", 5, -1), (7, "ada", 21, 1)],
    "customers$delta": [("cy", "Oslo", 1), ("ada", "Paris", -1)],
}
# Tie-free on every window's PARTITION BY and ORDER BY columns below.
ORDERED_ROWS = [(1, 10), (1, 30), (2, 20), (None, 40), (2, None), (1, 5)]
SCHEMAS = {
    "orders": [("id", "int"), ("customer", "str"), ("amount", "int")],
    "customers": [("name", "str"), ("city", "str")],
}
SCHEMAS |= {t + "$delta": [*cols, ("__weight", "int")] for t, cols in list(SCHEMAS.items())}
SCHEMAS["w"] = [("g", "int"), ("x", "int")]
TABLES = {"orders": ORDERS, "customers": CUSTOMERS, **DELTAS, "w": ORDERED_ROWS}


def substrait_literal(v: object) -> dict:
    if v is None:
        return {"literal": {"null": {"i64": {}}}}
    if isinstance(v, str):
        return {"literal": {"string": v}}
    return {"literal": {"i64": str(v)}}


def inline(plan: dict, tables: Mapping[str, list[tuple]]) -> dict:
    """A copy of `plan` with its named tables replaced by literal rows."""
    plan = json.loads(json.dumps(plan))

    def walk(node: object) -> None:
        if isinstance(node, dict):
            if "namedTable" in node:
                name = ".".join(node.pop("namedTable")["names"])
                rows = [{"fields": [substrait_literal(v) for v in r]} for r in tables[name]]
                node["virtualTable"] = {"expressions": rows}
            for v in node.values():
                walk(v)
        elif isinstance(node, list):
            for v in node:
                walk(v)

    walk(plan)
    return plan


def accepted_fixtures() -> list[Path]:
    return [
        p
        for p in sorted(FIXTURES.glob("*.json"))
        if p.with_suffix(".expected").read_text().rstrip().endswith("[exit 0]")
    ]


def fixture_plan(path: Path) -> dict:
    """A fixture's plan; Isthmus's in the form Lean writes them, which is
    what the engines get (they use encodings only Lean reads)."""
    text = path.read_text()
    if path.stem.startswith("isthmus_"):
        text = written_plan(text)
    return json.loads(text)


def pipeline_plans() -> dict[str, dict]:
    con = sv.connect()
    create_tables(con, ORDERS, CUSTOMERS)
    queries = {name: sv.engine.to_sql(expr) for name, expr in PIPELINES.items()}
    queries["sql_query"] = SQL_QUERY
    return {name: json.loads(substrait_json(con, q)) for name, q in queries.items()}


PLANS = pipeline_plans()

# Windows and FETCH over named tables are refused (no row order). Over
# literal rows, which have one, they run, and so do windows with tie_free.
ORDERED_QUERIES = {
    "window": "select g, x, lag(x) over (partition by g order by x nulls first) as p, "
    "lead(x, 2, -1) over (order by x desc nulls last) as n, "
    "row_number() over (partition by g order by x asc nulls last) as rn from w",
    "fetch": "select x from w where g is not null limit 2 offset 1",
}


def ordered_plans() -> dict[str, dict]:
    con = sv.connect()
    create_table(con, "w", sv.engine.ibis.schema({"g": "int64", "x": "int64"}), ORDERED_ROWS)
    return {name: json.loads(substrait_json(con, q)) for name, q in ORDERED_QUERIES.items()}


def feature_plans() -> dict[str, dict]:
    """DISTINCT, aggregates, semi, anti and outer joins and string functions."""
    o, c = sv.examples.orders, sv.examples.customers
    exprs = {
        "distinct": o.select("customer", "amount").distinct(),
        "semi_join": o.semi_join(c, o.customer == c.name),
        "anti_join": o.anti_join(c, o.customer == c.name),
        "outer_join": o.outer_join(c, o.customer == c.name),
        "union_distinct": o.select(x=o.customer).union(c.select(x=c.city), distinct=True),
        "aggregate": o.group_by("customer").aggregate(
            n=o.count(), s=o.amount.sum(), m=o.amount.max(), u=o.id.nunique()
        ),
        "global_aggregate": o.aggregate(n=o.amount.count(), lo=o.customer.min()),
        "strings": c.select(
            u=c.name.upper(),
            n=c.city.length(),
            s=c.city.substr(1, 3),
            p=c.city.find("o"),
            l=c.city.like("%r%"),
            t=(c.city + "  ").rstrip(),
            b=c.name.startswith("a"),
        ),
    }
    con = sv.connect()
    create_tables(con, ORDERS, CUSTOMERS)
    return {k: json.loads(substrait_json(con, sv.engine.to_sql(e))) for k, e in exprs.items()}


FEATURE_PLANS = feature_plans()
#: Sorted in Lean's order: the only ties in `ORDERS` are equal rows.
SORTED = {"order_by": sv.examples.orders.order_by([sv.examples.orders.amount.desc(), "id"])}


DELTA_PLANS = {
    f"{name}_delta{i}": json.loads(d)
    for name, plan in PLANS.items()
    for i, d in enumerate(delta_plans(json.dumps(plan)))
}


NAMED_ORDERED = ordered_plans()
ORDERED_PLANS = {f"{k}_inlined": inline(p, {"w": ORDERED_ROWS}) for k, p in NAMED_ORDERED.items()}
TIE_FREE = {"window_tie_free": NAMED_ORDERED["window"]}


def snowflake_sql(plan: dict, tie_free: bool = False) -> str:
    """The query, or the reason it is refused, for snapshots."""
    try:
        return to_sql(plan, SNOWFLAKE, tie_free=tie_free)
    except Unsupported as e:
        return f"-- Unsupported: {e}"


def check_snapshot(name: str, sql: str, dialect: str = "snowflake") -> None:
    path = SNAPSHOTS / f"{name}.{dialect}.sql"
    if UPDATE:
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(sql + "\n")
    assert path.exists(), f"no snapshot {path.name}; run with SVERIFY_UPDATE_SNAPSHOTS=1"
    assert sql + "\n" == path.read_text()
    if not sql.startswith("-- Unsupported"):
        sqlglot.parse_one(sql, read=dialect)


@pytest.mark.parametrize("path", accepted_fixtures(), ids=lambda p: p.stem)
def test_fixture_snapshot(path: Path):
    check_snapshot(path.stem, snowflake_sql(fixture_plan(path)))


ALL_PLANS = {**PLANS, **DELTA_PLANS, **ORDERED_PLANS, **TIE_FREE}


@pytest.mark.parametrize("name", sorted(ALL_PLANS))
def test_pipeline_snapshot(name: str):
    sql = snowflake_sql(ALL_PLANS[name], tie_free=name in TIE_FREE)
    assert not sql.startswith("-- Unsupported"), sql  # the incremental fragment all maps
    check_snapshot(f"pipeline_{name}", sql)


# ------------------------------------------------------------ hooks on their own


def parses(sql: str) -> str:
    sqlglot.parse_one(f"SELECT {sql}", read="snowflake")
    return sql


def test_float_literals():
    assert parses(SNOWFLAKE.float_lit(math.nan)) == "CAST('NaN' AS FLOAT)"
    assert parses(SNOWFLAKE.float_lit(-math.inf)) == "CAST('-inf' AS FLOAT)"
    assert parses(SNOWFLAKE.float_lit(0.1)) == "CAST('0.1' AS FLOAT)"
    # The model's one zero and one NaN.
    assert parses(SNOWFLAKE.float_lit(-0.0)) == "CAST('0.0' AS FLOAT)"
    assert SNOWFLAKE.float_lit(-math.nan) == SNOWFLAKE.float_lit(math.nan)


def test_temporal_literals():
    assert parses(SNOWFLAKE.timestamp_lit(1_500)) == (
        "CAST('1970-01-01 00:00:00.001500' AS TIMESTAMP_NTZ(6))"
    )
    assert parses(SNOWFLAKE.date_lit(-1)) == "CAST('1969-12-31' AS DATE)"
    # Intervals are NUMBERs of microseconds; Snowflake has no interval type.
    assert SNOWFLAKE.interval_lit(-10_000) == "-10000"
    ts = SNOWFLAKE.timestamp_lit(0)
    iv = SNOWFLAKE.interval_lit(-10_000)
    assert parses(SNOWFLAKE.time_add_interval(ts, iv)).startswith("DATEADD(MICROSECOND, -10000, ")
    assert parses(SNOWFLAKE.time_sub_interval(ts, iv)).startswith(
        "DATEADD(MICROSECOND, - (-10000), "
    )
    assert parses(SNOWFLAKE.time_diff("a", "b")) == "DATEDIFF(MICROSECOND, b, a)"
    with pytest.raises(Unsupported, match="years 1-9999"):
        SNOWFLAKE.timestamp_lit(-(10**18))
    with pytest.raises(Unsupported, match="interval result column"):
        SNOWFLAKE.result_kind("interval")


def test_strings_escape_backslashes():
    assert SNOWFLAKE.str_lit("it's a\\b") == "'it''s a\\\\b'"


def test_windows_and_relations():
    over = SNOWFLAKE.over(['"c0"'], [SNOWFLAKE.sort_key('"c1"', True, False)])
    assert over == 'OVER (PARTITION BY "c0" ORDER BY "c1" DESC NULLS LAST)'
    assert SNOWFLAKE.lag('"c1"', 0, "NULL", over) == '"c1"'
    assert parses(SNOWFLAKE.lead('"c1"', 2, "0", over)) == f'LEAD("c1", 2, 0) {over}'
    with pytest.raises(Unsupported, match="ORDER BY"):
        SNOWFLAKE.over(['"c0"'], [])
    with pytest.raises(Unsupported, match="no row order"):
        SNOWFLAKE.row_ordinal()
    assert SNOWFLAKE.limit_offset(3, None) == "LIMIT NULL OFFSET 3"
    assert SNOWFLAKE.limit_offset(0, 2) == "LIMIT 2"
    with pytest.raises(Unsupported, match="no row order"):
        to_sql(NAMED_ORDERED["window"], SNOWFLAKE)
    with pytest.raises(Unsupported, match="no row order"):
        to_sql(NAMED_ORDERED["fetch"], SNOWFLAKE, tie_free=True)


def test_identifiers_are_quoted():
    con = sv.connect()
    create_tables(con)
    sql = to_sql(
        json.loads(substrait_json(con, sv.engine.to_sql(PIPELINES["inner_join"]))), SNOWFLAKE
    )
    assert '"orders"' in sql
    assert re.search(r'(?<!")\borders\b(?!")', sql) is None


# ------------------------------------------------------------ execution


def lean_value(token: str) -> object:
    if token == "NULL":
        return None
    if token.startswith('"'):
        return json.loads(token)
    if token in ("true", "false"):
        return token == "true"
    return int(token)


def parse_lean_rows(out: str) -> list[tuple]:
    """The `rows (n):` section of `substrait-check` output."""
    token = re.compile(r'"(?:[^"\\]|\\.)*"|NULL|-?\d+|true|false')
    rows = []
    for line in out.split("rows (")[1].splitlines()[1:]:
        if not line.startswith("  ("):
            break
        rows.append(tuple(lean_value(t) for t in token.findall(line)))
    return rows


def lean_rows(plan: dict, tables: Mapping[str, list[tuple]]) -> list[tuple]:
    """`Rel.eval` of `plan` with its named tables replaced by `tables`."""
    code, out, err = run_checker((), json.dumps(inline(plan, tables)))
    assert code == 0, err
    return parse_lean_rows(out)


def normalize(v: object) -> object:
    if isinstance(v, Decimal) and v == v.to_integral_value():
        return int(v)
    return v


def canonical(rows) -> list[str]:
    return sorted(repr(tuple(normalize(v) for v in r)) for r in rows)


Run = Callable[[str], list[tuple]]


def load_tables(cur, suffix: str) -> Callable[[str], str]:
    """Create every test table (as a temporary table named `name + suffix`) and
    return a function that points a query at them."""
    d = SNOWFLAKE
    for name, cols in SCHEMAS.items():
        table = d.quote(name + suffix)
        defs = ", ".join(f"{d.quote(c)} {d.type_name(k)}" for c, k in cols)  # type: ignore[arg-type]
        cur.execute(f"CREATE TEMPORARY TABLE {table} ({defs})")
        for row in TABLES[name]:
            lits = [
                d.null(k) if v is None else d.str_lit(v) if k == "str" else d.int_lit(v)  # type: ignore[arg-type]
                for v, (_, k) in zip(row, cols, strict=True)
            ]
            cur.execute(f"INSERT INTO {table} VALUES ({', '.join(lits)})")

    def retarget(sql: str) -> str:
        for name in sorted(SCHEMAS, key=len, reverse=True):
            sql = re.sub(f'FROM "{re.escape(name)}"(?=[ )])', f'FROM "{name}{suffix}"', sql)
        return sql

    return retarget


def run_differential(
    run: Callable[[str], list[tuple]], retarget: Callable[[str], str], d: Dialect = SNOWFLAKE
) -> None:
    """Every plan of this module, as `d`'s SQL (`run` executes a query), against
    Lean's evaluation; `retarget` points a query at the loaded tables."""
    plans = {**PLANS, **DELTA_PLANS}
    for name, plan in plans.items():
        got = run(retarget(to_sql(plan, d)))
        assert canonical(got) == canonical(lean_rows(plan, TABLES)), name
    for name, plan in ORDERED_PLANS.items():
        got = run(to_sql(plan, d))
        assert got == lean_rows(plan, {}), name  # in Lean's row order
    for name, plan in TIE_FREE.items():
        got = run(retarget(to_sql(plan, d, tie_free=True)))
        assert canonical(got) == canonical(lean_rows(plan, TABLES)), name
    for name, plan in FEATURE_PLANS.items():
        got = run(retarget(to_sql(plan, d)))
        assert canonical(got) == canonical(lean_rows(plan, TABLES)), name
    con = sv.connect()
    create_tables(con, ORDERS, CUSTOMERS)
    for name, expr in SORTED.items():
        plan = json.loads(substrait_json(con, sv.engine.to_sql(expr)))
        got = run(retarget(to_sql(plan, d, tie_free=True)))
        assert [tuple(map(normalize, r)) for r in got] == lean_rows(plan, TABLES), name
    for path in accepted_fixtures():
        plan = json.loads(path.read_text())
        if "namedTable" in path.read_text():
            continue  # schema-only tables: covered by the pipelines above
        got = run(to_sql(plan, d))
        assert canonical(got) == canonical(lean_rows(plan, {})), path.stem


def snowflake_differential(cur, suffix: str) -> None:
    retarget = load_tables(cur, suffix)
    run_differential(lambda sql: cur.execute(sql).fetchall(), retarget)


def run_semantics(cur) -> None:
    """Hooks whose Snowflake behaviour the Lean model depends on."""
    d = SNOWFLAKE
    nan, inf, zero = d.float_lit(math.nan), d.float_lit(math.inf), d.float_lit(0.0)
    one = d.float_lit(1.0)
    exprs = [d.float_eq(nan, nan), d.float_lt(inf, nan), d.float_lt(nan, one)]
    exprs += [d.is_nan(nan), d.float_eq(zero, one), d.float_lt(one, nan)]
    # Aliased: two of these are the same SQL, and would share a column name.
    row = cur.execute("SELECT " + ", ".join(f"{e} AS c{i}" for i, e in enumerate(exprs))).fetchone()
    assert row == (True, True, False, True, False, True)
    # Kleene logic, and COALESCE(…, FALSE) for IS TRUE.
    null = d.null("bool")
    row = cur.execute(
        f"SELECT {d.and3(null, 'FALSE')}, {d.or3(null, 'TRUE')}, {d.and3(null, 'TRUE')}, "
        f"{d.not3(null)}, {d.is_true(null)}"
    ).fetchone()
    assert row == (False, True, None, None, False)
    assert cur.execute(f"SELECT {d.str_lit('a\\b')}").fetchone() == ("a\\b",)
    ts = d.time_add_interval(d.timestamp_lit(0), d.interval_lit(86_400_000_001))
    assert str(cur.execute(f"SELECT {ts}").fetchone()[0]) == "1970-01-02 00:00:00.000001"
    # One zero: -0.0 equals 0.0, and `canon` makes a computed -0.0 zero.
    neg0 = d.float_neg(zero)
    row = cur.execute(f"SELECT {d.float_eq(neg0, zero)}, {d.canon(neg0)}").fetchone()
    assert row[0] is True and math.copysign(1.0, row[1]) == 1.0
    big = d.int_lit(2**62)
    with pytest.raises(Exception, match="(?i)overflow"):
        cur.execute(f"SELECT {d.int_add(big, big)}").fetchall()
    assert cur.execute(f"SELECT {d.int_mul(d.int_lit(-(2**31)), d.int_lit(2**32))}").fetchone() == (
        -(2**63),
    )
    # The remainder of doubles is C's `fmod`; NaN by zero and for ±inf (#203).
    m = [d.float_lit(v) for v in (7.5, -7.5, 2.0)]
    mods = [d.float_mod(m[0], m[2]), d.float_mod(m[1], m[2]), d.float_mod(m[0], inf)]
    mods += [d.float_mod(m[0], zero), d.float_mod(inf, m[2])]
    row = cur.execute("SELECT " + ", ".join(f"{e} AS m{i}" for i, e in enumerate(mods))).fetchone()
    assert row[:3] == (1.5, -1.5, 7.5) and all(map(math.isnan, row[3:]))


@pytest.fixture(scope="module")
def fakesnow_cursor():
    fakesnow = pytest.importorskip("fakesnow")
    import snowflake.connector

    with fakesnow.patch():
        conn = snowflake.connector.connect(database="sverify", schema="emulation")
        yield conn.cursor()


@pytest.mark.filterwarnings("ignore::UserWarning")
def test_emulated_on_fakesnow_matches_lean(fakesnow_cursor):
    """EMULATION: fakesnow runs the queries on DuckDB, not on Snowflake."""
    snowflake_differential(fakesnow_cursor, "")


@pytest.mark.filterwarnings("ignore::UserWarning")
def test_emulated_semantics_on_fakesnow(fakesnow_cursor):
    """EMULATION: fakesnow runs the queries on DuckDB, not on Snowflake."""
    run_semantics(fakesnow_cursor)


def snowflake_connection():
    env = os.environ
    if not (env.get("SNOWFLAKE_ACCOUNT") and env.get("SNOWFLAKE_USER")):
        pytest.skip("set SNOWFLAKE_ACCOUNT, SNOWFLAKE_USER and a credential to run on Snowflake")
    import snowflake.connector

    keys = ("account", "user", "password", "authenticator", "private_key_file", "role")
    keys += ("warehouse", "database", "schema", "token")
    params = {k: env[f"SNOWFLAKE_{k.upper()}"] for k in keys if env.get(f"SNOWFLAKE_{k.upper()}")}
    return snowflake.connector.connect(**params)


def test_real_snowflake_matches_lean():
    """Opt-in: runs only with SNOWFLAKE_* connection variables set."""
    with snowflake_connection() as conn:
        cur = conn.cursor()
        snowflake_differential(cur, f"_{uuid.uuid4().hex[:8]}")
        run_semantics(cur)
