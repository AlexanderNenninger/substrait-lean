"""Every Ibis operation the checker verifies runs on every engine.

Each `verified` case of the coverage harness (`sverify.coverage`) runs on
random tables: on DataFusion as Ibis compiles it, and on Polars and DuckDB as
the plan Lean writes back out (`written_plan`). The results agree as bags with
DataFusion's, and Polars and DuckDB, which both follow `Rel.eval`'s list
order, agree row for row where the order is part of the result (below a
FETCH, a window or a sort). Where a FETCH takes "the first rows" of an unsorted
input DataFusion may take others, so there only Polars and DuckDB are
compared. The Snowflake SQL is generated for every case too (and parsed).
"""

import datetime as dt
import json
import math
from decimal import Decimal

import duckdb
import pyarrow as pa
import pytest
import sqlglot
from hypothesis import HealthCheck, given, settings
from hypothesis import strategies as st

from sverify import coverage, polars_engine
from sverify.engine import put_table, run_plan, run_sql, substrait_json, to_sql, written_plan
from sverify.sql import Unsupported, parse_plan
from sverify.sql import to_sql as plan_sql
from sverify.sql.core import Fetch, Rel, order_matters
from sverify.sql.snowflake import SNOWFLAKE
from sverify.testing import canonical

VERIFIED = [c for c in coverage.CASES if c.expected == "verified"]

#: Cases an engine refuses, with the reason (`sverify.coverage` says why).
REFUSED, TIE_FREE = coverage.REFUSED, coverage.TIE_FREE

T0 = dt.datetime(2024, 2, 28, 23, 0)
STAMPS = [
    T0 + dt.timedelta(hours=h, minutes=m, microseconds=u)
    for h, m, u in [(0, 0, 0), (1, 30, 5), (49, 0, 999_999), (-24 * 400, 7, 1), (24 * 365, 59, 0)]
] + [dt.datetime(1969, 12, 31, 23, 59, 59, 999_999), dt.datetime(2021, 1, 3, 12)]

ints = st.one_of(st.none(), st.integers(-3, 6))
names = st.sampled_from([None, "ada", "bob", "", "a%b", "Émile", " cy "])
doubles = st.sampled_from([None, 0.0, -0.0, 0.5, 1.5, -2.25, 1e300, math.inf, -math.inf, math.nan])


@st.composite
def tables(draw) -> dict[str, pa.Table]:
    """Rows for `t` and `u`. Timestamps are distinct within `t`, so the window
    cases (ordered by `ts`) have no ties."""
    n = draw(st.integers(0, len(STAMPS)))
    ts = draw(st.lists(st.sampled_from(STAMPS), min_size=n, max_size=n, unique=True))
    t = {
        "id": draw(st.lists(ints, min_size=n, max_size=n)),
        "name": draw(st.lists(names, min_size=n, max_size=n)),
        "amount": draw(st.lists(doubles, min_size=n, max_size=n)),
        "qty": draw(st.lists(ints, min_size=n, max_size=n)),
        "ts": ts,
        "flag": draw(st.lists(st.sampled_from([None, True, False]), min_size=n, max_size=n)),
    }
    m = draw(st.integers(0, 4))
    u = {
        "name": draw(st.lists(names, min_size=m, max_size=m)),
        "region": draw(st.lists(st.sampled_from([None, "eu", "us"]), min_size=m, max_size=m)),
    }
    schema = {name: s.to_pyarrow() for name, s in coverage.T.schema().items()}
    return {
        "t": pa.table({k: pa.array(v, schema[k]) for k, v in t.items()}),
        "u": pa.table({k: pa.array(v, pa.string()) for k, v in u.items()}),
    }


def rows(table: pa.Table) -> list[tuple]:
    """DataFusion types `ROW_NUMBER()` as a decimal; the model has one integer type."""
    return [
        tuple(int(v) if isinstance(v, Decimal) else v for v in r.values())
        for r in table.to_pylist()
    ]


def same(a: list[tuple], b: list[tuple]) -> bool:
    """Equal row for row; NaN equals NaN and -0.0 is not 0.0."""
    return repr(a) == repr(b)


def has_fetch(r: Rel) -> bool:
    if isinstance(r, Fetch):
        return True
    return any(has_fetch(getattr(r, k)) for k in ("input", "left", "right") if hasattr(r, k))


@pytest.fixture(scope="module")
def con():
    return coverage.setup()


@pytest.mark.parametrize("case", VERIFIED, ids=lambda c: c.label)
@settings(max_examples=25, deadline=None, suppress_health_check=list(HealthCheck))
@given(data=tables())
def test_engines_agree(con, case, data):
    for name, table in data.items():
        put_table(con, name, table)
    sql = to_sql(case.build())
    plan = written_plan(substrait_json(con, sql))
    refused = REFUSED.get(case.label, {})
    results, failed = {}, set()
    for engine in ("polars", "duckdb"):
        if engine in refused:
            error = polars_engine.Unsupported if engine == "polars" else Unsupported
            with pytest.raises(error, match=refused[engine]):
                run_plan(con, plan, engine)
            continue
        try:
            results[engine] = rows(run_plan(con, plan, engine))
        except (polars_engine.RuntimeIssue, duckdb.Error):
            # A runtime error of `SubstraitLean/Safety.lean` (the data has
            # NaN and ±inf to cast): both engines raise it.
            failed.add(engine)
    if failed:
        assert failed | set(refused) == {"polars", "duckdb"}
        return
    if not results:
        return
    root = parse_plan(json.loads(plan)).root
    if "polars" in results and "duckdb" in results:
        pl_rows, duck = results["polars"], results["duckdb"]
        assert same(pl_rows, duck) if order_matters(root) else canonical(pl_rows) == canonical(duck)
    if not has_fetch(root):
        df = canonical(rows(run_sql(con, sql)))
        for got in results.values():
            assert canonical(got) == df


@pytest.mark.parametrize("case", VERIFIED, ids=lambda c: c.label)
def test_snowflake_sql(con, case):
    plan = json.loads(written_plan(substrait_json(con, to_sql(case.build()))))
    if "snowflake" in REFUSED.get(case.label, {}):
        with pytest.raises(Unsupported, match=REFUSED[case.label]["snowflake"]):
            plan_sql(plan, SNOWFLAKE)
        if case.label not in TIE_FREE:
            return
        sql = plan_sql(plan, SNOWFLAKE, tie_free=True)
    else:
        sql = plan_sql(plan, SNOWFLAKE)
    sqlglot.parse_one(sql, read="snowflake")
