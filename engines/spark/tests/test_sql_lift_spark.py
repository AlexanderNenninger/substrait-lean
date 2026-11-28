"""Spark's SQL through sverify's lift (#866, `sverify_spark.sql`), ruling 288
and its amendment: each construct the lift reads rests on a Spark fact (H1),
its values are Lean's `Profile.spark` (H4), Spark has no generated lift yet
(H5), names resolve by their case (C2), reading imports no pyspark (E1), and
each construct's lift gives what Spark 4.3 computes under `SPARK_CONF` (H2:
the queries run on a local Spark session, compared with `Rel.eval`)."""

from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

import ibis
import pyarrow as pa
import pytest

from _repo import needs_repo
from sverify._checker import checker_path
from sverify._lean_eval import with_tables
from sverify.plan_json import Unsupported
from sverify.testing import LeanRaised, canonical, lean_values
from sverify_spark import ASSUMES, SETTINGS
from sverify_spark.sql import RULES, lift_spark, spark_profile, spark_sql

pytestmark = pytest.mark.backend("spark")

TABLES = {
    "t": pa.table(
        {
            "a": pa.array([1, 2, None, -7, 2**62], pa.int64()),
            "c": pa.array([3, None, 3, 4, -2], pa.int32()),
            "b": pa.array(["x", "y", None, "x", ""], pa.string()),
            "p": pa.array([True, False, None, True, False], pa.bool_()),
        }
    ),
    "u": pa.table({"k": pa.array([1, 2, 2, None], pa.int64()), "v": ["one", "two", "deux", "n"]}),
}
SCHEMAS = {n: ibis.Schema.from_pyarrow(t.schema) for n, t in TABLES.items()}
ROWS = {n: [tuple(r.values()) for r in t.to_pylist()] for n, t in TABLES.items()}

#: A query of each construct in `RULES` (its node class in the key), as Spark
#: runs it and as the lift reads it.
QUERIES = {
    "Where": "SELECT a FROM t WHERE p",
    "Having": "SELECT b, count(*) AS n FROM t GROUP BY b HAVING count(*) > 1",
    "Group": "SELECT b, max(a) AS m FROM t GROUP BY b",
    "Join": "SELECT t.a, u.v FROM t JOIN u ON t.a = u.k",
    "Join left": "SELECT t.a, u.v FROM t LEFT JOIN u ON t.a = u.k",
    "Order": "SELECT a, b FROM t ORDER BY a",
    "Ordered": "SELECT a, c FROM t ORDER BY c DESC, a",
    "Limit": "SELECT a FROM t ORDER BY a DESC LIMIT 2",
    "Distinct": "SELECT DISTINCT b FROM t",
    "Union": "SELECT a FROM t UNION ALL SELECT k FROM u",
    "Intersect": "SELECT a FROM t INTERSECT SELECT k FROM u",
    "Except": "SELECT a FROM t EXCEPT SELECT k FROM u",
    "Literal": "SELECT 1 AS i, 'z' AS s, 2147483648 AS big FROM t",
    "Null": "SELECT NULL AS n, a FROM t",
    "Boolean": "SELECT TRUE AS y, NOT p AS q FROM t",
    "And": "SELECT p AND a > 1 AS r FROM t",
    "Or": "SELECT p OR a > 1 AS r FROM t",
    "Not": "SELECT NOT p AS r FROM t",
    "In": "SELECT a IN (1, 2, NULL) AS r, b IN ('x') AS s FROM t",
    "Is": "SELECT a IS NULL AS r, b IS NOT NULL AS s FROM t",
    "EQ": "SELECT a = c AS r, b = 'x' AS s FROM t",
    "NEQ": "SELECT a <> c AS r FROM t",
    "NullSafeEQ": "SELECT a <=> c AS r FROM t",
    "NullSafeNEQ": "SELECT NOT (a <=> c) AS r FROM t",
    "LT": "SELECT a < c AS r FROM t",
    "LTE": "SELECT a <= c AS r FROM t",
    "GT": "SELECT c > 3 AS r FROM t",
    "GTE": "SELECT a >= c AS r FROM t",
    "Case": "SELECT CASE WHEN a > 1 THEN 'big' WHEN a IS NULL THEN 'none' ELSE b END AS r FROM t",
    "If": "SELECT if(p, a, c) AS r FROM t",
    "Coalesce": "SELECT coalesce(a, c, 0) AS r FROM t",
    "Add": "SELECT a + c AS r, c + 1 AS s FROM t WHERE a < 1000",
    "Sub": "SELECT a - c AS r FROM t WHERE a < 1000",
    "Mul": "SELECT c * c AS r FROM t",
    "Neg": "SELECT -a AS r FROM t",
    "Mod": "SELECT a % 3 AS r, -7 % c AS s FROM t WHERE c <> 0",
    "Abs": "SELECT abs(c) AS r FROM t",
    "DPipe": "SELECT b || '!' AS r FROM t",
    "Length": "SELECT length(b) AS r FROM t",
    "Count": "SELECT count(*) AS n, count(b) AS m, count(DISTINCT c) AS d FROM t",
    "Min": "SELECT min(a) AS r FROM t",
    "Max": "SELECT max(c) AS r FROM t",
}

#: Queries Spark raises on, with ANSI mode: the reference raises too.
RAISES = {
    "overflow": "SELECT a * a AS r FROM t",
    "zero divisor": "SELECT a % 0 AS r FROM t",
}


FACTS = Path(__file__).resolve().parents[1] / "facts"


@needs_repo
def test_every_construct_rests_on_a_spark_fact() -> None:
    """H1: the table names a fact of Spark's for each construct it reads."""
    for construct, fact in RULES.items():
        assert (FACTS / f"{fact}.json").is_file(), (construct, fact)


def test_every_construct_has_its_query() -> None:
    """H2 checks each construct the lift reads."""
    assert set(RULES) <= {k.split()[0] for k in QUERIES}


def test_the_profile_is_lean_profile_spark() -> None:
    """H4: each value the lift reads is `Profile.spark`'s one choice
    (`substrait-check --options`), and the fields whose choice is not one
    value are read by no construct of `RULES`."""
    out = subprocess.run(
        [str(checker_path()), "--options"], capture_output=True, text=True, check=True
    ).stdout
    data = json.loads(out)
    rows = {(r["group"], r["option"]): r["choice"] for r in data["choices"]["spark"]}

    def one(group: str | None, option: str) -> str:
        choice = rows.get((group, option)) or rows[(None, option)]
        assert len(choice["behaviours"]) == 1, (group, option, choice)
        return choice["behaviours"][0]

    spark = spark_profile()
    assert spark.overflow == one(None, "overflow") == "ERROR"
    assert spark.on_division_by_zero == one(None, "on_division_by_zero") == "ERROR"
    assert spark.min_mod_neg_one == one(None, "min_mod_neg_one") == "ZERO"
    assert spark.float_division_by_zero == one("fp.div", "on_division_by_zero") == "ERROR"
    # `domain_error`, `log_zero` and `corr_degenerate` are open in `Profile.spark`.
    assert not set(RULES) & {"Sqrt", "Ln", "Log", "Exp", "Pow", "Sin", "Cos", "Corr"}
    assert ASSUMES.startswith(f"Spark {data['versions']['spark']} SQL")


def test_the_report_names_every_setting_the_reading_assumes() -> None:
    """C1: the front end's label names the version and each setting."""
    for s in SETTINGS:
        assert f"{s.name}=" in ASSUMES


def test_spark_has_no_generated_lift_yet() -> None:
    """H5: Spark has no generated Lean table, so every construct DuckDB's lift
    reads from one is refused under Spark until #866's Lean part (C): its
    doubles, its `/`, `avg` and the casts between BIGINT and DOUBLE among them."""
    assert spark_sql().generated == {}
    for q in (
        "SELECT a / 2 AS r FROM t",
        "SELECT CAST(a AS DOUBLE) AS r FROM t",
        "SELECT avg(a) AS r FROM t",
        "SELECT 1.5e0 AS r FROM t",
    ):
        with pytest.raises(Unsupported, match="866"):
            lift_spark(q, SCHEMAS)


@pytest.mark.parametrize(
    "query",
    [
        "SELECT A FROM t",
        "SELECT a FROM T",
        "SELECT X.a FROM t x",
        "SELECT sum(a) AS s FROM t",
        # String and boolean order: no Spark fact states it yet (#2629).
        "SELECT b < 'y' AS r FROM t",
        "SELECT min(b) AS r FROM t",
        "SELECT a FROM t ORDER BY b",
        "SELECT max(p) AS r FROM t",
        # Spark counts no argument as 0 (count.sql.out L127).
        "SELECT count() AS n FROM t",
        # A TINYINT: Spark widens `n + 100`, DuckDB's literal rule would not.
        "SELECT n + 100 AS r FROM s",
    ],
)
def test_refused(query: str) -> None:
    """C2 (names that resolve only in another case), a construct with no
    fact (`sum`: a partial sum of BIGINT raises in Spark, spark-sum-int), an
    order no fact states and a narrow integer."""
    with pytest.raises(Unsupported):
        lift_spark(query, {**SCHEMAS, "s": ibis.schema({"n": "int8"})})


def test_reading_imports_no_pyspark() -> None:
    """E1: the front end reads Spark's SQL without a JVM."""
    code = (
        "import sys, ibis; from sverify_spark.sql import lift_spark; "
        "lift_spark('SELECT a FROM t', {'t': ibis.schema({'a': 'int64'})}); "
        "assert 'pyspark' not in sys.modules"
    )
    subprocess.run([sys.executable, "-c", code], check=True)


def _lean(query: str, semantics: str = "spark") -> list[tuple]:
    plan = lift_spark(query, SCHEMAS, semantics).plan
    return lean_values(json.dumps(with_tables(plan, ROWS)))


@pytest.fixture(scope="module")
def spark():
    spark_session = pytest.importorskip("spark_session")
    if not spark_session.has_java():
        pytest.skip("Spark needs a JVM")
    spark_session.put_tables(TABLES)
    return spark_session


@pytest.mark.parametrize("query", list(QUERIES.values()), ids=list(QUERIES))
@pytest.mark.parametrize("semantics", ["spark", "portable"])
def test_the_lift_gives_what_spark_computes(spark, query: str, semantics: str) -> None:
    """H2: Spark's own result for the text, and `Rel.eval` of the lifted plan,
    as bags of rows (in order under ORDER BY)."""
    got = _lean(query, semantics)
    want = spark.query(query)
    if "ORDER BY" in query:
        # Each query sorts by keys no two rows share: one order.
        assert [repr(r) for r in got] == [repr(r) for r in want]
    else:
        assert sorted(canonical(got)) == sorted(canonical(want))


@pytest.mark.parametrize("query", list(RAISES.values()), ids=list(RAISES))
def test_the_lift_raises_where_spark_does(spark, query: str) -> None:
    with pytest.raises(Exception):  # noqa: B017, PT011 - Spark's ArithmeticException
        spark.query(query)
    with pytest.raises(LeanRaised):
        _lean(query)
