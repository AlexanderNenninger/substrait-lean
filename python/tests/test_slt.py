"""The sqllogictest replay harness (`sverify_dev.slt`): parsing DuckDB's `.test`
format, comparing results as DuckDB's runner does, and replaying a small
test file end to end. No network: the files are written here, in DuckDB's
format."""

import hashlib
import json
import textwrap

import pytest

from sverify_dev import slt

pytestmark = pytest.mark.backend("duckdb")


def _parse(text: str) -> slt.TestFile:
    return slt.parse(textwrap.dedent(text))


def test_parse_records():
    tf = _parse(
        """\
        # name: test/sql/x.test
        statement ok
        CREATE TABLE t(i INTEGER)

        statement error
        SELECT 1/0
        ----
        Division by zero

        query IT rowsort
        SELECT i, s
        FROM t
        ----
        1\ta
        NULL\t(empty)

        skipif duckdb
        query I
        SELECT 2
        ----
        2

        statement ok con2
        SELECT 1
        """
    )
    assert tf.skip is None
    create, err, q, skipped, con = tf.records
    assert (create.kind, create.expect, create.line) == ("statement", "ok", 2)
    assert (err.expect, err.expected) == ("error", ["Division by zero"])
    assert (q.types, q.sort, q.sql) == ("IT", "rowsort", "SELECT i, s\nFROM t")
    assert q.expected == ["1\ta", "NULL\t(empty)"]
    assert skipped.skip == "skipif duckdb"
    assert con.connection == "con2"


def test_parse_loops_and_tokens():
    tf = _parse(
        """\
        loop i 0 2

        foreach t <signed>

        query I
        SELECT ${i}::${t}
        ----
        ${i}

        endloop

        endloop
        """
    )
    sqls = [r.sql for r in tf.records]
    assert len(sqls) == 2 * len(slt.SIGNED)
    assert sqls[0] == "SELECT 0::tinyint" and sqls[-1] == "SELECT 1::hugeint"
    assert tf.records[-1].expected == ["1"]


def test_parse_skips():
    assert _parse("require parquet\n\nquery I\nSELECT 1\n----\n1\n").skip == "require parquet"
    assert _parse("require skip_reload\n\nquery I\nSELECT 1\n----\n1\n").skip is None
    tf = _parse(
        "mode skip\n\nquery I\nSELECT 1\n----\n1\n\nmode unskip\n\nquery I\nSELECT 2\n----\n2\n"
    )
    assert [r.skip for r in tf.records] == ["mode skip", None]
    tf = _parse("loop i 0 100000\n\nstatement ok\nSELECT 1\n\nendloop\n")
    assert tf.skip == "loops too long"


def _query(types: str, expected: list[str], sort: str = "nosort") -> slt.Record:
    return slt.Record("query", 1, "SELECT 1", "rows", types, sort, expected)


def test_matches():
    rec = _query("IR", ["1\t0.5", "NULL\t2"])
    assert slt.matches(rec, [["1", "0.5"], ["NULL", "2.0"]], ordered=True)
    # Lean prints six decimals.
    assert slt.matches(rec, [["1", "0.500000"], ["NULL", "2"]], ordered=True)
    assert not slt.matches(rec, [["NULL", "2"], ["1", "0.5"]], ordered=True)
    # Without ORDER BY, rows compare as a bag even under nosort.
    assert slt.matches(rec, [["NULL", "2"], ["1", "0.5"]], ordered=False)
    assert not slt.matches(rec, [["1", "0.6"], ["NULL", "2"]], ordered=False)
    # One value per line, and booleans as 1/0 or true/false.
    assert slt.matches(_query("IT", ["1", "a", "2", "b"]), [["1", "a"], ["2", "b"]], True)
    assert slt.matches(_query("T", ["true", "0"]), [["1"], ["false"]], True)


def test_matches_hash():
    values = ["1", "a", "2", "b"]
    digest = hashlib.md5("".join(v + "\n" for v in values).encode()).hexdigest()
    rec = _query("IT", [f"4 values hashing to {digest}"], "rowsort")
    assert slt.matches(rec, [["2", "b"], ["1", "a"]], ordered=False)
    assert not slt.matches(rec, [["2", "c"], ["1", "a"]], ordered=False)


TEST_FILE = """\
statement ok
CREATE TABLE t(i BIGINT, d DOUBLE);

statement ok
INSERT INTO t VALUES (1, 0.5), (2, 1.5), (NULL, NULL)

query I rowsort
SELECT i + 1 FROM t
----
2
3
NULL

statement error
SELECT 9223372036854775807::BIGINT + i FROM t WHERE i = 1
----
Overflow

statement error
SELECT i // 0 FROM t
----
Division by zero

query I
SELECT list_value(i) FROM t WHERE i = 1
----
[1]

statement ok
CREATE TABLE u(i BIGINT);

query I
WITH ins AS (INSERT INTO u VALUES (1) RETURNING i) SELECT 1
----
1

query I
SELECT count(*) FROM u
----
1

statement ok
SET default_null_order='nulls_first'

query I
SELECT i FROM t ORDER BY i
----
NULL
1
2

statement ok
SET integer_division = true

query I
SELECT 1
----
1
"""


@pytest.fixture(scope="module")
def replayed(tmp_path_factory):
    path = tmp_path_factory.mktemp("slt") / "x.test"
    path.write_text(TEST_FILE)
    results, skip = slt.replay_file(path, "area/x.test")
    assert skip is None
    return results


def _result(results, prefix):
    (r,) = [r for r in results if r.sql.startswith(prefix)]
    return r


def test_replay(replayed):
    # DuckDB's SQL as it is, through `sverify.sql_lift`.
    assert _result(replayed, "SELECT i + 1").cls == "agree"
    # DuckDB raises on 64-bit overflow; `Rel.eval`'s integers are unbounded,
    # and the verifier warns.
    overflow = _result(replayed, "SELECT 9223372036854775807")
    assert (overflow.cls, overflow.side) == ("disagree", "lean")
    assert overflow.lean == '[["9223372036854775808"]]'
    assert overflow.engine.startswith("error: Out of Range Error")
    # Lean's division by zero is NULL; DuckDB 2.0 raises (and so does the
    # written plan, guarded); the verifier flags it.
    div = _result(replayed, "SELECT i // 0")
    assert (div.cls, div.side) == ("disagree", "lean")
    assert div.reason.startswith("verify: division by zero")
    assert _result(replayed, "SELECT list_value").reason.startswith("lift: ")
    # Data-modifying CTEs are outside sverify's scope (#318); DuckDB still
    # runs them, so the next query sees the row.
    dml = _result(replayed, "WITH ins AS (INSERT")
    assert (dml.cls, dml.reason) == (
        "skipped",
        "modifies data (INSERT in a query), outside sverify's scope",
    )
    assert _result(replayed, "SELECT count(*) FROM u").cls == "agree"
    # The lift reads DuckDB's default NULL order only.
    nulls = _result(replayed, "SELECT i FROM t ORDER BY i")
    assert (nulls.cls, nulls.reason) == ("skipped", "setting default_null_order")
    # Not followed: a setting that changes what `/` means.
    last = _result(replayed, "SELECT 1")
    assert (last.cls, last.reason) == ("skipped", "setting integer_division")


def test_ledger(replayed, tmp_path):
    rows = [slt.asdict(r) for r in replayed]
    path = slt.write_ledger("area", "2.0.0", rows, {"area/y.test": "require json"}, tmp_path)
    assert path.name == "area.json"
    led = json.loads(path.read_text())
    assert led["summary"] == {"agree": 2, "disagree": 2, "refused": 1, "skipped": 3}
    assert led["disagree_sides"] == {"lean": 2}
    assert len(led["results"]) == len(rows)
    summary = slt.write_summary(tmp_path).read_text()
    assert "| [area](area.json) | 2 | 0 | 2 | lean 2 | 1 | 3 | 1 |" in summary
    # Rewriting keeps one table.
    assert slt.write_summary(tmp_path).read_text().count("<!-- slt:start -->") == 1


def test_area_of():
    assert slt.area_of("overflow/integer_overflow.test") == "overflow"
    assert slt.area_of("function/numeric/test_mod.test") == "function/numeric"
    assert slt.area_of("types/decimal/x/y.test") == "types/decimal"


def test_the_watchdog_kills_a_busy_checker():
    # A query that keeps the checker busy past the limit loses its checker,
    # and the next request starts a fresh one.
    import time

    from sverify import engine

    engine.run_checker(("--lowering-coverage",), "")
    proc = engine._CHECKER.proc
    assert proc is not None
    with slt._watchdog(0.05) as fired:
        time.sleep(0.5)
    assert fired[0]
    assert proc.wait(timeout=5) is not None
    with slt._watchdog(5) as fired:
        pass
    assert not fired[0]


@pytest.mark.parametrize(
    "sql",
    ["SELECT 7::TINYINT // 0::TINYINT", "SELECT 7::BIGINT % 0::BIGINT", "SELECT mod(42, 0)"],
)
def test_issues_of_queries_without_tables(sql):
    """A query that reads no table still gets `verify`'s issues (#333):
    `sverify.sql` refuses such queries, which hid these."""
    assert any("division by zero" in i for i in slt._lift_issues(sql, {}))


def test_the_summary_skips_files_that_are_not_ledgers(tmp_path):
    # `characterization/duckdb/` also holds `probes.json`.
    (tmp_path / "probes.json").write_text(json.dumps({"duckdb": "2.0.0", "probes": []}))
    (tmp_path / "area.json").write_text(
        json.dumps(
            {
                "area": "area",
                "summary": {"agree": 1, "disagree": 0, "refused": 0, "skipped": 0},
                "skipped_files": [],
                "results": [{"cls": "agree"}],
            }
        )
    )
    text = slt.write_summary(tmp_path).read_text()
    assert "| [area](area.json) | 1 | 0 |" in text and "probes" not in text


def test_nested_values_become_arrow_structs():
    """A struct is the list of its fields in the model, a dict in Arrow."""
    import pyarrow as pa

    t = pa.list_(pa.struct([("a", pa.int64()), ("b", pa.list_(pa.int64()))]))
    assert slt._nested([[1, [2]], None, [None, None]], t) == [
        {"a": 1, "b": [2]},
        None,
        {"a": None, "b": None},
    ]


def test_large_queries_are_condensed(tmp_path):
    """A query reading more than `MAX_ROWS` rows runs on the tables' first
    rows, and Lean is compared with DuckDB's result on those (#357)."""
    path = tmp_path / "big.test"
    n = slt.MAX_ROWS + 500
    path.write_text(
        textwrap.dedent(
            f"""\
            statement ok
            CREATE TABLE a AS SELECT range AS k FROM range({n})

            statement ok
            CREATE TABLE b AS SELECT range AS k, range * 2 AS v FROM range({n})

            query I
            SELECT count(*) FROM a JOIN b ON a.k = b.k
            ----
            {n}
            """
        )
    )
    results, _ = slt.replay_file(path, "area/big.test")
    (r,) = results
    assert (r.cls, r.reason) == ("agree", f"condensed to {slt.MAX_ROWS} rows")
    # Lean counted the condensed join, not the test's full one.
    assert r.lean == f'[["{slt.MAX_ROWS // 2}"]]'


def test_tables_of_128_bit_integers_are_refused(tmp_path):
    """DuckDB exports `UHUGEINT` to Arrow as `decimal128(38, 0)`, its maximum
    as -1 (DD-5): the harness refuses such tables rather than mirror them
    (#618)."""
    path = tmp_path / "huge.test"
    path.write_text(
        textwrap.dedent(
            """\
            statement ok
            CREATE TABLE u AS SELECT '340282366920938463463374607431768211455'::UHUGEINT AS i

            query R
            SELECT i::DOUBLE FROM u
            ----
            340282366920938463463374607431768211455

            statement ok
            CREATE TABLE h AS SELECT [1::HUGEINT] AS l

            query I
            SELECT l[1] FROM h
            ----
            1
            """
        )
    )
    results, _ = slt.replay_file(path, "area/huge.test")
    assert [r.cls for r in results] == ["refused", "refused"]
    assert all("DD-5" in r.reason for r in results)
