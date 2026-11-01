"""The sqllogictest replay harness (`sverify_dev.slt`): parsing DuckDB's `.test`
format, comparing results as DuckDB's runner does, translating DuckDB SQL,
and replaying a small test file end to end. No network: the files are
written here, in DuckDB's format."""

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


def test_translate():
    sql, back, tables, ordered = slt.translate("SELECT i // 2, 7 / 2, x::TINYINT FROM t ORDER BY i")
    assert sql == ("SELECT (i / 2), CAST(7 AS DOUBLE) / 2, CAST(x AS TINYINT) FROM t ORDER BY i")
    assert (tables, ordered) == (["t"], True)
    assert "//" in back  # DuckDB's own reading, for the check against DuckDB
    sql, _, tables, ordered = slt.translate("SELECT 1 UNION ALL SELECT 2")
    assert sql == f"SELECT 1 FROM {slt.ONE} UNION ALL SELECT 2 FROM {slt.ONE}"
    assert not ordered
    # sqlglot would drop TRY: refused rather than translated wrongly.
    with pytest.raises(ValueError, match="TRY"):
        slt.translate("SELECT TRY(1 // 0)")
    with pytest.raises(ValueError, match="not a query"):
        slt.translate("CREATE TABLE t(i INT)")


def test_translate_null_order():
    q = "SELECT i FROM t ORDER BY i, j DESC, k NULLS LAST"
    assert slt.translate(q)[0].endswith("ORDER BY i, j DESC NULLS LAST, k")
    first = slt.translate(q, "nulls_first")[0]
    assert first.endswith("ORDER BY i NULLS FIRST, j DESC, k")


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
    assert _result(replayed, "SELECT i + 1").cls == "agree"
    # DuckDB raises on 64-bit overflow; `Rel.eval`'s integers are unbounded.
    overflow = _result(replayed, "SELECT 9223372036854775807")
    assert (overflow.cls, overflow.side) == ("disagree", "lean")
    assert overflow.lean == '[["9223372036854775808"]]'
    assert overflow.engine.startswith("error: Out of Range Error")
    # Lean's division by zero is NULL; DuckDB 2.0 raises (and so does the
    # written plan, guarded); the verifier flags it.
    div = _result(replayed, "SELECT i // 0")
    assert (div.cls, div.side) == ("disagree", "lean")
    assert div.reason.startswith("verify: division by zero")
    assert _result(replayed, "SELECT list_value").cls == "refused"
    # Followed: DuckDB's NULL order setting.
    nulls = _result(replayed, "SELECT i FROM t ORDER BY i")
    assert nulls.cls == "agree"
    assert "NULLS FIRST" in nulls.translated
    # Not followed: a setting that changes what `/` means.
    last = _result(replayed, "SELECT 1")
    assert (last.cls, last.reason) == ("skipped", "setting integer_division")


def test_ledger(replayed, tmp_path):
    rows = [slt.asdict(r) for r in replayed]
    path = slt.write_ledger("area", "2.0.0", rows, {"area/y.test": "require json"}, tmp_path)
    assert path.name == "area.json"
    led = json.loads(path.read_text())
    assert led["summary"] == {"agree": 2, "disagree": 2, "refused": 1, "skipped": 1}
    assert led["disagree_sides"] == {"lean": 2}
    assert len(led["results"]) == len(rows)
    summary = slt.write_summary(tmp_path).read_text()
    assert "| [area](area.json) | 2 | 2 | lean 2 | 1 | 1 | 1 |" in summary
    # Rewriting keeps one table.
    assert slt.write_summary(tmp_path).read_text().count("<!-- slt:start -->") == 1


def test_area_of():
    assert slt.area_of("overflow/integer_overflow.test") == "overflow"
    assert slt.area_of("function/numeric/test_mod.test") == "function/numeric"
    assert slt.area_of("types/decimal/x/y.test") == "types/decimal"
