"""The sqllogictest replay harness (`sverify_dev.slt`): parsing DuckDB's `.test`
format, comparing results as DuckDB's runner does, and replaying a small
test file end to end. No network: the files are written here, in DuckDB's
format."""

import hashlib
import json
import textwrap

import pytest

from _repo import needs_repo
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
SELECT list_sort([2, i]) FROM t WHERE i = 1
----
[1, 2]

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
    # DuckDB raises on 64-bit overflow, and so does the reference (`lean_values`
    # reports the error, #747).
    overflow = _result(replayed, "SELECT 9223372036854775807")
    assert (overflow.cls, overflow.side) == ("agree", None)
    assert overflow.lean == "error: Substrait.Issue.wraps"
    assert overflow.engine.startswith("error: Out of Range Error")
    # Division by zero: DuckDB 2.0 raises (and so does the written plan,
    # guarded), and so does the reference.
    div = _result(replayed, "SELECT i // 0")
    assert (div.cls, div.side) == ("agree", None)
    assert div.lean == "error: Substrait.Issue.divByZero"
    assert _result(replayed, "SELECT list_sort").reason.startswith("lift: ")
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
    assert led["summary"] == {"agree": 4, "disagree": 0, "refused": 1, "skipped": 3}
    assert led["disagree_sides"] == {}
    assert len(led["results"]) == len(rows)
    summary = slt.write_summary(tmp_path).read_text()
    assert "| [area](area.json) | 4 | 0 | 0 |  | 1 | 3 | 1 |" in summary
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
    # `engines/duckdb/` also holds `probes.json`.
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


def test_the_summary_counts_the_fuzzer_apart(tmp_path):
    """The totals line counts DuckDB's tests and the fuzzer's queries apart,
    and the links are relative to the README written."""

    def ledger(area, agree, disagree, files):
        name = area.replace("/", "__") + ".json"
        (tmp_path / name).write_text(
            json.dumps(
                {
                    "area": area,
                    "summary": {"agree": agree, "disagree": disagree, "refused": 2, "skipped": 1},
                    "skipped_files": files,
                    "results": [],
                }
            )
        )

    ledger("cast", 3, 1, {"cast/a.test": "require json"})
    ledger("fuzz/int_overflow", 10, 0, {})
    readme = tmp_path / "facts" / "README.md"
    readme.parent.mkdir()
    text = slt.write_summary(tmp_path, readme).read_text()
    assert (
        "Totals over 7 queries of DuckDB's tests: 3 agree, 1 disagree, 2 refused, 1 skipped "
        "(1 files skipped whole). The fuzzer's ledgers (`fuzz/*`) hold 13 generated queries: "
        "10 agree, 0 disagree."
    ) in text
    assert "| [cast](../cast.json) |" in text


@needs_repo
def test_the_committed_summary_goes_to_the_facts_readme():
    assert slt.FACTS_README.relative_to(slt.REPO).as_posix() == "engines/duckdb/facts/README.md"
    assert "<!-- slt:start -->" in slt.FACTS_README.read_text()


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


def test_tables_of_128_bit_integers_out_of_arrow_range_are_refused(tmp_path):
    """DuckDB exports `UHUGEINT` to Arrow as `decimal128(38, 0)`, its maximum
    as -1 (DD-5): the harness refuses such tables rather than mirror them
    (#618). Values Arrow holds mirror as they are."""
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

            statement ok
            CREATE TABLE k AS SELECT 5::HUGEINT AS k UNION ALL SELECT NULL

            query I
            SELECT k FROM k WHERE k IS NOT NULL
            ----
            5
            """
        )
    )
    results, _ = slt.replay_file(path, "area/huge.test")
    assert [r.cls for r in results] == ["refused", "refused", "agree"]
    assert all("DD-5" in (r.reason or "") for r in results[:2])


def test_a_domain_error_is_the_verifiers(tmp_path):
    """`sin` of infinity raises in the reference, where DuckDB gives NaN
    (`duckdb-R15-math-domain`, #617)."""
    path = tmp_path / "trig.test"
    path.write_text(
        textwrap.dedent(
            """\
            query I
            select sin('inf'::DOUBLE)
            ----
            nan
            """
        )
    )
    (r,), _ = slt.replay_file(path, "area/trig.test")
    # DuckDB prints the NaN of sin(inf) as -nan on Linux, nan on macOS.
    assert (r.cls, r.lean) == ("disagree", "error: Substrait.Issue.domain")
    assert r.duckdb in ('[["nan"]]', '[["-nan"]]'), r.duckdb


def test_the_reference_replay_agrees_where_the_reference_raises(tmp_path, monkeypatch):
    """L2 of #1484 (`--semantics reference`): the reference raising where
    DuckDB gives NaN agrees, and a `verify` issue agrees as static (no value
    differs here since #1484's refusal of the rounding casts, so `disagree` has
    no cheap case)."""
    monkeypatch.setenv(slt.SEMANTICS_ENV, "reference")
    path = tmp_path / "ref.test"
    path.write_text(
        textwrap.dedent(
            """\
            query I
            select sin('inf'::DOUBLE)
            ----
            nan

            query I
            select corr(x, y) from (values (1.0::DOUBLE, 1.0::DOUBLE)) t(x, y)
            ----
            nan
            """
        )
    )
    results, _ = slt.replay_file(path, "area/ref.test")
    assert [r.cls for r in results] == ["agree", "agree"], [(r.cls, r.reason) for r in results]
    # `corr` of one pair is NULL here and NaN in DuckDB: only `verify`'s issue
    # (a static check) agrees, marked as such.
    assert (results[1].reason or "").startswith(slt.STATIC), results[1].reason
    # `sin('inf')` is the evaluator's own raise (`LeanRaised`), not a static issue.
    assert (results[0].reason or "").startswith("reference raises"), results[0].reason


def test_an_expected_error_the_verifier_reports_agrees(tmp_path):
    """Where the test expects an error, the reference raises with DuckDB:
    Lean's side agrees (#747)."""
    path = tmp_path / "mod.test"
    path.write_text(
        textwrap.dedent(
            """\
            statement error
            select mod(42, 0)
            ----
            Division by zero
            """
        )
    )
    (r,), _ = slt.replay_file(path, "area/mod.test")
    assert r.cls == "agree", r
    assert r.lean == "error: Substrait.Issue.divByZero"
    # The default mode has no static agreements, however the case is judged.
    led = slt.write_ledger("area", "2.0.0", [slt.asdict(r)], {}, tmp_path)
    assert "agree_static" not in json.loads(led.read_text())
    assert not (r.reason or "").startswith(slt.STATIC)
    # Counted apart under the reference's reading, from the reason alone.
    static = {**slt.asdict(r), "reason": slt.STATIC + " an issue"}
    led = slt.write_ledger("area", "2.0.0", [static, slt.asdict(r)], {}, tmp_path)
    assert json.loads(led.read_text())["agree_static"] == 1


def test_a_tagged_raise_of_a_reported_assumption_is_checked_not_a_disagreement(tmp_path):
    """The written plan's `SUM` guard raises where a sum leaves 64 bits and
    DuckDB gives a HUGEINT: the report lists "SUM overflow" and the checker
    finds it on the data, so the replay agrees with `checked:` (ruling 230,
    #2162)."""
    path = tmp_path / "sum.test"
    path.write_text(
        textwrap.dedent(
            """\
            statement ok
            CREATE TABLE bigints AS SELECT 4611686018427387904 AS b FROM range(3)

            query I
            SELECT SUM(b) FROM bigints
            ----
            13835058055282163712
            """
        )
    )
    (r,), _ = slt.replay_file(path, "area/sum.test")
    assert r.cls == "agree", r
    assert (r.reason or "").startswith(slt.CHECKED + " SUM overflow"), r.reason
    assert "sverify: integer overflow in SUM" in (r.engine or "")
    led = slt.write_ledger("area", "2.0.0", [slt.asdict(r)], {}, tmp_path)
    assert json.loads(led.read_text())["agree_checked"] == 1


@pytest.mark.parametrize(
    ("listed", "lean"),
    [
        # Two issues of the kind: the harness cannot tell which one raised.
        (["SUM overflow: SUM(a)", "SUM overflow: SUM(b)"], "Substrait.Issue.sumWraps"),
        # Lean finds an issue of another kind than the raise's tag.
        (["SUM overflow: SUM(a)"], "Substrait.Issue.wraps"),
        # The report lists no issue of the kind.
        (["overflow: a * b"], "Substrait.Issue.sumWraps"),
    ],
)
def test_a_tagged_raise_without_one_matching_issue_stays_a_disagreement(monkeypatch, listed, lean):
    """The class ties the raise to one listed issue and to the same kind of
    issue in the checker (rulings 230 and 236); otherwise it is a gap (C2)."""
    from sverify import _lean_eval, engine
    from sverify_dev.checked import checked

    monkeypatch.setattr(_lean_eval, "lean_assumed", lambda plan: lean)
    monkeypatch.setattr(engine, "run_checker", lambda args, plan: (0, "", ""))
    msg = "Invalid Input Error: sverify: integer overflow in SUM: 9223372036854775808"
    assert checked(msg, listed, "{}") is None


def test_a_time_of_24_00_is_refused(tmp_path):
    """Python's `datetime.time`, through which the rows reach Lean, has no
    `24:00:00`: it became midnight (#619)."""
    path = tmp_path / "t24.test"
    path.write_text(
        textwrap.dedent(
            """\
            statement ok
            CREATE TABLE times AS SELECT t::TIME AS t FROM (VALUES ('24:00:00'), ('13:00:00')) v(t)

            query I
            SELECT t FROM times
            ----
            24:00:00
            13:00:00
            """
        )
    )
    (r,), _ = slt.replay_file(path, "area/t24.test")
    assert (r.cls, r.reason) == (
        "refused",
        "tables: column t of times holds 24:00:00, "
        "which the rows inlined for Lean (Python times) cannot",
    )


def _row(file, line, cls):
    return {"file": file, "line": line, "sql": "SELECT 1", "cls": cls, "side": "", "reason": ""}


def test_replaying_named_files_replaces_only_their_entries(tmp_path):
    """`--files` (#2045): the entries of the files replayed alone replace the ones of the
    same files, the rest of the area's ledger and its version stay, and the head says
    which files are newer."""
    old = [_row("a/x.test", 1, "agree"), _row("a/y.test", 1, "agree"), _row("a/y.test", 2, "agree")]
    slt.write_ledger("a", "2.0.0", old, {"a/z.test": "require windows"}, tmp_path)
    before = json.loads((tmp_path / "a.json").read_text())

    new = [
        _row("a/y.test", 1, "agree"),
        _row("a/y.test", 2, "refused"),
        _row("a/n.test", 1, "agree"),
    ]
    results, skipped, head = slt.refresh_ledger(
        before, ["a/y.test", "a/n.test"], "2.0.1", new, {"a/n.test": "require x"}
    )
    path = slt.write_ledger("a", before["duckdb"], results, skipped, tmp_path, head=head)
    after = json.loads(path.read_text())

    assert after["duckdb"] == "2.0.0" and after["source"] == before["source"]
    assert after["refreshed"] == {"a/n.test": "2.0.1", "a/y.test": "2.0.1"}
    assert [(r["file"], r["line"], r["cls"]) for r in after["results"]] == [
        ("a/n.test", 1, "agree"),
        ("a/x.test", 1, "agree"),
        ("a/y.test", 1, "agree"),
        ("a/y.test", 2, "refused"),
    ]
    assert after["summary"] == {"agree": 3, "disagree": 0, "refused": 1, "skipped": 0}
    assert after["skipped_files"] == {"a/n.test": "require x", "a/z.test": "require windows"}


def test_a_new_area_is_written_whole_at_the_replayed_version():
    results, skipped, head = slt.refresh_ledger(
        None, ["b/x.test"], "2.0.1", [_row("b/x.test", 1, "agree")], {}
    )
    assert head is None and len(results) == 1 and skipped == {}
