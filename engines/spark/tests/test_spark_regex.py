"""Regular expressions and digests on Spark (#2540): `regexp_extract` and
`regexp_replace` through `java_regex` and `java_rewrite`, and `md5` and
`sha256`, against the rows `Rel.eval` gives."""

import json

import ibis
import pytest

from sverify._lean_eval import inline_tables, lean_rows
from sverify.engine import connect, run_plan, substrait_json, written_plan

pytestmark = pytest.mark.backend("spark")

TEXTS = ["abc", "bab", "", "aXbY", "a\nb", "a\r\nb", "ab\n", "aaa", "bbb", " \x0b\t", "ab ab",
         "xay", "cab", "a$1\\", "é日", None]  # fmt: skip
SCHEMA = ibis.schema({"i": "int64", "s": "string"})
CALLS = [
    "regexp_extract(s, '^(a|b)(.)', 2)",
    "regexp_extract(s, '(x)?b', 1)",
    "regexp_extract(s, 'a+', 0)",
    "regexp_extract(s, '(a|ab)(c|bcd)?', 0)",
    "regexp_extract(s, '.$', 0)",
    "regexp_extract(s, 'b$', 0)",
    "regexp_extract(s, 'a', 3)",
    "regexp_extract(s, 'x(?:a)(y)', 1)",
    "regexp_extract(s, '[^b]+', 0)",
    "regexp_replace(s, 'a+', '<\\0>', 'g')",
    "regexp_replace(s, '(a)(b)?', '\\2$\\1\\\\')",
    "regexp_replace(s, '(a)', '\\12')",
    "regexp_replace(s, 'b', '[\\0]')",
    "regexp_replace(s, '.', '.')",
    "regexp_replace(s, 'b+', '-', 'g')",
    "regexp_replace(s, '^', '>')",
    "md5(s)",
    "sha256(s)",
]
ASCII_CALLS = ["regexp_replace(s, '\\s+', '_', 'g')", "regexp_extract(s, '[^\\s]+', 0)"]


@pytest.fixture(scope="module")
def spark():
    from spark_session import session

    return session()


def check(spark, call: str, texts: list) -> None:
    rows = [(i, s) for i, s in enumerate(texts)]
    con = connect()
    con.create("r", SCHEMA, rows)
    plan = written_plan(substrait_json(con, f"SELECT i, {call} AS o FROM r", "portable"))
    want = sorted(lean_rows(json.dumps(inline_tables(json.loads(plan), {"r": rows}))))
    got = sorted(tuple(r.values()) for r in run_plan(con, plan, spark, tie_free=False).to_pylist())
    assert got == want


@pytest.mark.parametrize("call", CALLS)
def test_spark_is_the_reference(spark, call):
    check(spark, call, TEXTS)


@pytest.mark.parametrize("call", ASCII_CALLS)
def test_classes_on_ascii_text_are_the_reference(spark, call):
    """`\\s` is RE2's on Spark, without `\\x0B`. The writer raises for a class
    pattern on text outside ASCII or holding `\\x0B` (`ascii_only`,
    `Text.classesDiffer`), so the engines see neither."""
    check(spark, call, [t for t in TEXTS if t is None or (t.isascii() and "\x0b" not in t)])


@pytest.mark.parametrize(
    "call, message",
    [("regexp_extract(s, '(a*)*', 1)", "one more, empty, iteration"),
     ("regexp_extract(s, '(?:(b?)c?)+', 1)", "one more, empty, iteration"),
     ("regexp_replace(s, 'b*', '-', 'g')", "can match ''"),
     ("regexp_replace(s, '$', '!', 'g')", "can match ''"),
     ("regexp_replace(s, '(x|)', '-', 'g')", "can match ''"),
     ("regexp_replace(s, '[\\]]*', '-', 'g')", "can match ''"),
     ("regexp_replace(s, '[\\](]*', '-', 'g')", "can match ''"),
     ("regexp_extract(s, '([\\]]*)*', 1)", "one more, empty, iteration")],
)  # fmt: skip
def test_empty_matches_java_treats_otherwise_are_refused(spark, call, message):
    con = connect()
    con.create("r", SCHEMA, [(0, "abc")])
    plan = written_plan(substrait_json(con, f"SELECT i, {call} AS o FROM r", "portable"))
    with pytest.raises(Exception, match=message):
        run_plan(con, plan, spark, tie_free=False)
