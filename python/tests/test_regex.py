"""Regular expressions with a constant pattern, and digests (#50).

`regexp_extract`, `regexp_replace`, `md5` and `sha256` are black boxes in the
proofs (`core/Sverify/Core/Text.lean`); Lean evaluates them, regular expressions
with RE2's meaning (`core/Sverify/Core/Regex.lean`). Here:

* Lean's evaluator agrees with DuckDB, which uses RE2, on patterns drawn from
  the subset `Text.simpleRegex` accepts: the leftmost-first match, its groups,
  and replacing the first match or every match;
* every pattern in that subset compiles in DuckDB, as it does in DataFusion
  (`test_text.py`);
* DuckDB's edge cases are pinned: `''` where nothing matches, `\\1` in the
  replacement, empty matches;
* `md5` and `sha256` agree with DuckDB on Unicode text;
* what is not modelled is refused: other flags, column patterns, invalid
  replacements, DuckDB's `hash()`, URL parts, and every engine but DuckDB
  (#271).
"""

import json
import subprocess

import duckdb
import ibis
import pyarrow as pa
import pytest
from hypothesis import HealthCheck, event, given, settings
from hypothesis import strategies as st
from ibis import _

import sverify as sv
from sverify.engine import connect, put_table, run_plan, written_plan
from sverify.ibis_substrait import to_substrait_json
from sverify.sql import Unsupported
from sverify.testing import canonical, duckdb_ibis, inline_tables, lean_values

R = ibis.schema({"s": "string"})


def three_ways(rows: list[tuple], build) -> tuple[list, list, list]:
    """Lean's rows of `build(r)`, DuckDB's of the plan Lean writes, and
    DuckDB's of Ibis's own SQL."""
    con = connect()
    con.create("r", R, rows)
    expr = build(con.table("r"))
    plan = to_substrait_json(expr)
    lean = lean_values(json.dumps(inline_tables(json.loads(plan), {"r": rows})))
    duck = run_plan(con, written_plan(plan), "duckdb").to_pylist()
    native = duckdb_ibis(con, expr).to_pylist()
    return (
        canonical(lean),
        canonical(tuple(d.values()) for d in duck),
        canonical(tuple(d.values()) for d in native),
    )


def test_duckdb_edge_cases():
    rows = [("abc",), ("aaa",), ("",), (None,), ("a\nb",), ("xay",)]
    lean, duck, native = three_ways(
        rows,
        lambda r: r.select(
            none=r.s.re_extract("x", 0),
            second=r.s.re_extract("(b)(c)", 2),
            unset=r.s.re_extract("(x)?b", 1),
            missing=r.s.re_extract("(b)", 2),
            star=r.s.re_extract("(a*)*", 1),
            first=r.s.re_extract("(a|ab)(c|bcd)?", 0),
            dot=r.s.re_extract("a.b", 0),
            noncap=r.s.re_extract("(?:x)(a)", 1),
            groups=r.s.re_replace("(b)", r"[\1\0]"),
            empty=r.s.re_replace("b*", "-"),
            bound=r.s.re_replace(r"\b", "|"),
        ),
    )
    assert lean == duck == native
    assert repr(("", "c", "", "", "a", "a", "", "", "a[bb]c", "-a-c-", "|abc|")) in lean


#: Patterns of the shapes `Text.simpleRegex` accepts, over a small alphabet.
patterns = st.text(alphabet="ab.^$*+?|()[]{}\\-,0123dwsbB:", max_size=10) | st.from_regex(
    r"\^?(\(\?:)?[a-c.]*(\[\^?a-c\]|\\[dwsb]|\((a|b|)\))?[*+?]?\)?(\{[0-2](,[0-3]?)?\})?\$?",
    fullmatch=True,
)
#: ASCII text, where RE2 and Lean's evaluator read every class alike.
ascii_text = st.text(alphabet="ab1_ -.\n", max_size=8)


@given(pattern=patterns, texts=st.lists(ascii_text, min_size=1, max_size=5))
@settings(max_examples=150, deadline=None, suppress_health_check=list(HealthCheck))
def test_the_evaluator_matches_re2(pattern, texts):
    """Lean's leftmost-first matcher against DuckDB's RE2: the match, its
    first group, and replacing the first match and every match."""
    con = connect()
    rows = [(t,) for t in texts]
    con.create("r", R, rows)
    r = con.table("r")
    expr = r.select(
        m=r.s.re_extract(pattern, 0),
        g=r.s.re_extract(pattern, 1),
        every=r.s.re_replace(pattern, r"<\0>"),
    )
    plan = to_substrait_json(expr)
    try:
        sql_plan = written_plan(plan)
    except Exception as e:
        # Outside the subset: Lean refuses it.
        assert "outside the supported subset" in str(e), str(e)
        event("outside the subset")
        return
    event("compared")
    lean = lean_values(json.dumps(inline_tables(json.loads(plan), {"r": rows})))
    duck = run_plan(con, sql_plan, "duckdb").to_pylist()
    assert canonical(lean) == canonical(tuple(d.values()) for d in duck), pattern
    # The first match only: not something Ibis writes, so the SQL directly.
    first = lean_values(
        json.dumps(inline_tables(json.loads(_first_only_plan(pattern)), {"r": rows}))
    )
    native = duckdb.connect()
    q = [
        native.execute("SELECT regexp_replace(?, ?, '<\\0>')", [t, pattern]).fetchone()
        for t in texts
    ]
    assert first == q, pattern


def _first_only_plan(pattern: str) -> str:
    """A plan of `regexp_replace(s, pattern, '<\\0>')` without the `'g'` flag."""
    plan = json.loads(
        to_substrait_json(ibis.table(R, name="r").select(x=_.s.re_replace(pattern, "<\\0>")))
    )

    def walk(node):
        if isinstance(node, dict):
            f = node.get("scalarFunction")
            if isinstance(f, dict) and len(f.get("arguments", [])) == 4:
                f["arguments"].pop()
            for v in node.values():
                walk(v)
        elif isinstance(node, list):
            for v in node:
                walk(v)

    walk(plan)
    return json.dumps(plan)


@given(pattern=patterns)
@settings(max_examples=60, deadline=None)
def test_patterns_said_to_compile_do_in_duckdb(pattern):
    """The trusted part of `Text.simpleRegex`: RE2 compiles what it accepts."""
    t = ibis.table(R, name="r")
    try:
        written_plan(to_substrait_json(t.select(x=t.s.re_extract(pattern, 0))))
    except ValueError as e:
        assert "outside the supported subset" in str(e), str(e)
        return
    duckdb.connect().execute("SELECT regexp_extract('abc', ?, 0)", [pattern]).fetchall()


text = st.one_of(st.none(), st.text(max_size=12))


@given(rows=st.lists(st.tuples(text), max_size=6))
@settings(max_examples=40, deadline=None, suppress_health_check=list(HealthCheck))
def test_digests_match_duckdb(rows):
    lean, duck, native = three_ways(
        rows, lambda r: r.select(m=r.s.hexdigest("md5"), h=r.s.hexdigest("sha256"))
    )
    assert lean == duck == native


def test_contracts_see_types_and_nulls_only():
    t = ibis.table(R, name="r")
    report = sv.verify(
        t.filter(t.s.notnull()).select(
            e=t.s.re_extract("a(b)", 1), p=t.s.re_replace("a", "b"), m=t.s.hexdigest("md5")
        ),
        ensures=[_.e.notnull(), _.p.notnull(), _.m.notnull()],
    )
    assert report.proved, str(report)


def test_lean_refuses_rows_whose_classes_differ_between_engines():
    """`\\d`, `\\w`, `\\s` and `\\b` are ASCII in RE2 and Unicode in Rust:
    Lean does not pick one, and DuckDB raises (#70)."""
    rows = [("é1",)]
    con = connect()
    con.create("r", R, rows)
    expr = con.table("r").select(x=_.s.re_extract(r"\w", 0))
    plan = to_substrait_json(expr)
    with pytest.raises(subprocess.CalledProcessError) as e:
        lean_values(json.dumps(inline_tables(json.loads(plan), {"r": rows})))
    assert "rows not evaluated: regular expression" in e.value.stderr
    with pytest.raises(Exception, match="non-ASCII text differs between engines"):
        run_plan(con, written_plan(plan), "duckdb")


@pytest.mark.parametrize(
    ("build", "message"),
    [
        (lambda t: t.s.re_extract(t.s, 0), "constant pattern"),
        (lambda t: t.s.re_replace("(a)", r"\2"), "replacement"),
        (lambda t: t.s.re_replace("(?i)a", "b"), "outside the supported subset"),
        (lambda t: t.s.hash(), "hexdigest"),
        (lambda t: t.s.hexdigest("sha1"), "md5 and sha256"),
        (lambda t: t.s.host(), "URL parts"),
    ],
)
def test_refused(build, message):
    t = ibis.table(R, name="r")
    with pytest.raises((Unsupported, ValueError), match=message):
        written_plan(to_substrait_json(t.select(x=build(t))))


@pytest.mark.parametrize("engine", ["polars", "datafusion"])
def test_other_engines_refuse_until_271(engine):
    con = connect()
    put_table(con, "r", pa.table({"s": ["abc"]}))
    t = ibis.table(R, name="r")
    for e in (t.s.re_extract("b", 0), t.s.re_replace("b", "c"), t.s.hexdigest("md5")):
        plan = written_plan(to_substrait_json(t.select(x=e)))
        with pytest.raises(Exception, match="see #271"):
            run_plan(con, plan, engine)
