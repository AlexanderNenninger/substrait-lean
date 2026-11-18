"""D51's generated case-mapping source (`sverify_dev.case_mapping`): the committed
Lean table and Python raise sets are what the probed tables generate, and the raise
sets have the shape the decision states."""

from __future__ import annotations

import pytest

from _repo import needs_repo
from sverify import _case_tables
from sverify.sql.core import case_class, case_raises
from sverify_dev import case_mapping

SUPPLEMENTARY = 0x10000


@needs_repo
def test_the_committed_source_is_the_generated_one():
    """A new probe or engine version that moves a scalar changes the table:
    regenerate with `python -m sverify_dev.case_mapping --write`."""
    g = case_mapping.generate()
    assert case_mapping.LEAN.read_text() == case_mapping.lean(g)
    assert case_mapping.PY.read_text() == case_mapping.python(g)


def test_the_raise_sets_are_the_decisions():
    assert len(_case_tables.UPPER_RAISE) == 157
    assert len(_case_tables.LOWER_RAISE) == 57
    assert 0x3A3 in _case_tables.LOWER_RAISE
    assert 0x3A3 not in _case_tables.UPPER_RAISE
    for s in (_case_tables.UPPER_RAISE, _case_tables.LOWER_RAISE):
        assert list(s) == sorted(set(s))
        # ASCII text is outside both sets (`Text.upperRaises_of_isAscii`).
        assert min(s) >= 0x80


def test_the_sets_have_the_supplementary_plane_members_the_run_check_covers():
    """47 in each set (U+10Dxx and U+16Exx): a UTF-16 regex and a byte-wise
    `translate` treat them differently from one scalar."""
    for which in ("upper", "lower"):
        assert sum(c >= SUPPLEMENTARY for c in _case_tables.raise_set(which)) == 47


@needs_repo
def test_the_agreed_mapping_is_one_scalar_each_and_outside_the_raise_sets():
    g = case_mapping.generate()
    for d in ("upper", "lower"):
        assert not set(g[d]["map"]) & set(g[d]["raise"])
    assert g["upper"]["map"][ord("a")] == ord("A")
    assert g["lower"]["map"][ord("A")] == ord("a")
    assert (len(g["upper"]["map"]), len(g["lower"]["map"])) == (1423, 1431)


@pytest.mark.parametrize("which", ["upper", "lower"])
def test_case_raises_reads_the_set(which):
    for c in _case_tables.raise_set(which):
        assert case_raises(f"a{chr(c)}b", which)
    assert not case_raises("Hello, world", which)
    # `ß` is `UPPER`'s only member below U+0100, `İ` `LOWER`'s.
    assert case_raises("ß", "upper") and not case_raises("ß", "lower")
    assert case_raises("İ", "lower") and not case_raises("İ", "upper")
    assert case_raises("ΑΣ", "lower") and not case_raises("ΑΣ", "upper")


@pytest.mark.parametrize("which", ["upper", "lower"])
def test_the_class_is_in_the_supported_regex_subset(which):
    """The lift reads the inferred precondition's SQL back (`Text.simpleRegex`): at most
    200 characters, and no metacharacter, since every member is outside ASCII."""
    cls = case_class(which)
    assert len(cls) <= 200
    assert cls[0] == "[" and cls[-1] == "]"
    assert not any(c in cls[1:-1] for c in "[]^\\&~")
    assert all(ord(c) >= 0x80 or c == "-" for c in cls[1:-1])


def _members(which):
    return [chr(c) for c in _case_tables.raise_set(which)]


def _agreed(which):
    g = case_mapping.generate()
    return [chr(c) for c in g[which]["map"]]


@needs_repo
@pytest.mark.parametrize("which", ["upper", "lower"])
@pytest.mark.parametrize(
    "engine", ["duckdb", "polars", pytest.param("spark", marks=pytest.mark.slow)]
)
def test_the_run_check_finds_every_member_of_the_set_and_no_agreed_scalar(which, engine):
    """The precondition `Report.check_inputs` runs on the data, written natively for each
    engine, flags each scalar of the raise set (the 47 supplementary-plane members among
    them: a UTF-16 regular expression and a byte-wise `translate` treat them differently
    from one scalar) and none the engines agree on."""
    import pyarrow as pa

    from sverify.contracts import _text_condition
    from sverify.engine import connect, put_table
    from sverify.report import violation_counts

    if engine == "spark":
        pytest.importorskip("pyspark")
        from spark_session import has_java

        if not has_java():
            pytest.skip("Spark needs a JVM")
    cond = _text_condition("s", which)
    con = connect()
    for name, scalars, flagged in (
        ("raised", _members(which), True),
        ("agreed", _agreed(which), False),
    ):
        put_table(con, name, pa.table({"s": [*scalars, None]}))
        ((_, n, error),) = violation_counts(con.table(name), [cond], engine)
        assert error is None
        assert n == (len(scalars) if flagged else 0), (name, engine)


@needs_repo
@pytest.mark.parametrize("which", ["upper", "lower"])
@pytest.mark.parametrize(
    "engine", ["duckdb", "polars", pytest.param("spark", marks=pytest.mark.slow)]
)
def test_the_engines_give_the_agreed_mapping(which, engine):
    """The table is the engines' value: on every scalar of the agreed mapping (and a
    few that no engine maps) each engine, through the written plan, gives the generated
    Lean table's value (`Text.upper`, `Text.lower`)."""
    import pyarrow as pa

    from sverify.engine import connect, put_table, run_plan, substrait_json, written_plan

    if engine == "spark":
        pytest.importorskip("pyspark")
        from spark_session import has_java

        if not has_java():
            pytest.skip("Spark needs a JVM")
    table = case_mapping.generate()[which]["map"]
    scalars = [*table, *range(0x20, 0x7F), 0x4E00, 0x1F600]
    con = connect()
    put_table(con, "r", pa.table({"s": [chr(c) for c in scalars]}))
    plan = written_plan(substrait_json(con, f"SELECT {which}(s) AS u FROM r", semantics="duckdb"))
    got = run_plan(con, plan, engine).column(0).to_pylist()
    assert got == [chr(table.get(c, c)) for c in scalars]


@needs_repo
@pytest.mark.parametrize("which", ["upper", "lower"])
def test_the_written_guard_raises_on_every_member_of_the_set_on_duckdb(which):
    """The same predicate as the inferred precondition, written into the plan: each member
    of the raise set, one scalar at a time, raises; the report lists the issue."""
    import pyarrow as pa

    from sverify.engine import connect, put_table, run_plan, substrait_json, written_plan

    con = connect()
    put_table(con, "r", pa.table({"s": ["a"]}))
    plan = written_plan(substrait_json(con, f"SELECT {which}(s) AS u FROM r", semantics="duckdb"))
    for c in _case_tables.raise_set(which):
        put_table(con, "r", pa.table({"s": ["a" + chr(c) + "b"]}))
        with pytest.raises(Exception, match="scalar the engines map differently"):
            run_plan(con, plan, "duckdb")


@needs_repo
@pytest.mark.parametrize("which", ["upper", "lower"])
def test_lean_evaluates_the_generated_table(which):
    """`Text.upper` and `Text.lower` (a binary search of `CaseTable`) give the table's
    value on each scalar, and the scalar itself where none is listed."""
    import json

    from sverify.testing import inline_tables, lean_values
    from test_text import R, connect, plan_of

    table = case_mapping.generate()[which]["map"]
    scalars = [*table, *range(0x20, 0x7F), 0x4E00, 0x1F600]
    con = connect()
    con.create("r", R, [])
    plan = json.loads(plan_of(con, f"SELECT {which}(s) AS u FROM r"))
    rows = [(chr(c), "x", 1) for c in scalars]
    got = lean_values(json.dumps(inline_tables(plan, {"r": rows})))
    assert [r[0] for r in got] == [chr(table.get(c, c)) for c in scalars]
