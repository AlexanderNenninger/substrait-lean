"""The generated lowering to DuckDB as SQL (`sverify.sql.lowering`, #241): each
template, written by the interpreter, gives the reference's outcome on DuckDB.

The probes of `sverify_dev.probe` (#242) run each function on edge cases; here
DuckDB runs the function's template instead, and every row must give what
Lean's reference gives, errors included. That checks the interpreter and the
proved template together against the real engine."""

import dataclasses
import itertools

import duckdb
import pytest

from sverify.sql import lowering
from sverify_dev import probe
from sverify_duckdb.dialect import DuckDBDialect

pytestmark = pytest.mark.backend("duckdb")

#: The probes' constructs by the table's function names.
FUNCTIONS = {
    ("{0} + {1}", "float64"): "fadd",
    ("{0} - {1}", "float64"): "fsub",
    ("{0} * {1}", "float64"): "fmul",
    ("{0} / {1}", "float64"): "fdiv",
    ("{0} % {1}", "float64"): "fmod",
    ("{0} // {1}", "int64"): "idiv",
    ("{0} % {1}", "int64"): "imod",
    ("power({0}, {1})", "float64"): "fpow",
    ("atan2({0}, {1})", "float64"): "fatan2",
    ("{0} << {1}", "int64"): "bit:bitwise_shift_left",
    ("{0} >> {1}", "int64"): "bit:bitwise_shift_right",
    **{
        (f"{f}({{0}})", "float64"): f"fmath:{f}"
        for f in ("sqrt", "exp", "ln", "log10", "log2", "sin", "cos", "tan", "asin", "acos")
    },
}

D = DuckDBDialect(name="DuckDB")


def _template(p: probe.Probe) -> str | None:
    fn = FUNCTIONS.get((p.construct, p.args[0]))
    if fn is None:
        return None
    kind = "float" if p.result == "float64" else "int"
    args = [f"{{{i}}}" for i in range(len(p.args))]
    return lowering.render(
        fn, args, lambda m, dep: D.raise_(m, dep, kind, "raised"), D.float_lit, D.int_lit
    )


CASES = [p for p in probe.PROBES if not p.constants and _template(p) is not None]


def test_the_table_covers_the_probed_differences():
    found = {FUNCTIONS[(p.construct, p.args[0])] for p in CASES}
    # Every function DuckDB computes differently has a template (FACTS R15);
    # exp and atan, which DuckDB computes as the reference does, have none.
    assert {"fadd", "fdiv", "fmod", "fpow", "imod", "fmath:sqrt", "bit:bitwise_shift_left"} <= found
    assert lowering.table().get("fmath:exp") is None


@pytest.mark.parametrize("p", CASES, ids=lambda p: p.construct.format(*p.args))
def test_template_gives_the_reference_outcome(p):
    sql = _template(p)
    assert sql is not None
    # The arguments are `{0}`, `{1}`: the SQL has no braces of its own.
    lowered = dataclasses.replace(p, construct=sql)
    rows = list(itertools.product(*(probe.TYPES[t][1] for t in p.args)))
    con = duckdb.connect()
    engine = [probe.duckdb_outcome(con, lowered, r) for r in rows]
    lean = probe.lean_outcomes(p, rows, None)
    differ = [
        (r, e, x) for r, e, x in zip(rows, engine, lean, strict=True) if not probe._same(e, x)
    ]
    assert not differ, differ[:5]


def test_guard_free_sql_has_no_errors():
    """Without guards the template's raising arms are left out; what stays is
    the semantics (`MIN % -1` is 0, `<<` wraps around)."""
    sql = lowering.render(
        "bit:bitwise_shift_left",
        ["x", "y"],
        lambda m, dep: f"error({m})",
        D.float_lit,
        D.int_lit,
        guards=False,
    )
    assert sql is not None and "error(" not in sql and "HUGEINT" in sql


def _raise_arms(t, chain: bool) -> list[bool]:
    """Whether each `raise` arm of a template sits on its outer `ELSE` chain."""
    if "if" in t:
        here = [chain] if t["then"].get("fn") == "raise" else []
        return (here + _raise_arms(t["if"], False) + _raise_arms(t["then"], False)
                + _raise_arms(t["else"], chain))  # fmt: skip
    return [a for x in t.get("args", []) for a in _raise_arms(x, False)]


def test_every_guard_is_on_the_outer_else_chain():
    # `render(..., guards=False)` leaves out every `raise` arm; Lean's
    # `Expr.keepGuards` (none kept), which `Rel.duckdb_guardFree_sound`
    # proves sound, leaves out those of the outer `ELSE` chain. They are the
    # same SQL while every guard sits there.
    for fn, t in lowering.table().items():
        assert all(_raise_arms(t, True)), fn


@pytest.mark.parametrize("table", [True, False], ids=["template", "fallback"])
def test_a_double_to_bigint_truncates(monkeypatch, table):
    """DuckDB's cast rounds half to even (duckdb-R9); the reference truncates.
    The template does (`Lowering.ftoi_agree`), and so does the fallback when the
    table has no entry."""
    if not table:
        monkeypatch.setattr(DuckDBDialect, "lowered", lambda *_a, **_k: None)
    xs = [3.5, -3.5, 2.5, -2.5, 0.5, -0.5, 2.7, -2.7]
    want = [3, -3, 2, -2, 0, 0, 2, -2]
    con = duckdb.connect()
    for write in (D.float_to_int, D.float_to_int_or_null):
        got = [con.execute(f"SELECT {write(f'CAST({x!r} AS DOUBLE)')}").fetchone() for x in xs]
        assert got == [(w,) for w in want], write.__name__
    nan = "CAST('NaN' AS DOUBLE)"
    assert con.execute(f"SELECT {D.float_to_int_or_null(nan)}").fetchone() == (None,)


def test_the_split_entry_is_the_reference_on_duckdb():
    """`sverify_split_first`'s entry (ruling 286, ruling 290): `split_part(s, t, 1)`,
    with an empty `t` passed through as `s`, where DuckDB would give the first code
    point (duckdb-split-part)."""
    sql = lowering.render(
        "Substrait.BinFn.splitFirst",
        ["s", "t"],
        lambda m, dep: D.raise_(m, dep, "str", "raised"),
        D.float_lit,
        D.int_lit,
    )
    assert sql is not None and "split_part(s, t, 1)" in sql
    cases = [("héllo wörld", "ö"), ("aaa", "aa"), ("abc", "d"), ("abc", ""), ("", ""),
             ("éx", ""), (None, "a"), ("abc", None), (None, "")]  # fmt: skip
    con = duckdb.connect()
    for s, t in cases:
        got = con.execute(f"SELECT {sql} FROM (SELECT ?::VARCHAR AS s, ?::VARCHAR AS t)", [s, t])
        want = None if s is None or t is None else (s if t == "" or t not in s else s[: s.find(t)])
        assert got.fetchone()[0] == want, (s, t)
