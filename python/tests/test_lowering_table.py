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
from sverify.sql.duckdb import DuckDBDialect
from sverify_dev import probe

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
    return lowering.render(fn, args, lambda m, dep: D.raise_(m, dep, kind), D.float_lit, D.int_lit)


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
