"""What a tool built on sverify reads from it as data (#177's API notes):
one `Unsupported` for every refusal, each postcondition's condition and
reason, the needed preconditions as `Needed`, and DuckDB type names in
`verify(tables=...)`."""

import ibis
import pytest

import sverify as sv
import sverify.engines
import sverify.errors
from sverify.contracts import Needed


def _needed(report):
    """The labels of `report.needs` per input table."""
    out: dict[str, list[str]] = {}
    for n in report.needs:
        out.setdefault(n.table, []).append(n.label)
    return out


T = {"t": {"k": "BIGINT", "q": "BIGINT", "s": "VARCHAR"}}


def test_one_unsupported_for_every_refusal() -> None:
    assert sverify.engines.Unsupported is sverify.errors.Unsupported
    assert issubclass(sverify.errors.Unsupported, ValueError)
    # The SQL lift's refusal, which used to escape `except engines.Unsupported`.
    with pytest.raises(sverify.errors.Unsupported, match="WITH RECURSIVE"):
        sv.verify("with recursive c as (select 1 as x) select * from c", tables=T)
    # The SQL writer's.
    from sverify.sql import Unsupported as WriterRefused

    assert issubclass(WriterRefused, sverify.errors.Unsupported)


def test_a_postcondition_keeps_its_condition_and_reason() -> None:
    key = sv.unique("k")
    report = sv.verify(
        "select k, q, 'a' as s from t where q > 0",
        tables=T,
        semantics="duckdb",
        ensures=["q > 0", "s = 'b'", key, "q > 5", "k IS NOT NULL"],
    )
    got = {c.label: (c.condition, c.reason) for c in report.ensures}
    assert got == {
        "q > 0": ("q > 0", None),
        "s = 'b'": ("s = 'b'", "always_false"),
        "unique(k)": (key, "not_a_key"),
        "q > 5": ("q > 5", "may_be_false"),
        "k IS NOT NULL": ("k IS NOT NULL", "may_be_false"),
    }


def test_reason_of_a_condition_that_may_be_null() -> None:
    report = sv.verify(
        "select q from t", tables=T, requires={"t": ["q IS NULL OR q > 0"]}, ensures=["q > 0"]
    )
    [c] = report.ensures
    assert (c.proved, c.value, c.reason) == (False, "TRUE or NULL", "may_be_null")
    assert c.why.startswith("it may be NULL on some rows")


def test_needs_as_data() -> None:
    report = sv.verify("select q + 1 as a, k * 3 as b from t", tables=T, semantics="duckdb")
    assert not report.proved
    needs = report.needs
    assert [(n.table, n.column, n.op, n.value) for n in needs] == [
        ("t", "q", "<", "9000000000000000000"),
        ("t", "k", ">=", "-3000000000000000000"),
        ("t", "k", "<", "3000000000000000000"),
    ]
    first = needs[0]
    assert isinstance(first, Needed)
    assert first.sql == '"q" IS NULL OR "q" < 9000000000000000000'
    assert first.label == "(_.q < 9 * 10**18)"
    assert first.code == "_.q < 9 * 10**18"
    assert first.issue is not None and first.issue.shown == "q + 1"
    assert [n.label for n in needs] == [lab for labs in _needed(report).values() for lab in labs]


def test_needs_code_is_what_requires_takes() -> None:
    t = ibis.table({"g": "int64", "total": "int64", "qty": "int64"}, name="t")
    report = sv.verify(t.select(t.g, per=t.total // t.qty))
    codes = [n.code for n in report.needs]
    assert "_.qty != 0" in codes
    from ibis import _

    proved = sv.verify(
        t.select(t.g, per=t.total // t.qty),
        requires={"t": [eval(c, {"_": _}) for c in codes]},  # noqa: S307 - our own code
    )
    assert proved.proved


def test_needs_is_empty_when_inferred_bounds_are_assumed() -> None:
    report = sv.verify("select q + 1 as a from t", tables=T, on_inferred="silent")
    assert report.needs == [] and report.inferred


def test_tables_take_duckdb_type_names() -> None:
    report = sv.verify(
        "select id, n, s from t",
        tables={"t": {"id": "BIGINT", "n": "HUGEINT", "s": "VARCHAR NOT NULL", "x": "!int64"}},
        ensures=["s IS NOT NULL"],
    )
    assert report.proved
    assert report.output["id"] == ibis.dtype("int64")
    assert report.output["n"] == ibis.dtype("decimal(38, 0)")
    with pytest.raises(ValueError, match="neither an Ibis type nor one of DuckDB's"):
        sv.verify("select a from t", tables={"t": {"a": "frob"}})


def test_checker_pipes_close() -> None:
    from sverify.engine import _CHECKER

    sv.verify("select k from t", tables=T)
    proc = _CHECKER.proc
    assert proc is not None
    _CHECKER.close()
    assert proc.stdin is not None and proc.stdin.closed
    assert proc.stdout is not None and proc.stdout.closed
