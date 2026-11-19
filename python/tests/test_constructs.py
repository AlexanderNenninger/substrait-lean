"""#700: a refusal of the SQL lift or the Ibis producer names its construct as data.

`UnsupportedError.construct` is `"function md5"` for a function (its lower-case
name as the user writes it) and otherwise the SQL keywords in upper case
(`"WITH RECURSIVE"`, `"IS DISTINCT FROM"`). `sverify_dev.exits` counts the
refusals of `sql_lift/` and `ibis_substrait/` that set none, per file;
`construct_baseline.json` is `{}`: every site sets one, and a refusal without
`construct=` fails here.
"""

import json

import pytest

from _repo import needs_repo

pytestmark = needs_repo

exits = pytest.importorskip("sverify_dev.exits")


def test_no_new_refusal_without_a_construct():
    base = json.loads(exits.CONSTRUCT_BASELINE.read_text())
    now = exits.missing_construct_by_file()
    risen = {f: (base.get(f, 0), n) for f, n in now.items() if n > base.get(f, 0)}
    assert not risen, f"refusals with no `construct=`, as (baseline, now) per file: {risen}"


def test_baseline_is_lowered_with_the_count():
    base = json.loads(exits.CONSTRUCT_BASELINE.read_text())
    assert exits.missing_construct_by_file() == base, (
        "lower construct_baseline.json with `python -m sverify_dev.exits --write-baseline`"
    )


def test_every_construct_has_the_one_spelling():
    bad = [
        f"{s.file}:{s.line}: {s.construct!r}"
        for s in exits.construct_sites()
        if s.construct is not None and not exits.CONSTRUCT_FORM.fullmatch(s.construct)
    ]
    assert not bad, "\n".join(bad)


def test_the_producer_sets_no_sql():
    """An Ibis expression's repr is not SQL: only the SQL lift sets `sql=`."""
    import ast
    from pathlib import Path

    root = exits.SRC / "ibis_substrait"
    bad = [
        f"{p.name}:{n.lineno}"
        for p in root.rglob("*.py")
        for n in ast.walk(ast.parse(p.read_text()))
        if isinstance(n, ast.Call)
        and any(k.arg == "sql" for k in n.keywords)
        and isinstance(n.func, ast.Name)
        and n.func.id.endswith("Unsupported")
    ]
    assert not bad, bad
    assert Path(root).is_dir()


def test_a_refusal_carries_its_construct_and_sql():
    import sverify as sv

    with pytest.raises(sv.errors.UnsupportedError) as e:
        sv.verify("select md5(x) as h from t", tables={"t": {"x": "BIGINT"}})
    assert str(e.value)  # unchanged text
    assert hasattr(e.value, "construct") and hasattr(e.value, "sql")


def test_an_ibis_aggregate_refusal_names_its_function():
    import ibis

    import sverify as sv

    t = ibis.table({"k": "string", "v": "float64"}, name="t")
    with pytest.raises(sv.errors.UnsupportedError) as e:
        sv.verify(t.group_by("k").agg(n=t.v.approx_nunique()))
    assert e.value.construct == "function approx_nunique" and e.value.sql is None


def test_the_sql_lift_names_the_fragment_it_refused():
    import sverify as sv

    with pytest.raises(sv.errors.UnsupportedError) as e:
        sv.verify("select md5(x) as h from t", tables={"t": {"x": "BIGINT"}})
    assert e.value.construct == "function md5"
    assert "MD5" in (e.value.sql or "").upper()


def test_the_op_table_names_real_ibis_operations_by_one_spelling():
    """The method names a user calls, for the operations a refusal can name."""
    import ibis.expr.operations as ops

    from sverify.ibis_substrait._constructs import OP_METHODS

    assert all(hasattr(ops, name) for name in OP_METHODS), [
        n for n in OP_METHODS if not hasattr(ops, n)
    ]
    assert all(exits.CONSTRUCT_FORM.fullmatch(f"function {m}") for m in OP_METHODS.values())
