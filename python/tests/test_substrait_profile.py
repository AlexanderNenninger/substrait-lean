"""`Profile.substrait` (#444, step 2): its table, the published diff with the
reference, and checking under it (`verify(semantics="substrait")`)."""

from __future__ import annotations

import json
import subprocess

import ibis
import pyarrow as pa
import pytest
from ibis import _

import sverify as sv
from _repo import needs_repo
from sverify.engine import Connection, checker_path
from sverify_dev import profile_diff


def _checker(*args: str, stdin: str | None = None) -> dict | list:
    out = subprocess.run(
        [str(checker_path()), *args], input=stdin, capture_output=True, text=True, check=True
    )
    return json.loads(out.stdout)


@needs_repo
def test_diff_is_published() -> None:
    """`docs/core-semantics.md` shows the diff the tables give; after a change
    to either table, `python -m sverify_dev.profile_diff --write` updates it."""
    assert profile_diff.published() == profile_diff.table(profile_diff.rows())


def test_diff_names_the_differences() -> None:
    """One zero, one NaN, `nan_creation` and the open defaults differ; where
    the YAML lists values with no default, Substrait allows them all."""
    rows = {(r["group"], r["option"]): r for r in profile_diff.rows()}
    assert rows[(None, "zero_sign")]["substrait"]["default"] == ["IEEE"]
    assert rows[(None, "zero_sign")]["reference"]["default"] == ["ONE_ZERO"]
    assert rows[(None, "nan_kind")]["substrait"]["default"] == ["IEEE"]
    assert set(rows[(None, "nan_creation")]["substrait"]["default"]) == {"NAN", "ERROR"}
    assert set(rows[(None, "overflow")]["substrait"]["default"]) == {"ERROR", "SILENT", "SATURATE"}
    assert set(rows[(None, "null_order")]["substrait"]["default"]) == {
        "NULLS_FIRST",
        "NULLS_LAST",
    }
    # Where they agree there is no row.
    assert (None, "string_positions") not in rows
    assert (None, "empty_group_aggregates") not in rows


def test_tables_have_substrait() -> None:
    """`--options` has Substrait's choices at every option, as a profile with
    no engine, and its observation rows."""
    tables = _checker("--options")
    assert isinstance(tables, dict)
    options = {o["id"] for o in tables["options"]}
    assert {r["option"] for r in tables["choices"]["substrait"]} == options
    assert tables["profiles"]["substrait"] == {"engine": None, "yaml": "0.106.0"}
    obs = {r["option"]: r["row"] for r in tables["observations"]["substrait"]}
    assert obs["zero_sign"]["class"] == "refines_up_to"


@pytest.mark.parametrize(
    ("row", "ok"),
    [
        ({"group": "int.arith", "option": "overflow"}, False),
        ({"group": "fp.arith", "option": "zero_sign"}, False),
        ({"group": "str.sub", "option": "string_positions"}, True),
        ({"group": "rel.sort", "option": "null_order", "preferences": ["NULLS_FIRST"]}, True),
        ({"group": "rel.sort", "option": "null_order"}, False),
    ],
)
def test_transfer_from_reference(row: dict, ok: bool) -> None:
    """`--transfer` from the reference to Substrait: a proof carries over
    where Substrait allows nothing more."""
    out = _checker(
        "--transfer", stdin=json.dumps({"from": "reference", "to": "substrait", "depends": [row]})
    )
    assert isinstance(out, dict)
    assert out["ok"] is ok, out


@pytest.fixture(scope="module")
def con() -> Connection:
    c = sv.connect()
    c.put("t", pa.table({"k": [1, 2, 3], "s": ["a", "bb", "ccc"], "i": [4, -5, 6]}))
    return c


def test_verify_carries_over(con: Connection) -> None:
    """A string's length meets no option where Substrait allows more: proved
    under Substrait as under the reference. (A comparison meets the NaN
    options whatever its type, `Rel.reads`, so it would not carry over.)"""
    t = con.table("t")
    report = sv.verify(
        t.select("k", n=t.s.length()),
        requires={"t": [_.s.notnull()]},
        ensures=[_.n >= 0],
        semantics="substrait",
    )
    assert report.semantics == "substrait"
    assert report._transfer == []
    assert report.proved, report


def test_verify_fails_where_substrait_is_looser(con: Connection) -> None:
    """Integer `+` leaves `overflow` open in Substrait, where the reference
    raises: the reference's proof does not carry over, and the report says
    which option."""
    t = con.table("t")
    expr = t.select(n=t.k + t.i)
    under_ref = sv.verify(
        expr, requires={"t": [_.k.between(0, 10), _.i.between(-10, 10)]}, ensures=[_.n >= -10]
    )
    assert under_ref.proved
    report = sv.verify(
        expr,
        requires={"t": [_.k.between(0, 10), _.i.between(-10, 10)]},
        ensures=[_.n >= -10],
        semantics="substrait",
    )
    assert not report.proved
    assert any(f["option"] == "overflow" for f in report._transfer or ())
    assert 'not proved under semantics="substrait": int.arith\'s overflow' in str(report)


def test_sql_is_refused(con: Connection) -> None:
    """SQL is DuckDB's, so it is not checked under Substrait."""
    with pytest.raises(ValueError, match="checks Ibis transformations"):
        sv.verify(
            "SELECT k FROM t", tables={"t": ibis.schema({"k": "int64"})}, semantics="substrait"
        )
