"""The table of which engines run each function (`sverify._support`, #271)."""

import re
from pathlib import Path

import pytest

from _repo import needs_repo
from sverify import _support, black_box
from sverify.sql import Unsupported

FUNCTIONS_LEAN = Path(__file__).resolve().parents[2] / "SubstraitLean" / "Functions.lean"


def lean_functions() -> set[str]:
    """The function names Lean's written plans declare (`Functions.lean`'s tables)."""
    return set(re.findall(r'name := "([a-z0-9_]+)"', FUNCTIONS_LEAN.read_text()))


@needs_repo
def test_rows_are_functions_lean_writes() -> None:
    known = lean_functions() | black_box.NAMES
    assert set(_support.SUPPORT) <= known, set(_support.SUPPORT) - known
    for name, engines in _support.SUPPORT.items():
        assert engines <= _support.ENGINES, name
        assert "duckdb" in engines, name


def plan(name: str, key: str = "scalarFunction", anchor: int = 7) -> dict:
    """A plan that declares `add` and `name`, and calls `name`."""
    call = {"arguments": []} if anchor == 0 else {"functionReference": anchor, "arguments": []}
    return {
        "extensions": [
            {"extensionFunction": {"functionAnchor": 1, "name": "add"}},
            {"extensionFunction": {"functionAnchor": anchor, "name": f"{name}:str"}},
        ],
        "relations": [{"root": {"input": {"project": {"expressions": [{key: call}]}}}}],
    }


@pytest.mark.parametrize("dialect", ["spark", "snowflake", "DataFusion", "Polars"])
@pytest.mark.parametrize("name", ["regexp_extract", "md5", "first", "median", "corr"])
def test_duckdb_only(name: str, dialect: str) -> None:
    label = re.escape(_support._LABELS.get(name, name))
    with pytest.raises(
        Unsupported,
        match=f"^{label} runs on duckdb only: run it with engine='duckdb' "
        f"\\({dialect} does not run it yet; see #271, https://github.com/.*/issues/271\\)$",
    ):
        _support.check(plan(name, "measure"), dialect, Unsupported)
    _support.check(plan(name, "measure"), "duckdb", Unsupported)


def test_messages() -> None:
    bb = sorted(black_box.NAMES)[0]
    assert _support.refusal(bb, "spark") == black_box.refusal(bb, "spark")
    assert _support.refusal("sverify_pair", "spark").startswith(
        "covariance and correlation (Ibis cov, corr) runs on duckdb only: "
        "run it with engine='duckdb' (spark does not run it yet; see #271, https://"
    )
    assert _support.refusal("ntile", "DataFusion") == (
        "DataFusion's NTILE does not deal out buckets as SQL does"
    )


def test_engine_specific_rows() -> None:
    assert _support.supported("array_agg", "Polars")
    assert not _support.supported("array_agg", "spark")
    assert _support.supported("ntile", "spark")
    assert not _support.supported("ntile", "datafusion")
    assert _support.supported("add:i64_i64", "snowflake")


def test_only_called_functions() -> None:
    """Lean declares every function; only the calls count."""
    declared = plan("md5")
    declared["relations"] = []
    _support.check(declared, "spark", Unsupported)


def test_anchor_zero() -> None:
    """Protobuf JSON leaves out anchor 0."""
    with pytest.raises(Unsupported, match="sha256"):
        _support.check(plan("sha256", anchor=0), "Polars", Unsupported)
