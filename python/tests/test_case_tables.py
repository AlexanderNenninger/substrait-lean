"""The case-mapping tables of the tier-1 engines (D51,
`sverify_dev.case_tables`): the recorded differences are what the per-engine
tables give, and Polars and Spark agree on every one-character string."""

from __future__ import annotations

import json

import pytest

from _repo import needs_repo
from sverify_dev import case_tables

ROOT = case_tables.ROOT


@needs_repo
def test_the_differences_are_the_tables_differences():
    tables = {
        e: json.loads((ROOT / "engines" / e / "probes" / "case-tables.json").read_text())
        for e in ("duckdb", "polars", "spark")
    }
    recorded = json.loads((ROOT / "characterization" / "case-differences.json").read_text())
    assert case_tables.differences(tables) == {k: recorded[k] for k in ("upper", "lower")}
    assert (recorded["upper"]["scalars_that_differ"], recorded["lower"]["scalars_that_differ"]) == (
        157,
        56,
    )
    for d in ("upper", "lower"):
        assert tables["polars"][d] == tables["spark"][d]


def _recorded(engine: str) -> dict:
    return json.loads((ROOT / "engines" / engine / "probes" / "case-tables.json").read_text())


@needs_repo
@pytest.mark.parametrize("engine", ["duckdb", "polars"])
def test_the_tables_are_current_at_the_installed_version(engine):
    """D51 (C3): the table holds for the probed versions, and CI's versions keep
    it honest. A new version that maps an agreed scalar differently moves that
    scalar into a raise set: regenerate with `python -m sverify_dev.case_tables
    --write`."""
    now = getattr(case_tables, f"{engine}_tables")()
    recorded = _recorded(engine)
    assert now == {d: recorded[d] for d in ("upper", "lower")}


@needs_repo
@pytest.mark.slow
def test_the_spark_table_is_current_at_the_installed_version():
    pytest.importorskip("pyspark")
    from spark_session import has_java

    if not has_java():
        pytest.skip("Spark needs a JVM")
    recorded = _recorded("spark")
    assert case_tables.spark_tables() == {d: recorded[d] for d in ("upper", "lower")}
