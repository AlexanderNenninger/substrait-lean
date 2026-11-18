"""The case-mapping tables of the tier-1 engines (D51,
`sverify_dev.case_tables`): the recorded differences are what the per-engine
tables give, and Polars and Spark agree on every one-character string."""

from __future__ import annotations

import json

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
