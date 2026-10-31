"""The query catalogue (`catalogue/`) is well-formed and its claims hold.

Every query is probed again exactly as `python -m sverify.catalogue --write`
recorded it in `catalogue/status.json`: compiled, checked by `substrait-check`,
and, when verified, run on DataFusion, Polars and DuckDB over the synthetic
tables (with the results compared) and written as Snowflake SQL. A change in
coverage, in an engine or in the catalogue shows up here as a status that no
longer matches; regenerate with `--write` and review the diff.
"""

import json

import pytest

from sverify import catalogue as cat

QUERIES = cat.load_queries()
FEATURES = cat.load_features()
SCHEMAS = cat.load_schemas()
PITFALLS = cat.load_pitfalls()
STATUS = json.loads((cat.ROOT / "status.json").read_text())


def test_well_formed():
    assert cat.validate(QUERIES, FEATURES, SCHEMAS, PITFALLS) == []
    assert len(QUERIES) >= 60


def test_annotations_agree_with_probes():
    """Lean support in features.toml matches what the probes found: no verified
    query needs an unsupported feature, and every failure points at a feature
    the query lists as not (fully) supported."""
    assert sorted(STATUS) == sorted(q.id for q in QUERIES)
    assert cat.consistency(QUERIES, FEATURES, STATUS) == []


def test_generated_files_are_current():
    assert (cat.ROOT / "INDEX.md").read_text() == cat.index(QUERIES, FEATURES, STATUS)
    findings = (cat.ROOT / "FINDINGS.md").read_text()
    table = cat.stats(QUERIES, FEATURES, STATUS, PITFALLS)
    assert cat.with_stats(findings, table) == findings


def test_some_queries_run_everywhere():
    """The catalogue exercises the engines, not only the checker."""
    everywhere = [
        q.id
        for q in QUERIES
        if all(
            cat.runs_on(STATUS[q.id], e) for e in ("datafusion", "polars", "duckdb", "snowflake")
        )
    ]
    assert len(everywhere) >= 10


@pytest.fixture(scope="module")
def con():
    from sverify.engine import connect

    return connect()


@pytest.mark.parametrize("query", QUERIES, ids=lambda q: q.id)
def test_status_holds(con, query):
    got = cat.probe(con, query, SCHEMAS)
    assert got == STATUS[query.id]
    for engine, result in cat.effective(got).get("engines", {}).items():
        assert result != "differs", f"{engine} disagrees with DataFusion"
