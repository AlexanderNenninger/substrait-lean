"""The realizability table (#444, step 3b): `obligations reference E` for each
engine, as `substrait-check --realizability` prints it and
`docs/realizability.md` renders it (`sverify_dev.realizability`)."""

import json

import pytest

from _repo import needs_repo
from _sql_lift import TABLES
from sverify._polars_shims import SHIMS
from sverify.engine import connect, run_plan, written_plan
from sverify.sql_lift import lift
from sverify_dev import realizability

ROOT = realizability.ROOT


@pytest.fixture(scope="module")
def table() -> dict:
    return realizability.table()


@needs_repo
def test_doc_renders(table):
    """The table renders on this branch. Whether `docs/realizability.md` is
    current is not checked here: the `Generated files` workflow rewrites it on
    `main`, so feature branches leave it alone and two PRs never conflict
    over it."""
    assert realizability.render(table).startswith("# Realizability")


def test_engines_and_their_translations(table):
    assert set(table) == {"duckdb", "polars", "spark"}
    assert table["duckdb"]["theorem"] == "Rel.duckdb_refines"
    assert table["polars"]["theorem"] == "Rel.polars_sound"
    assert table["spark"]["theorem"] == "Rel.spark_sound"
    for e in table.values():
        assert e["version"]
        assert not [r for r in e["rows"] if r["case"] == "inconsistent"]


def _ids_exist(engine: str, ids: list[str]) -> list[str]:
    """The ids that name neither a fact nor a test of this repository."""
    missing = []
    for i in ids:
        if "::" in i:
            path, name = i.split("::", 1)
            src = ROOT / "python" / path
            if not src.exists() or f"def {name}(" not in src.read_text():
                missing.append(i)
        elif not any(
            (ROOT / "characterization" / e / "facts" / f"{i}.json").exists()
            for e in (engine, "duckdb", "polars", "spark")
        ):
            missing.append(i)
    return missing


@needs_repo
def test_every_shim_is_proved_or_tested(table):
    """Each shim the table names rests on a Lean theorem (whose existence the
    Lean build checks, `SubstraitLean/Obligations.lean`) or on facts and tests
    that exist here; and each has a cost class."""
    for engine, e in table.items():
        named = {s["name"]: s["cost"] for s in e["shims"]}
        for r in e["rows"]:
            if r["case"] != "shim":
                continue
            assert named[r["shim"]] in ("argument", "expression", "sort"), (engine, r)
            if r["evidence"] == "proved":
                assert r["theorem"], (engine, r)
            else:
                assert r["evidence"] == "tested" and r["facts"], (engine, r)
            assert not _ids_exist(engine, r["facts"]), (engine, r)


@needs_repo
def test_every_row_names_real_facts(table):
    for engine, e in table.items():
        for r in e["rows"]:
            assert not _ids_exist(engine, r["facts"]), (engine, r["option"], r["facts"])
        for f in e["refused_functions"]:
            assert not _ids_exist(engine, f["facts"]), (engine, f)


def test_shim_counts(table):
    """D9's measure: the shims per engine. A new one is a deliberate edit."""
    assert {k: len(e["shims"]) for k, e in table.items()} == {
        "duckdb": 3,
        "polars": 14,
        "spark": 6,
    }


def test_polars_shims_match_the_python_table(table):
    """Each shim of `_polars_shims.SHIMS` is proved as `Polars.<name>` by some
    row, and each Polars shim the table proves by `Polars.<name>` is a row of
    `SHIMS` with the same cost."""
    rows = table["polars"]["rows"]
    theorems = {r.get("theorem") for r in rows}
    by_name = {s.name: s for s in SHIMS}
    for s in SHIMS:
        assert f"Polars.{s.name}" in theorems, s.name
    costs = {s["name"]: s["cost"] for s in table["polars"]["shims"]}
    for r in rows:
        if r["case"] == "shim" and r.get("theorem") == f"Polars.{r['shim']}":
            assert r["shim"] in by_name, r
            assert by_name[r["shim"]].cost == costs[r["shim"]], r


def test_duckdb_error_side_needs_no_shim(table):
    """The reference raises at its error-side options, so DuckDB's IEEE values
    there are preconditions, not shims."""
    rows = {(r["group"], r["option"]): r for r in table["duckdb"]["rows"]}
    error_side = [
        (None, "nan_creation"),
        (None, "on_domain_error"),
        ("fp.div", "on_division_by_zero"),
    ]
    for key in error_side:
        assert rows[key]["case"] == "precondition", key
        assert rows[key]["tool"] == "raise"


SCHEMAS = {"orders": __import__("ibis").Schema.from_pyarrow(TABLES["orders"].schema)}


def test_clustered_is_a_sort():
    """DuckDB's row of `clustered`: a clustered key runs as `ORDER BY` the
    keys, which puts equal keys next to each other."""
    plan = lift("SELECT id, price FROM orders ORDER BY price", SCHEMAS).plan
    text = json.dumps(plan).replace("SORT_DIRECTION_ASC_NULLS_LAST", "SORT_DIRECTION_CLUSTERED")
    assert "SORT_DIRECTION_CLUSTERED" in text
    orders = TABLES["orders"]
    con = connect("duckdb")
    con.create("orders", orders.schema, [tuple(r.values()) for r in orders.to_pylist()])
    prices = run_plan(con, written_plan(text), "duckdb").column("price").to_pylist()
    assert sorted(prices, key=lambda p: (p is None, p)) == sorted(
        orders.column("price").to_pylist(), key=lambda p: (p is None, p)
    )
    seen: list = []
    for p in prices:
        if seen and seen[-1] != p:
            assert p not in seen, prices
        seen.append(p)


@needs_repo
def test_evidence_levels(table):
    """Each row has a level; a row the Polars lemmas cover is `proof`, a row
    with no fact `missing`, and a fact's level is its strongest check."""
    for engine, e in table.items():
        for r in e["rows"]:
            assert realizability.row_level(engine, r) in realizability.LEVELS
    rows = {(r["group"], r["option"]): r for r in table["polars"]["rows"]}
    assert realizability.row_level("polars", rows[("int.div", "division_type")]) == "proof"
    assert realizability.row_level("duckdb", {"facts": []}) == "missing"
    assert (
        realizability.row_level(
            "duckdb", {"evidence": "proved", "theorem": "Choice.le_sound", "facts": []}
        )
        == "missing"
    )
    # A fact is never `missing`, and only a Lean lemma is `proof`.
    assert realizability.fact_level("duckdb", "duckdb-R1") not in ("missing", "proof")
