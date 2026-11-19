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


@needs_repo
@pytest.mark.slow
def test_the_collated_form_is_a_byte_compared_string():
    """D51 (L3, L4): `collate(upper(collate(x, 'UNICODE')), 'UTF8_BINARY')` is a
    string that compares, groups, orders and joins by bytes and mixes with an
    uncollated string; invalid UTF-8 becomes U+FFFD as in the plain function."""
    pytest.importorskip("pyspark")
    from spark_session import has_java, session

    if not has_java():
        pytest.skip("Spark needs a JVM")
    got = case_tables.collated_string_checks(session())
    assert got["schema"] == "StringType()"
    # By bytes: `e` + U+0301 (canonically `é`) is its own value and sorts before `Z` and `É`;
    # under `UNICODE` it would be four values with `É` before `Z`.
    assert got["order_by"] == ["A", "B", "E\u0301", "Z", "É", "É"] and got["distinct"] == 5
    assert tuple(got["equal_decomposed"]) == (False,)
    assert got["equal_bytes"] == (True, False) or got["equal_bytes"] == [True, False]
    assert got["mixes_with_plain"] == ("Aa", "Aa", True) or got["mixes_with_plain"] == [
        "Aa",
        "Aa",
        True,
    ]
    assert got["invalid_utf8_plain"] == got["invalid_utf8_collated"] == ["efbfbd"]


#: The pyspark versions `pyspark>=4.0` covers and the conf that picks the JVM's or ICU's path.
PYSPARKS = ("4.0.1", "4.1.1", "4.2.0", "4.3.0")


@needs_repo
def test_every_pyspark_and_conf_has_an_entry_and_differs_only_inside_the_raise_sets():
    """D51 (ruling 68, L2): the collated form's table on each supported pyspark and each
    value of `spark.sql.icu.caseMappings.enabled`, as differences from the default
    table; every scalar that differs lies in the raise sets, so the narrowed guard (the
    raise sets) holds on all of them, and each entry names the pyspark, ICU and Unicode
    version that explain it."""
    from sverify import _case_tables

    probes = json.loads(
        (ROOT / "engines" / "spark" / "probes" / "case-tables-collated.json").read_text()
    )
    for v in PYSPARKS:
        for icu in ("true", "false"):
            entry = probes[f"pyspark_{v}_icu_{icu}"]
            assert entry["pyspark"] == v
            assert entry["icu"] and entry["unicode"] and entry["java"]
            for d, raised in (
                ("upper", _case_tables.UPPER_RAISE),
                ("lower", _case_tables.LOWER_RAISE),
            ):
                assert {int(h, 16) for h in entry[d]} <= set(raised), (v, icu, d)
