"""`substrait-check --dependencies` (#444, step 3c): the options a plan meets,
each profile's choice there, the option-wise transfer check between
profiles, and the shims each engine needs for the plan."""

import json
import subprocess

import ibis

from sverify.engine import checker_path
from sverify.sql_lift import lift

SCHEMAS = {"t": ibis.schema({"a": "int64", "b": "float64", "c": "int64"})}


def report(query: str, tmp_path) -> dict:
    path = tmp_path / "plan.json"
    path.write_text(json.dumps(lift(query, SCHEMAS).plan))
    out = subprocess.run(
        [str(checker_path()), "--dependencies", str(path)],
        capture_output=True,
        text=True,
        check=True,
    )
    return json.loads(out.stdout)


def test_options_a_plan_meets(tmp_path):
    r = report("SELECT a + c AS x, SUM(b) AS s FROM t GROUP BY a + c ORDER BY x", tmp_path)
    met = {(o["group"], o["option"]) for o in r["options"]}
    assert ("int.arith", "overflow") in met
    assert ("agg.fsum", "sum_order") in met
    assert ("rel.sort", "null_order") in met
    assert ("rel.sort", "clustered") not in met
    sort = next(o for o in r["options"] if o["option"] == "null_order")
    assert sort["preferences"] == ["NULLS_LAST"]
    assert sort["reference"]["allows"] == ["NULLS_LAST"]


def test_transfer_and_shims(tmp_path):
    r = report("SELECT a * c AS x FROM t ORDER BY x", tmp_path)
    # Each profile transfers to itself; Polars wraps where the reference raises.
    for p in ("reference", "duckdb", "polars"):
        assert r["transfer"][p][p] is True
    assert r["transfer"]["reference"]["duckdb"] is True
    assert r["transfer"]["reference"]["polars"] is False
    assert r["shims"]["duckdb"] == []
    assert {s["option"] for s in r["shims"]["polars"]} == {"null_order"}
