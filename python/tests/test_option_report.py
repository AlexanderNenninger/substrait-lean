"""`substrait-check --dependencies` (#444, step 3c): the options a plan meets,
each profile's choice there, the option-wise transfer check between
profiles, and the shims each engine needs for the plan."""

import json
import subprocess

import ibis

from sverify.engine import checker_path
from sverify.ibis_substrait import to_substrait_json
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
    # A stated NULL placement is native on Polars (`nulls_last`).
    assert r["shims"]["polars"] == []


STRINGS = {"t": ibis.schema({"a": "int64", "b": "float64", "s": "string"})}


def dependencies(plan: dict, tmp_path) -> dict:
    path = tmp_path / "plan.json"
    path.write_text(json.dumps(plan))
    out = subprocess.run(
        [str(checker_path()), "--dependencies", str(path)],
        capture_output=True,
        text=True,
        check=True,
    )
    return json.loads(out.stdout)


def transfer(request: dict) -> dict:
    out = subprocess.run(
        [str(checker_path()), "--transfer"],
        input=json.dumps(request),
        capture_output=True,
        text=True,
        check=True,
    )
    return json.loads(out.stdout)


def depends_of(report: dict) -> list[dict]:
    return [
        {"group": o["group"], "option": o["option"], "preferences": o["preferences"]}
        for o in report["options"]
    ]


def test_f2_double_arithmetic_transfers_from_duckdb_to_polars(tmp_path):
    """F2: arithmetic that may reach ±∞, under DuckDB's profile: Polars's IEEE
    choices are within DuckDB's at every option the plan meets."""
    r = dependencies(lift("SELECT b * b + b AS y FROM t", STRINGS).plan, tmp_path)
    met = {o["option"] for o in r["options"]}
    assert {"float_overflow", "nan_creation", "zero_sign", "rounding"} <= met
    assert r["transfer"]["duckdb"]["polars"] is True
    assert r["transfer"]["reference"]["polars"] is False
    out = transfer({"from": "duckdb", "to": "polars", "depends": depends_of(r)})
    assert out == {"ok": True, "failures": []}


def test_f3_default_null_order_does_not_transfer(tmp_path):
    """F3: an UNSPECIFIED sort key read as DuckDB's NULLs last: Polars puts
    NULLs first, so the transfer fails on `null_order`, with its fact."""
    plan = lift("SELECT a FROM t ORDER BY a", STRINGS).plan
    text = json.dumps(plan).replace("SORT_DIRECTION_ASC_NULLS_LAST", "SORT_DIRECTION_UNSPECIFIED")
    r = dependencies(json.loads(text), tmp_path)
    assert r["transfer"]["duckdb"]["polars"] is False
    out = transfer({"from": "duckdb", "to": "polars", "depends": depends_of(r)})
    assert out["ok"] is False
    [failure] = out["failures"]
    assert (failure["option"], failure["from"], failure["to"]) == (
        "null_order",
        ["NULLS_LAST"],
        ["NULLS_FIRST"],
    )
    assert failure["facts"] == ["polars-null-order"]


def test_g1_md5_is_missing_on_polars(tmp_path):
    t = ibis.table(STRINGS["t"], name="t")
    plan = json.loads(to_substrait_json(t.select(h=t.s.hexdigest("md5"))))
    r = dependencies(plan, tmp_path)
    assert "md5" in r["functions"]
    assert r["missing"]["duckdb"] == []
    assert [m["function"] for m in r["missing"]["polars"]] == ["md5"]
    out = transfer({"from": "duckdb", "to": "polars", "depends": [], "functions": ["md5"]})
    assert out["ok"] is False
    assert out["failures"][0]["function"] == "md5"


def test_b2_double_group_keys(tmp_path):
    """B2: grouping by a double meets NaN equality and the zeros; Polars is
    the reference's up to one zero, or after the `one_zero` shim."""
    r = dependencies(lift("SELECT b, COUNT(*) AS n FROM t GROUP BY b", STRINGS).plan, tmp_path)
    keys = {o["option"]: o for o in r["options"] if o["group"] == "rel.keys"}
    assert set(keys) == {"nan_equality", "zero_sign"}
    row = keys["zero_sign"]["polars"]["row"]
    assert row["class"] == "refines_up_to" and row["q"]["zeros"] == "canon"
    assert row["shim"] == "one_zero"


def test_options_rows_for_python():
    """`--options`' rows: choice, class, q (only what is not exact), shim,
    evidence and facts; the reference's tool; the profiles' versions."""
    out = subprocess.run(
        [str(checker_path()), "--options"], capture_output=True, text=True, check=True
    )
    tables = json.loads(out.stdout)
    assert tables["profiles"]["polars"]["versions"] == ["2.1.0"]
    assert {m["function"] for m in tables["profiles"]["polars"]["missing"]} >= {"md5"}
    rows = {(r["group"], r["option"]): r for r in tables["choices"]["polars"]}
    mod = rows[("int.mod", "division_type")]
    assert mod["choice"]["behaviours"] == ["FLOOR"] and mod["shim"] == "int_mod_trunc"
    duck = {(r["group"], r["option"]): r for r in tables["choices"]["duckdb"]}
    assert duck[("int.mod", "division_type")]["choice"]["behaviours"] == ["TRUNCATE"]
    ref = {(r["group"], r["option"]): r for r in tables["choices"]["reference"]}
    assert ref[(None, "overflow")]["tool"] == "raise" and ref[(None, "overflow")]["precondition"]
    assert ref[(None, "tie_order")]["tool"] == "open"
    assert ref[(None, "tie_order")]["q"] == {"rows": "multiset", "elements": "multiset"}
    assert ref[(None, "rounding")]["q"] == {}
    # Every engine row of the slice says how it relates to the reference.
    for engine in ("duckdb", "polars"):
        for r in tables["choices"][engine]:
            if r["choice"]["kind"] != "loose":
                assert {"class", "q", "shim", "facts"} <= set(r), (engine, r)
    zero = {(r["group"], r["option"]): r for r in tables["choices"]["polars"]}[(None, "zero_sign")]
    assert (zero["class"], zero["q"]) == ("refines_up_to", {"zeros": "canon"})


def test_contract_reports_its_dependencies(tmp_path):
    path = tmp_path / "contract.json"
    plan = lift("SELECT a * a AS x FROM t ORDER BY x", STRINGS).plan
    path.write_text(json.dumps({"transform": plan, "ensures": []}))
    out = subprocess.run(
        [str(checker_path()), "--contract", str(path)], capture_output=True, text=True
    )
    report = json.loads(out.stdout)
    assert report["profile"] == "reference"
    depends = {(d["group"], d["option"]): d["behaviours"] for d in report["depends"]}
    assert depends[("int.arith", "overflow")] == ["ERROR"]
    assert depends[("rel.sort", "null_order")] == ["NULLS_LAST"]


def test_contract_epsilon_per_double_aggregate(monkeypatch):
    """B1: a float `SUM`/`AVG` row is `approx` with `{"floats": {"bound":
    "plan"}}`; `--contract` gives each such output column its bound, from
    the bounds and row caps the preconditions state (#85)."""
    import sverify as sv
    from sverify import contracts

    seen: dict[str, str] = {}
    run = contracts.run_checker

    def spy(args, stdin):
        out = run(args, stdin)
        seen["out"] = out[1]
        return out

    monkeypatch.setattr(contracts, "run_checker", spy)
    t = ibis.table({"k": "int64", "x": "float64"}, name="t")
    sv.verify(
        t.group_by("k").aggregate(total=t.x.sum(), mean=t.x.mean(), n=t.x.count()),
        requires={"t": [ibis._.x.between(-1e6, 1e6), sv.max_rows(1_000_000)]},
    )
    eps = json.loads(seen["out"])["epsilon"]
    assert set(eps) == {"total", "mean"}
    # About twice γ(n)·n·B: 2 · 10⁶ · 2⁻⁵³ · 10⁶ · 10⁶.
    assert 200 < eps["total"]["abs"] < 250
    assert 2e-4 < eps["mean"]["abs"] < 2.5e-4
    assert "rel" not in eps["total"]  # ±10⁶ can cancel
    assert eps["total"]["proved"] == {"abs": False}
    out = subprocess.run(
        [str(checker_path()), "--options"], capture_output=True, text=True, check=True
    )
    rows = {(r["group"], r["option"]): r for r in json.loads(out.stdout)["choices"]["polars"]}
    assert rows[(None, "sum_order")]["q"] == {"floats": {"bound": "plan"}}


def test_rerun_variation():
    """D20: what two runs of an engine may differ in, next to its `q`; absent
    where every run gives the same result."""
    out = subprocess.run(
        [str(checker_path()), "--options"], capture_output=True, text=True, check=True
    )
    choices = json.loads(out.stdout)["choices"]
    polars = {(r["group"], r["option"]): r for r in choices["polars"]}
    duck = {(r["group"], r["option"]): r for r in choices["duckdb"]}
    assert polars[(None, "sum_order")]["rerun"] == {"floats": {"bound": "plan"}}
    assert polars[(None, "tie_order")]["rerun"] == {"rows": "ties permuted"}
    assert duck[(None, "sum_order")]["rerun"] == {"floats": {"bound": "plan"}}
    assert "rerun" not in polars[(None, "tie_pick")]  # input order on streaming
    assert "rerun" not in duck[(None, "overflow")]
