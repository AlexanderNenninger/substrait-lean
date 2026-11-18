"""`Report.to_substrait` and `sv.Report.from_substrait` (#664): the export of a
verified plan for any Substrait consumer, with its contract as metadata.

The round trips export, read back and prove the contract again."""

from __future__ import annotations

import json
import re
from pathlib import Path
from typing import Literal

import ibis
import pyarrow as pa
import pytest
from ibis import _

import sverify as sv
from _repo import needs_repo
from sverify import substrait_export as se
from sverify.engine import connect, put_table
from sverify.errors import PreconditionError
from sverify.substrait_export import ExportError, read

ROOT = Path(__file__).resolve().parents[2]

orders = ibis.table(
    {"id": "int64", "amount": "int64", "x": "float64", "d": "decimal(10,2)"}, name="orders"
)
other = ibis.table({"k": "float64", "w": "int64"}, name="other")
BOUNDED = {"orders": [_.amount >= 0, _.amount < 1000]}

NAN = float("nan")
DATA = {
    "orders": pa.table(
        {
            "id": [1, 2, 2, 3, 4, 4],
            "amount": [5, 7, 0, 9, 1, 2],
            "x": [1.5, -0.0, 0.0, NAN, NAN, 2.5],
            "d": pa.array([1, 2, 3, 4, 5, 6], pa.decimal128(10, 2)),
        }
    ),
    "other": pa.table({"k": [0.0, NAN, 2.5], "w": [10, 20, 30]}),
}


def _verify(expr, requires=None, ensures=(), **kw) -> sv.Report:
    report = sv.verify(expr, requires=requires, ensures=list(ensures), **kw)
    assert report.verdict in (sv.Verdict.PROVED, sv.Verdict.PROVED_WITH_CHECKS), str(report)
    return report


# -- the plan -------------------------------------------------------------------


def test_calls_name_urn_compound_name_and_type() -> None:
    """Each call declares its YAML's URN and compound name, and states its
    output type; the plan says which Substrait version it is."""
    report = _verify(orders.select(orders.id, total=_.amount + 1, m=_.amount % 3), BOUNDED)
    plan = read(report.to_substrait()).plan
    urns = {u["extensionUrnAnchor"]: u["urn"] for u in plan["extensionUrns"]}
    names = {
        e["extensionFunction"]["name"]: urns[e["extensionFunction"]["extensionUrnReference"]]
        for e in plan["extensions"]
    }
    assert names == {
        "add:i64_i64": "extension:io.substrait:functions_arithmetic",
        "modulus:i64_i64": "extension:io.substrait:functions_arithmetic",
    }
    assert plan["version"]["minorNumber"] == 106
    assert '"outputType"' in json.dumps(plan)


def test_pins_the_options_the_proof_uses() -> None:
    """`overflow` and `division_type` are pinned at the reference's
    behaviour, in each call's options and in the manifest."""
    report = _verify(orders.select(m=_.amount % 3, t=_.amount + 1), BOUNDED)
    imp = read(report.to_substrait())
    pinned = {(p["group"], p["option"]): p["values"] for p in imp.manifest["pinned"]}
    assert pinned[("int.arith", "overflow")] == ["ERROR"]
    assert pinned[("int.mod", "division_type")] == ["TRUNCATE"]
    text = json.dumps(imp.plan)
    assert '{"name": "division_type", "preference": ["TRUNCATE"]}' in text
    # The reference raises at `y = 0`, and `% 3` never meets it.
    assert any(u["option"] == "on_division_by_zero" for u in imp.manifest["unexercised"])


def test_manifest() -> None:
    """The manifest names the semantics, the versions, the URNs and the class."""
    report = _verify(orders.select(t=_.amount + 1), BOUNDED, ensures=[_.t >= 1])
    m = read(report.to_substrait()).manifest
    assert m["format"] == se.FORMAT
    assert m["substrait"] == "0.106.0"
    assert m["semantics"] == "reference"
    assert m["class"] == "exact"
    assert m["shims_mode"] == "apply"
    assert m["extension_urns"] == ["extension:io.substrait:functions_arithmetic"]


def test_contract_travels_with_the_plan() -> None:
    """`requires`, declared and inferred, and `ensures`, each as text and as
    a Substrait plan over the inputs."""
    expr = orders.select(orders.id, total=_.amount * 2)
    report = _verify(
        expr,
        {"orders": [_.amount >= 0, sv.unique("id")]},
        ensures=[_.total >= 0, sv.unique("id")],
        on_inferred="warn",
    )
    imp = read(report.to_substrait())
    texts = [r["text"] for r in imp.requires]
    assert "(_.amount >= 0)" in texts
    assert any(r.get("inferred") for r in imp.requires), texts  # the bound on `amount`
    assert [e["text"] for e in imp.ensures] == ["(_.total >= 0)", "unique(id)"]
    row = imp.ensures[0]
    assert row["kind"] == "row" and row["proved"]
    assert row["plan"]["relations"][0]["root"]["names"] == ["(_.total >= 0)"]
    assert imp.ensures[1]["kind"] == "Unique"


def test_sidecar_is_the_embedded_contract() -> None:
    report = _verify(orders.select(t=_.amount + 1), BOUNDED, ensures=[_.t >= 1])
    sidecar = report.substrait_contract()
    imp = read(report.to_substrait())
    assert sidecar["manifest"] == imp.manifest
    assert [c["text"] for c in sidecar["ensures"]] == [c["text"] for c in imp.ensures]


# -- round trips ------------------------------------------------------------------

ROUND_TRIPS = {
    "integers": (
        orders.select(orders.id, total=_.amount + 1, m=_.amount % 3),
        BOUNDED,
        [_.total >= 1],
    ),
    "doubles": (orders.select(orders.id, y=_.x / 2.0), None, []),
    "aggregate": (
        orders.group_by("id").aggregate(s=_.amount.sum(), m=_.amount.mean()).order_by("id"),
        BOUNDED,
        [sv.unique("id")],
    ),
    "decimals": (orders.select(q=_.d * _.d), None, []),
    "double keys": (orders.group_by("x").aggregate(n=_.id.count()), None, []),
}


@pytest.mark.parametrize("fmt", ["json", "binary"])
@pytest.mark.parametrize("case", list(ROUND_TRIPS))
def test_round_trip(case: str, fmt: Literal["json", "binary"]) -> None:
    """Export, import and prove again: the same plan, the same contract and
    the same verdict."""
    expr, requires, ensures = ROUND_TRIPS[case]
    report = _verify(expr, requires, ensures)
    out = report.to_substrait(fmt)
    again = sv.Report.from_substrait(out)
    # The exported plan carries the `+ 0.0` shims of the double keys, whose
    # overflow the import assumes and checks on the data.
    expected = sv.Verdict.PROVED_WITH_CHECKS if case == "double keys" else report.verdict
    assert again.verdict == expected
    assert [(c.label, c.proved) for c in again.ensures] == [
        (c.label, c.proved) for c in report.ensures
    ]
    assert again.requires == {t: cs for t, cs in report.requires.items() if cs}
    assert again._exact == report._exact
    # The canon shim the export writes above a double key's pick reads the
    # picked value, which the class level's first stage admits only as a
    # bare column (D48): the import is determined exactly as before, and at
    # the class level only once the congruence check covers the shim.
    assert again.deterministic == (report.deterministic and case != "double keys")
    # The same plan: reading it back and writing it again gives the bytes.
    imp = read(out)
    assert again.internal_plan is not None
    assert json.loads(again.internal_plan) == imp.plan


def test_from_substrait_needs_the_contract() -> None:
    with pytest.raises(ValueError, match="no sverify contract"):
        sv.Report.from_substrait('{"relations": []}')


# -- refusals ---------------------------------------------------------------------


def test_unproved_plan_is_refused() -> None:
    report = sv.verify(orders.select(t=_.amount + 1), ensures=[_.t >= 1])
    with pytest.raises(ExportError, match="not verified"):
        report.to_substrait()


def test_engine_profile_is_refused() -> None:
    report = sv.verify("SELECT id FROM orders", tables={"orders": orders}, semantics="duckdb")
    with pytest.raises(ExportError, match="semantics='reference'"):
        report.to_substrait()


def test_st10_refuses_in_every_mode() -> None:
    t = ibis.table({"s": "string"}, name="t")
    report = _verify(t.select(u=_.s.upper()))
    for mode in se.SHIMS:
        with pytest.raises(ExportError, match="ST-10"):
            report.to_substrait(shims=mode)


def test_function_outside_the_yamls_is_refused() -> None:
    t = ibis.table({"s": "string"}, name="t")
    report = _verify(t.select(h=_.s.levenshtein("a")))
    with pytest.raises(ExportError, match="not a function of Substrait's YAMLs"):
        report.to_substrait()


def test_bad_arguments() -> None:
    report = _verify(orders.select(t=_.amount + 1), BOUNDED)
    with pytest.raises(ValueError, match="format"):
        report.to_substrait("yaml")  # type: ignore[arg-type]
    with pytest.raises(ValueError, match="shims"):
        report.to_substrait(shims="maybe")  # type: ignore[arg-type]


# -- the shim modes -----------------------------------------------------------------

#: A gap per shim, the plan that meets it and the option.
GAP_CASES = {
    "ST-3": (orders.group_by("id").aggregate(v=_.amount.var()), None, "stat_degenerate"),
    "ST-4 keys": (orders.group_by("x").aggregate(n=_.id.count()), None, "nan_equality"),
    "ST-4 join": (orders.join(other, orders.x == other.k).select("id", "w"), None, "nan_equality"),
}


@pytest.mark.parametrize("case", list(GAP_CASES))
def test_apply_rewrites_the_gap(case: str) -> None:
    expr, requires, option = GAP_CASES[case]
    m = read(_verify(expr, requires).to_substrait(shims="apply")).manifest
    # D30: a consumer's own variance is within the plan's bound of the
    # reference's exact moments rounded once.
    assert m["class"] == ("observed" if case == "ST-3" else "exact")
    assert any(s["option"] == option for s in m["shims"]), m["shims"]
    assert not m["assumptions"]


@pytest.mark.parametrize("case", list(GAP_CASES))
def test_annotate_ships_the_assumption(case: str) -> None:
    expr, requires, option = GAP_CASES[case]
    report = _verify(expr, requires)
    m = read(report.to_substrait(shims="annotate")).manifest
    assert m["class"] == "assumed"
    assert not [s for s in m["shims"] if s.get("source") != "written plan"]
    [found] = [a for a in m["assumptions"] if a["option"] == option][:1]
    assert found["gap"] == "ST-3" if option == "stat_degenerate" else "ST-4"
    # The plan is the written one: it calls no shim's functions.
    assert (
        "is_nan" not in json.dumps(read(report.to_substrait(shims="annotate")).plan)
        or case == "ST-4 keys"
    )


@pytest.mark.parametrize("case", list(GAP_CASES))
def test_refuse_names_the_gap(case: str) -> None:
    expr, requires, option = GAP_CASES[case]
    gap = "ST-3" if option == "stat_degenerate" else "ST-4"
    with pytest.raises(ExportError, match=re.escape(f"({gap}, upstream/bugs/{gap}.json)")):
        _verify(expr, requires).to_substrait(shims="refuse")


def test_gaps_where_the_reference_raises_need_no_shim() -> None:
    """ST-1: the reference raises on a shift count outside [0, 63], and the
    proof rules it out: every mode exports, with the choice unexercised."""
    report = _verify(orders.select(u=_.amount << 2), BOUNDED)
    for mode in se.SHIMS:
        m = read(report.to_substrait(shims=mode)).manifest
        [u] = [u for u in m["unexercised"] if u["option"] == "shift_range"]
        assert u["gap"] == "ST-1"


@needs_repo
def test_gaps_name_existing_entries() -> None:
    for gap in {*se.GAPS.values(), *se.FUNCTION_GAPS.values()}:
        doc = json.loads((ROOT / "upstream" / "bugs" / f"{gap}.json").read_text())
        assert doc["kind"] == "spec-gap", gap


# -- the generated table and the .proto ------------------------------------------------


@needs_repo
def test_extension_table_is_fresh() -> None:
    """`_substrait_extensions.json` is what the YAMLs at the pinned tag give
    (`python -m sverify_dev.substrait_extensions --write`)."""
    from sverify_dev import substrait_cases, substrait_extensions

    ext = substrait_cases.CACHE / "extensions"
    if not ext.is_dir():
        pytest.skip("the Substrait YAMLs are not fetched (python -m sverify_dev.substrait_cases)")
    assert substrait_extensions.TABLE.read_text() == substrait_extensions.render(
        substrait_extensions.build(ext)
    )


def test_proto_file_matches_the_messages() -> None:
    contract, condition = se._messages()
    text = (Path(se.__file__).parent / "substrait_contract.proto").read_text()
    declared = {
        (msg, name, int(num))
        for msg, body in re.findall(r"message (\w+) \{(.*?)\n\}", text, re.S)
        for name, num in re.findall(r"^\s+(?:repeated )?[\w.]+ (\w+) = (\d+);", body, re.M)
    }
    built = {
        (cls.DESCRIPTOR.name, f.name, f.number)
        for cls in (contract, condition)
        for f in cls.DESCRIPTOR.fields
    }
    assert declared == built
    assert f"type.googleapis.com/{contract.DESCRIPTOR.full_name}" == se.TYPE_URL


# -- The preconditions of a re-read report are checked on the data (#1513) --------

RO = ibis.table({"id": "int64", "amt": "int64"}, name="o")


def _imported(requires, ensures, expr=None):
    report = sv.verify(
        expr if expr is not None else RO.select("id", y=RO.amt),
        requires={"o": requires},
        ensures=ensures,
    )
    return report, sv.Report.from_substrait(report.to_substrait())


def _o(rows):
    con = connect()
    put_table(
        con,
        "o",
        pa.table(
            {
                "id": pa.array([r[0] for r in rows], pa.int64()),
                "amt": pa.array([r[1] for r in rows], pa.int64()),
            }
        ),
    )
    return con


@pytest.mark.parametrize("engine", ["duckdb", "polars"])
def test_a_report_read_back_checks_its_row_preconditions(engine):
    report, back = _imported([_.amt > 0], [_.y > 0])
    assert [str(c) for c in back._conditions["o"]] and len(back._conditions["o"]) == len(
        back.requires["o"]
    )
    bad = _o([(1, 5), (2, 0)])
    for r in (report, back):
        with pytest.raises(PreconditionError, match="refused before the run"):
            r.run(bad, engine)
    assert back.run(_o([(1, 5), (2, 7)]), engine).num_rows == 2


@pytest.mark.parametrize("engine", ["duckdb", "polars"])
def test_a_report_read_back_checks_its_unique_precondition(engine):
    report, back = _imported([sv.unique("id")], [sv.unique("id")])
    bad = _o([(1, 5), (1, 6)])
    for r in (report, back):
        with pytest.raises(PreconditionError, match="refused before the run"):
            r.run(bad, engine)


@pytest.mark.parametrize("engine", ["duckdb", "polars"])
def test_a_report_read_back_does_not_drop_guards_on_unchecked_data(engine):
    """`100 // amt` with `amt` in 1..1000 declared: the batch with `amt = 0` is refused
    by the precondition, not by the engine's own error or a NULL."""
    expr = RO.select("id", q=100 // RO.amt)
    _unused, back = _imported([_.amt.notnull(), _.amt.between(1, 1000)], [_.q >= 0], expr)
    with pytest.raises(PreconditionError, match="refused before the run"):
        back.run(_o([(1, 5), (2, 0)]), engine)


def test_every_report_with_requires_has_a_check_for_each():
    for case, (expr, requires, ensures) in ROUND_TRIPS.items():
        report = _verify(expr, requires, ensures)
        for r in (report, sv.Report.from_substrait(report.to_substrait())):
            assert r._unchecked_requires() == [], case


def test_a_report_with_a_precondition_it_cannot_check_refuses_to_run():
    _unused, back = _imported([_.amt > 0], [_.y > 0])
    back._conditions = {}
    with pytest.raises(PreconditionError, match="no run-time check"):
        back.run(_o([(1, 5)]), "duckdb")


@needs_repo
def test_a_condition_over_another_relation_is_refused() -> None:
    """`from_substrait` proves an export's postconditions over the exported
    plan; a condition whose plan reads another relation (a join's select
    that Ibis merged, before #1484) is refused with an error that says to
    export again."""
    import copy

    from sverify.substrait_export import _lean_plan, _over, read

    fixture = Path(__file__).parent / "formats" / "main-3f971d1e" / "substrait"
    imp = read((fixture / "row_and_table.json").read_text())
    plan = _lean_plan(imp.plan)
    cond = _lean_plan(next(e for e in imp.ensures if e.get("kind") == "row")["plan"])
    assert (
        _over(plan, cond, "c")["relations"][0]["root"]["input"]["project"]["input"]
        == (plan["relations"][0]["root"]["input"])
    )
    other = copy.deepcopy(cond)
    project = other["relations"][0]["root"]["input"]["project"]
    project["input"] = project["input"]["project"]["input"]
    with pytest.raises(ValueError, match="export it with this version"):
        _over(plan, other, "c")
